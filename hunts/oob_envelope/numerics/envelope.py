"""Per-prime out-of-band envelope for the prime comb, with Arb enclosures.

For supp f in [-L, L] the prime comb of Zhu (arXiv:2608.24827, eq. (3)) is
P_L(t) = sum_p phi_p(t log p), with

    phi_p(theta) = sum_{k <= m_p} 2 t_{p,k} cos(k theta),
    t_{p,k} = log p / p^{k/2},   m_p = max{k : k log p < 2L}.

Terms cos(k theta) with k > m_p have t-frequency k log p >= 2L, so they are
invisible to the window form. This script builds, per prime,

    Phi_p(theta) = M_p - phi_p(theta) + h_p(theta),
    h_p(theta)   = sum_{m_p < k <= D} b_{p,k} cos(k theta),

with exact dyadic b_{p,k} and an exact rational M_p, and proves Phi_p >= 0
twice:

  (a) Decomposition. Phi_p = (mu * K) + R, where K = |q(e^{ix})|^2 / |q|^2
      is a nonnegative kernel with exact dyadic q, mu = sum_j a_j
      (delta_{theta_j} + delta_{-theta_j}) / 2 with dyadic a_j >= 0 and
      dyadic nodes, and R = r_0 + sum_k r_k cos(k theta) is the residual,
      every r_k an Arb ball. M_p is chosen >= sum a_j + sum |r_k| + eta, so
      Phi_p >= eta. Only the sign of an explicit sum is used.
  (b) Scan. Adaptive bisection of [0, pi] with the bound
      Phi(theta) >= Phi(c) - r |Phi'(c)| - r^2 B2 / 2,  B2 = sum k^2 |coef_k|,
      evaluated in Arb. Independent of (a): it reads only the coefficients.

Then P_L - H <= S := sum_p M_p for every real t, with H(t) = sum_p h_p(t log p).
The float step (roots and weights of the Caratheodory-Toeplitz extremal
measure) only proposes the data; neither proof depends on its accuracy.

Also decided in Arb, per prime: log p < 2L, m_p log p < 2L < (m_p + 1) log p.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from flint import arb, ctx, fmpq

PREC = 256
ETA = Fraction(1, 10**8)          # margin added to every M_p
HERE = Path(__file__).resolve().parent


def to_arb(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def arb_upper_fraction(x: arb) -> Fraction:
    m, e = x.upper().man_exp()
    m, e = int(m), int(e)
    return Fraction(m) * (Fraction(2) ** e)


def certain_pos(x: arb) -> bool:
    return bool(x > 0)


def primes_upto(n: int) -> list[int]:
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, math.isqrt(p) + 1))]


def prime_set(L: Fraction):
    """Primes with log p < 2L and their m_p, decided in Arb. Returns list of
    dicts with the two gaps 2L - m log p > 0 and (m+1) log p - 2L > 0."""
    twoL = 2 * to_arb(L)
    out = []
    for p in primes_upto(int(math.exp(2 * float(L))) + 2):
        lp = arb(p).log()
        g = twoL - lp
        if certain_pos(-g):
            continue
        if not certain_pos(g):
            raise RuntimeError(f"undecided log {p} vs 2L")
        m = 1
        while certain_pos(twoL - (m + 1) * lp):
            m += 1
        lo, hi = twoL - m * lp, (m + 1) * lp - twoL
        if not (certain_pos(lo) and certain_pos(hi)):
            raise RuntimeError(f"undecided m_p for p={p}")
        out.append({"p": p, "m": m, "gap_below": float(lo.mid()), "gap_above": float(hi.mid())})
    return out


# ---------------------------------------------------------------- kernels

def kernel_q(kind: str, D: int) -> list[Fraction]:
    """Dyadic coefficients q_0..q_D; K(x) = |sum q_j e^{ijx}|^2 / sum q_j^2 >= 0."""
    if kind == "fejer":
        return [Fraction(1)] * (D + 1)
    if kind == "sine":  # maximises the first autocorrelation (Fejer-Korovkin)
        return [Fraction(math.sin(math.pi * (j + 1) / (D + 2))) for j in range(D + 1)]
    raise ValueError(kind)


def kernel_w(q: list[Fraction]) -> list[Fraction]:
    """Exact normalised autocorrelation w_0 = 1, ..., w_D: K = 1 + 2 sum w_k cos kx."""
    n2 = sum(x * x for x in q)
    D = len(q) - 1
    return [sum(q[j] * q[j + k] for j in range(D + 1 - k)) / n2 for k in range(D + 1)]


# ------------------------------------------------------- float proposal

def propose(p: int, m: int, wf: np.ndarray):
    """Extremal measure for Toeplitz(0, t_k / w_k): nodes theta_j, weights a_j."""
    t = np.array([math.log(p) / p ** (k / 2) for k in range(1, m + 1)])
    s = t / wf[1 : m + 1]
    first = np.concatenate([[0.0], s])
    T = np.array([[first[abs(i - j)] for j in range(m + 1)] for i in range(m + 1)])
    ev, V = np.linalg.eigh(T)
    lam = ev[-1]
    A = lam * np.eye(m + 1) - T
    w, U = np.linalg.eigh(A)
    u = U[:, 0]
    roots = np.roots(u[::-1])
    th = np.angle(roots)
    Ck = np.cos(np.outer(np.arange(m + 1), th))
    a = np.linalg.lstsq(Ck, A[:, 0], rcond=None)[0]
    a = np.clip(a, 0.0, None)
    return float(lam), [float(x) for x in th], [float(x) for x in a], float(np.max(np.abs(np.abs(roots) - 1)))


# ------------------------------------------------------------ the proof

def build_prime(p: int, m: int, D: int, w: list[Fraction]):
    wf = np.array([float(x) for x in w])
    lam_float, th, a, root_dev = propose(p, m, wf)
    lp = arb(p).log()
    t = [lp / arb(p) ** (arb(k) / 2) for k in range(1, m + 1)]
    wa = [to_arb(x) for x in w]
    th_a = [to_arb(Fraction(x)) for x in th]
    a_fr = [Fraction(x) for x in a]
    a_a = [to_arb(x) for x in a_fr]
    chat = [sum((aj * (k * tj).cos() for aj, tj in zip(a_a, th_a)), arb(0)) for k in range(D + 1)]
    # dyadic out-of-band coefficients
    b = {k: Fraction(float((2 * wa[k] * chat[k]).mid())) for k in range(m + 1, D + 1)}
    r = [None] + [-2 * t[k - 1] - 2 * wa[k] * chat[k] for k in range(1, m + 1)] + \
        [to_arb(b[k]) - 2 * wa[k] * chat[k] for k in range(m + 1, D + 1)]
    bound = sum(a_a, arb(0)) + sum((abs(x) for x in r[1:]), arb(0))
    Mp = arb_upper_fraction(bound) + ETA
    # round M_p up to 1e-15 for a readable rational
    Mp = Fraction(math.ceil(Mp * 10**15), 10**15)
    resid = float(sum((abs(x) for x in r[1:]), arb(0)).mid())
    return {
        "p": p, "m": m, "D": D, "lam_float": lam_float, "root_dev": root_dev,
        "M_p": Mp, "b": b, "sum_a": float(sum(a_fr)), "resid_l1": resid,
        "min_weight": min(a) if a else None,
    }


def phi_coeffs(p: int, m: int, Mp: Fraction, b: dict[int, Fraction], D: int) -> list[arb]:
    lp = arb(p).log()
    c = [to_arb(Mp)] + [arb(0)] * D
    for k in range(1, m + 1):
        c[k] = -2 * lp / arb(p) ** (arb(k) / 2)
    for k, v in b.items():
        c[k] = to_arb(v)
    return c


def _derivs(c: list[arb], x: arb):
    """Phi, Phi', Phi'' at x for Phi = sum c_k cos(k x), via the Chebyshev
    recurrences cos((k+1)x) = 2 cos x cos kx - cos((k-1)x) (same for sin)."""
    s1, c1 = x.sin_cos()
    ck, ckm = c1, arb(1)
    sk, skm = s1, arb(0)
    v, d1, d2 = c[0], arb(0), arb(0)
    for k in range(1, len(c)):
        v += c[k] * ck
        d1 -= c[k] * k * sk
        d2 -= c[k] * k * k * ck
        ck, ckm = 2 * c1 * ck - ckm, ck
        sk, skm = 2 * c1 * sk - skm, sk
    return v, d1, d2


def scan_min(c: list[arb], n0: int = 1024, rmin: float = 1e-14):
    """Lower bound for min over [0, pi] of sum c_k cos(k theta), by bisection.
    On [x - r, x + r]: Phi >= min_{|s|<=r} (Phi + Phi' s + Phi'' s^2 / 2) - B3 r^3 / 6,
    B3 = sum k^3 |c_k|. The quadratic minimum is taken exactly (in Arb)."""
    B3 = sum((abs(ck) * k * k * k for k, ck in enumerate(c)), arb(0))
    pi = arb.pi()
    stack = [(pi * i / n0, pi * (i + 1) / n0) for i in range(n0)]
    best = None
    evals = 0
    while stack:
        lo, hi = stack.pop()
        cc, rr = (lo + hi) / 2, (hi - lo) / 2
        val, der, d2 = _derivs(c, cc)
        evals += 1
        ends = [val + der * rr + d2 * rr * rr / 2, val - der * rr + d2 * rr * rr / 2]
        if certain_pos(d2) and certain_pos(rr * d2 - abs(der)):
            ends.append(val - der * der / (2 * d2))       # interior vertex
        elif not (certain_pos(-d2) or certain_pos(abs(der) - rr * abs(d2))):
            ends.append(val - abs(der) * rr - abs(d2) * rr * rr / 2)  # undecided: crude
        quad_min = ends[0]
        for e in ends[1:]:
            quad_min = quad_min.min(e)
        lower = quad_min - B3 * rr ** 3 / 6
        if certain_pos(lower):
            lb = float(lower.lower().mid())
            best = lb if best is None else min(best, lb)
            continue
        if float(rr.mid()) < rmin or certain_pos(-val):
            return {"ok": False, "at": float(cc.mid()), "val": float(val.mid()), "evals": evals}
        stack += [(lo, cc), (cc, hi)]
    return {"ok": True, "min_lower": best, "evals": evals}


def run(L: Fraction, kind: str, D: int, scan: bool = True):
    q = kernel_q(kind, D)
    w = kernel_w(q)
    ps = prime_set(L)
    rows = []
    S = Fraction(0)
    for pr in ps:
        res = build_prime(pr["p"], pr["m"], D, w)
        if scan:
            c = phi_coeffs(pr["p"], pr["m"], res["M_p"], res["b"], D)
            res["scan"] = scan_min(c)
            if not res["scan"]["ok"]:
                raise RuntimeError(f"scan failed p={pr['p']} L={L} {kind} D={D}: {res['scan']}")
        res.update(gap_below=pr["gap_below"], gap_above=pr["gap_above"])
        S += res["M_p"]
        rows.append(res)
    lp_max = max(math.log(r["p"]) for r in rows if r["b"])
    return {
        "L": str(L), "kernel": kind, "D": D, "S": S, "S_float": float(S),
        "max_freq": D * lp_max, "w1": float(w[1]), "primes": rows,
    }


def A_L(L: Fraction) -> float:
    ps = prime_set(L)
    return sum(2 * math.log(r["p"]) / r["p"] ** (k / 2) for r in ps for k in range(1, r["m"] + 1))


def S_inf(L: Fraction) -> float:
    tot = 0.0
    for r in prime_set(L):
        p, m = r["p"], r["m"]
        first = [0.0] + [math.log(p) / p ** (k / 2) for k in range(1, m + 1)]
        T = np.array([[first[abs(i - j)] for j in range(m + 1)] for i in range(m + 1)])
        tot += float(np.linalg.eigvalsh(T)[-1])
    return tot


def jsonable(res):
    out = dict(res)
    out["S"] = str(res["S"])
    prs = []
    for r in res["primes"]:
        r = dict(r)
        r["M_p"] = str(r["M_p"])
        r["b"] = {str(k): str(v) for k, v in r["b"].items()}
        prs.append(r)
    out["primes"] = prs
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", nargs="*", default=["4/5", "1", "119/100"])
    ap.add_argument("--D", nargs="*", type=int, default=[8, 16, 32, 64])
    ap.add_argument("--kernels", nargs="*", default=["sine", "fejer"])
    ap.add_argument("--no-scan", action="store_true")
    ap.add_argument("--out", default=str(HERE / "envelope.json"))
    args = ap.parse_args()
    ctx.prec = PREC
    t0 = time.time()
    table = []
    for Ls in args.L:
        L = Fraction(Ls)
        a, si = A_L(L), S_inf(L)
        print(f"L={float(L):.4f}  A_L={a:.6f}  S_inf(float)={si:.6f}  primes={[(r['p'], r['m']) for r in prime_set(L)]}")
        for kind in args.kernels:
            for D in args.D:
                res = run(L, kind, D, scan=not args.no_scan)
                scans = [r.get("scan", {}).get("min_lower") for r in res["primes"]]
                print(f"   {kind:5s} D={D:4d}  S={res['S_float']:.10f}  S-S_inf={res['S_float'] - si:.2e}"
                      f"  maxfreq={res['max_freq']:7.1f}  scan_min={['%.1e' % s if s else s for s in scans]}"
                      f"  resid={max(r['resid_l1'] for r in res['primes']):.1e}")
                sys.stdout.flush()
                res["A_L"], res["S_inf_float"] = a, si
                table.append(jsonable(res))
    Path(args.out).write_text(json.dumps({"prec_bits": PREC, "eta": str(ETA), "runs": table}, indent=1))
    print(f"wrote {args.out}  ({time.time() - t0:.1f} s)")


if __name__ == "__main__":
    main()
