"""Zhu's reduced window form with an out-of-band envelope, assembled in Arb.

Window [-L, L], even real f, basis T_n(x) = Pbar_n(x/L)/sqrt(L), n = 0, 2, ...,
2N-2 (orthonormal), with Fourier transforms (Zhu, arXiv:2608.24827, eq. (6))

    That_n(t) = (-1)^{n/2} 2 sqrt(L nu_n) j_n(tL),   nu_n = n + 1/2.

The reduced form at split T# (Zhu eq. (4), with Psi_L replaced by Psi_L + H):

    R(T#) = 2 p p^T + C_Psi(T#) + C_H(T#) + beta*(T#) (I - G(T#)),
    C_X(T)  = (1/pi) int_0^T X(t) That_n That_m dt,
    G(T)    = (1/pi) int_0^T That_n That_m dt,
    beta*(T) = log(T / 2 pi) - 1/T - S,

with Psi_L(t) = Re digamma(1/4 + it/2) - log pi - P_L(t), p_n = int T_n cosh(x/2)
= 2 sqrt(L nu_n) i_n(L/2), S = A_L when H = 0 and S = sum_p M_p (envelope.json)
otherwise. Q(f) >= R(T#)(f) needs beta*(T#) > 0 and P_L - H <= S on
[T#, infinity) (Lemma 3.1 of Zhu with A_L -> S; see MISSION.md).

Integrals over [0, Tmax] by Gauss-Legendre panels in Arb; C_X and G are
accumulated panel by panel, so one pass gives R at every checkpoint T#. The
quadrature error, the Legendre tail and the coupling bounds are NOT included
here: every lambda_min printed by this script is a measured value, one route.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, arb_mat, ctx, fmpq

HERE = Path(__file__).resolve().parent


def to_arb(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def prime_powers(L: Fraction):
    """(n, 2 Lambda(n)/sqrt(n) as arb, log n as arb) for log n < 2L, decided in Arb."""
    twoL = 2 * to_arb(L)
    out = []
    for n in range(2, int(math.exp(2 * float(L))) + 3):
        p = next(q for q in range(2, n + 1) if n % q == 0)
        m = n
        while m % p == 0:
            m //= p
        if m != 1:
            continue
        ln = arb(n).log()
        if bool(ln < twoL):
            out.append((n, 2 * arb(p).log() / arb(n).sqrt(), ln))
        elif not bool(ln > twoL):
            raise RuntimeError(f"undecided log {n} vs 2L")
    return out


def load_envelope(L: Fraction, kind: str, D: int):
    d = json.loads((HERE / "envelope.json").read_text())
    for r in d["runs"]:
        if Fraction(r["L"]) == L and r["kernel"] == kind and r["D"] == D:
            S = Fraction(r["S"])
            terms = []  # (log p, [(k, b_k)])
            for pr in r["primes"]:
                terms.append((pr["p"], [(int(k), Fraction(v)) for k, v in pr["b"].items()]))
            return S, terms
    raise KeyError((L, kind, D))


class Symbol:
    def __init__(self, L: Fraction, envs: dict):
        self.pp = prime_powers(L)
        self.A_L = sum((c for _, c, _ in self.pp), arb(0))
        self.logpi = arb.pi().log()
        self.envs = {}
        for name, (S, terms) in envs.items():
            self.envs[name] = (to_arb(S), [(arb(p).log(), [(k, to_arb(b)) for k, b in bs]) for p, bs in terms])

    def psi(self, t: arb) -> arb:
        v = acb(arb(1) / 4, t / 2).digamma().real - self.logpi
        for _, c, ln in self.pp:
            v -= c * (t * ln).cos()
        return v

    def H(self, name: str, t: arb) -> arb:
        _, terms = self.envs[name]
        tot = arb(0)
        for lp, bs in terms:
            if not bs:
                continue
            kmax = bs[-1][0]
            c1 = (t * lp).cos()
            ck = {0: arb(1), 1: c1}
            for k in range(2, kmax + 1):
                ck[k] = 2 * c1 * ck[k - 1] - ck[k - 2]
            for k, b in bs:
                tot += b * ck[k]
        return tot


def sph_j_all(K: int, x: arb, seed_every: int = 16) -> list[arb]:
    """j_0..j_K at x > 0 by the downward recurrence j_{n-1} = (2n+1)/x j_n - j_{n+1},
    re-seeded with two Arb Bessel values every `seed_every` steps wherever
    n < x + 20. In that oscillatory range the Arb radius of the recurrence
    grows geometrically (it follows |c| r_n + r_{n+1}), so without re-seeding
    the enclosures become useless at large x; re-seeding caps the growth."""
    half = arb(1) / 2
    if not x.is_exact():
        raise ValueError("sph_j_all needs an exact argument (arb amplifies input radius ~e^x)")

    def exact(n):
        # arb's Bessel J loses accuracy at large order for moderate x unless the
        # working precision is raised; the result is a valid ball either way.
        p0 = ctx.prec
        ctx.prec = p0 + 512
        try:
            v = x.bessel_j(arb(n) + half) * (arb.pi() / (2 * x)).sqrt()
        finally:
            ctx.prec = p0
        return v

    out = [arb(0)] * (K + 1)
    out[K], out[K - 1] = exact(K), exact(K - 1)
    xf = float(x.mid())
    n, since = K - 1, 0          # out[n], out[n+1] known; produce out[n-1]
    while n >= 1:
        if n - 1 < xf + 20 and since >= seed_every and n >= 2:
            out[n - 1], out[n - 2] = exact(n - 1), exact(n - 2)
            n -= 2
            since = 0
            continue
        out[n - 1] = (2 * n + 1) / x * out[n] - out[n + 1]
        n -= 1
        since += 1
    return out


def ldl_inertia(A: list[list[arb]]):
    """LDL^T without pivoting in Arb. Returns (n_neg, n_pos, n_undecided, pivots)."""
    n = len(A)
    a = [row[:] for row in A]
    piv = []
    for k in range(n):
        d = a[k][k]
        piv.append(d)
        if not (bool(d > 0) or bool(d < 0)):
            return None, None, n - k, piv
        inv = 1 / d
        for i in range(k + 1, n):   # lower triangle only; column k is read, not written
            li = a[i][k] * inv
            ai = a[i]
            for j in range(k + 1, i + 1):
                ai[j] -= li * a[j][k]
    neg = sum(1 for d in piv if bool(d < 0))
    return neg, n - neg, 0, piv


def lam_min_inverse(R: arb_mat, iters: int = 4):
    n = R.nrows()
    x = arb_mat(n, 1, [arb(1) / (1 + i) for i in range(n)])
    for _ in range(iters):
        y = R.solve(x)
        nrm = sum((y[i, 0] ** 2 for i in range(n)), arb(0)).sqrt()
        x = arb_mat(n, 1, [y[i, 0] / nrm for i in range(n)])
    Rx = R * x
    return sum((x[i, 0] * Rx[i, 0] for i in range(n)), arb(0))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", default="4/5")
    ap.add_argument("--N", type=int, default=200, help="number of even Legendre modes")
    ap.add_argument("--Tmax", type=float, default=200)
    ap.add_argument("--h", default="1/2", help="panel width")
    ap.add_argument("--q", type=int, default=32, help="Gauss-Legendre nodes per panel")
    ap.add_argument("--prec", type=int, default=192)
    ap.add_argument("--env", nargs="*", default=["sine:32"], help="kernel:D entries of envelope.json")
    ap.add_argument("--checks", nargs="*", type=float, default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    ctx.prec = args.prec
    L = Fraction(args.L)
    La = to_arb(L)
    h = Fraction(args.h)
    npan = int(round(args.Tmax / float(h)))
    Tmax = h * npan
    envs = {e: load_envelope(L, *(e.split(":")[0], int(e.split(":")[1]))) for e in args.env}
    sym = Symbol(L, envs)
    N = args.N
    K = 2 * N - 1
    nus = [arb(2 * i) + arb(1) / 2 for i in range(N)]
    scale = [(-1) ** i * 2 * (La * nu).sqrt() for i, nu in enumerate(nus)]
    # pole vector p_n = 2 sqrt(L nu_n) i_n(L/2)
    a = La / 2
    sa = (arb.pi() / (2 * a)).sqrt()
    pvec = [2 * (La * nu).sqrt() * a.bessel_i(nu) * sa for nu in nus]
    P2 = arb_mat(N, N, [2 * pvec[i] * pvec[j] for i in range(N) for j in range(N)])
    gl = [arb.legendre_p_root(args.q, k, weight=True) for k in range(args.q)]
    checks = sorted(set(args.checks or [float(Tmax)]))
    check_panels = {min(npan, max(1, int(round(c / float(h))))) for c in checks}
    names = ["G", "Psi"] + [f"H:{e}" for e in args.env]
    acc = {nm: arb_mat(N, N) for nm in names}
    ha = to_arb(h)
    t0 = time.time()
    results = []
    node_shift = 0.0
    for k in range(npan):
        a0 = ha * k
        V = []
        wts = {nm: [] for nm in names}
        for x, w in gl:
            t_gl = a0 + ha * (1 + x) / 2
            xl = arb((t_gl * La).mid())       # exact dyadic Bessel argument
            t = xl / La                        # node actually used, |t - t_gl| ~ 2^-prec
            node_shift = max(node_shift, float(abs(t - t_gl).upper()))
            ww = w * ha / 2 / arb.pi()
            j = sph_j_all(K, xl)
            V.append([scale[i] * j[2 * i] for i in range(N)])
            wts["G"].append(ww)
            wts["Psi"].append(ww * sym.psi(t))
            for e in args.env:
                wts[f"H:{e}"].append(ww * sym.H(e, t))
        Vt = arb_mat(N, args.q, [V[c][r] for r in range(N) for c in range(args.q)])
        VtT = Vt.transpose()
        for nm in names:
            Ws = arb_mat(N, args.q, [V[c][r] * wts[nm][c] for r in range(N) for c in range(args.q)])
            acc[nm] += Ws * VtT
        if (k + 1) in check_panels:
            T = ha * (k + 1)
            Tf = float(T.mid())
            row = {"T": Tf, "elapsed": time.time() - t0, "node_shift": node_shift}
            I = arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
            variants = [("none", sym.A_L, None)] + [(e, sym.envs[e][0], f"H:{e}") for e in args.env]
            for vname, S, hk in variants:
                beta = (T / (2 * arb.pi())).log() - 1 / T - S
                R = P2 + acc["Psi"] + beta * (I - acc["G"])
                if hk:
                    R = R + acc[hk]
                rec = {"beta": float(beta.mid())}
                if bool(beta > 0):
                    try:
                        lam = lam_min_inverse(R)
                    except ZeroDivisionError:
                        lam = arb("nan")
                    rows = [[R[i, j] for j in range(N)] for i in range(N)]
                    neg, pos, und, _ = ldl_inertia(rows)
                    rec.update(lam=float(lam.mid()), lam_rad=float(lam.rad()), n_neg=neg, undecided=und)
                row[vname] = rec
            gdiag = [float(acc["G"][i, i].mid()) for i in (0, 1, N // 2, N - 1)]
            row["G_diag"] = gdiag
            results.append(row)
            print(json.dumps(row))
            sys.stdout.flush()
            if args.out:
                Path(args.out).write_text(json.dumps({"rows": results}, indent=1))
    meta = {"L": str(L), "N": N, "Tmax": float(Tmax), "h": str(h), "q": args.q, "prec": args.prec,
            "env": args.env, "A_L": float(sym.A_L.mid()),
            "S": {e: str(envs[e][0]) for e in args.env}, "grade": "measured (no quadrature/tail bound)"}
    if args.out:
        Path(args.out).write_text(json.dumps({"meta": meta, "rows": results}, indent=1))
    print(f"done {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()
