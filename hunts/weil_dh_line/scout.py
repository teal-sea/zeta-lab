"""Stage-A scout of lambda_min(R_H) against T# (hunt weil_dh_line, #146).

Measured only. The reduced form is Zhu's (arXiv:2608.24827, eq. (4)) with the
symbol Psi_L replaced by Psi_L + H (hunts/oob_envelope theory, Theorem 1'):

    R(T#) = s p p^T + C(T#) + beta*(T#) (I - G(T#)),
    C(T)  = (1/pi) int_0^T (Psi_L + H)(t) That_n(t) That_m(t) dt,
    G(T)  = (1/pi) int_0^T That_n(t) That_m(t) dt,

on the Legendre basis T_n(x) = Pbar_n(x/L)/sqrt(L) of one parity sector:
even orders n = 0, 2, ..., 2N-2 or odd orders n = 1, 3, ..., 2N-1, with
|F|^2 = (sum_n c_n sigma_n j_n(tL))^2, sigma_n = (-1)^{floor(n/2)} 2 sqrt(L nu_n),
nu_n = n + 1/2. Pole term (functions with a pole at s = 1, zeta and Epstein):
s = +2 (even, 2 F(i/2)^2) or s = -2 (odd, -2 (int f sinh(x/2))^2), with
p_n = 2 sqrt(L nu_n) i_n(L/2); DH is entire, s = 0. beta*(T) is the margin
the archimedean lower bound leaves above the envelope constant S:

    zeta     log(T/2 pi) - 1/T - S                 (Zhu Lemma 3.1)
    dh       log(5T/2 pi) - 1/T - S                (Re psi(3/4 + it/2) >= log(t/2) - 1/t for t >= 2: Binet, PRICE.md item 7)
    epstein  log 23 + 2 log(T/2 pi) - 2/T - S      (both bounds)

H is a joint cluster envelope from joint.py (exact dyadic coefficients,
every frequency at least 2L) and S its whole-torus bound. Integrals by
Gauss-Legendre panels of width h in Arb, nodes snapped so that tL is an exact
dyadic. Spherical Bessel columns: "enclosed" is the routine of
hunts/oob_envelope/numerics/assemble.py (imported read-only, re-seeded every 16
orders so the Arb radius stays meaningful); "fast" seeds j_K and j_{K-1} with
Arb at raised precision and runs the downward recurrence on midpoints (no
radius tracking), which this module checks against "enclosed" at the largest
argument. No quadrature error, Legendre tail or coupling bound is computed:
every lambda here describes the N-mode block and is measured.

One unit = a contiguous range of panels; it writes the partial sums of C and G
(exact Arb midpoints, radii as floats) to a checkpoint file. The reducer sums
units in order and, at every checkpoint T# on a unit boundary, reports the
midpoint LDL inertia and the inverse-iteration eigenvalue nearest 0.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import pickle
import sys
import time
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, arb_mat, ctx

HERE = Path(__file__).resolve().parent
CACHE = Path(os.environ.get("WEIL_DH_LINE_CACHE", os.path.expanduser("~/.cache/zeta-lab/weil_dh_line")))
sys.path.insert(0, str(HERE))
import price  # noqa: E402

sys.path.insert(0, str(HERE.parent / "oob_envelope" / "numerics"))
from assemble import sph_j_all  # noqa: E402  (read-only reuse)
sys.path.pop(0)

_HALF = arb(1) / 2


def _seed(n: int, x: arb) -> arb:
    """j_n(x) from Arb's Bessel J at raised precision (as in assemble.py)."""
    p0 = ctx.prec
    extra = 512
    while True:
        with ctx.workprec(p0 + extra):
            v = x.bessel_j(arb(n) + _HALF)
            v = v * (arb.pi() / (2 * x)).sqrt()
        if (v.is_finite() and not v.is_zero() and v.rel_accuracy_bits() >= p0 - 8) or extra >= 8192:
            return v
        extra *= 2


def sph_j_fast(K: int, x: arb) -> list[arb]:
    """j_0..j_K at exact x > 0: Arb seeds at K and K-1, then the downward
    recurrence j_{n-1} = (2n+1)/x j_n - j_{n+1} on midpoints. The recurrence
    is stable downward (j_n is the minimal solution for n > x and neutral
    below), so the midpoints carry nearly the working precision; the radius
    is not tracked, so these values are measured, not enclosures."""
    if not x.is_exact():
        raise ValueError("needs an exact argument")
    out = [arb(0)] * (K + 1)
    out[K] = _seed(K, x).mid()
    out[K - 1] = _seed(K - 1, x).mid()
    for n in range(K - 1, 0, -1):
        out[n - 1] = ((2 * n + 1) * out[n] / x - out[n + 1]).mid()
    return out


def load_envelope(path: Path, with_kind: bool = False):
    """Joint envelope JSON written by price.py: clusters with primes, omega and
    dyadic h, the total bound S as an exact rational, and the comb kind."""
    d = json.loads(path.read_text())
    clusters = []
    for c in d["clusters"]:
        clusters.append((c["primes"], [tuple(k) for k in c["omega"]], [Fraction(x) for x in c["h"]]))
    if with_kind:
        return Fraction(d["S_exact"]), clusters, d.get("kind", "zeta")
    return Fraction(d["S_exact"]), clusters


class Symbol:
    """Psi_L(t) + H(t) in Arb. zeta: Re digamma(1/4 + it/2) - log pi - P_L(t) + H(t).
    dh: Re digamma(3/4 + it/2) + log(5/pi) - P_DH(t) + H(t) (no pole term; the
    normalization of oob_envelope/numerics/k2_modal.py). epstein (1,1,6):
    log 23 + [Re digamma(1/4 + it/2) - log pi] + [Re digamma(3/4 + it/2) - log pi]
    - P_Q(t) + H(t) (weil_propagation numerics s9.1)."""

    def __init__(self, L: Fraction, clusters, kind: str = "zeta"):
        self.L = L
        self.kind = kind
        self.second = False
        if kind == "zeta":
            self.a = arb(1) / 4
            self.shift = -arb.pi().log()
            self.comb = [(2 * price.w_arb(p, m), arb(n).log()) for n, p, m in price.prime_powers(L)]
        elif kind == "dh":
            self.a = arb(3) / 4
            self.shift = (arb(5) / arb.pi()).log()
            self.comb = [(c, arb(n).log()) for n, c in price.dh_comb(L)]
        elif kind == "epstein":
            self.a = arb(1) / 4
            self.second = True
            self.shift = arb(23).log() - 2 * arb.pi().log()
            self.comb = [(c, arb(n).log()) for n, c in price.epstein_comb(L)]
        else:
            raise ValueError(kind)
        self.clusters = []
        for primes, om, hs in clusters:
            logs = [arb(p).log() for p in primes]
            D = [max(abs(k[i]) for k in om) for i in range(len(primes))]
            self.clusters.append((logs, D, om, [price.to_arb(x) for x in hs]))

    def psi(self, t: arb) -> arb:
        v = acb(self.a, t / 2).digamma().real + self.shift
        if self.second:
            v += acb(arb(3) / 4, t / 2).digamma().real
        for c, ln in self.comb:
            v -= c * (t * ln).cos()
        return v

    def H(self, t: arb) -> arb:
        tot = arb(0)
        for logs, D, om, hs in self.clusters:
            tabs = []
            for li, Di in zip(logs, D):
                s1, c1 = (t * li).sin_cos()
                cs, ss = [arb(1), c1], [arb(0), s1]
                for j in range(2, Di + 1):
                    cs.append(2 * c1 * cs[-1] - cs[-2])
                    ss.append(2 * c1 * ss[-1] - ss[-2])
                tabs.append((cs, ss))
            for k, hk in zip(om, hs):
                re, im = arb(1), arb(0)
                for (cs, ss), ki in zip(tabs, k):
                    if ki == 0:
                        continue
                    c, s = cs[abs(ki)], ss[abs(ki)]
                    if ki < 0:
                        s = -s
                    re, im = re * c - im * s, re * s + im * c
                tot += hk * re
        return tot


def orders(N: int, parity: str) -> list[int]:
    return [2 * i + (0 if parity == "even" else 1) for i in range(N)]


def basis(L: Fraction, N: int, parity: str = "even"):
    La = price.to_arb(L)
    ns = orders(N, parity)
    nus = [arb(n) + _HALF for n in ns]
    scale = [(-1) ** (n // 2) * 2 * (La * nu).sqrt() for n, nu in zip(ns, nus)]
    a = La / 2
    pvec = [2 * (La * nu).sqrt() * a.bessel_i(nu) * (arb.pi() / (2 * a)).sqrt() for nu in nus]
    return La, scale, pvec


def unit(L: Fraction, env_path: Path, N: int, q: int, h: Fraction, k0: int, k1: int, prec: int,
         parity: str = "even", bessel: str = "fast"):
    """Partial sums over panels k0..k1-1 of C and G (see module docstring)."""
    ctx.prec = prec
    _, clusters, kind = load_envelope(env_path, with_kind=True)
    sym = Symbol(L, clusters, kind)
    La, scale, _ = basis(L, N, parity)
    ns = orders(N, parity)
    ha = price.to_arb(h)
    K = ns[-1] + 1
    jfun = sph_j_fast if bessel == "fast" else sph_j_all
    gl = [arb.legendre_p_root(q, k, weight=True) for k in range(q)]
    C, G = arb_mat(N, N), arb_mat(N, N)
    shift = 0.0
    for k in range(k0, k1):
        a0 = ha * k
        V, wg, wc = [], [], []
        for x, w in gl:
            t_gl = a0 + ha * (1 + x) / 2
            xl = arb((t_gl * La).mid())
            t = xl / La
            shift = max(shift, float(abs(t - t_gl).upper()))
            ww = w * ha / 2 / arb.pi()
            j = jfun(K, xl)
            V.append([scale[i] * j[n] for i, n in enumerate(ns)])
            wg.append(ww)
            wc.append(ww * (sym.psi(t) + sym.H(t)))
        VtT = arb_mat(q, N, [V[c][r] for c in range(q) for r in range(N)])
        G += arb_mat(N, q, [V[c][r] * wg[c] for r in range(N) for c in range(q)]) * VtT
        C += arb_mat(N, q, [V[c][r] * wc[c] for r in range(N) for c in range(q)]) * VtT
    return C, G, shift


def _enc(M: arb_mat):
    out = []
    for i in range(M.nrows()):
        for j in range(i + 1):
            m, e = M[i, j].mid().man_exp()
            out.append((int(m), int(e), float(M[i, j].rad())))
    return out


def _dec(rows, N: int) -> arb_mat:
    M = arb_mat(N, N)
    it = iter(rows)
    for i in range(N):
        for j in range(i + 1):
            m, e, _ = next(it)
            v = arb(m) * arb(2) ** e if m else arb(0)
            M[i, j] = v
            M[j, i] = v
    return M


def run_unit(args):
    L, env_path, N, q, h, k0, k1, prec, out_dir, tag, parity, bessel = args
    path = Path(out_dir) / f"{tag}_panels_{k0:05d}_{k1:05d}.pkl"
    if path.exists():
        return str(path), 0.0
    t0 = time.time()
    C, G, shift = unit(L, Path(env_path), N, q, h, k0, k1, prec, parity, bessel)
    dt = time.time() - t0
    tmp = path.with_suffix(".tmp")
    with open(tmp, "wb") as fh:
        pickle.dump({"C": _enc(C), "G": _enc(G), "N": N, "k0": k0, "k1": k1, "prec": prec,
                     "q": q, "h": str(h), "seconds": dt, "node_shift": shift, "parity": parity,
                     "bessel": bessel, "env": str(env_path)}, fh, protocol=5)
    os.replace(tmp, path)
    return str(path), dt


def ldl_midpoint(R: arb_mat):
    """Plain LDL^T on the midpoint matrix at the working precision (measured):
    returns (negative pivots, undecided pivots, smallest |pivot|)."""
    n = R.nrows()
    a = [[R[i, j].mid() for j in range(i + 1)] for i in range(n)]
    neg = und = 0
    small = None
    piv = []
    for k in range(n):
        d = a[k][k]
        for m in range(k):
            d -= a[k][m] * a[k][m] * piv[m]
        d = d.mid()
        piv.append(d)
        if bool(d < 0):
            neg += 1
        elif not bool(d > 0):
            und += 1
        small = abs(d) if small is None or bool(abs(d) < small) else small
        if bool(d == 0):
            return neg, und + (n - k - 1), 0.0
        for i in range(k + 1, n):
            s = a[i][k]
            for m in range(k):
                s -= a[i][m] * a[k][m] * piv[m]
            a[i][k] = (s / d).mid()
    return neg, und, float(small)


def lam_nearest(R: arb_mat, shift=None, iters: int = 8):
    """Inverse iteration on the midpoint matrix (shifted by `shift` if given):
    the eigenvalue nearest the shift (nearest 0 by default) and its residual."""
    n = R.nrows()
    Rm = arb_mat(n, n, [R[i, j].mid() for i in range(n) for j in range(n)])
    A = Rm
    if shift is not None:
        A = arb_mat(n, n, [Rm[i, j] - (shift if i == j else 0) for i in range(n) for j in range(n)])
    x = arb_mat(n, 1, [arb(1) / (1 + i) for i in range(n)])
    for _ in range(iters):
        y = A.solve(x, algorithm="approx")
        nrm = sum((y[i, 0] ** 2 for i in range(n)), arb(0)).sqrt()
        x = arb_mat(n, 1, [(y[i, 0] / nrm).mid() for i in range(n)])
    Rx = Rm * x
    lam = sum((x[i, 0] * Rx[i, 0] for i in range(n)), arb(0))
    res = sum(((Rx[i, 0] - lam * x[i, 0]) ** 2 for i in range(n)), arb(0)).sqrt()
    return lam, res


def lam_min_estimate(R: arb_mat, n_neg: int):
    """lambda_min of the midpoint block (measured). With no negative pivot it
    is the eigenvalue nearest 0 (inverse iteration). With negative pivots, a
    float64 spectrum of the midpoint matrix locates the bottom when it is
    resolvable (below -1e-10 of the largest eigenvalue) and shifted inverse
    iteration refines it at the working precision; otherwise the eigenvalue
    nearest 0 is reported."""
    if n_neg == 0:
        return lam_nearest(R)
    import numpy as np
    n = R.nrows()
    M = np.array([[float(R[i, j].mid()) for j in range(n)] for i in range(n)])
    ev = np.linalg.eigvalsh(M)
    scale = float(np.max(np.abs(ev)))
    if ev[0] < -1e-10 * scale:
        return lam_nearest(R, shift=arb(float(ev[0])))
    return lam_nearest(R)


def beta_star(kind: str, T: arb, S: arb) -> arb:
    if kind == "epstein":
        return arb(23).log() + 2 * (T / (2 * arb.pi())).log() - 2 / T - S
    arch = arb(1) if kind == "zeta" else arb(5)
    return (arch * T / (2 * arb.pi())).log() - 1 / T - S


def checkpoint_row(T: Fraction, kind: str, Sa: arb, P2: arb_mat, I: arb_mat, C: arb_mat, G: arb_mat,
                   N: int, prec: int, responses=None) -> dict:
    """One checkpoint of the reducer: beta*, and where beta* > 0 the midpoint
    LDL inertia and lambda_min of R(T#), with the N and precision responses
    at the checkpoints listed in `responses`."""
    Ta = price.to_arb(T)
    beta = beta_star(kind, Ta, Sa)
    rec = {"T": float(T), "beta": float(beta.mid())}
    if bool(beta > 0):
        R = P2 + C + beta * (I - G)
        t0 = time.time()
        neg, und, small = ldl_midpoint(R)
        lam, res = lam_min_estimate(R, neg)
        rec.update(n_neg=neg, undecided=und, min_abs_pivot=small,
                   lam_min=lam.mid().str(12, radius=False),
                   residual=float(res.upper()), seconds=time.time() - t0)
        if responses and float(T) in responses:
            rec["response"] = responses_of(R, N, prec)
    return rec


def responses_of(R: arb_mat, N: int, prec: int) -> dict:
    """Two responses of one checkpoint block (measured).

    leading_N_<n2>: the leading N - N//13 principal block. By Cauchy
    interlacing its least eigenvalue lies at or above the full block's, and a
    larger N can only lower it, so this shows where a negative direction lives;
    it is not a mode-count refinement and cannot undo a refusal.

    rounded_<prec-128>: every entry of the block rounded to prec - 128 bits
    (unary plus rounds to the working precision; arb(x.mid()) would copy x
    exactly), then reduced at that precision. It tests the reduction and the
    last 128 bits of the stored data, not the assembly (which would need the
    units recomputed at another precision).

    Rows written before 2026-10-27 carry the older keys N_<n2> and
    prec_<prec-128>; their precision response copied the data unrounded."""
    n2 = N - max(1, N // 13)
    R2 = arb_mat(n2, n2, [R[i, j] for i in range(n2) for j in range(n2)])
    neg2, _, _ = ldl_midpoint(R2)
    lam2, _ = lam_min_estimate(R2, neg2)
    with ctx.workprec(prec - 128):
        R3 = arb_mat(N, N, [+(R[i, j].mid()) for i in range(N) for j in range(N)])
        neg3, _, _ = ldl_midpoint(R3)
        lam3, _ = lam_min_estimate(R3, neg3)
        lam3s = lam3.mid().str(12, radius=False)
    return {f"leading_N_{n2}": {"n_neg": neg2, "lam_min": lam2.mid().str(12, radius=False)},
            f"rounded_{prec - 128}": {"n_neg": neg3, "lam_min": lam3s}}


def lesion_rows(T: Fraction, kind: str, S: Fraction, C: arb_mat, G: arb_mat, N: int, prec: int,
                dS_list, full: bool = True) -> list[dict]:
    """S-lesion of one checkpoint: the block C + (beta* + dS)(I - G), i.e. the
    pipeline run with the envelope constant understated by dS (an invalid
    envelope). R(T#) depends on S only through beta*, so no unit is recomputed.
    full=True gives checkpoint rows (LDL inertia and lambda_min); full=False
    only the eigenvalue nearest 0 (inverse iteration), for bisection. DH has
    no pole term (P2 = 0). Measured."""
    ctx.prec = prec
    if kind != "dh":
        raise ValueError("lesion rows are written for the entire DH case only")
    I = arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
    Z = arb_mat(N, N)
    out = []
    for dS in dS_list:
        Sa = price.to_arb(S) - price.to_arb(Fraction(dS))
        t0 = time.time()
        if full:
            rec = checkpoint_row(T, kind, Sa, Z, I, C, G, N, prec)
        else:
            beta = beta_star(kind, price.to_arb(T), Sa)
            lam, res = lam_nearest(C + beta * (I - G))
            rec = {"T": float(T), "beta": float(beta.mid()), "lam_nearest": lam.mid().str(12, radius=False),
                   "residual": float(res.upper())}
        rec["dS"] = str(Fraction(dS))
        rec["seconds"] = time.time() - t0
        out.append(rec)
        print(json.dumps(rec), flush=True)
    return out


def _fixed_terms(L: Fraction, env_path: Path, N: int, parity: str):
    S, _, kind = load_envelope(env_path, with_kind=True)
    _, _, pvec = basis(L, N, parity)
    pole = 0 if kind == "dh" else (2 if parity == "even" else -2)
    P2 = arb_mat(N, N, [pole * pvec[i] * pvec[j] for i in range(N) for j in range(N)])
    I = arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
    return S, kind, price.to_arb(S), P2, I


def reduce(L: Fraction, env_path: Path, N: int, h: Fraction, units, checkpoints, prec: int,
           responses=None, parity: str = "even", keep: dict | None = None):
    """Sum unit files in panel order; at each checkpoint T (on a unit boundary)
    report beta*, midpoint LDL inertia and lambda_min of the block. `keep`, if
    given, receives the final sums C and G."""
    ctx.prec = prec
    _, kind, Sa, P2, I = _fixed_terms(L, env_path, N, parity)
    C, G = arb_mat(N, N), arb_mat(N, N)
    rows = []
    for path in sorted(units, key=lambda p: int(Path(p).stem.split("_")[-2])):
        with open(path, "rb") as fh:
            u = pickle.load(fh)
        C += _dec(u["C"], N)
        G += _dec(u["G"], N)
        T = h * u["k1"]
        if float(T) in checkpoints:
            rec = checkpoint_row(T, kind, Sa, P2, I, C, G, N, prec, responses)
            rows.append(rec)
            print(json.dumps(rec), flush=True)
    if keep is not None:
        keep.update(C=C, G=G)
    return rows


# ------------------------------------------------------------- the streaming driver
#
# The units are consumed in panel order as they finish (ordered imap), added to
# the running sums C and G, and every checkpoint row is computed as soon as its
# unit arrives. No unit file is written: the restart checkpoint is the running
# sums, saved after every unit in files of at most _CHUNK encoded entries (about
# 20 MB at 1280 bits, under a 100 MB per-file limit), with at most two
# generations on disk. Midpoint arithmetic does not see radii, so dropping the
# radii of the running sums at a restart leaves every row unchanged.

_CHUNK = 100_000


def _stream_job(args):
    """One unit for the streaming driver: computed, or (src given) read from a
    unit file written by run_unit."""
    L, env_path, N, q, h, k0, k1, prec, parity, bessel, src = args
    if src:
        with open(src, "rb") as fh:
            u = pickle.load(fh)
        return k0, k1, u["C"], u["G"], u["seconds"], u["node_shift"]
    t0 = time.time()
    C, G, shift = unit(L, Path(env_path), N, q, h, k0, k1, prec, parity, bessel)
    return k0, k1, _enc(C), _enc(G), time.time() - t0, shift


def mem_available_gib() -> float:
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 2 ** 20
    except OSError:
        pass
    return float("inf")


def _write_atomic(path: Path, data: bytes):
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "wb") as fh:
        fh.write(data)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def _save_state(state_dir: Path, C: arb_mat, G: arb_mat, meta: dict):
    gen = f"state_{meta['k1']:05d}"
    files = {}
    for name, M in (("C", C), ("G", G)):
        enc = _enc(M)
        files[name] = []
        for i in range(0, len(enc), _CHUNK):
            f = f"{gen}_{name}_{i // _CHUNK:03d}.pkl"
            _write_atomic(state_dir / f, pickle.dumps(enc[i:i + _CHUNK], protocol=5))
            files[name].append(f)
    _write_atomic(state_dir / "state.json", json.dumps(dict(meta, files=files), indent=1).encode())
    keep = set(files["C"]) | set(files["G"])
    for f in state_dir.glob("state_*.pkl"):
        if f.name not in keep:
            f.unlink()


def _load_state(state_dir: Path, N: int):
    meta = json.loads((state_dir / "state.json").read_text())
    mats = []
    for name in ("C", "G"):
        enc = []
        for f in meta["files"][name]:
            with open(state_dir / f, "rb") as fh:
                enc += pickle.load(fh)
        mats.append(_dec(enc, N))
    return meta, mats[0], mats[1]


def stream(L: Fraction, env_path: Path, N: int, q: int, h: Fraction, units, prec: int, state_dir: Path,
           checkpoints, responses=None, parity: str = "even", bessel: str = "fast", procs: int = 1,
           sources=None, stop_after: int | None = None, cap_core_seconds: float | None = None,
           min_mem_gib: float = 0.0, keep: dict | None = None):
    """Units and reduction in one pass (see the comment above). Resumes from
    state_dir/state.json if present. `sources` maps (k0, k1) to a unit file to
    read instead of computing (tests); `stop_after` stops after that many units
    are consumed in this call (tests); the run also stops, with its state saved,
    if the projected core-seconds pass `cap_core_seconds` or MemAvailable falls
    below `min_mem_gib`. Returns (rows, status) with status 'done' or the reason
    it stopped. Rows are appended to state_dir/rows.jsonl as they arrive."""
    import multiprocessing as mpc
    ctx.prec = prec
    state_dir = Path(state_dir)
    state_dir.mkdir(parents=True, exist_ok=True)
    _, kind, Sa, P2, I = _fixed_terms(L, env_path, N, parity)
    params = {"L": f"{L.numerator}/{L.denominator}", "env": Path(env_path).name, "N": N, "q": q, "h": str(h),
              "prec": prec, "parity": parity, "bessel": bessel, "units": [list(u) for u in units]}
    if (state_dir / "state.json").exists():
        meta, C, G = _load_state(state_dir, N)
        if meta["params"] != params:
            raise SystemExit(f"state in {state_dir} was made with other parameters")
    else:
        meta = {"params": params, "k1": 0, "rows": [], "unit_seconds": [], "reduce_seconds": 0.0,
                "max_entry_radius": 0.0, "max_node_shift": 0.0}
        C, G = arb_mat(N, N), arb_mat(N, N)
    rows = meta["rows"]
    (state_dir / "rows.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
    todo = [(k0, k1) for k0, k1 in units if k1 > meta["k1"]]
    live_cps = [T for T in (float(h * k1) for _, k1 in units)
                if T in checkpoints and bool(beta_star(kind, price.to_arb(Fraction(T)), Sa) > 0)]
    sources = sources or {}
    jobs = [(L, str(env_path), N, q, h, k0, k1, prec, parity, bessel, sources.get((k0, k1))) for k0, k1 in todo]
    status = "done"
    pool = mpc.get_context("spawn").Pool(procs) if procs > 1 else None
    try:
        it = pool.imap(_stream_job, jobs, chunksize=1) if pool else map(_stream_job, jobs)
        for n_done, (k0, k1, Ce, Ge, sec, shift) in enumerate(it, 1):
            if k0 != meta["k1"]:
                raise RuntimeError(f"unit {k0}..{k1} arrived after panel {meta['k1']}")
            C += _dec(Ce, N)
            G += _dec(Ge, N)
            meta["unit_seconds"].append(sec)
            meta["max_entry_radius"] = max(meta["max_entry_radius"], max(r for _, _, r in Ce),
                                           max(r for _, _, r in Ge))
            meta["max_node_shift"] = max(meta["max_node_shift"], shift)
            del Ce, Ge
            T = h * k1
            new_row = None
            if float(T) in checkpoints:
                t0 = time.time()
                new_row = checkpoint_row(T, kind, Sa, P2, I, C, G, N, prec, responses)
                meta["reduce_seconds"] += time.time() - t0
                rows.append(new_row)
            meta["k1"] = k1
            _save_state(state_dir, C, G, meta)
            if new_row is not None:
                with open(state_dir / "rows.jsonl", "a") as fh:
                    fh.write(json.dumps(new_row) + "\n")
                print(json.dumps(new_row), flush=True)
            us = meta["unit_seconds"]
            n_left = len(units) - len(us)
            cps_done = sum(1 for r in rows if "n_neg" in r)
            per_cp = meta["reduce_seconds"] / cps_done if cps_done else 0.0
            proj = sum(us) + n_left * sum(us) / len(us) + meta["reduce_seconds"] \
                + per_cp * max(0, len(live_cps) - cps_done)
            print(json.dumps({"unit": [k0, k1], "seconds": sec, "projected_core_seconds": proj,
                              "mem_available_gib": round(mem_available_gib(), 1)}), flush=True)
            if k1 == units[-1][1]:
                break
            if cap_core_seconds is not None and proj > cap_core_seconds:
                status = f"stopped: projected {proj:.0f} core-seconds > cap {cap_core_seconds:.0f}"
                break
            if mem_available_gib() < min_mem_gib:
                status = f"stopped: MemAvailable below {min_mem_gib} GiB"
                break
            if stop_after is not None and n_done >= stop_after:
                status = "stopped: stop_after"
                break
    finally:
        if pool:
            pool.terminate()
            pool.join()
    if keep is not None:
        keep.update(C=C, G=G, meta=meta)
    return rows, status


def plan(T_max: float, units_per: int, h: Fraction, T_min: float = 0.0):
    """Units of `units_per` panels covering [0, T_max]."""
    npan = int(Fraction(T_max) / h)
    return [(k, min(k + units_per, npan)) for k in range(0, npan, units_per)]


def bessel_timing(cases=((1039, 840, 640), (2079, 1700, 640), (4159, 3400, 640), (2079, 1700, 1280))):
    """bessel_scaling.json: seconds per node of the enclosed (re-seeded) and the
    fast (midpoint recurrence) spherical Bessel columns j_0..j_K at x, and the
    largest relative deviation of the fast midpoints from the enclosed ones
    (measured, on whatever load the box carries)."""
    out = []
    for K, xf, prec in cases:
        ctx.prec = prec
        x = arb(xf)
        t = time.time()
        a = sph_j_all(K, x)
        ta = time.time() - t
        t = time.time()
        b = sph_j_fast(K, x)
        tb = time.time() - t
        def log10_max(vals):
            best = None
            for v in vals:
                if v.is_zero():
                    continue
                lv = float(v.log().mid()) / math.log(10)
                best = lv if best is None or lv > best else best
            return best
        dev = log10_max(abs((b[n] - a[n].mid()) / a[n].mid()).mid() for n in range(K + 1) if not a[n].is_zero())
        rad = log10_max(arb(a[n].rad()) / abs(a[n].mid()) for n in range(K + 1) if not a[n].is_zero())
        out.append({"K": K, "x": xf, "prec": prec, "enclosed_s": ta, "fast_s": tb, "ratio": ta / tb,
                    "log10_max_rel_dev": dev, "log10_enclosed_max_rel_radius": rad})
        print(json.dumps(out[-1]), flush=True)
    return out



def main():
    import multiprocessing as mpc
    ap = argparse.ArgumentParser(description="stage-A scout")
    ap.add_argument("--L", default="7/5")
    ap.add_argument("--env", default=str(HERE / "joint_1.4.json"))
    ap.add_argument("--N", type=int, default=520)
    ap.add_argument("--q", type=int, default=64)
    ap.add_argument("--h", default="1/2")
    ap.add_argument("--prec", type=int, default=640)
    ap.add_argument("--Tmax", type=float, default=600)
    ap.add_argument("--unit-panels", type=int, default=40)
    ap.add_argument("--parity", default="even", choices=["even", "odd"])
    ap.add_argument("--bessel", default="fast", choices=["fast", "enclosed"])
    ap.add_argument("--checkpoints", nargs="*", type=float, default=None)
    ap.add_argument("--responses", nargs="*", type=float, default=None,
                    help="checkpoints at which to add the N - N//13 and prec - 128 responses")
    ap.add_argument("--dir", default=str(CACHE / "scout_L140"))
    ap.add_argument("--tag", default="scout")
    ap.add_argument("--time-unit", type=int, default=None, help="run only this unit index (timing)")
    ap.add_argument("--procs", type=int, default=8)
    ap.add_argument("--order", default="desc", choices=["desc", "asc"],
                    help="unit order; a second instance on the same directory can take the other end")
    ap.add_argument("--units-only", action="store_true", help="run the units and stop before the reducer")
    ap.add_argument("--reduce", action="store_true")
    ap.add_argument("--stream", action="store_true",
                    help="units and reduction in one ordered pass, no unit files; --dir holds the restart state")
    ap.add_argument("--cap-core-hours", type=float, default=None,
                    help="streaming: stop, state saved, if the projected core-hours pass this")
    ap.add_argument("--min-mem-gib", type=float, default=20.0,
                    help="streaming: stop, state saved, if MemAvailable falls below this")
    ap.add_argument("--out", default=str(HERE / "scout_L140.json"))
    ap.add_argument("--bessel-timing", default=None, help="write the Bessel column timing table to this file")
    ap.add_argument("--lesion", nargs="*", default=None,
                    help="S-lesion rows at the restart state in --dir (exact rationals dS, e.g. 0 7085/1000)")
    ap.add_argument("--lesion-nearest", action="store_true", help="lesion: eigenvalue nearest 0 only (no LDL)")
    ap.add_argument("--responses-at-state", action="store_true",
                    help="the responses (leading block, rounded data) of the block at the restart state in --dir")
    args = ap.parse_args()
    if args.bessel_timing:
        Path(args.bessel_timing).write_text(json.dumps(bessel_timing(), indent=1))
        return
    if args.lesion is not None or args.responses_at_state:
        L, h = Fraction(args.L), Fraction(args.h)
        ctx.prec = args.prec
        meta, C, G = _load_state(Path(args.dir), args.N)
        S, _, kind = load_envelope(Path(args.env), with_kind=True)
        T = h * meta["k1"]
        out = {"state_k1": meta["k1"], "T": float(T), "N": args.N, "prec": args.prec, "envelope": Path(args.env).name,
               "S_exact": f"{S.numerator}/{S.denominator}", "kind": kind}
        if args.lesion is not None:
            out["rows"] = lesion_rows(T, kind, S, C, G, args.N, args.prec, [Fraction(x) for x in args.lesion],
                                      full=not args.lesion_nearest)
        if args.responses_at_state:
            Sa = price.to_arb(S)
            beta = beta_star(kind, price.to_arb(T), Sa)
            I = arb_mat(args.N, args.N, [1 if i == j else 0 for i in range(args.N) for j in range(args.N)])
            t0 = time.time()
            out["responses"] = responses_of(C + beta * (I - G), args.N, args.prec)
            out["responses_seconds"] = time.time() - t0
            print(json.dumps(out["responses"]), flush=True)
        Path(args.out).write_text(json.dumps(out, indent=1))
        print("wrote", args.out)
        return
    L, h = Fraction(args.L), Fraction(args.h)
    Path(args.dir).mkdir(parents=True, exist_ok=True)
    units = plan(args.Tmax, args.unit_panels, h)
    job = [(L, args.env, args.N, args.q, h, k0, k1, args.prec, args.dir, args.tag, args.parity, args.bessel)
           for k0, k1 in units]
    if args.stream:
        cps = set(args.checkpoints or [float(h * k1) for _, k1 in units])
        t0 = time.time()
        keep = {}
        rows, status = stream(L, Path(args.env), args.N, args.q, h, units, args.prec, Path(args.dir), cps,
                              responses=set(args.responses or []), parity=args.parity, bessel=args.bessel,
                              procs=min(args.procs, 3),
                              cap_core_seconds=None if args.cap_core_hours is None else 3600 * args.cap_core_hours,
                              min_mem_gib=args.min_mem_gib, keep=keep)
        meta = keep["meta"]
        print(json.dumps({"status": status, "k1": meta["k1"], "wall_seconds": time.time() - t0}), flush=True)
        if status != "done":
            raise SystemExit(3)
        S, _, kind = load_envelope(Path(args.env), with_kind=True)
        us = meta["unit_seconds"]
        out = {"L": args.L, "N": args.N, "q": args.q, "h": args.h, "prec": args.prec, "Tmax": args.Tmax,
               "parity": args.parity, "bessel": args.bessel, "kind": kind,
               "envelope": Path(args.env).name, "S_exact": f"{S.numerator}/{S.denominator}", "S": float(S),
               "grade": "measured: no quadrature, Legendre tail or coupling bound; midpoint LDL and inverse iteration",
               "driver": "stream (ordered units, running sums, no unit files)",
               "units": len(units), "unit_core_seconds": sum(us), "unit_seconds_max": max(us),
               "max_entry_radius": meta["max_entry_radius"], "max_node_shift": meta["max_node_shift"],
               "reduce_seconds": meta["reduce_seconds"], "rows": rows}
        Path(args.out).write_text(json.dumps(out, indent=1))
        print("wrote", args.out)
        return
    if args.time_unit is not None:
        path, dt = run_unit(job[args.time_unit])
        print(json.dumps({"unit": args.time_unit, "panels": units[args.time_unit], "seconds": dt, "file": path}))
        return
    if not args.reduce:
        procs = min(args.procs, 8)
        with mpc.get_context("spawn").Pool(procs) as pool:
            for path, dt in pool.imap_unordered(run_unit, job[::-1] if args.order == "desc" else job):
                print(json.dumps({"done": path, "seconds": dt}), flush=True)
        if args.units_only:
            return
    files = sorted(str(p) for p in Path(args.dir).glob(f"{args.tag}_panels_*.pkl"))
    if len(files) != len(units):
        raise SystemExit(f"{len(files)} of {len(units)} unit files present")
    cps = args.checkpoints or [float(h * k1) for _, k1 in units]
    t0 = time.time()
    rows = reduce(L, Path(args.env), args.N, h, files, set(cps), args.prec,
                  responses=set(args.responses or []), parity=args.parity)
    unit_s, max_rad, max_shift = [], 0.0, 0.0
    for f in files:
        with open(f, "rb") as fh:
            u = pickle.load(fh)
        unit_s.append(u["seconds"])
        max_rad = max(max_rad, max(r for _, _, r in u["C"]), max(r for _, _, r in u["G"]))
        max_shift = max(max_shift, u["node_shift"])
    S, _, kind = load_envelope(Path(args.env), with_kind=True)
    out = {"L": args.L, "N": args.N, "q": args.q, "h": args.h, "prec": args.prec, "Tmax": args.Tmax,
           "parity": args.parity, "bessel": args.bessel, "kind": kind,
           "envelope": Path(args.env).name, "S_exact": f"{S.numerator}/{S.denominator}", "S": float(S),
           "grade": "measured: no quadrature, Legendre tail or coupling bound; midpoint LDL and inverse iteration",
           "units": len(units), "unit_core_seconds": sum(unit_s), "unit_seconds_max": max(unit_s),
           "max_entry_radius": max_rad, "max_node_shift": max_shift,
           "reduce_seconds": time.time() - t0, "rows": rows}
    Path(args.out).write_text(json.dumps(out, indent=1))
    print("wrote", args.out)


if __name__ == "__main__":
    main()
