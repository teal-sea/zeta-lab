"""Prices of the out-of-band reduction on four Weil windows (hunt weil_dh_line, #146).

Normalization: arXiv:2608.24827 (Zhu) as used by hunts/oob_envelope. Window
supp f in [-L, L], prime comb

    P_L(t) = sum_{log n < 2L} 2 w_n cos(t log n),   w_n = Lambda(n) / sqrt(n),

and the windowed comb operator (P phi)(x) = sum_n w_n [phi(x - log n) + phi(x + log n)]
on L^2[-L, L]. For every admissible H (all frequencies at least 2L) the envelope
constant S >= sup_t (P_L - H)(t) obeys S >= S*_L := lambda_max(P) (oob_envelope
theory, Proposition 2.1), with equality in the limit (Theorem 2). The reduction
runs at T# with beta* = log(T#/2 pi) - 1/T# - S > 0.

What this module computes, and the grade of each piece:

1. ``s_star_enclosure``: S*_L in a ball. Lower end: the Rayleigh quotient of an
   explicit piecewise-constant trial function h, exactly (integer
   autocorrelations, Arb weights). Upper end: the Schur test
   sup_x (P h)(x) / h(x) for the same positive h, evaluated in Arb on every
   sub-interval on which the shifted cell indices are constant, so the supremum
   is over every x, not over samples. The float eigensolver only proposes h.
2. ``toeplitz_top`` and ``sep_floor``: the per-prime limit
   S_sep = sum_p lambda_max(T_p), each Toeplitz eigenvalue in an Arb ball.
3. ``sep_sine``: the evaluable per-prime envelope at sine-kernel degree D, by
   importing hunts/oob_envelope/numerics/envelope.py read-only (exact rational
   S, two independent Arb proofs per prime).
4. ``best_partition``: cluster floors lambda_max(P restricted to the primes of a
   cluster), float Galerkin, measured; the least constant reachable by any H
   that couples only primes inside one cluster.
5. ``price``: T#, N, bits, memory and core-hours from the rules recorded in
   hunts/oob_envelope (MISSION.md seed rule, numerics/RUNS.md unit costs, the
   stage B run). These are cost models calibrated on recorded runs.

The joint envelope (LP plus a whole-torus supremum bound) is ``joint.py``.
Nothing here is kernel-checked.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import sys
import time
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from flint import arb, arb_mat, ctx, fmpq

HERE = Path(__file__).resolve().parent
OOB_NUMERICS = HERE.parent / "oob_envelope" / "numerics"

PREC = 256

#: The four windows. "L_DH" is the least five-decimal rational at or above
#: (log 30.617188)/2 = 1.71078078; the task's 1.71078 lies below it.
WINDOWS = {
    "1.4": Fraction(7, 5),
    "1.55": Fraction(31, 20),
    "L_DH": Fraction(171079, 100000),
    "L_31": Fraction(171699, 100000),
}
DH_CUTOFF = Fraction(30617188, 1000000)   # weil_propagation s3.2, hardened negative cell
GO_THRESHOLD = 6.2                          # the task's go/no-go constant
BETA_RULE = 0.5                             # oob_envelope MISSION.md seed rule T# = 2 pi e^{S + 0.5}


def to_arb(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def arb_upper_fraction(x: arb) -> Fraction:
    m, e = x.upper().man_exp()
    return Fraction(int(m)) * Fraction(2) ** int(e)


def arb_lower_fraction(x: arb) -> Fraction:
    m, e = x.lower().man_exp()
    return Fraction(int(m)) * Fraction(2) ** int(e)


def rounded_down(x: Fraction, digits: int = 10) -> str:
    """Decimal string k * 10^-p with k * 10^-p <= x exactly (x > 0)."""
    p = digits - 1 - math.floor(math.log10(float(x)))
    k = math.floor(x * Fraction(10) ** p)
    return f"{k}e{-p}"


def rounded_up(x: Fraction, digits: int = 10) -> str:
    """Decimal string k * 10^-p with k * 10^-p >= x exactly (x > 0)."""
    p = digits - 1 - math.floor(math.log10(float(x)))
    k = math.ceil(x * Fraction(10) ** p)
    return f"{k}e{-p}"


def dec(s: str) -> float:
    return float(s)


# ------------------------------------------------------------------ the comb

def _smallest_prime_factor(n: int) -> int:
    return next(q for q in range(2, n + 1) if n % q == 0)


@lru_cache(None)
def prime_powers(L: Fraction):
    """Every prime power n = p^m with log n < 2L, decided in Arb.

    Returns a tuple of (n, p, m), sorted by n. Raises if a comparison is undecided."""
    with ctx.workprec(PREC):
        twoL = 2 * to_arb(L)
        out = []
        for n in range(2, int(math.exp(2 * float(L))) + 3):
            p = _smallest_prime_factor(n)
            m, k = n, 0
            while m % p == 0:
                m //= p
                k += 1
            if m != 1:
                continue
            ln = arb(n).log()
            if bool(ln < twoL):
                out.append((n, p, k))
            elif not bool(ln > twoL):
                raise RuntimeError(f"undecided: log {n} against 2L")
    return tuple(out)


def primes_of(L: Fraction) -> list[int]:
    return sorted({p for _, p, _ in prime_powers(L)})


def m_of(L: Fraction) -> dict[int, int]:
    out: dict[int, int] = {}
    for _, p, k in prime_powers(L):
        out[p] = max(out.get(p, 0), k)
    return out


def w_arb(p: int, m: int) -> arb:
    """w_{p^m} = log p / p^{m/2} as an Arb ball."""
    return arb(p).log() / arb(p) ** (arb(m) / 2)


def A_L(L: Fraction) -> arb:
    """Zhu's constant A_L = sup P_L = P_L(0) = sum 2 w_n, in Arb."""
    with ctx.workprec(PREC):
        return sum((2 * w_arb(p, m) for _, p, m in prime_powers(L)), arb(0))


# ------------------------------------------- the comb operator: Galerkin (float)

def _shifts(L: Fraction, primes=None, weights=None):
    """[(w float, log n float, p, m)] for the comb restricted to `primes`;
    `weights` optionally multiplies prime p's terms by weights[p]."""
    out = []
    for n, p, m in prime_powers(L):
        if primes is not None and p not in primes:
            continue
        sc = 1.0 if weights is None else float(weights[p])
        out.append((sc * math.log(p) / p ** (m / 2), math.log(n), p, m))
    return out


def galerkin_top(L: Fraction, M: int, primes=None, weights=None, want_vector=False):
    """Top eigenvalue (and Perron vector) of the piecewise-constant Galerkin
    matrix of the windowed comb operator on M equal cells of [-L, L]. Float,
    measured. The matrix is symmetric Toeplitz with A_ij = g(j - i),
    g(d) = sum_n w_n [tri(d delta - s_n) + tri(d delta + s_n)] / delta,
    tri(u) = max(0, delta - |u|), delta = 2L/M, s_n = log n."""
    Lf = float(L)
    d = 2 * Lf / M
    diags: dict[int, float] = {}
    for w, s, _, _ in _shifts(L, primes, weights):
        u = s / d
        k0 = math.floor(u)
        fr = u - k0
        for k, val in ((k0, w * (1 - fr)), (k0 + 1, w * fr)):
            if 0 < k < M:
                diags[k] = diags.get(k, 0.0) + val
                diags[-k] = diags.get(-k, 0.0) + val
    if not diags:
        return (0.0, np.ones(M) / math.sqrt(M)) if want_vector else 0.0
    offs = sorted(diags)
    A = sp.diags([np.full(M - abs(k), diags[k]) for k in offs], offs, shape=(M, M), format="csr")
    if want_vector:
        val, vec = spla.eigsh(A, k=1, which="LA", tol=1e-13)
        v = vec[:, 0]
        v = v if v.sum() > 0 else -v
        return float(val[0]), v
    return float(spla.eigsh(A, k=1, which="LA", tol=1e-11, return_eigenvectors=False)[0])


# ----------------------------------------- the comb operator: Arb enclosure

def _subinterval_types(L: Fraction, M: int, primes=None, weights=None):
    """Float description of the 2K + 1 sub-interval types (see s_star_enclosure):
    weights w_n and, per type, the cell offsets of x - s_n and x + s_n."""
    d = 2 * float(L) / M
    terms = []
    for w, s, _, _ in _shifts(L, primes, weights):
        u = s / d
        fl = math.floor(u)
        terms.append((w, fl, u - fl))
    thr = []
    for j, (_, _, fr) in enumerate(terms):
        thr.append((fr, j, "-"))
        thr.append((1 - fr, j, "+"))
    thr.sort()
    om = [-(fl + 1) for _, fl, _ in terms]
    op = [fl for _, fl, _ in terms]
    types = []
    for cut in range(len(thr) + 1):
        if cut > 0:
            _, j, side = thr[cut - 1]
            if side == "-":
                om[j] += 1
            else:
                op[j] += 1
        types.append((np.array(om), np.array(op)))
    return np.array([w for w, _, _ in terms]), types


def _max_system(h: np.ndarray, w: np.ndarray, types) -> np.ndarray:
    """(T h)_i = max over sub-interval types of sum_n w_n (h_{i+o-} + h_{i+o+}),
    h extended by zero outside the window."""
    M = h.size
    hp = np.zeros(3 * M)
    hp[M:2 * M] = h
    idx = np.arange(M) + M
    out = np.full(M, -np.inf)
    for om, op in types:
        s = (w[:, None] * (hp[idx[None, :] + om[:, None]] + hp[idx[None, :] + op[:, None]])).sum(axis=0)
        out = np.maximum(out, s)
    return out


def schur_vector(L: Fraction, M: int, primes=None, weights=None, iters: int = 800):
    """A positive piecewise-constant h for the Schur test: the float Perron
    vector, then the nonlinear power iteration h <- sqrt(h * T h / max(T h / h))
    on the max-system T, which drives sup_x (P h)(x)/h(x) down toward the floor.
    Float; only proposes h (the bound is evaluated in Arb)."""
    _, vec = galerkin_top(L, M, primes, weights, want_vector=True)
    w, types = _subinterval_types(L, M, primes, weights)
    h = np.maximum(vec / vec.max(), 1e-6)
    hist = []
    for _ in range(iters):
        Th = _max_system(h, w, types)
        r = float((Th / h).max())
        hist.append(r)
        h = np.sqrt(h * Th / r)
        h = np.maximum(h / h.max(), 1e-6)
    return h, hist


def s_star_enclosure(L: Fraction, M: int = 8000, primes=None, weights=None, bits: int = 24,
                     iters: int = 800):
    """Ball for lambda_max(P) (P restricted to `primes`, optional per-prime
    weight factors as Fractions). Both ends in Arb.

    Lower end: <P g, g> / <g, g> = v^T A v / v^T v exactly, for the
    piecewise-constant trial function g = sum_i v_i 1_{cell i}, v the float
    Perron vector of the Galerkin matrix scaled to `bits`-bit integers.

    Upper end: the Schur test. P is positivity preserving and self-adjoint, so
    its top spectral value is ||P||, and ||P|| <= c whenever P h <= c h almost
    everywhere with h > 0. Here h = sum_i h_i 1_{cell i} with integers h_i >= 1
    (from ``schur_vector``). For x in cell i at fraction xi of the cell,
    x - s lies in cell i - ceil(u) if xi < frac(u) and in cell i - floor(u)
    otherwise, and x + s lies in cell i + floor(u) if xi < 1 - frac(u) and in
    cell i + floor(u) + 1 otherwise (u = s / delta). Sorting the 2K thresholds
    frac(u_n), 1 - frac(u_n) (ordered in Arb) splits every cell into the same
    2K + 1 sub-interval types, on each of which (P h)(x) is constant. The
    supremum of (P h)/h over all x is the largest of these finitely many
    constants, each computed in Arb."""
    lam_f, vec = galerkin_top(L, M, primes, weights, want_vector=True)
    v = np.maximum(np.rint(vec / vec.max() * (2 ** bits)).astype(np.int64), 1)
    vi = [int(x) for x in v]
    hs, hist = schur_vector(L, M, primes, weights, iters)
    hv = np.maximum(np.rint(hs * (2 ** bits)).astype(np.int64), 1)
    hi_ = [int(x) for x in hv]
    with ctx.workprec(PREC):
        La = to_arb(L)
        delta = 2 * La / M
        terms = []   # (w arb, floor(u) int, frac(u) arb)
        for n, p, m in prime_powers(L):
            if primes is not None and p not in primes:
                continue
            w = w_arb(p, m)
            if weights is not None:
                w = w * to_arb(Fraction(weights[p]))
            u = arb(n).log() / delta
            fl = int(math.floor(float(u.mid())))
            if not (bool(u > fl) and bool(u < fl + 1)):
                raise RuntimeError("undecided floor of log n / delta")
            if fl + 1 >= M:
                raise RuntimeError("shift longer than the window")
            terms.append((w, fl, u - fl))
        K = len(terms)
        # ---- lower end
        R = {0: sum(x * x for x in vi)}
        for _, fl, _ in terms:
            for k in (fl, fl + 1):
                if k not in R:
                    R[k] = int(np.dot(v[: M - k].astype(object), v[k:].astype(object)))
        num = arb(0)
        for w, fl, fr in terms:
            num += 2 * w * ((1 - fr) * R[fl] + fr * R[fl + 1])
        lower = num / R[0]
        # ---- upper end
        thr = []
        for j, (_, _, fr) in enumerate(terms):
            thr.append((fr, j, "-"))
            thr.append((1 - fr, j, "+"))
        for a, b in itertools.combinations(thr, 2):
            if not (bool(a[0] < b[0]) or bool(a[0] > b[0])):
                raise RuntimeError("undecided threshold order")
        thr.sort(key=lambda z: float(z[0].mid()))
        off_minus = [-(fl + 1) for _, fl, _ in terms]     # xi < frac(u): cell i - ceil(u)
        off_plus = [fl for _, fl, _ in terms]             # xi < 1 - frac(u): cell i + floor(u)
        hpad = np.zeros(3 * M, dtype=np.int64)
        hpad[M:2 * M] = hv
        idx = np.arange(M)
        wrow = arb_mat(1, K, [w for w, _, _ in terms])
        inv_h = [arb(1) / x for x in hi_]
        wf = np.array([float(w.mid()) for w, _, _ in terms])
        best = arb(0)
        best_float = 0.0
        for cut in range(len(thr) + 1):
            if cut > 0:
                _, j, side = thr[cut - 1]
                if side == "-":
                    off_minus[j] += 1
                else:
                    off_plus[j] += 1
            X = np.stack([hpad[M + idx + off_minus[j]] + hpad[M + idx + off_plus[j]] for j in range(K)])
            # float pass (a cross-check only) and the Arb pass (the bound)
            best_float = max(best_float, float(((wf @ X.astype(np.float64)) / hv).max()))
            Y = wrow * arb_mat(K, M, [int(z) for z in X.ravel()])
            for i in range(M):
                best = best.max(Y[0, i] * inv_h[i])
        upper = arb(best.upper())
    return {
        "L": str(L), "M": M, "primes": None if primes is None else sorted(primes),
        "galerkin_float": lam_f, "schur_float": best_float,
        "schur_iteration": [hist[0], hist[min(9, len(hist) - 1)], hist[-1]],
        "lower": lower, "upper": upper,
        "lower_str": rounded_down(arb_lower_fraction(lower), 10),
        "upper_str": rounded_up(arb_upper_fraction(upper), 10),
        "n_subinterval_types": len(thr) + 1,
    }


# ------------------------------------------------------- per-prime floors

def toeplitz_top(p: int, m: int, scale: Fraction | None = None):
    """lambda_max of the (m+1)x(m+1) Toeplitz matrix with first row
    (0, t_1, ..., t_m), t_k = log p / p^{k/2}, as an Arb ball: Rayleigh quotient
    of a dyadic vector below, Collatz-Wielandt max_i (T v)_i / v_i above (the
    matrix is entrywise nonnegative and v > 0)."""
    t = [0.0] + [math.log(p) / p ** (k / 2) for k in range(1, m + 1)]
    T = np.array([[t[abs(i - j)] for j in range(m + 1)] for i in range(m + 1)])
    _, V = np.linalg.eigh(T)
    v = np.abs(V[:, -1])
    vq = [Fraction(max(1, int(round(x * 2 ** 40))), 2 ** 40) for x in v]
    with ctx.workprec(PREC):
        ta = [arb(0)] + [w_arb(p, k) for k in range(1, m + 1)]
        if scale is not None:
            ta = [x * to_arb(scale) for x in ta]
        va = [to_arb(x) for x in vq]
        Tv = [sum((ta[abs(i - j)] * va[j] for j in range(m + 1)), arb(0)) for i in range(m + 1)]
        lower = sum((va[i] * Tv[i] for i in range(m + 1)), arb(0)) / sum((x * x for x in va), arb(0))
        upper = arb(0)
        for i in range(m + 1):
            upper = upper.max(Tv[i] / va[i])
        return lower, arb(upper.upper())


def sep_floor(L: Fraction):
    """S_sep = sum_p lambda_max(T_p), the per-prime limit (Theorem 2, one prime
    at a time), as a ball."""
    mp_ = m_of(L)
    lo, hi = arb(0), arb(0)
    per = {}
    with ctx.workprec(PREC):
        for p in sorted(mp_):
            a, b = toeplitz_top(p, mp_[p])
            lo += arb(a.lower())
            hi += arb(b.upper())
            per[p] = {"m": mp_[p], "lam": float(a.mid())}
    return {"lower": lo, "upper": hi, "per_prime": per,
            "lower_str": rounded_down(arb_lower_fraction(lo), 10),
            "upper_str": rounded_up(arb_upper_fraction(hi), 10)}


def sep_sine(L: Fraction, D: int):
    """Evaluable per-prime envelope at sine-kernel degree D, by the oob_envelope
    code imported read-only: exact rational S and out-of-band coefficients, two
    independent Arb proofs per prime (decomposition and adaptive scan)."""
    sys.path.insert(0, str(OOB_NUMERICS))
    try:
        import envelope as oob_env  # noqa: E402
    finally:
        sys.path.pop(0)
    with ctx.workprec(oob_env.PREC):
        res = oob_env.run(L, "sine", D, scan=True)
    return {"S": res["S"], "S_float": float(res["S"]), "max_freq": res["max_freq"],
            "per_prime_M": {r["p"]: str(r["M_p"]) for r in res["primes"]},
            "b": {r["p"]: {int(k): v for k, v in r["b"].items()} for r in res["primes"]},
            "scan_ok": all(r["scan"]["ok"] for r in res["primes"])}


# ---------------------------------------------- cluster floors and partitions

def best_partition(L: Fraction, block_max: int, M: int = 1200):
    """Best partition of the primes below e^{2L} into clusters of at most
    `block_max` primes, minimizing the sum of cluster floors (float Galerkin,
    measured; a Galerkin value sits slightly below its floor). Exact search by
    dynamic programming over subsets."""
    ps = primes_of(L)
    n = len(ps)
    fl = {}
    for r in range(1, block_max + 1):
        for c in itertools.combinations(ps, r):
            fl[c] = galerkin_top(L, M, set(c))

    @lru_cache(None)
    def dp(mask):
        if mask == 0:
            return (0.0, ())
        i = next(k for k in range(n) if mask >> k & 1)
        best = (math.inf, ())
        others = [k for k in range(n) if (mask >> k & 1) and k != i]
        for r in range(0, block_max):
            for cc in itertools.combinations(others, r):
                blk = (i,) + cc
                m2 = mask
                for k in blk:
                    m2 &= ~(1 << k)
                val, parts = dp(m2)
                key = tuple(ps[k] for k in sorted(blk))
                if val + fl[key] < best[0]:
                    best = (val + fl[key], parts + (key,))
        return best

    val, parts = dp((1 << n) - 1)
    return {"block_max": block_max, "M": M, "value": val,
            "clusters": [list(c) for c in sorted(parts)],
            "cluster_floors": {",".join(map(str, c)): fl[c] for c in sorted(parts)}}


# ------------------------------------------------------------------ prices

#: Recorded calibration runs (hunts/oob_envelope/numerics/RUNS.md, RESULTS.md).
STAGE_B_L119 = {"L": 1.19, "T": 500, "N": 500, "q": 96, "bits": 384, "panels": 1000,
                "unit_core_s": 4849.0, "reducer_s": 88.0, "lam_min": 5.77564879389e-48}
STAGE_A_L119 = {"L": 1.19, "T": 525, "N": 360, "q": 64, "bits": 384, "panels": 1050,
                "unit_core_s": 2776.0, "n_mat": 3}
#: Unit costs measured on the M1 (RUNS.md "Measured unit costs", 384 bits).
M1_BESSEL = ((629, 0.033), (1259, 0.151))       # (K, seconds per node)
M1_PRODUCT = ((315, 0.3), (630, 1.4))           # (N, seconds per panel product, q = 96)
BESSEL_EXP = math.log(M1_BESSEL[1][1] / M1_BESSEL[0][1]) / math.log(M1_BESSEL[1][0] / M1_BESSEL[0][0])
PRODUCT_EXP = math.log(M1_PRODUCT[1][1] / M1_PRODUCT[0][1]) / math.log(M1_PRODUCT[1][0] / M1_PRODUCT[0][0])
BITS_EXP = 1.6   # assumed growth of Arb multiplication with precision (a model)


def bessel_s(K: int, bits: int) -> float:
    return M1_BESSEL[0][1] * (K / M1_BESSEL[0][0]) ** BESSEL_EXP * (bits / 384) ** BITS_EXP


def product_s(N: int, q: int, bits: int) -> float:
    return M1_PRODUCT[1][1] * (N / M1_PRODUCT[1][0]) ** PRODUCT_EXP * (q / 96) * (bits / 384) ** BITS_EXP


def _m1_seconds(N, T, bits, q, n_mat, h=0.5):
    panels = T / h
    return panels * q * bessel_s(2 * N, bits) + panels * n_mat * product_s(N, q, bits)


#: Remote speed factor, fitted so the model reproduces stage B's 4849 unit core-s.
SPEED = STAGE_B_L119["unit_core_s"] / _m1_seconds(500, 500, 384, 96, 1)


def assembly_core_hours(N: int, T: float, bits: int, q: int = 96, n_mat: int = 1) -> float:
    return SPEED * _m1_seconds(N, T, bits, q, n_mat) / 3600.0


def positivity_core_hours(N: int, bits: int) -> float:
    """Shifted Cholesky plus residual, scaled as N^3 bits^1.6 from stage B's
    88 s reducer at N = 500, 384 bits."""
    return STAGE_B_L119["reducer_s"] * (N / 500) ** 3 * (bits / 384) ** BITS_EXP / 3600.0


def memory_gb(N: int, bits: int, matrices: int = 4) -> float:
    """Dense N x N Arb matrices: 48 bytes of arb struct, ceil(bits/64) heap limbs
    of 8 bytes and about 16 bytes of allocator overhead per entry. The
    positivity step holds the block, its factor, the residual and a temporary."""
    per = 48 + 8 * math.ceil(bits / 64) + 16
    return matrices * N * N * per / 2 ** 30


#: Window floors lambda* used by the bits rule: CCM even-sector zeta floors from
#: hunts/weil_propagation/numerics/RESULTS.md (s9.4 table, N = 128, at c = 10,
#: 13, 20; the N-saturated value 6.6e-153 at c = 30.5 from s5), with c = e^{2L}.
#: The CCM window form is Zhu's form on a translated window (Fact A there), and
#: stage B's lambda_min(R_H) = 5.78e-48 at L = 1.19 (c = 10.8) sits within a
#: factor 2 of this line; a measured proxy, used only to set precision.
FLOOR_POINTS = ((10.0, 1.74e-43), (13.0, 3.30e-59), (20.0, 2.18e-96), (30.5, 6.6e-153))


def log10_floor(L: float) -> float:
    """Least-squares line log10 lambda* = a + b c through FLOOR_POINTS."""
    xs = np.array([c for c, _ in FLOOR_POINTS])
    ys = np.array([math.log10(v) for _, v in FLOOR_POINTS])
    b, a = np.polyfit(xs, ys, 1)
    return float(a + b * math.exp(2 * L))


def bits_rule(L: float) -> int:
    """Stage B carried lambda = 5.78e-48 (157.3 bits) at 384 bits: ratio 2.44.
    Same ratio, rounded up to a multiple of 64 bits."""
    ratio = 384 / math.log2(1 / STAGE_B_L119["lam_min"])
    need = -log10_floor(L) * math.log2(10)
    return int(64 * math.ceil(ratio * need / 64))


def price(S: float, L: float, beta: float = BETA_RULE) -> dict:
    """T#, N and costs for envelope constant S at half-width L.

    T# = 2 pi e^{S + beta}, beta = 0.5 (oob_envelope MISSION.md seed rule).
    N_rule = e L T# / 2 (same seed rule). N_cal = (500/595) L T#, the mode
    count stage B needed at L = 1.19 (tail coupling 1.4e-87 at x = 595).
    N_scout = 0.6 L T#, the measured stage A rule (2N/x = 1.2)."""
    T = 2 * math.pi * math.exp(S + beta)
    x = L * T
    N_rule = int(math.ceil(math.e * x / 2))
    N_cal = int(math.ceil(STAGE_B_L119["N"] / (STAGE_B_L119["L"] * STAGE_B_L119["T"]) * x))
    N_scout = int(math.ceil(0.6 * x))
    bits = bits_rule(L)
    out = {"S": S, "T_sharp": T, "x": x, "bits": bits,
           "log10_floor_proxy": log10_floor(L)}
    for tag, N in (("rule", N_rule), ("cal", N_cal)):
        out[f"N_{tag}"] = N
        out[f"core_hours_{tag}"] = assembly_core_hours(N, T, bits) + positivity_core_hours(N, bits)
        out[f"memory_gb_{tag}"] = memory_gb(N, bits)
    out["N_scout"] = N_scout
    out["core_hours_scout"] = assembly_core_hours(N_scout, T, bits, q=64, n_mat=3)
    out["memory_gb_scout"] = memory_gb(N_scout, bits, matrices=3)
    return out


# ------------------------------------------------------------------ the DH comb

def dh_lambda(nmax: int):
    """Lambda_f(n), n <= nmax, for the Davenport-Heilbronn function
    f(s) = sum a_n n^{-s}, a = (1, kappa, -kappa, -1, 0) by n mod 5, from
    -f'/f = sum Lambda_f(n) n^{-s}, i.e. a_n log n = sum_{d | n, d > 1}
    Lambda_f(d) a_{n/d}, in Arb (the recursion and kappa of
    oob_envelope/numerics/k2_modal.py, which pinned them against
    rogue_frontier/weil_trunc/galerkin.py to 5e-55)."""
    s5 = arb(5).sqrt()
    kappa = ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)
    pat = [arb(1), kappa, -kappa, arb(-1), arb(0)]
    lam = {}
    for n in range(2, nmax + 1):
        s = pat[(n - 1) % 5] * arb(n).log()
        for d in range(2, n):
            if n % d == 0:
                s -= lam[d] * pat[(n // d - 1) % 5]
        lam[n] = s
    return kappa, lam


#: Lambda_f(n) balls containing 0 with radius below this are treated as zero
#: (Lambda_f(22) = kappa (log 22 - log 2 - log 11) = 0 exactly, for instance);
#: ``dh_dropped_l1`` returns the l1 mass so dropped, which a bound must add.
DH_ZERO_RADIUS = 1e-60


def dh_comb(L: Fraction, with_dropped: bool = False):
    """[(n, 2 Lambda_f(n)/sqrt(n) as arb)] for log n < 2L, decided in Arb."""
    with ctx.workprec(PREC):
        twoL = 2 * to_arb(L)
        nmax = int(math.exp(2 * float(L))) + 2
        _, lam = dh_lambda(nmax)
        out, dropped = [], arb(0)
        for n in range(2, nmax + 1):
            ln = arb(n).log()
            if bool(ln < twoL):
                c = 2 * lam[n] / arb(n).sqrt()
                if lam[n].is_zero():
                    continue
                if c.contains(0) and float(c.rad()) < DH_ZERO_RADIUS:
                    dropped += abs(c)
                    continue
                out.append((n, c))
            elif not bool(ln > twoL):
                raise RuntimeError("undecided")
    return (out, dropped) if with_dropped else out


def dh_coupling_components(L: Fraction):
    """Connected components of the primes p < e^{2L} under 'p and q both divide
    some n with Lambda_f(n) != 0' for the DH comb. A cluster-separable envelope
    (joint.py) needs every comb term inside one cluster, so each component must
    lie inside one cluster."""
    comb = dh_comb(L)
    ps = sorted({q for n, _ in comb for q in range(2, n + 1) if n % q == 0 and _smallest_prime_factor(q) == q})
    parent = {p: p for p in ps}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for n, _ in comb:
        fac = [q for q in ps if n % q == 0]
        for q in fac[1:]:
            parent[find(q)] = find(fac[0])
    comps: dict[int, list[int]] = {}
    for p in ps:
        comps.setdefault(find(p), []).append(p)
    return sorted(comps.values(), key=lambda c: (-len(c), c))


def dh_galerkin_top(L: Fraction, M: int = 4000):
    """Top Galerkin eigenvalue of the DH windowed comb operator
    sum_n Lambda_f(n)/sqrt(n) [phi(x - log n) + phi(x + log n)] (signed
    weights, float, measured). By weak duality (oob_envelope theory (2.1) and
    Proposition 2.1, which use only the band limitation of |F|^2) every
    admissible H for the DH comb has sup(P_DH - H) >= lambda_max(P_DH) >= this
    Rayleigh value."""
    d = 2 * float(L) / M
    diags: dict[int, float] = {}
    for n, c in dh_comb(L):
        w = float(c.mid()) / 2
        u = math.log(n) / d
        k0 = math.floor(u)
        fr = u - k0
        for k, val in ((k0, w * (1 - fr)), (k0 + 1, w * fr)):
            if 0 < k < M:
                diags[k] = diags.get(k, 0.0) + val
                diags[-k] = diags.get(-k, 0.0) + val
    offs = sorted(diags)
    A = sp.diags([np.full(M - abs(k), diags[k]) for k in offs], offs, shape=(M, M), format="csr")
    return float(spla.eigsh(A, k=1, which="LA", tol=1e-11, return_eigenvectors=False)[0])


def dh_k2(L: Fraction, T_feasible: float = 1.0e6) -> dict:
    """K2 gate for DH at window L, the same pipeline as for zeta.

    Envelope stage: the comb is not separable over primes (composite n carry
    Lambda_f(n) != 0), so a cluster must contain each coupling component.
    Components with more than four primes are beyond the whole-torus bound of
    joint.py, so they get H = 0 and the bound sum |c_n|; a singleton prime p
    with only the term n = p gets the one-dimensional floor |c_p|/2 (the
    Fejer limit; any finite degree is larger). The DH symbol is
    Re digamma(3/4 + it/2) + log(5/pi) - P_DH(t) (k2_modal.py), and
    Re digamma(3/4 + it/2) <= log(t/2) + 1/t for t >= 1 (Stirling with the
    remainder sign of a completely monotone tail), so any valid
    beta*(T) <= log(5T/2pi) + 1/T - S. The gate is closed at every T up to
    T_feasible when that upper bound is negative there."""
    comb, dropped = dh_comb(L, with_dropped=True)
    comps = dh_coupling_components(L)
    S_parts = {}
    with ctx.workprec(PREC):
        S = arb(dropped.upper())
        for comp in comps:
            terms = [(n, c) for n, c in comb if prime_factors(n) <= set(comp)]
            if len(comp) == 1 and len(terms) == 1 and terms[0][0] == comp[0]:
                part = abs(terms[0][1]) / 2
                S_parts[",".join(map(str, comp))] = ["one-dimensional floor |c_p|/2", float(part.mid())]
            else:
                part = sum((abs(c) for _, c in terms), arb(0))
                S_parts[",".join(map(str, comp))] = [f"H = 0 on {len(comp)} primes, sum |c_n| over {len(terms)} terms",
                                                     float(part.mid())]
            S += part
        S_up = float(S.upper()) * (1 + 1e-15)
    # least T with log(5T/2pi) + 1/T >= S (increasing in T > 1), by bisection
    def g(T):
        return math.log(5 * T / (2 * math.pi)) + 1 / T - S_up
    lo, hi = 1.0, 1.0
    while g(hi) < 0 and hi < 1e300:
        hi *= 2
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if g(mid) < 0 else (lo, mid)
    T_min = lo
    floor = dh_galerkin_top(L)
    return {"L": str(L), "c": math.exp(2 * float(L)), "comb_terms": len(comb),
            "comb": [[n, float(c.mid())] for n, c in comb],
            "coupling_components": comps, "S_pipeline": S_up, "S_parts": S_parts,
            "T_min_for_beta_positive": T_min, "T_feasible": T_feasible,
            "N_rule_at_T_min": math.e * float(L) * T_min / 2,
            "gate_closed_to_T_feasible": T_min > T_feasible,
            "verdict": "no bound: the envelope gate is closed at every T# up to T_feasible"
            if T_min > T_feasible else "the gate opens: the positivity step decides",
            "dh_comb_floor_galerkin": floor,
            "T_oracle_floor": 2 * math.pi / 5 * math.exp(floor),
            "note": "T_oracle_floor = (2 pi/5) e^{lambda_max(P_DH)} is the least split any envelope for the DH comb "
                    "could reach (weak duality); no evaluable DH envelope is known to reach it"}


def prime_factors(n: int) -> set[int]:
    out, m, q = set(), n, 2
    while q * q <= m:
        while m % q == 0:
            out.add(q)
            m //= q
        q += 1
    if m > 1:
        out.add(m)
    return out


# --------------------------------------------------------------- the driver

def window_table(tag: str, M_enc: int = 8000, M_conv=(2000, 8000, 32000), sine_D=(16, 64)) -> dict:
    """Everything about one window that is cheap: comb, A_L, S*_L ball, S_sep
    ball, evaluable per-prime envelopes, ideal cluster floors by block size."""
    L = WINDOWS[tag]
    t0 = time.time()
    pp = prime_powers(L)
    out = {"tag": tag, "L": f"{L.numerator}/{L.denominator}", "L_float": float(L),
           "c": math.exp(2 * float(L)), "comb": [n for n, _, _ in pp],
           "primes": primes_of(L), "m_p": {str(p): m for p, m in m_of(L).items()}}
    a = A_L(L)
    out["A_L"] = a.str(12)
    enc = s_star_enclosure(L, M_enc)
    out["S_star"] = {"lower": enc["lower_str"], "upper": enc["upper_str"], "M": M_enc,
                     "schur_iteration": enc["schur_iteration"]}
    out["S_star_galerkin"] = {str(M): galerkin_top(L, M) for M in M_conv}
    sf = sep_floor(L)
    out["S_sep"] = {"lower": sf["lower_str"], "upper": sf["upper_str"],
                    "per_prime": {str(p): v for p, v in sf["per_prime"].items()}}
    out["S_sep_sine"] = {}
    for D in sine_D:
        r = sep_sine(L, D)
        out["S_sep_sine"][str(D)] = {"S": f"{r['S'].numerator}/{r['S'].denominator}", "S_float": r["S_float"],
                                     "max_freq": r["max_freq"], "scan_ok": r["scan_ok"]}
    out["partitions"] = {}
    for b in range(1, {6: 4, 8: 5}.get(len(out["primes"]), 6)):
        bp = best_partition(L, b)
        out["partitions"][str(b)] = {"value": bp["value"], "clusters": bp["clusters"],
                                     "cluster_floors": bp["cluster_floors"]}
    out["seconds"] = time.time() - t0
    return out


def price_rows(tab: dict, joint_S: float | None = None, extra=None) -> dict:
    """Prices for the envelopes of one window (see ``price``): Zhu's A_L, the
    evaluable per-prime sine:16 envelope, the per-prime limit, the floor's
    lower end, the joint envelope when built, any extra rows, and the go
    threshold."""
    Lf = tab["L_float"]
    rows = {"A_L (Zhu, H = 0)": float(tab["A_L"].split(" ")[0].strip("[")),
            "S_sep sine:16 (evaluable)": tab["S_sep_sine"]["16"]["S_float"],
            "S_sep limit (not evaluable at finite degree)": float(tab["S_sep"]["upper"]),
            "S*_L lower end (no envelope can go below)": float(tab["S_star"]["lower"])}
    if joint_S is not None:
        rows["joint cluster envelope (evaluable)"] = joint_S
    for k, v in (extra or {}).items():
        rows[k] = v
    rows["go threshold 6.2"] = GO_THRESHOLD
    return {k: price(v, Lf) for k, v in rows.items()}


def price_table_all() -> dict:
    """prices.json: price_rows for every window, reading price_table.json and
    the joint envelope files that exist."""
    tab = json.loads((HERE / "price_table.json").read_text())
    out = {}
    for tag, t in tab.items():
        jp = HERE / f"joint_{tag}.json"
        joint_S = json.loads(jp.read_text())["S"] if jp.exists() else None
        extra = {}
        jp4 = HERE / f"joint_{tag}_four.json"
        if jp4.exists():
            extra["joint four-prime clusters (evaluable)"] = json.loads(jp4.read_text())["S"]
        out[tag] = price_rows(t, joint_S, extra)
    return out


# ------------------------------------------------------ joint envelope drivers

def _weights_from_spec(w):
    return None if w is None else {int(n): Fraction(v) for n, v in w.items()}


def comb_terms(L: Fraction, kind: str) -> list[int]:
    """The integers n of the comb of `kind` on the window L."""
    if kind == "zeta":
        return [n for n, _, _ in prime_powers(L)]
    if kind == "dh":
        return [n for n, _ in dh_comb(L)]
    return [n for n, _ in epstein_comb(L)]


def check_weight_cover(L: Fraction, kind: str, clusters) -> None:
    """Every comb term n must be carried by the clusters with total weight
    exactly 1 (exact Fractions): a cluster without weights carries every term
    whose primes it contains with weight 1. Raises otherwise. This is what
    makes P_L = sum_c P_c an identity rather than an approximation."""
    total: dict[int, Fraction] = {}
    for primes, w in clusters:
        for n in comb_terms(L, kind):
            if not prime_factors(n) <= set(primes):
                continue
            total[n] = total.get(n, Fraction(0)) + (Fraction(1) if w is None else Fraction(w.get(n, 0)))
    bad = {n: str(total.get(n, 0)) for n in comb_terms(L, kind) if total.get(n, Fraction(0)) != 1}
    if bad:
        raise ValueError(f"comb terms not carried with total weight 1: {bad}")


#: K2 scouts: which rival forms are known negative on which window and sector
#: (weil_propagation numerics s3.2 for DH, s9.2 for Epstein; hardened cells plus
#: the nesting argument, ordinary and unreviewed).
K2_CASES = {
    "dh_140_even": {"rival": "Davenport-Heilbronn", "L": "7/5", "sector": "even", "form_known_negative": False,
                    "why": "c = e^{2L} = 16.44 lies below 30.617188; DH's finite-N floors are positive there, "
                           "so a refusal is not required by soundness"},
    "dh_LDH_even": {"rival": "Davenport-Heilbronn", "L": "171079/100000", "sector": "even",
                    "form_known_negative": True, "why": "c = 30.6178 >= 30.617188"},
    "ep_LDH_even": {"rival": "Epstein (1,1,6)", "L": "171079/100000", "sector": "even",
                    "form_known_negative": True, "why": "c = 30.6178 >= 29.304199 (even sector)"},
    "ep_16615_odd": {"rival": "Epstein (1,1,6)", "L": "3323/2000", "sector": "odd", "form_known_negative": True,
                     "why": "c = 27.7426 >= 27.741699 (odd sector)"},
    "ep_16615_even": {"rival": "Epstein (1,1,6)", "L": "3323/2000", "sector": "even",
                      "form_known_negative": False,
                      "why": "c = 27.7426 lies below 29.304199, the even-sector line"},
}


def assemble_k2_scouts(scout_dir: Path) -> dict:
    """k2_scouts.json from the K2 scout outputs in scout_dir (one JSON each)."""
    out = {}
    for key, meta in K2_CASES.items():
        p = Path(scout_dir) / f"{key}.json"
        if not p.exists():
            continue
        d = json.loads(p.read_text())
        rows = d["rows"]
        live = [r for r in rows if "n_neg" in r]
        S = d["S"]
        out[key] = dict(meta, S=S, S_exact=d["S_exact"], envelope=d["envelope"], N=d["N"], q=d["q"],
                        prec=d["prec"], Tmax=d["Tmax"], parity=d["parity"], kind=d["kind"],
                        unit_core_seconds=d["unit_core_seconds"], rows=rows,
                        refused_everywhere=bool(live) and all(r["n_neg"] >= 1 for r in live),
                        first_T_with_beta_positive=min((r["T"] for r in live), default=None))
    return out


def run_joint_spec(spec: dict) -> dict:
    """Build every cluster of a spec with joint.build_cluster (optimizer, then
    the whole-torus bound) and return a part file."""
    sys.path.insert(0, str(HERE))
    import joint  # noqa: E402
    tag = spec["tag"]
    L = WINDOWS[tag] if tag in WINDOWS else Fraction(tag)
    kind = spec.get("kind", "zeta")
    out = {"tag": tag, "L": f"{L.numerator}/{L.denominator}", "kind": kind, "clusters": []}
    for c in spec["clusters"]:
        t0 = time.time()
        r = joint.build_cluster(L, c["primes"], c["D"], tau=spec.get("tau", 2e-4), shell=c.get("shell"),
                                method=c.get("method", spec.get("method", "lse")), kind=kind,
                                weights=_weights_from_spec(c.get("weights")),
                                opt_kwargs=c.get("opt", {}), sb_kwargs=spec.get("sb", {}),
                                verbose=spec.get("verbose", False))
        out["clusters"].append(r)
        print(json.dumps({"cluster": c["primes"], "D": c["D"], "shell": c.get("shell"), "t_opt": r["t_opt"],
                          "U": r["U"], "boxes": r["sup_bound"]["boxes"], "seconds": time.time() - t0}), flush=True)
    return out


def merge_parts(paths, drop=()) -> dict:
    """Merge part files of one window and kind into a joint envelope, re-running
    every check with the current code on the saved dyadic coefficients: the
    whole-torus bound, the frequency audit at 512 bits, the Arb spot check of
    centre values and the Arb check of whole box bounds; and, for overlapping
    clusters, that every comb term's weights sum to exactly 1."""
    sys.path.insert(0, str(HERE))
    import joint  # noqa: E402
    parts = [json.loads(Path(f).read_text()) for f in paths]
    tag, kind = parts[0]["tag"], parts[0].get("kind", "zeta")
    L = WINDOWS[tag] if tag in WINDOWS else Fraction(tag)
    out = {"tag": tag, "L": parts[0]["L"], "kind": kind, "clusters": []}
    total = Fraction(0)
    for part in parts:
        if part["tag"] != tag or part.get("kind", "zeta") != kind:
            raise ValueError("parts of different windows or kinds")
        for c in part["clusters"]:
            if tuple(c["primes"]) in drop:
                continue
            om = [tuple(k) for k in c["omega"]]
            hq = [Fraction(x) for x in c["h"]]
            w = _weights_from_spec(c.get("weights"))
            sb = joint.sup_bound(L, c["primes"], om, hq, tau=c["sup_bound"]["tau"], kind=kind, weights=w)
            sb.pop("best_points", None)
            c["sup_bound_recheck"] = sb
            if abs(sb["U"] - c["U"]) > 2 * c["sup_bound"]["tau"]:
                raise RuntimeError(f"recheck disagrees for {c['primes']}: {sb['U']} vs {c['U']}")
            c["U"] = max(c["U"], sb["U"])
            c["frequency_audit"] = joint.frequency_audit(L, c["primes"], om)
            if not c["frequency_audit"]["ok"]:
                raise RuntimeError("in-band frequency")
            sc = joint.arb_spot_check(L, c["primes"], om, hq, n=60, kind=kind, weights=w)
            c["arb_spot_check"] = {"n": 60, "max_deviation": float(sc["max_deviation"]),
                                   "a_priori_bound": float(sc["a_priori_bound"]), "ok": bool(sc["ok"])}
            bc = joint.arb_box_check(L, c["primes"], om, hq, n=12, kind=kind, weights=w)
            c["arb_box_check"] = bc
            total += Fraction(c["U"])
            out["clusters"].append(c)
            print(json.dumps({"cluster": c["primes"], "U": c["U"], "recheck_U": sb["U"], "boxes": sb["boxes"],
                              "seconds": sb["seconds"]}), flush=True)
    check_weight_cover(L, kind, [(c["primes"], _weights_from_spec(c.get("weights"))) for c in out["clusters"]])
    out["weights_cover_comb"] = True
    if kind == "dh":
        _, dropped = dh_comb(L, with_dropped=True)
        drop = arb_upper_fraction(dropped) if not dropped.is_zero() else Fraction(0)
        out["dropped_l1_upper"] = float(drop)
        total += drop
    out["S_exact"] = f"{total.numerator}/{total.denominator}"
    out["S"] = float(total)
    out["S_rounded_up"] = rounded_up(total, 10)
    return out



def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--table", nargs="*", default=None, help="window tags for the cheap table")
    ap.add_argument("--joint-spec", default=None,
                    help="JSON spec of a joint envelope (tag, kind, tau, method, clusters with primes, D, shell, "
                         "weights); writes the part file given by --out")
    ap.add_argument("--k2", action="store_true")
    ap.add_argument("--overlap", default=None, help="window tag for the overlapping-cluster exploration")
    ap.add_argument("--hard-partitions", nargs="*", default=None,
                    help="window tags: Arb lower bounds for the best partitions into clusters")
    ap.add_argument("--transfer", default=None, help="window tag: K2 envelope-transfer witness")
    ap.add_argument("--prices", action="store_true", help="write prices.json from the table and joint files")
    ap.add_argument("--k2-scouts", default=None, help="directory of K2 scout outputs: write k2_scouts.json")
    ap.add_argument("--drop", nargs="*", default=None,
                    help="clusters (comma-separated primes) to leave out of a merge, e.g. a superseded build")
    ap.add_argument("--merge", nargs="*", default=None,
                    help="joint part files to merge and re-bound with the current sup_bound")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    if args.prices:
        (HERE / "prices.json").write_text(json.dumps(price_table_all(), indent=1))
    if args.k2_scouts:
        (HERE / "k2_scouts.json").write_text(json.dumps(assemble_k2_scouts(Path(args.k2_scouts)), indent=1))
    if args.merge is not None:
        drop = tuple(tuple(int(x) for x in g.split(",")) for g in (args.drop or []))
        out = merge_parts([Path(f) for f in args.merge], drop)
        Path(args.out or HERE / f"joint_{out['tag']}.json").write_text(json.dumps(out, indent=1))
    if args.table is not None:
        tags = args.table or list(WINDOWS)
        res = {}
        for tg in tags:
            res[tg] = window_table(tg)
            print(json.dumps({tg: {k: res[tg][k] for k in ("S_star", "S_sep", "seconds")}}), flush=True)
        Path(args.out or HERE / "price_table.json").write_text(json.dumps(res, indent=1))
    if args.joint_spec is not None:
        spec = json.loads(Path(args.joint_spec).read_text())
        out = run_joint_spec(spec)
        Path(args.out or HERE / f"joint_{spec['tag']}.json").write_text(json.dumps(out, indent=1))
    if args.hard_partitions is not None:
        res = {}
        for tg in args.hard_partitions:
            L = WINDOWS[tg]
            top = {6: 3, 8: 4}.get(len(primes_of(L)), 5)
            res[tg] = {str(b): hardened_partition_floor(L, b) for b in range(1, top + 1)}
            print(json.dumps({tg: res[tg]}), flush=True)
        Path(args.out or HERE / "partition_lower.json").write_text(json.dumps(res, indent=1))
    if args.overlap is not None:
        r = overlap_split(WINDOWS[args.overlap])
        Path(args.out or HERE / f"overlap_{args.overlap}.json").write_text(json.dumps(r, indent=1))
        print(json.dumps(r), flush=True)
    if args.transfer is not None:
        r = transfer_witness(WINDOWS[args.transfer], HERE / f"joint_{args.transfer}.json")
        Path(args.out or HERE / f"transfer_{args.transfer}.json").write_text(json.dumps(r, indent=1))
        print(json.dumps(r), flush=True)
    if args.k2:
        res = {}
        for tg in ("1.4", "L_DH"):
            r = dh_k2(WINDOWS[tg])
            res[tg] = r
            print(json.dumps({tg: r["verdict"], "S": r["S_pipeline"], "T_min": r["T_min_for_beta_positive"]}),
                  flush=True)
        Path(args.out or HERE / "k2_dh.json").write_text(json.dumps(res, indent=1))
        ep = {}
        for tag, L in (("1.6615", Fraction(16615, 10000)), ("L_DH", WINDOWS["L_DH"])):
            ep[tag] = epstein_k2(L)
            print(json.dumps({"epstein " + tag: ep[tag]["coupling_components"], "S_H0": ep[tag]["S_H0"],
                              "T_min_H0": ep[tag]["T_min_H0"], "floor": ep[tag]["comb_floor_galerkin"]}), flush=True)
        (HERE / "k2_epstein.json").write_text(json.dumps(ep, indent=1))



def line_values(L: Fraction, clusters, t: np.ndarray, comb: str = "zeta") -> np.ndarray:
    """Float values of P(t) - H(t) on the line, P the zeta or DH comb and H the
    joint cluster envelope (measured; used only to find witness points)."""
    if comb == "zeta":
        terms = [(2 * math.log(p) / p ** (m / 2), math.log(n)) for n, p, m in prime_powers(L)]
    else:
        terms = [(float(c.mid()), math.log(n)) for n, c in dh_comb(L)]
    out = np.zeros_like(t)
    for c, ln in terms:
        out += c * np.cos(t * ln)
    for primes, om, hs in clusters:
        logs = np.array([math.log(p) for p in primes])
        for k, hk in zip(om, hs):
            out -= float(hk) * np.cos(t * float(np.dot(k, logs)))
    return out


def transfer_witness(L: Fraction, joint_path: Path, t_max: float = 4.0e3, step: float = 1.0 / 128):
    """K2, envelope transfer: zeta's joint H and S are not an envelope for the
    DH comb. Scan t in [0, t_max] (float) for the largest P_DH - H_zeta, then
    evaluate it in Arb at that exact dyadic t. A value above S_zeta refutes the
    transfer at one explicit point. The same scan of P_zeta - H_zeta is the
    control and must stay below S_zeta."""
    d = json.loads(Path(joint_path).read_text())
    clusters = [(c["primes"], [tuple(k) for k in c["omega"]], [Fraction(x) for x in c["h"]]) for c in d["clusters"]]
    S = Fraction(d["S_exact"])
    best = {"dh": (-math.inf, 0.0), "zeta": (-math.inf, 0.0)}
    n = int(t_max / step)
    for s0 in range(0, n, 1 << 18):
        t = (np.arange(s0, min(n, s0 + (1 << 18))) * step).astype(float)
        for kind in ("dh", "zeta"):
            v = line_values(L, clusters, t, comb=kind)
            i = int(np.argmax(v))
            if v[i] > best[kind][0]:
                best[kind] = (float(v[i]), float(t[i]))
    out = {"S_zeta": float(S), "t_max": t_max, "step": step}
    with ctx.workprec(PREC):
        for kind, (vf, tf) in best.items():
            tq = Fraction(tf).limit_denominator(1 << 20)
            ta = to_arb(tq)
            if kind == "zeta":
                val = sum((2 * w_arb(p, m) * (ta * arb(nn).log()).cos() for nn, p, m in prime_powers(L)), arb(0))
            else:
                val = sum((c * (ta * arb(nn).log()).cos() for nn, c in dh_comb(L)), arb(0))
            for primes, om, hs in clusters:
                logs = [arb(p).log() for p in primes]
                for k, hk in zip(om, hs):
                    val -= to_arb(hk) * (ta * sum((ki * li for ki, li in zip(k, logs)), arb(0))).cos()
            out[kind] = {"t": f"{tq.numerator}/{tq.denominator}", "float_max": vf,
                         "arb_value": val.str(12), "exceeds_S": bool(val > to_arb(S)),
                         "below_S": bool(val < to_arb(S))}
    return out


def overlap_split(L: Fraction, block: int = 3, M: int = 600, iters: int = 120, eta: float = 0.5):
    """Ideal value of OVERLAPPING clusters (measured exploration). Every set of
    `block` primes is a cluster; prime p's comb is split as sum_c alpha_{c,p}
    phi_p over the clusters containing it (alpha >= 0, summing to 1). Then
    P_L = sum_c P_c^alpha, sup(P_L - H) <= sum_c sup(P_c^alpha - H_c), and by
    weak duality cluster by cluster the least value of the right side is
    V = min_alpha sum_c lambda_max(P_c^alpha), a convex problem (lambda_max of a
    nonnegative combination is convex in the weights). Mirror descent on each
    prime's simplex with the gradient <v_c, P_p v_c>, started from the best
    partition; float Galerkin at M cells, so V is measured, slightly low."""
    ps = primes_of(L)
    d = 2 * float(L) / M

    def mat_for(p):
        diags: dict[int, float] = {}
        for w, s, _, _ in _shifts(L, {p}):
            u = s / d
            k0 = math.floor(u)
            fr = u - k0
            for k, val in ((k0, w * (1 - fr)), (k0 + 1, w * fr)):
                if 0 < k < M:
                    diags[k] = diags.get(k, 0.0) + val
                    diags[-k] = diags.get(-k, 0.0) + val
        offs = sorted(diags)
        return sp.diags([np.full(M - abs(k), diags[k]) for k in offs], offs, shape=(M, M), format="csr")

    Pm = {p: mat_for(p) for p in ps}
    clusters = list(itertools.combinations(ps, block))
    start = best_partition(L, block, M)
    alpha = {c: {p: 1e-3 for p in c} for c in clusters}
    for c in start["clusters"]:
        if tuple(c) in alpha:
            for p in c:
                alpha[tuple(c)][p] = 1.0
    for p in ps:
        tot = sum(alpha[c][p] for c in clusters if p in c)
        for c in clusters:
            if p in c:
                alpha[c][p] /= tot
    best_V, hist = math.inf, []
    for _ in range(iters):
        V, grads = 0.0, {}
        for c in clusters:
            A = sum(alpha[c][p] * Pm[p] for p in c)
            val, vec = spla.eigsh(A, k=1, which="LA", tol=1e-9)
            v = vec[:, 0]
            V += float(val[0])
            grads[c] = {p: float(v @ (Pm[p] @ v)) for p in c}
        hist.append(V)
        best_V = min(best_V, V)
        for p in ps:
            cs = [c for c in clusters if p in c]
            lg = np.array([math.log(max(alpha[c][p], 1e-300)) - eta * grads[c][p] for c in cs])
            lg -= lg.max()
            wv = np.exp(lg)
            wv /= wv.sum()
            for c, x in zip(cs, wv):
                alpha[c][p] = float(x)
    return {"L": str(L), "block": block, "M": M, "iters": iters, "V_overlap": best_V,
            "partition_value": start["value"], "history": [hist[0], hist[len(hist) // 2], hist[-1]]}



# ------------------------------------------------------------ Epstein (1,1,6)

EPSTEIN_FORM = (1, 1, 6)


def epstein_lambda(nmax: int):
    """Lambda_Q(n), n <= nmax, for zeta_Q, Q = x^2 + xy + 6y^2, from
    b_n log n = sum_{d | n} Lambda_Q(d) b_{n/d}, b_n = r_Q(n) / r_Q(1) (exact
    rationals from zeta.epstein.epstein_representation_count), in Arb. The
    same recursion as zeta.epstein.log_derivative_coefficients, in balls."""
    from zeta.epstein import epstein_representation_count
    r = {n: epstein_representation_count(n, EPSTEIN_FORM) for n in range(1, nmax + 1)}
    b = {n: Fraction(r[n], r[1]) for n in r}
    lam = {}
    for n in range(2, nmax + 1):
        v = to_arb(b[n]) * arb(n).log()
        for d in range(2, n):
            if n % d == 0 and b[n // d] != 0:
                v -= lam[d] * to_arb(b[n // d])
        lam[n] = v
    return lam


def epstein_comb(L: Fraction):
    """[(n, 2 Lambda_Q(n)/sqrt(n) as arb)] for log n < 2L with Lambda_Q(n) != 0."""
    with ctx.workprec(PREC):
        twoL = 2 * to_arb(L)
        nmax = int(math.exp(2 * float(L))) + 2
        lam = epstein_lambda(nmax)
        out = []
        for n in range(2, nmax + 1):
            ln = arb(n).log()
            if bool(ln < twoL):
                c = 2 * lam[n] / arb(n).sqrt()
                if lam[n].is_zero() or (c.contains(0) and float(c.rad()) < DH_ZERO_RADIUS):
                    continue
                out.append((n, c))
            elif not bool(ln > twoL):
                raise RuntimeError("undecided")
    return out


def epstein_k2(L: Fraction) -> dict:
    """K2 gate for Epstein (1,1,6), the same pipeline. Its completed function
    23^{s/2} Gamma_R(s) Gamma_R(s+1) zeta_Q(s)/2 (weil_propagation s9.1) gives
    the symbol log 23 + [Re psi(1/4 + it/2) - log pi] + [Re psi(3/4 + it/2) - log pi]
    - P_Q(t), with the pole term of zeta. With Zhu's Lemma 3.1 and the measured
    bound Re psi(3/4 + it/2) >= log(t/2) - 1/t (test_price.py), a valid
    beta*(T) = log 23 + 2 log(T/2pi) - 2/T - S, so the gate opens at
    T ~ 2 pi e^{(S - log 23)/2}: degree two halves the exponent."""
    comb = epstein_comb(L)
    ps = sorted({q for n, _ in comb for q in prime_factors(n)})
    parent = {p: p for p in ps}

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for n, _ in comb:
        fac = sorted(prime_factors(n))
        for q in fac[1:]:
            parent[find(q)] = find(fac[0])
    comps: dict[int, list[int]] = {}
    for p in ps:
        comps.setdefault(find(p), []).append(p)
    comps = sorted(comps.values(), key=lambda c: (-len(c), c))
    with ctx.workprec(PREC):
        S = sum((abs(c) for _, c in comb), arb(0))
        S_up = float(S.upper()) * (1 + 1e-15)
        log23 = math.log(23)
    def g(T):
        return log23 + 2 * math.log(T / (2 * math.pi)) - 2 / T - S_up
    lo, hi = 1.0, 2.0
    while g(hi) < 0:
        hi *= 2
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if g(mid) < 0 else (lo, mid)
    # comb operator floor (positive weights here, so Galerkin is a lower bound)
    d = 2 * float(L) / 4000
    diags: dict[int, float] = {}
    for n, c in comb:
        w = float(c.mid()) / 2
        u = math.log(n) / d
        k0 = math.floor(u)
        fr = u - k0
        for k, val in ((k0, w * (1 - fr)), (k0 + 1, w * fr)):
            if 0 < k < 4000:
                diags[k] = diags.get(k, 0.0) + val
                diags[-k] = diags.get(-k, 0.0) + val
    offs = sorted(diags)
    A = sp.diags([np.full(4000 - abs(k), diags[k]) for k in offs], offs, shape=(4000, 4000), format="csr")
    floor = float(spla.eigsh(A, k=1, which="LA", tol=1e-11, return_eigenvectors=False)[0])
    return {"L": str(L), "c": math.exp(2 * float(L)), "comb": [[n, float(c.mid())] for n, c in comb],
            "coupling_components": comps, "S_H0": S_up, "T_min_H0": lo,
            "comb_floor_galerkin": floor,
            "T_floor": 2 * math.pi * math.exp((floor - log23) / 2),
            "note": "Epstein's even sector is negative only from L = 1.68887 and its odd sector from "
                    "L = 1.66147 (weil_propagation s9.2); an even-sector pipeline must refuse at L_DH, "
                    "not at L = 1.6615"}



def rayleigh_lower(L: Fraction, M: int, primes=None, bits: int = 24) -> Fraction:
    """Lower end only of ``s_star_enclosure``: the exact Rayleigh quotient of
    the rounded Galerkin Perron vector for the comb restricted to `primes`, as
    the lower endpoint of an Arb ball (a dyadic rational). A lower bound for
    lambda_max of that restricted comb operator, hence (weak duality, cluster by
    cluster) for the envelope constant of any H coupling only those primes."""
    _, vec = galerkin_top(L, M, primes, None, want_vector=True)
    v = np.maximum(np.rint(vec / vec.max() * (2 ** bits)).astype(np.int64), 1)
    with ctx.workprec(PREC):
        delta = 2 * to_arb(L) / M
        num = arb(0)
        R0 = int(np.dot(v.astype(object), v.astype(object)))
        for n, p, m in prime_powers(L):
            if primes is not None and p not in primes:
                continue
            u = arb(n).log() / delta
            fl = int(math.floor(float(u.mid())))
            if not (bool(u > fl) and bool(u < fl + 1)):
                raise RuntimeError("undecided floor")
            fr = u - fl
            R1 = int(np.dot(v[: M - fl].astype(object), v[fl:].astype(object))) if fl < M else 0
            R2 = int(np.dot(v[: M - fl - 1].astype(object), v[fl + 1:].astype(object))) if fl + 1 < M else 0
            num += 2 * w_arb(p, m) * ((1 - fr) * R1 + fr * R2)
        return arb_lower_fraction(num / R0)


def hardened_partition_floor(L: Fraction, block_max: int, M: int = 1200) -> dict:
    """The least sum over partitions into clusters of at most `block_max` primes
    of the Arb Rayleigh lower ends of the cluster floors: a lower bound for the
    envelope constant of every H that couples primes only within the clusters
    of some such partition (exact search over subsets)."""
    ps = primes_of(L)
    n = len(ps)
    lo = {}
    for r in range(1, block_max + 1):
        for c in itertools.combinations(ps, r):
            lo[c] = rayleigh_lower(L, M, set(c))

    @lru_cache(None)
    def dp(mask):
        if mask == 0:
            return (Fraction(0), ())
        i = next(k for k in range(n) if mask >> k & 1)
        best = None
        others = [k for k in range(n) if (mask >> k & 1) and k != i]
        for r in range(0, block_max):
            for cc in itertools.combinations(others, r):
                blk = (i,) + cc
                m2 = mask
                for k in blk:
                    m2 &= ~(1 << k)
                val, parts = dp(m2)
                key = tuple(ps[k] for k in sorted(blk))
                cand = (val + lo[key], parts + (key,))
                if best is None or cand[0] < best[0]:
                    best = cand
        return best

    val, parts = dp((1 << n) - 1)
    return {"block_max": block_max, "M": M, "value_lower": rounded_down(val, 10), "value_float": float(val),
            "clusters": [list(c) for c in sorted(parts)]}


if __name__ == "__main__":
    main()
