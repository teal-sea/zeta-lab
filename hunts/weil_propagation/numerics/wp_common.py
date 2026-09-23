"""Shared helpers for the window-transport numerics.

Everything that assembles the truncated Weil form is imported from
``hunts/rogue_frontier/weil_trunc`` (``enclosures.BallTruncation`` for the Arb
route, ``galerkin.Truncation`` for the mpmath route). Nothing is re-derived
here except the split of the prime block by coefficient subset (needed for
the "new prime-power terms" decomposition); ``components`` checks that the
split pieces sum back to the imported matrix entry by entry, so the split
cannot drift from the validated assembly.

Conventions (identical to weil_trunc):
  L = log c; even sector basis e_0 = L^{-1/2}, e_k = sqrt(2/L) cos(2 pi k y/L)
  on [0, L]; v in R^{N+1}. The window c is passed as an exact rational
  (flint.fmpq) so the Arb and mpmath routes see the same c; the grids use
  dyadic c only.

Linear algebra: the ground pair comes from inverse iteration on the
midpoint matrix (flint arb_mat.solve, algorithm="approx": a float solve at
the working precision), then every reported number about that exact vector
(Rayleigh quotient, residual, overlaps, energies) is computed in balls.
A ball Rayleigh quotient is a rigorous UPPER bound on lambda_min; a rigorous
lower bound needs a ball LDL^T at a shift (``temple_bracket``).
"""

from __future__ import annotations

import copy
import json
import math
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")
if WT not in sys.path:
    sys.path.insert(0, WT)

from flint import acb, arb, arb_mat, ctx, fmpq  # noqa: E402

import enclosures as EN  # noqa: E402
import galerkin as GK  # noqa: E402

# DH off-line zeros (weil_trunc/dhneg_scan.py pins rho_1 to 50 digits;
# rho_2 is the 10-digit findroot polish recorded in weil_trunc RESULTS s8.2).
GAMMA_OFF = "85.699348485377592171929267708941729037987829423408"
DELTA_OFF = "0.30851718245663738555335196060684412785067026830502"
GAMMA_OFF2 = "114.1633427308"
DELTA_OFF2 = "0.1508300806"

# working precision (bits) by kind; zeta eigenvalues reach 1e-140 at N=128
PREC = {"dh": 400, "zeta": 900}


def prec_for(kind: str, N: int) -> int:
    if kind == "dh":
        return 400 if N <= 192 else 600
    # zeta lam_min(31, N): 4.8e-100 (N=60), 2.9e-141 (N=128); keep >= 2x digits
    return 900 if N <= 128 else (1400 if N <= 192 else 2000)


# ---------------------------------------------------------------------------
# c as an exact rational
# ---------------------------------------------------------------------------


def cq(c) -> fmpq:
    """Exact rational window parameter (dyadic on every grid used here)."""
    if isinstance(c, fmpq):
        return c
    f = Fraction(c).limit_denominator(1 << 40) if isinstance(c, float) else Fraction(c)
    return fmpq(f.numerator, f.denominator)


def cstr(c) -> str:
    q = cq(c)
    return str(q.p) if q.q == 1 else f"{q.p}/{q.q}"


def cfloat(c) -> float:
    return float(cq(c))


# ---------------------------------------------------------------------------
# assembly (imported) and ball helpers
# ---------------------------------------------------------------------------


def build(c, N: int, kind: str, prec: int | None = None):
    """(BallTruncation, even-sector arb_mat) at exact window c."""
    prec = prec or prec_for(kind, N)
    bt = EN.BallTruncation(cq(c), N, kind=kind, prec=prec)
    return bt, arb_mat(bt.even_matrix())


def col(vals) -> arb_mat:
    return arb_mat(len(vals), 1, list(vals))


def dot(x: arb_mat, y: arb_mat) -> arb:
    n = x.nrows()
    return sum((x[i, 0] * y[i, 0] for i in range(n)), arb(0))


def quad(A: arb_mat, x: arb_mat) -> arb:
    """x^T A x in balls."""
    return dot(x, A * x)


def rq(A: arb_mat, x: arb_mat) -> arb:
    return quad(A, x) / dot(x, x)


def _mid_unit(y: arb_mat) -> arb_mat:
    n = y.nrows()
    nrm = dot(y, y).sqrt()
    return arb_mat(n, 1, [(y[i, 0] / nrm).mid() for i in range(n)])


def _fix_sign(x: arb_mat) -> arb_mat:
    """Sign convention: v_0 > 0 (the ground states here have |v_0| ~ 0.7)."""
    if x[0, 0] < 0:
        return arb_mat(x.nrows(), 1, [-x[i, 0] for i in range(x.nrows())])
    return x


def lowest_pairs(A: arb_mat, k: int = 2, iters: int = 6):
    """Lowest k eigenpairs of the symmetric ball matrix A (by midpoint).

    Inverse iteration with deflation. Returns list of (rq_ball, vector)
    with vectors as exact-midpoint unit columns (v_0 > 0 for the first).
    The lowest eigenvalues here are separated by ~1e6..1e9 ratios, so a few
    iterations saturate; the returned residual norms say how well.
    """
    Am = A.mid()
    n = A.nrows()
    out = []
    for j in range(k):
        x = _mid_unit(arb_mat(n, 1, [arb(1 + ((i * 7919 + 13 * j) % 97) / 97.0) for i in range(n)]))
        for _ in range(iters):
            y = Am.solve(x, algorithm="approx")
            for _, v in out:
                y = y - v * dot(v, y).mid()
            x = _mid_unit(y)
        if j == 0:
            x = _fix_sign(x)
        out.append((rq(A, x), x))
    return out


def residual_norm(A: arb_mat, x: arb_mat, rho: arb) -> arb:
    r = A * x - x * rho
    return dot(r, r).sqrt()


def temple_bracket(A: arb_mat, x: arb_mat, shift) -> dict:
    """Rigorous bracket for lambda_min from an exact vector x.

    Ball LDL^T of A - shift*I with exactly one negative pivot proves
    lambda_1 < shift <= lambda_2 (Sylvester); then Temple's inequality with
    rho = RQ(x) < shift gives lambda_1 >= rho - eps^2 / (shift - rho),
    eps = ||A x - rho x|| / ||x||. Upper bound: rho itself.
    """
    M = [[A[i, j] for j in range(A.ncols())] for i in range(A.nrows())]
    npos, nneg, concl = EN.ldlt_inertia(M, arb(shift))
    rho = rq(A, x)
    eps = residual_norm(A, x, rho) / dot(x, x).sqrt()
    ok = bool(concl and nneg == 1 and (rho < arb(shift)))
    lo = (rho - eps * eps / (arb(shift) - rho)) if ok else None
    return {
        "shift": str(shift),
        "ldl_inertia_at_shift": [npos, nneg, bool(concl)],
        "rq_ball": rho.str(20, radius=True),
        "upper": rho.upper().str(20, radius=False),
        "lower": lo.lower().str(20, radius=False) if ok else None,
        "residual_eps": eps.str(5),
        "conclusive": ok,
    }


def ldl_prec(kind: str, N: int) -> int:
    """Ball-LDL precision that was conclusive in the smoke tests (zeta at
    (31, 128) needed 1600 bits; prec 900 stalled at pivot 67). Callers retry
    at double precision when a factorization is inconclusive."""
    if kind == "dh":
        return 400 if N <= 128 else 800
    return 1600 if N <= 128 else 3200


def ldl_signs(A: arb_mat, shift=None):
    """Inertia (n_pos, n_neg, conclusive) of A - shift I by ball LDL^T."""
    M = [[A[i, j] for j in range(A.ncols())] for i in range(A.nrows())]
    return EN.ldlt_inertia(M, arb(shift) if shift is not None else arb(0))


def mu0(v: arb_mat) -> arb:
    """Edge amplitude mu_0 = v_0 + sqrt2 sum_k v_k = sqrt(L) f_v(0) = sqrt(L) f_v(L)."""
    s2 = arb(2).sqrt()
    return v[0, 0] + s2 * sum((v[i, 0] for i in range(1, v.nrows())), arb(0))


def as_str(x: arb, d: int = 20) -> str:
    return x.mid().str(d) if x.rad() == 0 else x.str(d, radius=True)


def fnum(x: arb) -> float:
    return float(x.mid())


# ---------------------------------------------------------------------------
# the common function space: zero extension (centered) between windows
# ---------------------------------------------------------------------------


def gram_zero_ext(c, N: int, c2, N2: int) -> arb_mat:
    """G[j,k] = <e_j^(L), e_k^(L2)> in L^2(R), both even bases centered at 0.

    e_j^(L)(x) = n_j (-1)^j cos(2 pi j x / L) on [-L/2, L/2], zero outside,
    n_0 = L^-1/2, n_j = (2/L)^1/2.  Requires L <= L2 (the smaller window's
    support is where the product lives):
      int_{-L/2}^{L/2} cos(a x) cos(b x) dx = (L/2)[sinc((a-b)L/2) + sinc((a+b)L/2)].
    For c == c2 this is the identity; the zero-extended vector v at window c
    has coordinates G^T v in the c2 basis (its orthogonal projection).
    """
    L = arb(cq(c)).log()
    L2 = arb(cq(c2)).log()
    pi = arb.pi()
    n1 = [L.rsqrt()] + [(2 / L).sqrt()] * N
    n2 = [L2.rsqrt()] + [(2 / L2).sqrt()] * N2
    G = arb_mat(N + 1, N2 + 1)
    half = L / 2
    for j in range(N + 1):
        a = 2 * pi * j / L
        for k in range(N2 + 1):
            b = 2 * pi * k / L2
            val = half * (((a - b) * half).sinc() + ((a + b) * half).sinc())
            sgn = -1 if (j + k) % 2 else 1
            G[j, k] = sgn * n1[j] * n2[k] * val
    return G


def transpose_times(G: arb_mat, v: arb_mat) -> arb_mat:
    return G.transpose() * v


# ---------------------------------------------------------------------------
# component split of the even-sector matrix (for the decomposition task)
# ---------------------------------------------------------------------------


def _coeffs(bt):
    """(y_n = log n as arb, w_n = Lambda(n) n^-1/2 as arb, n) for the
    coefficient list BallTruncation used (same formulas as its __init__)."""
    c = bt.c
    if bt.kind == "zeta":
        raw = [(q, arb(p).log()) for (q, p) in GK.prime_powers_upto(float(c))]
    else:
        raw = bt._dh_coeffs(int(c))
    return [(arb(q).log(), lam / arb(q).sqrt(), q) for q, lam in raw]


def _prime_seqs(bt, coeffs):
    N = bt.N
    L = bt.L
    pi = bt._pi
    P = [arb(0)] * (N + 1)
    R = [arb(0)] * (N + 1)
    for y, w, _ in coeffs:
        for k in range(N + 1):
            om = 2 * pi * k / L
            P[k] += w * (om * y).sin()
            R[k] += w * 2 * (1 - y / L) * (om * y).cos()
    return P, R


def _matrix_from(bt, S=None, archdiag=None, P=None, R=None, pole=False):
    b = copy.copy(bt)
    z = [arb(0)] * (bt.N + 1)
    b._S = S if S is not None else z
    b._archdiag = archdiag if archdiag is not None else z
    b._P = P if P is not None else z
    b._R = R if R is not None else z
    if not pole:
        b.kind = "dh"  # w02 is the only kind-dependent entry; "dh" zeroes it
    return arb_mat(b.even_matrix())


def components(bt, split=None, check: bool = True) -> dict:
    """Even-sector pieces of E: pole (W02), arch (-WR), prime (-Wp).

    If ``split`` is given the prime block is split into n <= split ("prime_old")
    and n > split ("prime_new"). With check=True, asserts that the pieces sum
    to the imported matrix (every entry of the difference is a ball
    containing 0) and returns the largest difference radius.
    """
    out = {}
    out["pole"] = _matrix_from(bt, pole=True) if bt.kind == "zeta" else None
    out["arch"] = _matrix_from(bt, S=bt._S, archdiag=bt._archdiag)
    cs = _coeffs(bt)
    if split is None:
        groups = {"prime": cs}
    else:
        s = int(math.floor(float(cq(split)) + 1e-12))
        groups = {
            "prime_old": [t for t in cs if t[2] <= s],
            "prime_new": [t for t in cs if t[2] > s],
        }
    for name, sub in groups.items():
        P, R = _prime_seqs(bt, sub)
        out[name] = _matrix_from(bt, P=P, R=R)
    if check:
        full = arb_mat(bt.even_matrix())
        tot = out["arch"]
        if out["pole"] is not None:
            tot = tot + out["pole"]
        for name in groups:
            tot = tot + out[name]
        D = full - tot
        worst = arb(0)
        for i in range(D.nrows()):
            for j in range(D.ncols()):
                if not D[i, j].contains(0):
                    raise AssertionError(f"component split disagrees at ({i},{j}): {D[i, j]}")
                worst = max(worst, abs(D[i, j]).mid() + D[i, j].rad(), key=float)
        out["_split_check_max"] = float(worst)
    return out


# ---------------------------------------------------------------------------
# the entire transform and the zero-side off-line terms
# ---------------------------------------------------------------------------


def F_even_acb(v: arb_mat, L: arb, z: acb) -> acb:
    """F_v(z) = 2 sin(zL/2) [v_0/z + sum_k sqrt2 v_k z/(z^2 - om_k^2)]."""
    s2 = arb(2).sqrt()
    pi = arb.pi()
    s = acb(v[0, 0]) / z
    for k in range(1, v.nrows()):
        om = 2 * pi * k / L
        s += s2 * v[k, 0] * z / (z * z - om * om)
    return 2 * (z * L / 2).sin() * s


def offline_quadruple(v: arb_mat, L: arb, gamma: str, delta: str) -> arb:
    """4 Re g_v(gamma - i delta), g_v = F_v^2 / L (weil_trunc THEOREM_FEASIBILITY s1.3)."""
    z = acb(arb(gamma), -arb(delta))
    F = F_even_acb(v, L, z)
    return 4 * (F * F).real / L


# ---------------------------------------------------------------------------
# checkpointed JSON store
# ---------------------------------------------------------------------------


def load(path: str, default):
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return default


def save(path: str, d) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(d, f, indent=1)
    os.replace(tmp, path)
