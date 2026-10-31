"""spectral_operator: the CCM zeta spectral triple, built and regularized.

Hunt #150 (``rh_moonshot``), mechanism 5.  Nothing here is a result about RH;
see NOTES.md.

The candidate is the operator of Connes, Consani and Moscovici, "Zeta spectral
triples", arXiv:2511.22755 (section 3, Lemma "key" and Theorem "finmain"):

* E_N: the span of V_n = e^{2 pi i n y / L} / sqrt(L), |n| <= N, on the window
  [0, L], L = log c (CCM write lambda = sqrt(c), L = 2 log lambda);
* T = QW^N: the truncated Weil quadratic form on E_N (real symmetric, entries
  (b_i - b_j)/(i - j) off the diagonal), assembled from the archimedean place,
  the pole and the prime powers n <= c only (``hunts/rogue_frontier/weil_trunc``
  ``enclosures.BallTruncation``, read-only);
* eps_N, xi: the smallest eigenvalue of T and its eigenvector, assumed simple
  and even (gamma V_j = V_{-j}), normalized by <eta | xi> = 1, eta = sum V_j;
* D = diag(n) (the scaling operator in units of 2 pi / L) and the rank-one
  perturbation D' = D - |D xi><eta|.

CCM prove: with W := T - eps_N >= 0 (the positive intertwiner), W D' = D'^T W,
so D' induces a self-adjoint operator D'' on E_N / C xi with the W inner
product; its spectrum is the zero set of the transform of xi, all real.
Spectrum in the z-variable: z = 2 pi s / L.

Provenance (the zero-importing check, MISSION.md and docs/09 s5.1): every
function in the section "definition" below reads only the window c, the band N,
the precision, the prime powers n <= c (zeta: Lambda(n); DH: its coefficients),
the digamma function and the pole.  ``DEFINITION`` lists them;
``test_spectral_operator.py`` scans their source for any read of zeros or of a
xi phase.  The zeros are read only in the section "comparison".
"""

from __future__ import annotations

import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
_WPN = os.path.join(ROOT, "hunts", "weil_propagation", "numerics")
_WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")
_CCM = os.path.join(ROOT, "hunts", "rh_moonshot", "ccm_arithmetic")
for _p in (_WPN, _WT, _CCM, ROOT):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from flint import acb, acb_mat, arb, arb_mat, ctx  # noqa: E402
from mpmath import mp  # noqa: E402

import enclosures as EN  # noqa: E402
import wp_common as WP  # noqa: E402

DEFINITION = ("prec_for", "sectors", "full_matrix", "ground", "xi_full", "operator")


# ---------------------------------------------------------------------------
# definition (reads primes, archimedean place, pole; never the zeros)
# ---------------------------------------------------------------------------


def prec_for(kind: str, c, N: int) -> int:
    """Bits: zeta's lowest eigenvalue falls to 1e-190 and below on this grid."""
    cf = float(WP.cq(c))
    if kind == "zeta":
        return 1000 + int(12 * cf) + 4 * N
    return 500 + 2 * N


def sectors(kind: str, c, N: int, prec: int):
    """(BallTruncation, even arb_mat (N+1), odd arb_mat (N)) at window c."""
    ctx.prec = prec
    bt = EN.BallTruncation(WP.cq(c), N, kind=kind, prec=prec)
    return bt, arb_mat(bt.even_matrix()), arb_mat(bt.odd_matrix())


def full_matrix(bt) -> arb_mat:
    """T in the basis V_n, n = -N..N (row/column index n + N)."""
    N = bt.N
    n = 2 * N + 1
    M = arb_mat(n, n)
    for i in range(-N, N + 1):
        for j in range(i, N + 1):
            v = bt.entry(i, j)
            M[i + N, j + N] = v
            M[j + N, i + N] = v
    return M


def ground(Te: arb_mat):
    """(Rayleigh ball of the lowest even eigenvector, the vector as mpf list)."""
    import ccm_common as C

    rq, x = C.lowest_pairs(Te, k=1)[0]
    with mp.workdps(int(ctx.prec / 3.32)):
        return rq, C.to_mp(x)


def xi_full(v: list) -> list:
    """Even vector in the cosine basis -> components xi_n, n = -N..N, with
    <eta | xi> = sum xi_n = 1 (CCM's normalization)."""
    N = len(v) - 1
    s2 = mp.sqrt(2)
    half = [v[k] / s2 for k in range(1, N + 1)]
    full = list(reversed(half)) + [v[0]] + half
    S = mp.fsum(full)
    return [x / S for x in full]


def operator(xi: list) -> list:
    """D' = diag(n) - |D xi><eta| as a list of rows (mpf), n = -N..N."""
    N = (len(xi) - 1) // 2
    ns = list(range(-N, N + 1))
    rows = []
    for a, na in enumerate(ns):
        dxa = na * xi[a]
        rows.append([(na if a == b else 0) - dxa for b in range(len(ns))])
    return rows


# ---------------------------------------------------------------------------
# measurement (still zero-free)
# ---------------------------------------------------------------------------


def inertia(M: arb_mat, shift) -> tuple:
    rows = [[M[i, j] for j in range(M.ncols())] for i in range(M.nrows())]
    return EN.ldlt_inertia(rows, arb(shift))


def lowest_odd_mid(To: arb_mat) -> float:
    import ccm_common as C

    return C.lowest_pairs(To, k=1)[0][0].mid()


def spectrum_matrix(Dp: list, L, prec: int):
    """Eigenvalues of D' by acb_mat.eig (approx), as z = 2 pi s / L (mpc list).

    ``prec`` here is the eigensolver's working precision, which may be far below
    the assembly precision: the entries of D' are integers and the rank-one
    column D xi, and 500 bits keep the low eigenvalues to about 1e-100.
    """
    ctx.prec = prec
    n = len(Dp)
    digits = int(prec / 3.32)
    A = acb_mat(n, n, [arb(mp.nstr(Dp[i][j], digits)) for i in range(n) for j in range(n)])
    E = A.eig(algorithm="approx")
    with mp.workdps(digits):
        fac = 2 * mp.pi / L
        out = [mp.mpc(mp.mpf(e.real.mid().str(digits, radius=False)), mp.mpf(e.imag.mid().str(digits, radius=False))) * fac for e in E]
    return out


def secular(xi: list, z, L):
    """g(z) = sum_n xi_n / (n - s), s = z L / (2 pi); its zeros are D''s spectrum."""
    N = (len(xi) - 1) // 2
    s = z * L / (2 * mp.pi)
    return mp.fsum(xi[k + N] / (k - s) for k in range(-N, N + 1))


def commutator_check(T: arb_mat, xi: list, eps) -> float:
    """max |(W D' - D'^T W)_{ij}| / max |W_{ij}|, W = T - eps I (Lemma key (ii))."""
    n = T.nrows()
    Dp = operator(xi)
    digits = int(ctx.prec / 3.32)
    with mp.workdps(digits):
        Wm = [[mp.mpf(T[i, j].mid().str(digits, radius=False)) - (eps if i == j else 0) for j in range(n)] for i in range(n)]
        WD = [[mp.fsum(Wm[i][k] * Dp[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        worst = max(abs(WD[i][j] - WD[j][i]) for i in range(n) for j in range(n))
        scale = max(abs(Wm[i][j]) for i in range(n) for j in range(n))
        return float(worst / scale)


# ---------------------------------------------------------------------------
# comparison (reads the zeros; never feeds back into the definition)
# ---------------------------------------------------------------------------


def zeta_ordinates(n: int, path: str | None = None) -> list:
    """First n zeta ordinates (mpmath.zetazero at dps 45), cached in ``path``."""
    import json

    if path and os.path.exists(path):
        with open(path) as fh:
            d = json.load(fh)
        if len(d["zeros"]) >= n:
            return [mp.mpf(x) for x in d["zeros"][:n]]
    with mp.workdps(45):
        zs = [mp.im(mp.zetazero(k)) for k in range(1, n + 1)]
        strs = [mp.nstr(g, 42) for g in zs]
    if path:
        with open(path, "w") as fh:
            json.dump({"source": "mpmath.zetazero at dps 45", "zeros": strs}, fh)
    return [mp.mpf(x) for x in strs]


def gram_points(n: int) -> list:
    """g_0 .. g_{n-1}: the counting-function control (theta(g_k) = k pi)."""
    with mp.workdps(20):
        return [mp.grampoint(k) for k in range(n)]
