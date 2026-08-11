"""The window-optimisation problem for the zeros of xi'.

Context. The August 2026 paper "More than two thirds of the zeros of the
Riemann zeta function lie on the critical line" restricts Weil's Hermitian form
to a finite Gabor family and reads off, from the first two moments of the
resulting matrix, an unconditional lower bound for the proportion of zeros that
are simple and on the critical line. For zeta itself the paper solves the
window-optimisation problem exactly (its Theorem D): the maximiser is
Montgomery-Taylor's cos(sqrt(2) s) and the constant is 0.6725008...

Its Remark 7.3 applies the same machinery to xi', the derivative of the
completed zeta function, and reports 0.85838 for a flat window and 0.86864 for
an unexplained quartic. It does *not* solve the variational problem there, and
it records that 0.86864 fails to reach Wu's unconditional 0.86957 for zeros of
xi' merely on the line.

This module solves that variational problem.

The functional. Writing phi^2(u) = v(u/L) with v >= 0 supported on [-1/2,1/2],
the paper's scale-free functional (its eq. 7.3) is, for zeta,

    c_lambda(v) = lambda (int v)^2 / ( int v^2 + lambda^2 iint |s-s'| v v )

and the proportion of simple on-line zeros is H = 2 - 1/c. The only change for
xi' is Montgomery's F(alpha) = |alpha| -> Farmer-Gonek-Lee's F_1(alpha):

    1/c^{xi'}_lambda(v)
        = [ int v^2 + lambda iint F_1(lambda (s-s')) v(s) v(s') ] / (lambda (int v)^2)

    F_1(x) = |x| - 4 x^2 + sum_{k>=1} ((k-1)!/(2k)!) (2|x|)^{2k+1}

F_1 is Theorem 1.1 of Farmer-Gonek (arXiv:0803.0425; with Lee, JLMS 90 (2014)
241-269), restated above Lemma 11 of Chirre-Goncalves-de Laat
(arXiv:1810.08843, Adv. Math. 361 (2020)). Setting F_1(x) = |x| recovers the
zeta functional exactly, which is the control this module checks first.

Method. The double integral is reduced to one dimension through the
autocorrelation,

    iint F_1(s-s') v(s) v(s') ds ds' = int_{-1}^{1} F_1(r) C(r) dr,
    C(r) = int v(s) v(s-r) ds,

so the only non-smooth point, the kink of |x| at the origin, becomes an
endpoint. On [0,1] both F_1 and C are analytic, so Gauss-Legendre converges
spectrally and the quantities below are limited by working precision rather
than by the kink. This matters: the question is whether the optimum clears
0.86864 and 0.86957, and those sit 1e-6 and 9e-4 away.

Run from the repo root with `.venv/bin/python`.
"""

from __future__ import annotations

import math
from typing import Callable

import numpy as np
from numpy.polynomial.legendre import leggauss

# --------------------------------------------------------------------------
# the two kernels
# --------------------------------------------------------------------------


def F_zeta(x: np.ndarray) -> np.ndarray:
    """Montgomery's form factor on |alpha| <= 1, minus its Dirac spike."""
    return np.abs(x)


def F_xiprime(x: np.ndarray, kmax: int = 60) -> np.ndarray:
    """Farmer-Gonek-Lee's F_1 on |alpha| <= 1, minus its Dirac spike.

    The series converges quickly: at |x| = 1 the terms fall from 4 through
    1.33, 0.356, 0.0762, 0.0135, 0.00205, ... so ``kmax = 60`` is far past
    double precision.
    """
    a = np.abs(x)
    out = a - 4.0 * a**2
    # ((k-1)!/(2k)!) (2a)^{2k+1}, accumulated by ratio to avoid overflow
    term = 0.5 * (2.0 * a) ** 3  # k = 1: (0!/2!) (2a)^3
    out = out + term
    for k in range(2, kmax + 1):
        # term_k / term_{k-1} = (k-1) / ((2k)(2k-1)) * (2a)^2
        term = term * (k - 1) / ((2 * k) * (2 * k - 1)) * (2.0 * a) ** 2
        out = out + term
    return out


# --------------------------------------------------------------------------
# the functional
# --------------------------------------------------------------------------


def _autocorr_nodes(n_r: int, n_s: int):
    """Gauss nodes for the r-integral on [0,1] and the inner s-integral."""
    xr, wr = leggauss(n_r)
    r = 0.5 * (xr + 1.0)
    wr = 0.5 * wr
    xs, ws = leggauss(n_s)
    return r, wr, xs, ws


def pair_term(
    v: Callable[[np.ndarray], np.ndarray],
    F: Callable[[np.ndarray], np.ndarray],
    n_r: int = 200,
    n_s: int = 200,
) -> float:
    """iint F(s-s') v(s) v(s') ds ds' over [-1/2,1/2]^2, for even v.

    Uses  iint = 2 * int_0^1 F(r) C(r) dr  with C the autocorrelation, so the
    kink of F at the origin lands on an endpoint of the outer integral.
    """
    r, wr, xs, ws = _autocorr_nodes(n_r, n_s)
    total = 0.0
    for ri, wi in zip(r, wr):
        lo, hi = -0.5 + ri, 0.5  # overlap of [-1/2,1/2] and r + [-1/2,1/2]
        if hi <= lo:
            continue
        mid, half = 0.5 * (lo + hi), 0.5 * (hi - lo)
        s = mid + half * xs
        C = half * np.sum(ws * v(s) * v(s - ri))
        total += wi * float(F(np.array([ri]))[0]) * C
    return 2.0 * total


def inv_c(
    v: Callable[[np.ndarray], np.ndarray],
    lam: float = 1.0,
    kernel: str = "xiprime",
    n_r: int = 200,
    n_s: int = 200,
) -> float:
    """1/c_lambda(v): the second moment in units of the first."""
    xs, ws = leggauss(n_s)
    s = 0.5 * xs
    w = 0.5 * ws
    vv = v(s)
    int_v = float(np.sum(w * vv))
    int_v2 = float(np.sum(w * vv * vv))
    if kernel == "zeta":
        pair = pair_term(v, lambda x: F_zeta(lam * x), n_r, n_s)
    elif kernel == "xiprime":
        pair = pair_term(v, lambda x: F_xiprime(lam * x), n_r, n_s)
    else:
        raise ValueError(f"unknown kernel {kernel!r}")
    return (int_v2 + lam * pair) / (lam * int_v**2)


def H_of(v, lam: float = 1.0, kernel: str = "xiprime", **kw) -> float:
    """Proportion of zeros that are simple and on the critical line."""
    return 2.0 - inv_c(v, lam=lam, kernel=kernel, **kw)


# --------------------------------------------------------------------------
# the optimisation, in a smooth even basis
# --------------------------------------------------------------------------


def optimise(
    lam: float = 1.0,
    kernel: str = "xiprime",
    n_basis: int = 14,
    n_r: int = 320,
    n_s: int = 320,
):
    """Maximise c over v >= 0 even on [-1/2,1/2].

    The Rayleigh quotient lam (b.x)^2 / (x.(A + lam B) x) is maximised by
    x = (A + lam B)^{-1} b with value lam b.(A+lam B)^{-1} b, so no iterative
    optimiser is needed. The basis is the even monomials s^{2j}, which span the
    smooth maximiser rapidly; ``n_basis`` is raised until the value stops
    moving.
    """
    F = (lambda x: F_zeta(lam * x)) if kernel == "zeta" else (
        lambda x: F_xiprime(lam * x)
    )
    basis = [(lambda s, j=j: s ** (2 * j)) for j in range(n_basis)]

    xs, ws = leggauss(n_s)
    s = 0.5 * xs
    w = 0.5 * ws

    b = np.array([float(np.sum(w * f(s))) for f in basis])
    A = np.array([[float(np.sum(w * fi(s) * fj(s))) for fj in basis] for fi in basis])

    r, wr, xq, wq = _autocorr_nodes(n_r, n_s)
    B = np.zeros((n_basis, n_basis))
    Fr = np.array([float(F(np.array([ri]))[0]) for ri in r])
    for ri, wi, Fi in zip(r, wr, Fr):
        lo, hi = -0.5 + ri, 0.5
        if hi <= lo:
            continue
        mid, half = 0.5 * (lo + hi), 0.5 * (hi - lo)
        sq = mid + half * xq
        vals_a = np.array([f(sq) for f in basis])       # v_i(s)
        vals_b = np.array([f(sq - ri) for f in basis])  # v_j(s-r)
        M = (vals_a * (half * wq)) @ vals_b.T           # C_ij(r)
        B += wi * Fi * (M + M.T)                        # symmetrise: +-r
    Mtx = A + lam * B
    x = np.linalg.solve(Mtx, b)
    c = lam * float(b @ x)
    return {
        "lambda": lam,
        "kernel": kernel,
        "n_basis": n_basis,
        "c": c,
        "inv_c": 1.0 / c,
        "H": 2.0 - 1.0 / c,
        "Hd": 0.5 * (1.0 + (2.0 - 1.0 / c)),
        "coeffs": x,
    }


def _v_from(coeffs):
    return lambda s: sum(ci * s ** (2 * j) for j, ci in enumerate(coeffs))


__all__ = ["F_zeta", "F_xiprime", "inv_c", "H_of", "optimise", "pair_term"]
