"""Exact sine-kernel Gram spectral moments m_k(lambda), as polynomials in lambda.

THE OBJECT.  Let the points x_1 < x_2 < ... be the sine process of density 1
(the universal bulk scaling limit of the CUE / GUE eigenvalues, and the
conjectural local law for the zeta zeros).  For 0 < lambda <= 1 put

    K_lambda(x) = sin(pi lambda x) / (pi x),      G_ij = K_lambda(x_i - x_j).

G is the Gram matrix of the exponentials e(x_i xi) restricted to
xi in [-lambda/2, lambda/2], hence positive semidefinite.  Write d = lambda N
for the dimension.  The normalised moments are

    m_k(lambda) = lim_{N -> infinity} tr G^k / d.

The 10 August 2026 paper "More than two thirds of the zeros of the Riemann
zeta function lie on the critical line", Remark 7.5(f), records
m_k(1) = 1, 4/3, 2, 13/4 for k = 1, 2, 3, 4 and uses them through a
Chebyshev-Markov-Stieltjes / Christoffel bound.

THE METHOD.  Work on a circle of circumference N with N points of unit
density.  The band-limited kernel is the Dirichlet kernel
D_M(x) = sum_{|m| <= M} e(m x / N) = N K_lambda(x) + O(1), with d = 2M + 1.
Then G = V^* V where V_{m,j} = e(m x_j / N), so for k >= 1

    tr G^k = tr T^k / N^k,      T_{m,m'} = sum_j e((m - m') x_j / N).

For the CUE, x_j = N theta_j / (2 pi), so T_{m,m'} = Tr(U^{m-m'}) is a Toeplitz
matrix built from the power traces of a Haar unitary.  By Diaconis-Shahshahani
the Tr(U^h), h >= 1, converge to independent complex Gaussians with
E |Tr(U^h)|^2 = h (exactly, for h <= N), while Tr(U^0) = N.  Hence with
h_i = m_i - m_{i+1} taken cyclically,

    E prod_i Tr(U^{h_i})
        = N^{#{i : h_i = 0}} * sum over perfect matchings of the nonzero
          indices, each matched pair (i,j) contributing |h_i| and requiring
          h_i + h_j = 0.

Summing over m in the band and rescaling m = N u shows that every pattern with
j nonzero edges contributes lambda^j times a pure number, so

    m_k(lambda) = sum_{j even, 0 <= j <= k} c_{k,j} lambda^j.

For one pattern, writing the free pair values as s_1 .. s_n (n = j/2), the
partial sums H_i = h_1 + ... + h_i for i = 0 .. k-1, and

    spread(s) = max_i H_i - min_i H_i        (positively homogeneous, degree 1),

the pattern's contribution is the integral

    J = integral over R^n of  prod_p |s_p| * (1 - spread(s))_+  ds.

Passing to polar coordinates and using homogeneity collapses the radial part:

    J = 1 / (2n (2n+1)) * integral over S^{n-1} of
        prod_p |omega_p| / spread(omega)^{2n}  d omega.

This module evaluates that, exactly for n <= 1 and by high-precision
quadrature over the piecewise-linear cells otherwise.

CONTROLS.  m_2 and m_3 are also derived by hand in RESULTS.md by an
independent position-space route (products of B-splines), and the whole
sequence is checked against the Monte Carlo in mc_moments.py.
"""

from __future__ import annotations

import itertools
from fractions import Fraction

from mpmath import mp, mpf, cos, sin, pi, quad


def _matchings(items: tuple[int, ...]) -> list[tuple[tuple[int, int], ...]]:
    """All perfect matchings of an even-sized tuple of indices."""
    if not items:
        return [()]
    first, rest = items[0], items[1:]
    out = []
    for pos in range(len(rest)):
        pair = (first, rest[pos])
        remainder = rest[:pos] + rest[pos + 1:]
        for tail in _matchings(remainder):
            out.append((pair,) + tail)
    return out


def patterns(k: int):
    """Yield (zero_set, matching) for every Wick pattern on the k-cycle."""
    idx = tuple(range(k))
    for j in range(0, k + 1, 2):
        for nonzero in itertools.combinations(idx, j):
            zero = tuple(i for i in idx if i not in nonzero)
            for match in _matchings(nonzero):
                yield zero, match


def spread_function(k: int, zero: tuple[int, ...], match: tuple[tuple[int, int], ...]):
    """Return spread(s) as a callable on R^n, n = len(match).

    Edge i carries h_i; h_i = 0 for i in `zero`; for pair (a, b) the free
    value s_p sits on edge a and -s_p on edge b.  The vertex positions are the
    partial sums H_i, i = 0 .. k-1, and spread is their range.
    """
    sign_of = {}
    for p, (a, b) in enumerate(match):
        sign_of[a] = (p, 1)
        sign_of[b] = (p, -1)

    def spread(s):
        h = []
        for i in range(k):
            if i in zero:
                h.append(0 * s[0] if s else 0)
            else:
                p, sg = sign_of[i]
                h.append(sg * s[p])
        partial = [0 * s[0] if s else 0]
        acc = partial[0]
        for i in range(k - 1):
            acc = acc + h[i]
            partial.append(acc)
        return max(partial) - min(partial)

    return spread


def pattern_integral(k: int, zero, match, quad_pts: int = 24) -> mpf:
    """The number J for one pattern."""
    n = len(match)
    if n == 0:
        return mpf(1)
    spread = spread_function(k, zero, match)
    if n == 1:
        total = mpf(0)
        for omega in (mpf(1), mpf(-1)):
            sp = spread([omega])
            if sp > 0:
                total += abs(omega) / sp ** 2
        return total / (2 * 1 * (2 * 1 + 1))
    if n == 2:
        def integrand(theta):
            w = [cos(theta), sin(theta)]
            sp = spread(w)
            if sp <= 0:
                return mpf(0)
            return abs(w[0]) * abs(w[1]) / sp ** 4
        # break the circle at the cell walls of the piecewise-linear spread
        nodes = [i * pi / 4 for i in range(9)]
        total = quad(integrand, nodes)
        return total / (2 * 2 * (2 * 2 + 1))
    if n == 3:
        # sphere S^2 in spherical coordinates
        def integrand(theta, phi):
            st = sin(theta)
            w = [st * cos(phi), st * sin(phi), cos(theta)]
            sp = spread(w)
            if sp <= 0:
                return mpf(0)
            return abs(w[0] * w[1] * w[2]) / sp ** 6 * st
        theta_nodes = [i * pi / 4 for i in range(5)]
        phi_nodes = [i * pi / 4 for i in range(9)]
        total = quad(lambda t, p: integrand(t, p), theta_nodes, phi_nodes)
        return total / (2 * 3 * (2 * 3 + 1))
    raise NotImplementedError(f"n = {n} not implemented")


def moment_polynomial(k: int, dps: int = 30) -> dict[int, mpf]:
    """Coefficients c_{k,j} of m_k(lambda) = sum_j c_{k,j} lambda^j."""
    with mp.workdps(dps):
        coeffs: dict[int, mpf] = {}
        for zero, match in patterns(k):
            j = 2 * len(match)
            coeffs[j] = coeffs.get(j, mpf(0)) + pattern_integral(k, zero, match)
        return coeffs


def rationalise(x: mpf, max_den: int = 20000, tol: float = 1e-18) -> Fraction | None:
    """Best small-denominator rational within tol, or None."""
    fr = Fraction(float(x)).limit_denominator(max_den)
    if abs(mpf(fr.numerator) / fr.denominator - x) < tol:
        return fr
    return None


if __name__ == "__main__":
    published = {1: "1", 2: "4/3", 3: "2", 4: "13/4"}
    for k in range(1, 7):
        coeffs = moment_polynomial(k)
        at_one = sum(coeffs.values())
        terms = []
        for j in sorted(coeffs):
            fr = rationalise(coeffs[j])
            shown = str(fr) if fr is not None else mp.nstr(coeffs[j], 12)
            terms.append(f"{shown}*lam^{j}" if j else f"{shown}")
        fr1 = rationalise(at_one)
        got = str(fr1) if fr1 is not None else mp.nstr(at_one, 14)
        mark = ""
        if k in published:
            mark = "  [paper: " + published[k] + "]"
            mark += "  OK" if got == published[k] else "  MISMATCH"
        print(f"m_{k}(lam) = " + " + ".join(terms))
        print(f"    m_{k}(1) = {got}{mark}")
