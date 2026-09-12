"""A derived outer bound for sup F over the full admissible window class.

Claim proved here (grade: derived inequality chain; every numerical constant
is an exact rational, so nothing needs an enclosure):

    sup { F(v) : v even, v >= 0 on B = [-1/2, 1/2], int v > 0 }
        <= 1 - (1/U)^2  =  0.892744211644...  (exact rational below)

where U is an exact rational upper bound for <1, (I - T)^{-1} 1> and T is
convolution with tri(t) = (1 - |t|)_+ restricted to B.

Derivation, step by step (see also RESULTS.md section 9):

1.  Spectral reformulation.  With l1 = int v and A = H/l1 the normalised
    windowed Gram matrix, the limiting moments m_k = lim E tr A^k / N are,
    for every finite N, moments of the positive measure E nu_N (the expected
    empirical spectral distribution: mass 1, supported on [0, inf) because H
    is a Gram matrix, hence PSD).  The closed forms of functional.py give

        m0 = 1,  m1 = 1,  m2 = 1 + D2,  m3 = 1 + 3 D2 + D3,

    so D2 and D3 are the second and third central moments of the limiting
    spectral measure about 1, and F = 2 m2 - m3 = 1 - D2 - D3.

2.  Cauchy-Schwarz at every finite N.  For the positive measure E nu_N,
    (int lam^2)^2 <= (int lam)(int lam^3), i.e. (m2^N)^2 <= m1^N m3^N.
    Hence 2 m2^N - m3^N <= 2 m2^N - (m2^N)^2 / m1^N; passing to the limit
    that defines the m_k:  F <= 2 m2 - m2^2 = 1 - D2^2.
    (Same mechanism gives F <= 1 outright: lam (lam-1)^2 >= 0 on [0, inf).)

3.  The map D2 -> 1 - D2^2 is decreasing for D2 >= 0, so
        sup F <= 1 - (inf D2)^2,
    with the inf over the same class.  D2 is the explicit quadratic
    functional  D2 = <v, (I - T) v> / l1^2  on L^2(B).

4.  Dual lower bound for the quadratic functional.  A = I - T is positive
    definite (T is PSD with ||T|| <= ||T||_HS = sqrt(tr T^2) = sqrt(1/2)),
    so for every c and every v with int v = l1 = 1 (WLOG by scale
    invariance):
        <v, A v> >= 2 c <1, v> - c^2 <1, A^{-1} 1> = 2 c - c^2 U0,
    U0 := <1, A^{-1} 1> = sum_k t_k,  t_k := <1, T^k 1>.
    With any rational U >= U0 and the rational choice c = 1/U:
        inf D2 >= 2/U - U0/U^2 >= 1/U.

5.  Exact rational evaluation of U.  T maps polynomials on B to polynomials
    (degree + 2), so every t_k is an exact rational, computed below in
    Fraction arithmetic.  Tail: for even K,
        sum_{k >= K} t_k = <T^{K/2} 1, (I-T)^{-1} T^{K/2} 1>
                        <= t_K / (1 - lam_max)
    and lam_max <= 1/sqrt(2) <= 707107/1000000 (since 707107^2 >= 5*10^11),
    so U = sum_{k<K} t_k + t_K * 1000000/292893 >= U0, all rational.

What the chain inherits: the identification of D2, D3 with the limiting
spectral moments is the hardened closed-form derivation of functional.py
(validated four independent ways, including the exact finite-N CUE lattice
cross-check), inside the source paper's asymptotic framework.  Steps 2-5 are
elementary inequalities with exact rational constants.

The bound is essentially sharp FOR THIS ROUTE: inf D2 is bracketed here to
[1/U, D2(w_K)] with w_K = sum_{k<=24} T^k 1 an explicit nonnegative
polynomial window (T preserves nonnegativity, so w_K >= 0 needs no
computation), and the bracket has width ~2e-7.  Closing the remaining gap
0.6853 vs 0.8927 needs information beyond (m1, m2): with only these two
moments the extremal spectral measure (d/(1+d)) delta_0 + (1/(1+d))
delta_{1+d} cannot be excluded, and ruling it out for actual windowed
sine-Gram operators is real spectral theory, not bookkeeping.

Run: .venv/bin/python hunts/rogue_frontier/window_opt/global_bound.py
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functional import (OPT_Q, moments_polyeven_exact, moments_quad)  # noqa: E402

HALF = Fraction(1, 2)


# ---------------------------------------------------------------------------
# exact polynomial arithmetic over Fraction (independent of functional.py's,
# re-implemented here and cross-checked against it below)
# ---------------------------------------------------------------------------

def padd(p, q):
    n = max(len(p), len(q))
    p = list(p) + [Fraction(0)] * (n - len(p))
    q = list(q) + [Fraction(0)] * (n - len(q))
    return [x + y for x, y in zip(p, q)]


def pscale(p, c):
    c = Fraction(c)
    return [c * x for x in p]


def pmul(p, q):
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        if x:
            for j, y in enumerate(q):
                out[i + j] += x * y
    return out


def pmulx(p):
    return [Fraction(0)] + list(p)


def pint(p):
    return [Fraction(0)] + [x / (i + 1) for i, x in enumerate(p)]


def peval(p, x):
    acc = Fraction(0)
    for c in reversed(p):
        acc = acc * x + c
    return acc


def inner(f, g):
    """int_B f g, exact."""
    P = pint(pmul(f, g))
    return peval(P, HALF) - peval(P, -HALF)


def T_apply(f):
    """(T f)(xi) = int_B (1 - |xi - eta|) f(eta) deta, polynomial in, out.

    With F1(xi) = int_{-1/2}^{xi} f and F2(xi) = int_{-1/2}^{xi} eta f(eta):
        int_B |xi - eta| f(eta) deta
            = 2 xi F1(xi) - 2 F2(xi) + F2(1/2) - xi F1(1/2),
    so T f = F1(1/2) - the above.
    """
    F1 = pint(f)
    F2 = pint(pmulx(f))
    F1s = padd(F1, [-peval(F1, -HALF)])
    F2s = padd(F2, [-peval(F2, -HALF)])
    I0 = peval(F1s, HALF)
    F2h = peval(F2s, HALF)
    out = padd([I0 - F2h], pscale(pmulx(F1s), -2))
    out = padd(out, pscale(F2s, 2))
    out = padd(out, [Fraction(0), I0])
    return out


def D2_exact(vpoly):
    """D2 = (<v, v> - <v, T v>) / l1^2 for a polynomial window, exact."""
    l1 = inner(vpoly, [Fraction(1)])
    return (inner(vpoly, vpoly) - inner(vpoly, T_apply(vpoly))) / l1 ** 2


# ---------------------------------------------------------------------------
# validation gate
# ---------------------------------------------------------------------------

def gate() -> None:
    print("== gate: cross-check the T machinery against functional.py ==")
    # v = 1: D2 = 1/3 exactly, and T 1 = 3/4 - xi^2
    T1 = T_apply([Fraction(1)])
    assert T1 == [Fraction(3, 4), Fraction(0), Fraction(-1)], T1
    assert D2_exact([Fraction(1)]) == Fraction(1, 3)
    m2r, _, _ = moments_polyeven_exact([Fraction(0)])
    assert m2r - 1 == Fraction(1, 3)
    # the rational witness window: D2 must equal m2 - 1 from the hardened
    # closed forms, as an exact identity between two independent codes
    q1, q2 = OPT_Q
    vpoly = [Fraction(1), Fraction(0), q1, Fraction(0), q2]
    m2r, m3r, Fr = moments_polyeven_exact(OPT_Q)
    assert D2_exact(vpoly) == m2r - 1, "T-route D2 disagrees with functional"
    print("   T 1 = 3/4 - xi^2 (hand-derived); D2(1) = 1/3 exact")
    print(f"   D2(v*) = {D2_exact(vpoly)} = m2 - 1 exactly (two codes agree)")
    print(f"          = {float(D2_exact(vpoly)):.15f}")


# ---------------------------------------------------------------------------
# the bound
# ---------------------------------------------------------------------------

def compute_bound(K: int = 44, KW: int = 24) -> dict:
    assert K % 2 == 0
    print(f"\n== exact rational bound chain (K = {K}) ==")
    # t_k = <1, T^k 1>
    tks = []
    f = [Fraction(1)]
    one = [Fraction(1)]
    for _ in range(K + 1):
        tks.append(inner(one, f))
        f = T_apply(f)
    assert tks[1] == Fraction(2, 3) and tks[2] == Fraction(9, 20), tks[:3]
    print(f"   t_1 = {tks[1]}, t_2 = {tks[2]} (hand-derived anchors)")
    print(f"   Rayleigh ratios t_k+1/t_k -> lam_1 ~ {float(tks[K] / tks[K-1]):.13f}")

    # HS bound: tr T^2 = int int tri(xi-eta)^2 = 1/2 exactly; check by the
    # same machinery: int_B (T tri_xi)(xi) is harder, so verify the moment
    # identity  int int (1 - |d|)^2 = 1 - 2 E|d| + E d^2 = 1 - 2/3 + 1/6.
    trT2 = 1 - Fraction(2, 3) + Fraction(1, 6)
    assert trT2 == HALF
    assert 707107 ** 2 >= 5 * 10 ** 11
    lam_ub = Fraction(707107, 1000000)      # >= 1/sqrt(2) >= lam_max
    print(f"   tr T^2 = 1/2, so lam_max <= 1/sqrt(2) <= {lam_ub}")

    tail = tks[K] / (1 - lam_ub)
    U = sum(tks[:K]) + tail
    infD2_lb = 1 / U
    bound = 1 - infD2_lb ** 2
    print(f"   sum_(k<{K}) t_k       = {float(sum(tks[:K])):.15f}")
    print(f"   tail bound            = {float(tail):.3e}")
    print(f"   U                     = {float(U):.15f}  (exact rational)")
    print(f"   inf D2 >= 1/U         = {float(infD2_lb):.15f}")
    print(f"   sup F <= 1 - (1/U)^2  = {float(bound):.15f}")

    # bracket inf D2 from above with the explicit nonnegative polynomial
    # window w = sum_{k<=KW} T^k 1 (Neumann series for (I-T)^{-1} 1)
    w = [Fraction(0)]
    f = [Fraction(1)]
    for _ in range(KW + 1):
        w = padd(w, f)
        f = T_apply(f)
    d2_ub = D2_exact(w)
    print(f"   D2(w_{KW}) (w >= 0 by positivity of T) = {float(d2_ub):.15f}")
    print(f"   => inf over the cone of D2 lies in "
          f"[{float(infD2_lb):.10f}, {float(d2_ub):.10f}]"
          f"  (width {float(d2_ub - infD2_lb):.2e})")
    print(f"   => the 1 - D2^2 route cannot give better than "
          f"{float(1 - d2_ub ** 2):.10f}")
    return {"U": U, "bound": bound, "infD2_lb": infD2_lb, "d2_ub": d2_ub,
            "tks": tks}


# ---------------------------------------------------------------------------
# numerical sanity of the spectral chain (measured, not part of the proof)
# ---------------------------------------------------------------------------

def sanity(n_windows: int = 60, seed: int = 3) -> None:
    print(f"\n== sanity: D2 + D3 >= D2^2 at {n_windows} random admissible "
          "windows (measured) ==")
    rng = np.random.default_rng(seed)
    worst = np.inf
    for i in range(n_windows):
        kind = i % 3
        if kind == 0:
            c = rng.uniform(0.3, 3.0)
            v = lambda s: np.exp(-c * s ** 2)
        elif kind == 1:
            a = rng.uniform(-1.9, 0.5, size=2)
            v = lambda s: np.maximum(1 + a[0] * s ** 2 + a[1] * s ** 4, 0.0) + 1e-3
        else:
            J = 4
            co = rng.standard_normal(J) * 0.4 / np.arange(1, J + 1)
            v = lambda s: (1 + sum(co[k] * np.cos(2 * np.pi * (k + 1) * s)
                                   for k in range(J))) ** 2 + 1e-6
        r = moments_quad(v, ng=96)
        D2 = r["m2"] - 1
        D3 = r["m3"] - 3 * r["m2"] + 2
        slack = (D2 + D3) - D2 ** 2
        worst = min(worst, slack)
        assert slack > -1e-12, (i, D2, D3, slack)
        assert abs((1 - D2 - D3) - r["F"]) < 1e-12
    print(f"   all pass; smallest slack (D2 + D3) - D2^2 = {worst:.6f} > 0")
    # at the optimum: how much the Cauchy-Schwarz step gives away
    m2r, m3r, Fr = moments_polyeven_exact(OPT_Q)
    D2o = m2r - 1
    D3o = m3r - 3 * m2r + 2
    print(f"   at v*: D2 = {float(D2o):.9f}, D3 = {float(D3o):+.9f}, "
          f"pointwise bound 1 - D2^2 = {float(1 - D2o**2):.9f} "
          f"vs F = {float(Fr):.9f}")


def main() -> None:
    gate()
    res = compute_bound()
    sanity()
    b = res["bound"]
    print("\nSUMMARY (grades per repo ladder):")
    print(f"  sup F <= {float(b):.13f}   derived inequality chain, exact")
    print("     rational constants end to end; inherits only the hardened")
    print("     moment closed forms and the source paper's framework.")
    print(f"  exact rational bound: {b.numerator}")
    print(f"                      / {b.denominator}")
    print(f"  gap to the measured sup 0.6852870321770: {float(b) - 0.6852870321770:.6f}")


if __name__ == "__main__":
    main()
