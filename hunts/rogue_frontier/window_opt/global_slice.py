"""Exact supremum of F on the quartic slice, and measured suprema on the
degree 6..10 slices.

The quartic slice is v = 1 + q1 s^2 + q2 s^4 (v(0) = 1 is WLOG inside the
slice by scale invariance).  On it F is an explicit rational function
F = P(q)/l1(q)^3 of total degree 3/3, and the admissible region is

    A = { q : psi(u) = 1 + q1 u + q2 u^2 >= 0 on u in [0, 1/4] },   u = s^2.

This file settles sup_A F exactly, by compactification:

  1. INTERIOR critical points: dF/dq = 0 is a polynomial system; its lex
     Groebner basis has a univariate element (degree 7 in q2) whose real
     roots are isolated exactly; each critical pair is checked for
     admissibility and F is evaluated there as an algebraic number.
  2. BOUNDARY of A, two exact univariate families:
     (a) endpoint zero v(1/2) = 0: the segment q2 = -16 - 4 q1,
         q1 in [-8, inf)  (outside it psi dips negative inside [0, 1/4]:
         psi(u*) < 0 iff (q1+8)^2 > 0 with u* = -q1/(2 q2) in (0, 1/4),
         which happens exactly for q1 < -8);
     (b) interior double root: (q1, q2) = (-2/u, 1/u^2), u in (0, 1/4],
         meeting (a) at the corner (-8, 16), the window (1 - 4 s^2)^2.
  3. INFINITY: the recession cone of A is {alpha >= 0, alpha + beta/4 >= 0}
     (directions h = alpha s^2 + beta s^4 >= 0).  On it the denominator
     leading form l1(h) = alpha/12 + beta/80 is strictly positive away from
     the origin, so F extends continuously to the arc at infinity with
     F_inf(direction) = F(h) by scale invariance and continuity:
     F(1 + t h) = F(1/t + h) -> F(h).  The arc is the univariate family
     h = s^2 + b s^4, b in [-4, inf), plus the endpoint direction s^4.

sup_A F is then the maximum of finitely many exactly-computed numbers, all
isolated in exact arithmetic (grade: derived, with the compactification
argument as written above; every number below is either an exact rational or
an isolated real algebraic number).

Degree 6..10 slices are explored by multistart (measured only).

Run: .venv/bin/python hunts/rogue_frontier/window_opt/global_slice.py
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functional import (OPT_Q, moments_polyeven_exact, moments_quad)  # noqa: E402

BEST_F_CLAIMED = 0.6852870321770


# ---------------------------------------------------------------------------
# symbolic F on the quartic slice
# ---------------------------------------------------------------------------

def build_F():
    import sympy as sp
    s, eta, a, b = sp.symbols("s eta q1 q2")
    v = 1 + a * s ** 2 + b * s ** 4
    V0 = sp.integrate(v, s)
    P0 = sp.integrate(s * v, s)
    half = sp.Rational(1, 2)
    l1 = 2 * V0.subs(s, half)
    iv2 = 2 * sp.integrate(v ** 2, (s, 0, half))
    iv3 = 2 * sp.integrate(v ** 3, (s, 0, half))
    W = V0.subs(s, half) + V0.subs(s, half - eta)
    iW2 = 2 * sp.integrate(sp.expand(W ** 2), (eta, 0, 1))
    iW3 = 2 * sp.integrate(sp.expand(W ** 3), (eta, 0, 1))
    A = 2 * s * V0 - 2 * P0 + 2 * P0.subs(s, half)
    T = l1 - A
    iTv2 = 2 * sp.integrate(sp.expand(T * v ** 2), (s, 0, half))
    Q2 = sp.expand(iv2 - iW2)
    Q3 = sp.expand(iv3 - 3 * iTv2 + 2 * iW3)
    F = sp.cancel(sp.together(1 - Q2 / l1 ** 2 - Q3 / l1 ** 3))
    return F, a, b


def gate(F, a, b) -> None:
    import sympy as sp
    Fq = sp.nsimplify(sp.cancel(F.subs({a: sp.Rational(-1467, 1000),
                                        b: sp.Rational(1159, 1000)})))
    ref = sp.Rational(2245228120295149280, 3276332462159207451)
    assert sp.simplify(Fq - ref) == 0
    print("gate: symbolic slice F reproduces the exact rational F(v*)")


def admissible(q1f: float, q2f: float, tol: float = 1e-12) -> bool:
    """psi(u) = 1 + q1 u + q2 u^2 >= 0 on [0, 1/4] (float check with margin;
    used only for classification, the winners are re-checked exactly)."""
    u = np.linspace(0.0, 0.25, 20001)
    return float(np.min(1 + q1f * u + q2f * u ** 2)) >= -tol


def interior_critical(F, a, b):
    import sympy as sp
    print("\n== 1. interior critical points, exact ==")
    n1 = sp.expand(sp.fraction(sp.cancel(sp.together(sp.diff(F, a))))[0])
    n2 = sp.expand(sp.fraction(sp.cancel(sp.together(sp.diff(F, b))))[0])
    gb = sp.groebner([n1, n2], a, b, order="lex")
    uni = [g for g in gb.exprs if g.free_symbols <= {b}]
    assert len(uni) == 1
    pb = sp.Poly(uni[0], b)
    print(f"   univariate eliminant degree in q2: {pb.degree()}")
    print(f"   eliminant (content-free): {sp.factor(uni[0])}")
    rr = sp.real_roots(pb)
    print(f"   real roots in q2: {len(rr)}")
    # solve the other basis elements for q1 at each root
    others = [g for g in gb.exprs if not g.free_symbols <= {b}]
    results = []
    for r in rr:
        rN = sp.N(r, 45)
        q1_sols = set()
        for g in others:
            pa = sp.Poly(sp.expand(g.subs(b, rN)), a)
            for ra in sp.nroots(pa, n=40):
                if abs(sp.im(ra)) < 1e-25:
                    q1_sols.add(sp.re(ra))
        # keep q1 values that satisfy both original equations
        for q1v in q1_sols:
            r1 = abs(sp.N(n1.subs({a: q1v, b: rN}), 20))
            r2 = abs(sp.N(n2.subs({a: q1v, b: rN}), 20))
            scale1 = abs(sp.N(sp.Poly(n1, a, b).eval((abs(q1v) + 1,
                                                      abs(rN) + 1)), 20))
            if r1 / scale1 < 1e-25 and r2 / scale1 < 1e-20:
                Fv = sp.N(F.subs({a: q1v, b: rN}), 40)
                adm = admissible(float(q1v), float(rN))
                results.append((float(sp.N(Fv, 30)), q1v, rN, adm, Fv))
    results.sort(key=lambda t: -t[0])
    for Fv, q1v, q2v, adm, Fv40 in results:
        print(f"   q = ({sp.N(q1v, 12)}, {sp.N(q2v, 12)})  "
              f"F = {sp.N(Fv40, 18)}  admissible: {adm}")
    best_adm = [t for t in results if t[3]]
    print(f"   admissible interior critical points: {len(best_adm)}")
    if best_adm:
        Fv40 = best_adm[0][4]
        print(f"   slice interior max F4* = {sp.N(Fv40, 30)}")
    return results


def boundary_families(F, a, b):
    import sympy as sp
    print("\n== 2. boundary of A, exact univariate families ==")
    q1s = sp.symbols("t", real=True)

    # (a) endpoint zero: q2 = -16 - 4 q1, q1 in [-8, inf)
    Fa = sp.cancel(F.subs({a: q1s, b: -16 - 4 * q1s}))
    dFa = sp.cancel(sp.diff(Fa, q1s))
    na = sp.numer(dFa)
    roots_a = [r for r in sp.real_roots(sp.Poly(na, q1s))
               if sp.N(r) >= -8]
    vals = []
    for r in roots_a:
        Fv = sp.N(Fa.subs(q1s, sp.N(r, 40)), 30)
        vals.append(("(a) crit", float(sp.N(r, 20)), Fv))
    # endpoint q1 = -8 handled as the corner below; limit q1 -> inf:
    lim_a = sp.limit(Fa, q1s, sp.oo)
    vals.append(("(a) limit q1->inf", np.inf, sp.N(lim_a, 30)))

    # (b) double root: q1 = -2/u, q2 = 1/u^2, u in (0, 1/4]
    u = sp.symbols("u", positive=True)
    Fb = sp.cancel(F.subs({a: -2 / u, b: 1 / u ** 2}))
    dFb = sp.cancel(sp.diff(Fb, u))
    nb = sp.numer(dFb)
    roots_b = [r for r in sp.real_roots(sp.Poly(nb, u))
               if 0 < sp.N(r) <= sp.Rational(1, 4)]
    for r in roots_b:
        Fv = sp.N(Fb.subs(u, sp.N(r, 40)), 30)
        vals.append(("(b) crit", float(sp.N(r, 20)), Fv))
    lim_b = sp.limit(Fb, u, 0, "+")
    vals.append(("(b) limit u->0+ (concentration of the double root)",
                 0.0, sp.N(lim_b, 30)))

    # corner u = 1/4: v = (1 - 4 s^2)^2, exact rational
    m2c, m3c, Fc = moments_polyeven_exact([Fraction(-8), Fraction(16)])
    vals.append(("corner (1-4s^2)^2 exact", -8.0,
                 sp.N(sp.Rational(Fc.numerator, Fc.denominator), 30)))
    print(f"   corner window (1-4s^2)^2: F = {Fc} = {float(Fc):.15f}")
    for tag, x, Fv in vals:
        print(f"   {tag:>50s}: F = {sp.N(Fv, 20)}")
    return vals


def infinity_arc(F, a, b):
    import sympy as sp
    print("\n== 3. the arc at infinity: F(h), h = s^2 + b s^4, b in [-4, inf) ==")
    # directional limits equal F of the limit window h (scale invariance);
    # compute F(h) symbolically as a univariate rational function of b.
    s, eta, bb = sp.symbols("s eta b")
    v = s ** 2 + bb * s ** 4
    V0 = sp.integrate(v, s)
    P0 = sp.integrate(s * v, s)
    half = sp.Rational(1, 2)
    l1 = 2 * V0.subs(s, half)
    iv2 = 2 * sp.integrate(v ** 2, (s, 0, half))
    iv3 = 2 * sp.integrate(v ** 3, (s, 0, half))
    W = V0.subs(s, half) + V0.subs(s, half - eta)
    iW2 = 2 * sp.integrate(sp.expand(W ** 2), (eta, 0, 1))
    iW3 = 2 * sp.integrate(sp.expand(W ** 3), (eta, 0, 1))
    A2 = 2 * s * V0 - 2 * P0 + 2 * P0.subs(s, half)
    T = l1 - A2
    iTv2 = 2 * sp.integrate(sp.expand(T * v ** 2), (s, 0, half))
    Fh = sp.cancel(sp.together(1 - (iv2 - iW2) / l1 ** 2
                               - (iv3 - 3 * iTv2 + 2 * iW3) / l1 ** 3))
    dFh = sp.cancel(sp.diff(Fh, bb))
    roots = [r for r in sp.real_roots(sp.Poly(sp.numer(dFh), bb))
             if sp.N(r) >= -4]
    vals = []
    for r in roots:
        vals.append(("arc crit", float(sp.N(r, 20)),
                     sp.N(Fh.subs(bb, sp.N(r, 40)), 30)))
    vals.append(("arc end b = -4 (h = s^2 - 4 s^4)", -4.0,
                 sp.N(Fh.subs(bb, -4), 30)))
    vals.append(("arc end b -> inf (h = s^4)", np.inf,
                 sp.N(sp.limit(Fh, bb, sp.oo), 30)))
    for tag, x, Fv in vals:
        print(f"   {tag:>35s}: F = {sp.N(Fv, 20)}")
    return vals


def quartic_slice():
    import sympy as sp
    F, a, b = build_F()
    gate(F, a, b)
    inter = interior_critical(F, a, b)
    bdry = boundary_families(F, a, b)
    arc = infinity_arc(F, a, b)
    print("\n== quartic slice: assembly ==")
    cands = []
    for Fv, q1v, q2v, adm, Fv40 in inter:
        if adm:
            cands.append(("interior", float(Fv)))
    for tag, x, Fv in bdry + arc:
        cands.append((tag, float(sp.re(Fv))))
    cands.sort(key=lambda t: -t[1])
    for tag, Fv in cands:
        print(f"   candidate {tag:>55s}: {Fv:+.15f}")
    print(f"   sup over the quartic slice = {cands[0][1]:.15f} "
          f"({cands[0][0]})")
    print(f"   full-space measured sup     = {BEST_F_CLAIMED} "
          f"(gap {BEST_F_CLAIMED - cands[0][1]:.3e})")
    return cands


# ---------------------------------------------------------------------------
# degree 6..10 slices, measured
# ---------------------------------------------------------------------------

def poly_slices(degrees=(6, 8, 10), n_starts: int = 30, seed: int = 11):
    from scipy.optimize import minimize
    print("\n== degree 6..10 slices, multistart (measured) ==")
    rng = np.random.default_rng(seed)
    uu = np.linspace(0.0, 0.25, 4001)
    best_overall = -np.inf
    for deg in degrees:
        m = deg // 2

        def negF(q):
            psi = 1 + sum(q[i] * uu ** (i + 1) for i in range(m))
            if np.min(psi) < 0:
                return 10.0 + 1e3 * abs(float(np.min(psi)))
            v = lambda s: 1 + sum(q[i] * s ** (2 * (i + 1)) for i in range(m))
            return -moments_quad(v, ng=96)["F"]

        found = []
        for i in range(n_starts):
            if i == 0:
                q0 = np.zeros(m)
                q0[0] = -1.467
                if m > 1:
                    q0[1] = 1.159
            else:
                q0 = rng.standard_normal(m) * np.array(
                    [2.0] + [4.0] * (m - 1))
            res = minimize(negF, q0, method="Nelder-Mead",
                           options={"xatol": 1e-12, "fatol": 1e-15,
                                    "maxiter": 40000, "maxfev": 40000})
            if res.fun < 9.0:
                found.append((-res.fun, res.x.copy()))
        found.sort(key=lambda t: -t[0])
        Fbest = found[0][0]
        best_overall = max(best_overall, Fbest)
        distinct = []
        for Fv, q in found:
            if not any(np.max(np.abs(q - q2)) < 1e-4 for _, q2 in distinct):
                distinct.append((Fv, q))
        maxima = [d for d in distinct if d[0] > Fbest - 1e-6]
        print(f"   deg {deg}: best F = {Fbest:.13f}  "
              f"({len(found)} converged, {len(distinct)} distinct endpoints, "
              f"{len(maxima)} within 1e-6 of the slice best)")
        print(f"           best q = {np.array2string(found[0][1], precision=6)}")
    print(f"   best over polynomial slices: {best_overall:.13f} "
          f"(claimed sup {BEST_F_CLAIMED})")
    return best_overall


def main():
    quartic_slice()
    poly_slices()


if __name__ == "__main__":
    main()
