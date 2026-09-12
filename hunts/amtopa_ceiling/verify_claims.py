#!/usr/bin/env python3
"""Every quantitative claim in RESULTS.md that can be checked in seconds.

Run:  python3 verify_claims.py     (exits non-zero on the first failure)

Claims that cost more than seconds -- the eps* brackets, the pressure saturation
curve, the LP duals and the window search -- are not here; they are the Actions
jobs in ci-sweep.yml, and RESULTS.md section 7 records what they returned.
"""
from __future__ import annotations

import sys
from fractions import Fraction

import numpy as np

from exact_assembly import (AMTOPA_B, AMTOPA_EPS, AMTOPA_H, AMTOPA_M,
                            AMTOPA_PUBLISHED, bound_at, dec, scan)
from family import (H_of, PAIR_SPAN, amtopa_a, amtopa_b, amtopa_coeffs,
                    frequencies, kernel, window_ceiling, window_matrices, Wfun,
                    F_of, Q)

FAILS = []


def check(name, got, want, tol=0.0):
    ok = (got == want) if tol == 0.0 else (abs(got - want) <= tol)
    print(f"  [{'ok ' if ok else 'FAIL'}] {name}")
    if not ok:
        FAILS.append(f"{name}: got {got!r}, want {want!r} (tol {tol})")
    return ok


def main() -> int:
    c = amtopa_coeffs()
    w = frequencies(17)
    u, _, _, M = window_matrices(w)
    a, b = amtopa_a(), amtopa_b()

    print("RESULTS.md section 2 -- reproduction")
    lo = bound_at(AMTOPA_M, AMTOPA_H, AMTOPA_EPS, AMTOPA_B, Q, 200)
    check("their headline reproduces to 70 decimals, exact rational",
          dec(lo, 70)[:len(AMTOPA_PUBLISHED)], AMTOPA_PUBLISHED)
    best, best_m = scan(AMTOPA_H, AMTOPA_EPS, AMTOPA_B, Q, m_hi=3000, digits=60)
    check("their block length is the exact argmax", best_m, 145)
    check("their safe floor 0.6734164909 is cleared",
          best > Fraction(6734164909, 10**10), True)
    check("H(v) matches their published value to 1e-15",
          H_of(c, u, M), 0.67218815811823458517, 1e-15)
    check("span capacities are exactly 2 on all six spans",
          [float(a[PAIR_SPAN == s].sum()) for s in range(1, 7)], [2.0] * 6)
    check("total pressure is exactly 93/23000",
          float(b.sum()), 93 / 23000, 1e-18)
    gstar = np.array([1.978079145369, 1.044055102239, 1.973013931233,
                      1.045981098706, 1.974452906922, 1.042299648208])
    check("their float minimum reproduces at their basin, to 1e-15",
          F_of(gstar, a, b, c, w), 0.007911105155226424, 1e-15)
    check("W(0) = 1 exactly", float(Wfun(0.0, c, w)[0]), 1.0)

    print("\nRESULTS.md section 4.1 -- the window Rayleigh ceiling")
    HD1 = 0.6725007036794116457
    for n in (1, 2, 3, 7, 13, 17, 25):
        wn = frequencies(n)
        un, _, _, Mn = window_matrices(wn)
        hmax, cbest = window_ceiling(un, Mn)
        check(f"H_max over a {n}-term window is Anthropic HD(1)", hmax, HD1, 1e-15)
        if n > 1:
            check(f"  and its maximiser has no harmonic content ({n} terms)",
                  float(np.abs(cbest[1:]).max()) < 1e-12, True)
    un, _, _, Mn = window_matrices(w)
    check("the harmonics have zero window integral, u_j = 0",
          float(np.abs(un[1:]).max()) < 1e-14, True)
    check("the harmonics are M-orthogonal to the sqrt(2) term, M[0,j] = 0",
          float(np.abs(Mn[0, 1:]).max()) < 1e-14, True)
    # and the same computation off sqrt(2) does NOT decouple, which is the claim
    woff = w.copy()
    woff[0] = 1.5
    _, _, _, Moff = window_matrices(woff)
    check("off w_0 = sqrt(2) the coupling is nonzero (w_0 = 1.5)",
          float(np.abs(Moff[0, 1:]).max()) > 1e-6, True)
    check("AMTOPA give up 3.125e-04 of window constant",
          HD1 - H_of(c, u, M), 3.125456e-04, 1e-9)

    print("\nRESULTS.md section 4.3 -- the candidate constant")
    target = Fraction(19791, 2500000)
    v, m = None, None
    for mm in range(7, 3001):
        x = bound_at(mm, AMTOPA_H, target, AMTOPA_B, Q, 60)
        if v is None or x > v:
            v, m = x, mm
    check("our candidate assembles at m = 145", m, 145)
    check("our candidate constant, exact, to 40 decimals", dec(v, 40),
          "0.6734201550790580964457598685450152133015")
    check("it exceeds their headline by +3.664e-06",
          float(v) - 0.6734164909714992949, 3.664108e-06, 1e-11)
    check("the target sits below the polytope optimum floor",
          float(target) < 0.007916857810, True)
    check("the target sits above their accepted floor",
          float(target) > float(AMTOPA_EPS), True)

    print("\nRESULTS.md section 5.3 -- information class")
    ceiling = 0.6818286874638
    check("the family ceiling is below the configuration ceiling",
          0.6734204494726963 < ceiling, True)
    check("room left inside the information class",
          ceiling - 0.6734204494726963, 0.0084082, 1e-6)

    print()
    if FAILS:
        print(f"{len(FAILS)} FAILURES")
        for f in FAILS:
            print("  " + f)
        return 1
    print("all claims check")
    return 0


if __name__ == "__main__":
    sys.exit(main())
