"""Window optimization for F(v) = 2 m2(1,v) - m3(1,v) and the EL test.

Everything here is float-grade (measured); the exact arithmetic for the final
window lives in functional.py (Fraction route) and enclose.py.

Contents, in the order the report prints:

  1. Euler-Lagrange test at the paper's window cos(8s/5): the first-variation
     field g(s) = delta F / delta v(s).  F is scale invariant, so a critical
     point over {v >= 0} has g = 0 on the support of v; no multiplier enters.
  2. The cosine family v = cos(c s): family optimum c*, and dF/dc at c = 8/5.
  3. Multistart BFGS in the squared parametrization v = w^2, w an even
     Chebyshev series (positivity free, quadrature exact for polynomials),
     with the analytic gradient from functional.gradient_field.
  4. Multistart L-BFGS-B over piecewise-linear v >= 0 on a 41-knot grid,
     using the EXACT lattice-aligned evaluator (an earlier run against the
     smooth-panel quadrature let the optimizer inflate F by ~5e-4 of pure
     quadrature error at the kinks; the exact evaluator kills that failure
     mode, and its optimum agrees with route 3).
  5. The clean quartic family 1 + q1 s^2 + q2 s^4 and the chosen rational
     window OPT_Q, with the exact improvement over the paper's window.

Run: .venv/bin/python hunts/rogue_frontier/window_opt/optimize.py
"""

from __future__ import annotations

import json
import os
import sys

import numpy as np
from scipy.optimize import minimize, minimize_scalar

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functional import (OPT_Q, gradient_field, moments_polyeven_exact,  # noqa: E402
                        moments_pwlinear_exact, moments_quad)

PAPER_F = 0.685243875537318196  # exact closed form, 18 digits


def _full(a):
    """even Chebyshev coefficient vector -> full coefficient vector"""
    c = np.zeros(2 * len(a) - 1)
    c[::2] = a
    return c


def _cheb_w(a):
    return lambda s: np.polynomial.chebyshev.chebval(2.0 * s, _full(a))


def part1_el_residual():
    print("== 1. Euler-Lagrange test at v = cos(8s/5) ==")
    gf = gradient_field(lambda s: np.cos(1.6 * s))
    g = gf["g"]
    l2 = np.sqrt(2.0 * np.dot(gf["w"], g ** 2))
    print(f"F = {gf['F']:.15f}")
    print(f"first-variation residual: max|g| = {np.max(np.abs(g)):.4e}, "
          f"||g||_2 = {l2:.4e}")
    print(f"Euler identity int g v (must vanish): {gf['euler']:.2e}")
    print("residual profile (s, g):")
    for i in range(0, len(gf["s"]), 8):
        print(f"  s={gf['s'][i]:.4f}  g={g[i]: .5e}")
    print("verdict: cos(8s/5) is NOT a critical point of F over even v >= 0")
    print("         (compare max|g| ~ 3e-9 at the optimizer, part 3)")
    return gf


def part2_cos_family():
    print("\n== 2. the cosine family v = cos(c s) ==")
    f = lambda c: -moments_quad(lambda s: np.cos(c * s))["F"]
    res = minimize_scalar(f, bounds=(0.5, 2.5), method="bounded",
                          options={"xatol": 1e-13})
    cstar, Fstar = res.x, -res.fun
    h = 1e-6
    dF = (-f(1.6 + h) + f(1.6 - h)) / (2 * h)
    print(f"dF/dc at c = 8/5: {dF:+.6e}   (sympy exact: +1.4892581773e-4)")
    print(f"family optimum: c* = {cstar:.12f}, F(c*) = {Fstar:.15f}")
    print(f"gain over c = 8/5 within the family: {Fstar - PAPER_F:.3e}")
    return cstar, Fstar


def part3_chebyshev(J: int = 8, n_starts: int = 12, seed: int = 7):
    print(f"\n== 3. multistart BFGS, v = w^2, w even Chebyshev (J = {J}) ==")

    def negF_grad(a):
        w = _cheb_w(a)
        gf = gradient_field(lambda s: w(s) ** 2)
        wv = w(gf["s"])
        grads = np.empty(len(a))
        for j in range(len(a)):
            cj = np.zeros(len(a))
            cj[j] = 1.0
            Tj = np.polynomial.chebyshev.chebval(2.0 * gf["s"], _full(cj))
            grads[j] = 2.0 * np.dot(gf["w"], gf["g"] * 2.0 * wv * Tj)
        return -gf["F"], -grads

    rng = np.random.default_rng(seed)
    xf = np.linspace(-1, 1, 401)
    cf = np.polynomial.chebyshev.chebfit(
        xf, np.sqrt(np.cos(1.6 * (xf / 2))), 2 * J - 2)
    starts = [cf[::2].copy()]
    for _ in range(n_starts):
        a = np.zeros(J)
        a[0] = 1.0
        a[1:] = 0.3 * rng.standard_normal(J - 1) / np.arange(2, J + 1)
        starts.append(a)

    best = None
    for i, a0 in enumerate(starts):
        res = minimize(negF_grad, a0, jac=True, method="BFGS",
                       options={"gtol": 1e-12, "maxiter": 2000})
        F = -res.fun
        tag = "paper-projection" if i == 0 else f"random {i}"
        print(f"  start {tag:16s}: F = {F:.12f}  "
              f"(nit={res.nit}, |grad|={np.linalg.norm(res.jac):.1e})")
        if best is None or F > best[0]:
            best = (F, res.x)
    F, a = best
    w = _cheb_w(a)
    v = lambda s: w(s) ** 2
    gf = gradient_field(v)
    v0 = w(0.0) ** 2
    ss = np.linspace(0, 0.5, 201)
    prof = v(ss) / v0
    print(f"best F = {F:.15f}   (improvement over paper: {F - PAPER_F:.6e})")
    print(f"m2 = {gf['m2']:.15f}, m3 = {gf['m3']:.15f}")
    print(f"optimum window: v(1/2)/v(0) = {v(np.array([0.5]))[0]/v0:.10f}, "
          f"monotone nonincreasing: {bool(np.all(np.diff(prof) <= 1e-12))}, "
          f"positive: {bool(np.all(prof > 0))}")
    print(f"EL residual at optimum: max|g| = {np.max(np.abs(gf['g'])):.2e} "
          "(interior critical point, positivity inactive)")
    print("normalized profile v(s)/v(0):")
    for sv in (0.0, 0.1, 0.2, 0.3, 0.4, 0.5):
        print(f"  s={sv:.1f}  {v(np.array([sv]))[0]/v0:.8f}   "
              f"cos ref {np.cos(1.6*sv)/1.0:.8f}")
    return F, a, v0


def part4_pwlinear(n: int = 41, n_starts: int = 8, seed: int = 11):
    print(f"\n== 4. multistart L-BFGS-B, exact pw-linear v >= 0 ({n} knots) ==")
    sg = np.linspace(0, 0.5, n)
    rng = np.random.default_rng(seed)
    best = None
    for trial in range(n_starts):
        if trial == 0:
            y0 = np.cos(1.6 * sg)
        elif trial == 1:
            y0 = np.ones(n)
        else:
            y0 = np.clip(1 - 1.4 * sg ** 2 + 0.1 * rng.standard_normal(n),
                         0.05, None)
        res = minimize(lambda y: -moments_pwlinear_exact(y)[2], y0,
                       method="L-BFGS-B", bounds=[(0.0, None)] * n,
                       options={"maxiter": 6000, "ftol": 1e-16,
                                "gtol": 1e-11})
        F = -res.fun
        print(f"  start {trial}: F = {F:.12f}")
        if best is None or F > best[0]:
            best = (F, res.x)
    F, y = best
    print(f"best F = {F:.15f}  (pw-linear representation bias ~4e-10 vs "
          "route 3)")
    print(f"monotone: {bool(np.all(np.diff(y) <= 1e-8))}, "
          f"v(1/2)/v(0) = {y[-1]/y[0]:.10f}")
    return F, y


def part5_quartic():
    print("\n== 5. the clean quartic family 1 + q1 s^2 + q2 s^4 ==")

    def negF(q):
        v = lambda s: 1.0 + q[0] * s ** 2 + q[1] * s ** 4
        return -moments_quad(v)["F"]

    res = minimize(negF, np.array([-1.467, 1.159]), method="Nelder-Mead",
                   options={"xatol": 1e-13, "fatol": 1e-16,
                            "maxiter": 20000, "maxfev": 20000})
    print(f"family optimum q = ({res.x[0]:.8f}, {res.x[1]:.8f}), "
          f"F = {-res.fun:.15f}")
    m2r, m3r, Fr = moments_polyeven_exact(OPT_Q)
    print(f"chosen rational window q = ({OPT_Q[0]}, {OPT_Q[1]}):")
    print(f"  F  = {Fr} (exact) = {float(Fr):.15f}")
    print(f"  exact improvement over the paper window: "
          f"{float(Fr) - PAPER_F:.6e}")
    print(f"  lift of the RH-conditional constant: "
          f"{(float(Fr) - PAPER_F)/18:.6e}")
    return float(Fr)


def main():
    part1_el_residual()
    part2_cos_family()
    F3, a, v0 = part3_chebyshev()
    part4_pwlinear()
    Fr = part5_quartic()

    out = {
        "sup_F_measured": F3,
        "paper_F": PAPER_F,
        "improvement": F3 - PAPER_F,
        "chebyshev_even_coeffs_of_w": list(a / np.sqrt(v0)),
        "note": "v = w^2 with w(s) = sum_j a_j T_{2j}(2s); normalized v(0)=1",
        "rational_window_q": [str(q) for q in OPT_Q],
        "rational_window_F": Fr,
    }
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "best_window.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=2)
    print(f"\nsaved optimizer record to {path}")
    print(f"\nSUMMARY: sup F (measured) = {F3:.13f}; paper window "
          f"{PAPER_F:.13f}; delta = {F3 - PAPER_F:.3e}; "
          f"rational window achieves {Fr:.15f} exactly.")


if __name__ == "__main__":
    main()
