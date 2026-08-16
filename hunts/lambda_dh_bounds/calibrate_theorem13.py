"""Numeric calibration of the strip-to-time factor Delta^2/2 in de Bruijn (1950) Thm 13.

Convention under test (the hunt's H_t normalisation, multiplier e^{t u^2}):
if all zeros of G(z) = int F(u) e^{izu} du lie in |Im z| <= Delta, then all
zeros of G_t(z) = int e^{t u^2} F(u) e^{izu} du are real for t >= Delta^2 / 2.

House rule: the factor is DERIVED here, never recalled. Three routes:

  0. Operator identity: the multiplier e^{t u^2} under the integral equals the
     operator exp(-t d^2/dz^2) applied to G, checked numerically on a Gaussian.
  A. Bare conjugate pair p(z) = z^2 + Delta^2 evolved by exp(-t d^2/dz^2)
     (finite series for polynomials): measured landing time t* vs Delta^2/2.
  B. Cosine polynomial H_0(z) = cos(z) + c, c > 1 (an exponential-sum
     trigonometric integral; zeros all at |Im z| = Delta measured, not recalled):
     the flowed function is e^t cos(z) + c; the complex zero pair is tracked by
     continuation and the landing t* measured by bisection. The ratio
     2 t* / Delta^2 must approach 1 as c -> 1+ (sharpness of the factor 1/2)
     and must exceed 1/4 (killing a hypothetical Delta^2/8) while staying
     <= 1 (consistent with Delta^2/2 as an upper bound; Delta^2 * 2 would be
     un-sharp by a factor 4).
  C. Conjugate pair plus distant real zeros, (z^2 + Delta^2)(z^2 - A^2):
     repulsion from the real pair can only speed the landing, so t* < Delta^2/2
     with t* -> Delta^2/2 as A -> inf.

All numbers below are measured (mpmath floats / numpy eigenvalue roots, one
route each unless stated); precision is stated per block. Nothing here is an
enclosure.
"""

from __future__ import annotations

import json
import math
import os
import sys

import numpy as np
from mpmath import mp

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "calibration.json")

results: dict = {"convention": "multiplier e^{t u^2}; claim: all real for t >= Delta^2/2"}


# ---------------------------------------------------------------- route 0
def route0_operator_identity() -> dict:
    """The e^{t u^2} multiplier and the polynomial series both solve the same
    backward heat equation dG/dt = -d2G/dz2; that shared PDE (plus identical
    initial data) is what licenses calibrating the multiplier with polynomials.

    (i) G(z,t) = int e^{(t-1)u^2} e^{izu} du, quadrature only, no closed form:
        the PDE residual dG/dt + d2G/dz2 is measured at sample points.
    (ii) p_t = sum_k (-t)^k/k! p^(2k) for a polynomial p: the same residual,
        exact finite sums, measured at sample points.
    """
    mp.dps = 30
    t = mp.mpf("0.1")
    worst_i = mp.mpf(0)

    def G(z, tt):
        return mp.quad(lambda u: mp.e ** ((tt - 1) * u * u) * mp.cos(z * u), [0, mp.inf]) * 2

    for z in [mp.mpf("0.7"), mp.mpf("1.9")]:
        dGdt = mp.diff(lambda s: G(z, s), t, 1)
        d2Gdz2 = mp.diff(lambda w: G(w, t), z, 2)
        worst_i = max(worst_i, abs(dGdt + d2Gdz2) / abs(G(z, t)))

    # polynomial side, numpy float64, residual of the same PDE
    p = np.array([1.0, 0.3, -2.0, 0.5, 3.0])  # arbitrary quartic
    worst_ii = 0.0
    h = 1e-5
    for z in [0.4, 1.3]:
        for tt in [0.05, 0.2]:
            val = lambda a, b: float(np.polyval(heat_evolve(p, b), a))
            dpdt = (val(z, tt + h) - val(z, tt - h)) / (2 * h)
            d2pdz2 = (val(z + h, tt) - 2 * val(z, tt) + val(z - h, tt)) / (h * h)
            worst_ii = max(worst_ii, abs(dpdt + d2pdz2) / max(1.0, abs(val(z, tt))))
    return {
        "what": "backward-heat PDE residual: (i) e^{tu^2}-multiplier Gaussian quadrature, dps 30; "
        "(ii) polynomial series, float64 central differences h=1e-5",
        "worst_relative_residual_multiplier_measured": float(worst_i),
        "worst_relative_residual_polynomial_measured": float(worst_ii),
    }


# ---------------------------------------------------------------- helpers
def heat_evolve(coeffs: np.ndarray, t: float) -> np.ndarray:
    """exp(-t d^2/dz^2) p as the finite series sum_k (-t)^k/k! p^(2k)."""
    out = np.array(coeffs, dtype=float)
    d = np.array(coeffs, dtype=float)
    fact = 1.0
    for k in range(1, len(coeffs) // 2 + 1):
        d = np.polyder(d, 2)
        if d.size == 0:
            break
        fact *= k
        out = np.polyadd(out, ((-t) ** k / fact) * d)
    return out


def landing_time_poly(coeffs: np.ndarray, lo: float, hi: float, iters: int = 60) -> float:
    """Bisect the smallest t with all roots of exp(-t D^2) p real (imag tol 1e-10)."""

    def all_real(t: float) -> bool:
        r = np.roots(heat_evolve(coeffs, t))
        return bool(np.max(np.abs(r.imag)) < 1e-10)

    assert not all_real(lo) and all_real(hi)
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if all_real(mid):
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


# ---------------------------------------------------------------- route A
def routeA_bare_pair() -> dict:
    out = []
    for Delta in [0.6, 0.895136, 1.2]:
        coeffs = np.array([1.0, 0.0, Delta * Delta])  # z^2 + Delta^2
        tstar = landing_time_poly(coeffs, 0.0, 2.0 * Delta * Delta)
        out.append(
            {
                "Delta": Delta,
                "t_star_measured": tstar,
                "Delta2_over_2": Delta * Delta / 2,
                "ratio_2tstar_over_Delta2": 2 * tstar / (Delta * Delta),
            }
        )
    return {
        "what": "p = z^2 + Delta^2 under exp(-t D^2); float64, bisection 60 iters, imag tol 1e-10",
        "cases": out,
    }


# ---------------------------------------------------------------- route B
def routeB_cosine() -> dict:
    """H_0 = cos z + c, flowed to e^t cos z + c; Delta measured, t* by continuation."""
    mp.dps = 30
    out = []
    for c_str in ["2.0", "1.05", "1.001"]:
        c = mp.mpf(c_str)

        # measure Delta: find the zero of cos z + c nearest z = pi + i
        z0 = mp.findroot(lambda z: mp.cos(z) + c, mp.mpc(mp.pi, 1.0))
        Delta = abs(mp.im(z0))
        # sanity: it is a zero and off-axis
        assert abs(mp.cos(z0) + c) < mp.mpf(10) ** (-25)
        assert Delta > 0

        # track the zero of e^t cos z + c and bisect on Im z(t) -> 0.
        # Near the landing the pair merges into a double root, so Newton can
        # only reach residual ~ (root error)^2; tol is relaxed accordingly and
        # the classification threshold 1e-9 on |Im z| corresponds to t within
        # ~1e-18 of the landing (Im z ~ sqrt(t* - t) there).
        def imag_at(t):
            zt = mp.findroot(
                lambda z: mp.e**t * mp.cos(z) + c, z0, tol=mp.mpf(10) ** (-20), maxsteps=200
            )
            return abs(mp.im(zt))

        lo, hi = mp.mpf(0), Delta * Delta  # 2*(Delta^2/2): must land inside
        assert imag_at(lo) > mp.mpf(10) ** (-9)
        assert imag_at(hi) < mp.mpf(10) ** (-9)
        for _ in range(60):
            mid = (lo + hi) / 2
            if imag_at(mid) < mp.mpf(10) ** (-9):
                hi = mid
            else:
                lo = mid
        tstar = (lo + hi) / 2
        out.append(
            {
                "c": c_str,
                "Delta_measured": float(Delta),
                "t_star_measured": float(tstar),
                "Delta2_over_2": float(Delta * Delta / 2),
                "ratio_2tstar_over_Delta2": float(2 * tstar / (Delta * Delta)),
            }
        )
    return {
        "what": "H_t = e^t cos z + c; dps 30, zero tracked by findroot continuation, bisection 80 iters",
        "cases": out,
    }


# ---------------------------------------------------------------- route C
def routeC_pair_plus_real() -> dict:
    out = []
    Delta = 1.0
    for A in [5.0, 20.0, 100.0]:
        coeffs = np.polymul([1.0, 0.0, Delta * Delta], [1.0, 0.0, -A * A])
        tstar = landing_time_poly(coeffs, 0.0, 2.0)
        out.append(
            {
                "Delta": Delta,
                "A": A,
                "t_star_measured": tstar,
                "Delta2_over_2": Delta * Delta / 2,
                "ratio_2tstar_over_Delta2": 2 * tstar / (Delta * Delta),
            }
        )
    return {
        "what": "(z^2+1)(z^2-A^2) under exp(-t D^2); float64, bisection 60 iters, imag tol 1e-10",
        "cases": out,
    }


# ---------------------------------------------------------------- hypothesis numerics
def phi_dh_decay_domination() -> dict:
    """Dominate |Phi_DH(u)| <= C e^{-|u|^3} explicitly (b = 3 > 2 suffices).

    |Phi_DH(u)| <= 4 e^{3u/2} sum n |a_n| e^{-pi n^2 e^{2u}/5}
                <= 4 e^{3u/2} e^{-(pi/5) e^{2u}} * S(u),  S(u) = sum n e^{-pi(n^2-1)e^{2u}/5},
    and S(u) <= S(0) for u >= 0. Check numerically that
    (pi/5) e^{2u} - (3/2) u - u^3 is positive and increasing on [2, 30].
    """
    mp.dps = 30
    S0 = mp.nsum(lambda n: n * mp.e ** (-mp.pi * (n * n - 1) / 5), [1, mp.inf])
    g = lambda u: (mp.pi / 5) * mp.e ** (2 * u) - mp.mpf(3) / 2 * u - u**3
    grid = [mp.mpf(2) + mp.mpf(28) * k / 200 for k in range(201)]
    vals = [g(u) for u in grid]
    increasing = all(vals[i + 1] > vals[i] for i in range(len(vals) - 1))
    return {
        "what": "decay margin g(u) = (pi/5)e^{2u} - (3/2)u - u^3 on [2,30], dps 30",
        "S0_measured": float(S0),
        "g_at_2": float(vals[0]),
        "min_on_grid": float(min(vals)),
        "increasing_on_grid": bool(increasing),
    }


def sharp_class_dirichlet_sum() -> dict:
    """sum |a_n| n^{-sigma} < inf for sigma > 1: measured partial sums, period-5 coefficients."""
    mp.dps = 30
    sys.path.insert(0, "/home/user/zeta-lab")
    from zeta.epstein import kappa

    k = kappa(30)
    a = [mp.mpf(1), k, k, mp.mpf(1), mp.mpf(0)]  # |a_n| pattern, period 5
    out = {}
    for sigma in ["1.05", "1.5", "2.0"]:
        s = mp.mpf(sigma)
        total = mp.nsum(lambda n: a[int(n - 1) % 5] * n ** (-s), [1, mp.inf])
        out[sigma] = float(total)
    return {
        "what": "sum |a_n| n^{-sigma}, |a_n| periodic (1,kappa,kappa,1,0), dps 30, mp.nsum",
        "kappa_measured": float(k),
        "sums": out,
    }


if __name__ == "__main__":
    results["route0_operator_identity"] = route0_operator_identity()
    results["routeA_bare_pair"] = routeA_bare_pair()
    results["routeB_cosine"] = routeB_cosine()
    results["routeC_pair_plus_real"] = routeC_pair_plus_real()
    results["phi_dh_decay_domination"] = phi_dh_decay_domination()
    results["sharp_class_dirichlet_sum"] = sharp_class_dirichlet_sum()
    with open(OUT, "w") as f:
        json.dump(results, f, indent=2)
    print(json.dumps(results, indent=2))
