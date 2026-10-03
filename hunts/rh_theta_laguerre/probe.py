"""Bounded float checks for the derivations in RESULTS.md, never an RH test.

Run from the repository root. Output is local to this hunt, no zero table is
used. The exact identities are checked separately by test_probe.py.
"""

from __future__ import annotations

import json
from pathlib import Path
from time import perf_counter

from mpmath import mp

HERE = Path(__file__).resolve().parent


def phi_term(u, n):
    """One summand of the half-line theta kernel, at the caller's precision."""
    a = mp.pi * n * n
    return (2 * a**2 * mp.exp(9*u) - 3 * a * mp.exp(5*u)) * mp.exp(-a * mp.exp(4*u))


def phi_partial(u, terms):
    if terms < 1:
        raise ValueError("terms must be positive")
    return mp.fsum(phi_term(u, n) for n in range(1, terms + 1))


def endpoint_slope(terms):
    """Phi_N'(0), not a numerical finite difference."""
    if terms < 1:
        raise ValueError("terms must be positive")
    return mp.fsum(
        a * (-8*a*a + 30*a - 15) * mp.exp(-a)
        for a in (mp.pi*n*n for n in range(1, terms + 1))
    )


def partial_transform(t, terms):
    """H_N(t) by upper incomplete gamma functions, for real t only."""
    if terms < 1 or mp.im(t):
        raise ValueError("positive terms and a real argument are required")
    w = mp.j*t/4
    return mp.fsum(
        mp.re(a**(-mp.mpf(1)/4-w) * (
            2 * mp.gammainc(mp.mpf(9)/4+w, a, mp.inf)
            - 3 * mp.gammainc(mp.mpf(5)/4+w, a, mp.inf)
        )) / 4
        for a in (mp.pi*n*n for n in range(1, terms + 1))
    )


def quadrature_jet(t, terms):
    """Independent finite [0,2] integrals for H_N, H_N', H_N''.

    Floating-point diagnostic only. The proof of the infinite-domain
    asymptotics does not rely on this quadrature or its omitted tail.
    """
    breaks = [mp.mpf(j)/16 for j in range(33)]
    return [
        mp.quadgl(lambda u: phi_partial(u, terms)*weight(u), breaks)
        for weight in (
            lambda u: mp.cos(t*u),
            lambda u: -u*mp.sin(t*u),
            lambda u: -u*u*mp.cos(t*u),
        )
    ]


def xi(t):
    """Xi(t) from gamma and zeta, independent of the theta partial sums."""
    s = mp.mpf(1)/2 + mp.j*t
    return mp.re(s*(s-1)*mp.power(mp.pi, -s/2)*mp.gamma(s/2)*mp.zeta(s)/2)


def control(t):
    """Six-atom positive-measure control with explicit nonreal zeros."""
    return (17*mp.cos(4*t) + 8*mp.cos(5*t) + 8*mp.cos(3*t))/33


def laguerre_coefficient(f, t, order):
    """Coefficient of y^(2n) in |f(t+iy)|^2 for a real entire f.

    Real-axis derivatives suffice; no modulus-based numerical
    differentiation or assumption on zero locations enters the formula.
    """
    if order < 0:
        raise ValueError("order must be nonnegative")
    jet = [mp.diff(f, t, j) / mp.factorial(j) for j in range(2*order + 1)]
    return (-1)**order * mp.fsum(
        (-1)**j * jet[j] * jet[2*order-j] for j in range(2*order + 1)
    )


def _text(value):
    return mp.nstr(value, mp.dps - 8)


def run():
    started = perf_counter()
    data = {"grade": "measured, floating point", "rh_resolved": False,
            "truncations": [], "quadrature_checks": [], "xi_checks": [],
            "control_checks": []}
    for dps in (50, 80):
        with mp.workdps(dps):
            for terms in (1, 2, 3):
                d = endpoint_slope(terms)
                assert d > 0, (dps, terms, "endpoint slope")
                for t in (200, 400, 800):
                    jet = [mp.diff(lambda x: partial_transform(x, terms), mp.mpf(t), j)
                           for j in range(3)]
                    curvature = jet[1]**2 - jet[0]*jet[2]
                    # No universal threshold is inferred from these points.
                    row = {"dps": dps, "terms": terms, "t": t,
                           "slope": _text(d), "H": _text(jet[0]),
                           "L1": _text(curvature),
                           "scaled_H": _text(t*t*jet[0]/d),
                           "scaled_L1": _text(t**6*curvature/d**2)}
                    data["truncations"].append(row)
                print(f"truncation: dps={dps}, N={terms}, 3 points completed", flush=True)
            for t in (0, 7, 20, 50):
                coeff = laguerre_coefficient(xi, mp.mpf(t), 1)
                data["xi_checks"].append({"dps": dps, "t": t, "L1": _text(coeff)})
            l2 = laguerre_coefficient(control, mp.pi, 2)
            assert abs(l2 + mp.mpf(12)/121) < mp.power(10, -dps + 8)
            alpha = mp.acosh(mp.mpf(17)/16)
            residual = abs(control(mp.pi + mp.j*alpha))
            assert residual < mp.power(10, -dps + 8)
            data["control_checks"].append({"dps": dps, "alpha": _text(alpha),
                "L2_at_pi": _text(l2), "zero_residual": _text(residual)})
            print(f"Xi/control: dps={dps}, 4 Xi points and 1 control completed", flush=True)

    with mp.workdps(60):
        for terms, t in ((1, 40), (2, 80)):
            jet = quadrature_jet(mp.mpf(t), terms)
            reference = [mp.diff(lambda x: partial_transform(x, terms), mp.mpf(t), j)
                         for j in range(3)]
            errors = [abs(a-b)/abs(b) for a, b in zip(jet, reference)]
            assert max(errors) < mp.mpf("1e-45"), (terms, t, errors)
            data["quadrature_checks"].append({"dps": 60, "terms": terms, "t": t,
                "relative_errors": [_text(x) for x in errors]})
            print(f"quadrature: N={terms}, t={t}, 3 derivatives compared", flush=True)

    data["counts"] = {"truncation_points": len(data["truncations"]),
                      "negative_truncation_L1": sum(mp.mpf(r["L1"]) < 0
                                                    for r in data["truncations"]),
                      "xi_points": len(data["xi_checks"]),
                      "negative_xi_L1": sum(mp.mpf(r["L1"]) < 0 for r in data["xi_checks"]),
                      "quadrature_derivative_checks": 3*len(data["quadrature_checks"]),
                      "control_checks": len(data["control_checks"])}
    data["elapsed_seconds"] = round(perf_counter() - started, 3)
    (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({"status": "completed", **data["counts"],
                      "elapsed_seconds": data["elapsed_seconds"]}), flush=True)


if __name__ == "__main__":
    run()
