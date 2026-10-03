"""Exact and bounded numerical checks, not a formal verification of RH."""

import json
from pathlib import Path

import pytest
import sympy as sp
from mpmath import mp

from hunts.rh_theta_laguerre.probe import (
    control, endpoint_slope, laguerre_coefficient, partial_transform,
    phi_partial, xi,
)

HERE = Path(__file__).resolve().parent


def test_endpoint_derivative_polynomial():
    u, a, v = sp.symbols("u a v", real=True)
    phi = (2*a*a*sp.exp(9*u)-3*a*sp.exp(5*u))*sp.exp(-a*sp.exp(4*u))
    expected = a*(-8*a*a+30*a-15)*sp.exp(-a)
    assert sp.simplify(sp.diff(phi, u).subs(u, 0)-expected) == 0
    # For n>=2, a=pi*n^2>12; every coefficient below is negative.
    assert sp.expand((-8*a*a+30*a-15).subs(a, 12+v)) == -807-162*v-8*v*v


def test_exact_positive_first_order_control():
    u, q = sp.symbols("u q", real=True)
    c = sp.Rational(17, 16)
    p = (17*sp.chebyshevt(4, u)+8*sp.chebyshevt(5, u)+8*sp.chebyshevt(3, u))/33
    # d^2 P(cos t)/dt^2 = (1-u^2) P''(u) - u P'(u).
    l1 = (1-u*u)*sp.diff(p, u)**2-p*((1-u*u)*sp.diff(p, u, 2)-u*sp.diff(p, u))
    product_formula = (q*q*(1+c*u)+16*(c+u)**2)/(c+1)**2
    assert sp.expand(l1-product_formula.subs(q, sp.chebyshevt(4, u))) == 0
    nonnegative = ((1-q*q)/16+(u+1)*(2+sp.Rational(17, 16)*q*q)
                   +16*(u+1)**2)/(c+1)**2
    # Each term in nonnegative is >=0 for u=cos(t), q=cos(4t).
    assert sp.expand(product_formula-nonnegative) == 0
    assert p.subs(u, 1) == 1
    assert sum((sp.Rational(17, 33), sp.Rational(8, 33), sp.Rational(8, 33))) == 1


def test_exact_second_order_control_failure():
    # Even derivatives of sum w_k cos(k t) at t=pi, no float pi.
    weights = {3: sp.Rational(8, 33), 4: sp.Rational(17, 33), 5: sp.Rational(8, 33)}
    jet = [sum(w*(-1)**k*(-1)**j*k**(2*j) for k, w in weights.items())
           for j in range(3)]
    assert jet == [sp.Rational(1, 33), 0, -sp.Rational(432, 11)]
    assert jet[0]*jet[2]/12+jet[1]**2/4 == -sp.Rational(12, 121)
    # cosh(alpha)=17/16 and cosh(1/2)>1+(1/2)^2/2>17/16.
    assert sp.Rational(17, 16) < 1+sp.Rational(1, 8)
    r = (17+sp.sqrt(33))/16
    assert sp.simplify((r+1/r)/2) == sp.Rational(17, 16)


def test_laguerre_formula_against_polynomial_expansion():
    x, y = sp.symbols("x y", real=True)
    f = lambda z: (z*z+1)*(z*z-4)
    modulus_square = sp.expand(f(x+sp.I*y)*f(x-sp.I*y))
    for n in range(5):
        derivative_formula = (-1)**n * sum(
            (-1)**j*sp.diff(f(x), x, j)*sp.diff(f(x), x, 2*n-j)
            / (sp.factorial(j)*sp.factorial(2*n-j))
            for j in range(2*n+1)
        )
        assert sp.expand(derivative_formula-modulus_square.coeff(y, 2*n)) == 0
    # A planted nonreal pair is detected at x=0.
    assert modulus_square.coeff(y, 2).subs(x, 0) < 0


def test_remainder_algebra():
    t, d, r0, r1, r2 = sp.symbols("t d r0 r1 r2")
    l1 = (2*d/t**3+r1)**2-(-d/t**2+r0)*(-6*d/t**4+r2)
    error = 4*d*r1/t**3+r1*r1+d*r2/t**2+6*d*r0/t**4-r0*r2
    assert sp.expand(l1+2*d*d/t**6-error) == 0


@pytest.mark.parametrize("terms", [1, 2, 3])
def test_slope_from_differentiation_and_omitted_tail(terms):
    with mp.workdps(75):
        d = endpoint_slope(terms)
        derivative = mp.diff(lambda u: phi_partial(u, terms), 0)
        omitted = mp.fsum(
            a*(-8*a*a+30*a-15)*mp.exp(-a)
            for a in (mp.pi*n*n for n in range(terms+1, 13))
        )
        assert d > 0
        assert abs(d-derivative) < mp.mpf("1e-65")
        assert abs(d+omitted) < mp.mpf("1e-65")


def test_theta_normalization_and_evenness():
    with mp.workdps(75):
        # Twelve terms are used here only as a finite diagnostic.
        for order in (1, 3, 5):
            assert abs(mp.diff(lambda u: phi_partial(u, 12), 0, order)) < mp.mpf("1e-65")
        for t in (0, 10, 40):
            assert abs(partial_transform(mp.mpf(t), 12)-xi(mp.mpf(t)/2)/8) < mp.mpf("1e-65")


def test_saved_precision_response_and_counts():
    data = json.loads((HERE / "results.json").read_text())
    assert data["rh_resolved"] is False
    assert data["counts"] == {
        "truncation_points": 18, "negative_truncation_L1": 16,
        "xi_points": 8, "negative_xi_L1": 0,
        "quadrature_derivative_checks": 6, "control_checks": 2,
    }
    with mp.workdps(85):
        rows = {(r["dps"], r["terms"], r["t"]): r for r in data["truncations"]}
        for terms in (1, 2, 3):
            for t in (200, 400, 800):
                lo, hi = rows[50, terms, t], rows[80, terms, t]
                for key in ("slope", "H", "L1"):
                    assert abs(mp.mpf(lo[key])/mp.mpf(hi[key])-1) < mp.mpf("1e-30")
            assert mp.mpf(rows[80, terms, 800]["L1"]) < 0
        # Retain the pre-asymptotic positive value instead of hiding it.
        assert mp.mpf(rows[80, 3, 200]["L1"]) > 0
        for row in data["quadrature_checks"]:
            assert max(map(mp.mpf, row["relative_errors"])) < mp.mpf("1e-45")
        for row in data["xi_checks"]:
            assert mp.mpf(row["L1"]) > 0
        for row in data["control_checks"]:
            assert abs(mp.mpf(row["L2_at_pi"])+mp.mpf(12)/121) < mp.mpf("1e-40")
            assert mp.mpf(row["alpha"]) < mp.mpf(1)/2


def test_negative_control_recomputed_without_saved_values():
    with mp.workdps(50):
        assert abs(laguerre_coefficient(control, mp.pi, 2)+mp.mpf(12)/121) < mp.mpf("1e-45")
        assert laguerre_coefficient(lambda t: partial_transform(t, 1), mp.mpf(400), 1) < 0


def test_any_finite_order_cutoff_bound_algebra():
    n, r = sp.symbols("n r", positive=True)
    # K=n+r: delta*q_n/q_(n-1)>=1 reduces to this positive numerator.
    assert sp.expand(4*(n+r)**2-2*n*(2*n-1)) == 4*r*r+8*n*r+2*n
    # K=1+r: the separate n=1 bound has this nonnegative numerator.
    assert sp.expand((1+r)**2-1) == r*r+2*r
    c = sp.Rational(17, 16)
    assert 8-2*c > 0  # Lower bound for every h_j, j>=2, before (2j)!.


@pytest.mark.parametrize("cutoff,order,expected", [
    (2, 3, -sp.Rational(2806, 495)),
    (3, 4, -sp.Rational(407815057, 1372140)),
])
def test_higher_cutoff_control_eventually_detected(cutoff, order, expected):
    c = sp.Rational(17, 16)
    frequency = 4*cutoff
    h = [(c-1)**2]+[(2**(2*j-1)-2*c)/sp.factorial(2*j) for j in range(1, order+1)]
    q = [sp.Integer(1)]+[sp.Rational((2*frequency)**(2*j), 2*sp.factorial(2*j))
                         for j in range(1, order+1)]
    assert sum(h[j]*q[order-j] for j in range(order+1))/(c+1)**2 == expected
    with mp.workdps(60):
        f = lambda t: control(t, cutoff)
        for n in range(1, cutoff+1):
            for t in (mp.mpf(0), mp.pi/3, mp.pi):
                assert laguerre_coefficient(f, t, n) > 0
        assert abs(laguerre_coefficient(f, mp.pi, order)-mp.mpf(str(expected.p))/int(expected.q)) < mp.mpf("1e-50")
        assert abs(f(mp.pi+mp.j*mp.acosh(mp.mpf(17)/16))) < mp.mpf("1e-50")


def test_kernel_jacobian_and_factorials_on_gaussian():
    x, w, t = sp.symbols("x w t", real=True)
    f = sp.sqrt(sp.pi)*sp.exp(-t*t/4)
    for n in range(4):
        kernel = sp.exp(-x*x/2)*sp.integrate(
            w**(2*n)*sp.exp(-w*w/2), (w, -sp.oo, sp.oo)
        ) / (2*sp.factorial(2*n))
        expected_kernel = sp.sqrt(2*sp.pi)*sp.exp(-x*x/2)/(2**(n+1)*sp.factorial(n))
        assert sp.simplify(kernel-expected_kernel) == 0
        coefficient = (-1)**n * sum(
            (-1)**j*sp.diff(f, t, j)*sp.diff(f, t, 2*n-j)
            / (sp.factorial(j)*sp.factorial(2*n-j))
            for j in range(2*n+1)
        )
        # Fourier transform of exp(-x^2/2) is sqrt(2*pi)*exp(-t^2/2).
        expected = sp.pi*sp.exp(-t*t/2)/(2**n*sp.factorial(n))
        assert sp.simplify(coefficient-expected) == 0


def test_integration_by_parts_identities_on_exponential():
    u, t = sp.symbols("u t", real=True)
    phi = sp.exp(-u)
    g, h = u*phi, u*u*phi
    # Exact cosine integrals of polynomial times exp(-u), independent of
    # the numerical gamma implementation used for the theta kernel.
    def cosine_integral(expr):
        poly = sp.Poly(sp.expand(expr/phi), u)
        return sum(coef*sp.factorial(power[0])/2*(
            (1-sp.I*t)**(-power[0]-1)+(1+sp.I*t)**(-power[0]-1)
        ) for power, coef in poly.terms())
    H = 1/(1+t*t)
    d = sp.diff(phi, u).subs(u, 0)
    identities = [
        -d/t**2+(sp.diff(phi, u, 3).subs(u, 0)+cosine_integral(sp.diff(phi, u, 4)))/t**4,
        2*d/t**3-(sp.diff(g, u, 4).subs(u, 0)+cosine_integral(sp.diff(g, u, 5)))/t**5,
        -6*d/t**4+(sp.diff(h, u, 5).subs(u, 0)+cosine_integral(sp.diff(h, u, 6)))/t**6,
    ]
    for j, rhs in enumerate(identities):
        assert sp.simplify(sp.diff(H, t, j)-rhs) == 0


def test_precision_is_not_left_modified():
    before = mp.dps
    with mp.workdps(45):
        partial_transform(mp.mpf(10), 1)
        laguerre_coefficient(control, mp.pi, 1)
    assert mp.dps == before
