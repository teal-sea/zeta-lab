"""Exact identities and independent checks for the square-construction attempt."""

import json
from pathlib import Path

from flint import arb, ctx
from mpmath import mp
import pytest
import sympy as sp

from hunts.rh_theta_laguerre.probe import phi_partial
from hunts.rh_theta_laguerre.ratio_witness import (
    NORM2, WITNESS, global_bounds, quadratic_form, ratio_ball, x2_tail,
)
from hunts.rh_theta_laguerre.squares import (
    conditional_ratios, derivative_polynomial, theta_jet_ball,
)

HERE = Path(__file__).resolve().parent


def test_score_integration_by_parts_at_arbitrary_order():
    u, v = sp.symbols("u v", real=True)
    n = sp.symbols("n", integer=True, positive=True)
    r = sp.Function("r")
    w, s = u+v, r(u)+r(v)
    A = w**(2*n)/s
    B = 4*n*w**(2*n-1)/s-w**(2*n)*(sp.diff(r(u), u)+sp.diff(r(v), v))/s**2
    assert sp.simplify(sp.diff(A, u)+sp.diff(A, v)-B) == 0
    # D(k(u)k(v)) = -S k(u)k(v): the full integrand identity.
    assert sp.simplify(A*s-w**(2*n)) == 0


def test_score_two_point_negative_square_identity():
    h, r, rp = sp.symbols("h r rp", positive=True)
    diagonal = 4*h/r-2*h*h*rp/(r*r)
    off_diagonal = 2/rp
    exact = -2*(h*rp-r)**2/(r*r*rp)
    assert sp.simplify(diagonal-off_diagonal-exact) == 0
    a = sp.symbols("a", positive=True)
    assert sp.simplify(exact.subs({r: a*h, rp: a})) == 0


def test_gaussian_all_order_recurrence_and_squares():
    a, t = sp.symbols("a t", positive=True)
    f = sp.exp(-t*t/(2*a))
    for n in range(6):
        actual = (-1)**n*sum(
            (-1)**j*sp.diff(f, t, j)*sp.diff(f, t, 2*n-j)
            /(sp.factorial(j)*sp.factorial(2*n-j)) for j in range(2*n+1)
        )
        assert sp.simplify(actual-f*f/(a**n*sp.factorial(n))) == 0


def test_theta_jet_polynomials_against_symbolic_differentiation():
    u, a = sp.symbols("u a", real=True)
    x = a*sp.exp(2*u)
    kernel = sp.exp(u/2)*(4*x*x-6*x)*sp.exp(-x)
    for order in range(5):
        coefficients = derivative_polynomial(order)
        polynomial = sum(sp.Rational(c.numerator, c.denominator)*a**j
                         for j, c in enumerate(coefficients))
        assert sp.simplify(sp.diff(kernel, u, order).subs(u, 0)-polynomial*sp.exp(-a)) == 0


def test_full_score_enclosures_against_direct_mpmath_jets():
    data = json.loads((HERE/"squares_results.json").read_text())
    with mp.workdps(85), ctx.workprec(320):
        k = lambda u: 2*phi_partial(u/2, 16)
        jets = [mp.diff(k, mp.mpf(1)/10, j) for j in range(3)]
        r = -jets[1]/jets[0]
        rp = r*r-jets[2]/jets[0]
        h = mp.mpf(1)/10
        eigenvalue = 4*h/r-2*h*h*rp/(r*r)-2/rp
        for run in data["score_runs"]:
            for text, value in zip(run["jets"], jets):
                assert arb(text).contains(arb(mp.nstr(value, 80)))
            assert arb(run["negative_eigenvalue"]) < 0
            assert arb(run["negative_eigenvalue"]).contains(arb(mp.nstr(eigenvalue, 80)))
            assert arb(run["central_linear"]) > 0
            assert arb(run["central_cubic"]) > 0
            assert all(arb(t) > 0 for t in run["tail_bounds"])


def test_geometric_theta_tails_cover_added_terms():
    with mp.workdps(85), ctx.workprec(256):
        for u_text in ("0", "0.1", "1"):
            u = mp.mpf(u_text)
            u_ball = arb(u_text)
            for order in (0, 1, 2, 4):
                enclosed, tail = theta_jet_ball(u_ball, order, terms=8)
                reference = mp.diff(lambda t: 2*phi_partial(t/2, 16), u, order)
                assert tail > 0
                assert enclosed.contains(arb(mp.nstr(reference, 80)))
        epsilon, tail0, tail2 = global_bounds(8, arb(4))
        assert epsilon > 0 and tail0 > 0 and tail2 > 0
        assert x2_tail(9) < x2_tail(8)


def test_exponential_integration_tail_constants():
    w, W, rate = sp.symbols("w W rate", positive=True)
    assert sp.integrate(sp.exp(-rate*w), (w, 0, sp.oo)) == 1/rate
    second = sp.integrate((W+w)**2*sp.exp(-rate*w), (w, 0, sp.oo))
    assert sp.simplify(second-(W*W/rate+2*W/rate**2+2/rate**3)) == 0


def test_saved_witness_recomputed_by_lag_grouping():
    data = json.loads((HERE/"ratio_witness_results.json").read_text())
    assert tuple(data["witness"]) == WITNESS
    assert NORM2 == data["norm2"] == 99984942
    assert len(WITNESS) == 24
    with ctx.workprec(256):
        for run in data["runs"]:
            ratios = [arb(row["ratio"]) for row in run["rows"]]
            # Independent summation by lag, not the implementation's i,j loop.
            total = NORM2*ratios[0]
            for lag in range(1, len(WITNESS)):
                weight = sum(WITNESS[j]*WITNESS[j+lag] for j in range(len(WITNESS)-lag))
                total += 2*weight*ratios[lag]
            result = total/(NORM2*ratios[0])
            assert result < 0
            assert result.overlaps(arb(run["quadratic_form"]))
            assert quadratic_form(ratios) < 0
            # Replace the kernel by a constant positive-definite one: no kill.
            assert quadratic_form([ratios[0]]*24) >= 0
            for row in run["rows"]:
                assert all(arb(bound) > 0 for bound in row["error_bounds"].values())
    assert data["counts"] == {"ratio_enclosures": 48, "negative_witness_enclosures": 2, "failures": 0}


@pytest.mark.parametrize("index", [0, 5, 23])
def test_ratio_enclosures_against_refined_independent_quadrature(index):
    # Different library, 12 instead of 8 theta terms, and [0,5] instead of [0,4].
    with mp.workdps(75), ctx.workprec(256):
        value = conditional_ratios(mp.mpf(index)/10, max_order=1, cutoff=5, terms=12)[0]
        enclosure, _ = ratio_ball(index, bits=192)
        assert enclosure.contains(arb(mp.nstr(value, 70)))


def test_coarse_pass_is_preserved_with_its_actual_scope():
    data = json.loads((HERE/"squares_results.json").read_text())
    assert data["rh_resolved"] is False
    assert data["counts"] == {"score_enclosures": 2, "conditional_ratios": 72,
                              "gram_matrices": 12, "negative_ratio_gram_matrices": 0}
    with mp.workdps(65):
        lo, hi = data["ratio_runs"]
        assert len(lo["rows"]) == len(hi["rows"]) == 12
        for a, b in zip(lo["rows"], hi["rows"]):
            assert a["x"] == b["x"]
            for x, y in zip(a["ratios"], b["ratios"]):
                assert abs(mp.mpf(x)/mp.mpf(y)-1) < mp.mpf("1e-27")
        assert all(mp.mpf(m["min_eigenvalue"]) > 0 for run in data["ratio_runs"] for m in run["matrices"])


def test_fine_probe_and_witness_rounding_from_saved_midpoints():
    data = json.loads((HERE/"ratio_witness_results.json").read_text())
    with mp.workdps(60), ctx.workprec(256):
        ratios = [mp.mpf(arb(row["ratio"]).mid().str(75, radius=False))
                  for row in data["runs"][-1]["rows"]]
        matrix = mp.matrix([[ratios[abs(i-j)]/ratios[0] for j in range(24)] for i in range(24)])
        eigenvalues, vectors = mp.eigsy(matrix)
        assert sum(value < 0 for value in eigenvalues) == 7
        assert abs(eigenvalues[0]-mp.mpf("-0.000001571730889123257173473247286308470137828")) < mp.mpf("1e-25")
        direction = 1 if vectors[0, 0] > 0 else -1
        for scale, negative in ((1000, False), (10000, True)):
            vector = tuple(int(mp.nint(direction*scale*vectors[j, 0])) for j in range(24))
            if scale == 10000:
                assert vector == WITNESS
            q = mp.fsum(vector[i]*vector[j]*matrix[i, j] for i in range(24) for j in range(24))
            assert (q < 0) == negative


def test_ratio_condition_is_not_necessary_for_real_zeros():
    x, b, c = sp.symbols("x b c", positive=True)
    ratio = 1+2*b*b*c/(sp.cosh(b*x)+c)
    # Gaussian half-line integral: I(b)=sqrt(pi)*exp(b^2),
    # integral w^2 exp(-w^2/4) cosh(bw) dw = I''(b).
    I = sp.sqrt(sp.pi)*sp.exp(b*b)
    assert sp.simplify(sp.diff(I, b, 2)/I-(2+4*b*b)) == 0
    m0 = sp.cosh(b*x)+c
    m2 = 2*sp.cosh(b*x)+(2+4*b*b)*c
    assert sp.simplify(m2/(2*m0)-ratio) == 0
    fourth = sp.diff(ratio, x, 4).subs(x, 0)
    assert sp.simplify(fourth-2*b**6*c*(5-c)/(c+1)**3) == 0
    assert sp.simplify(fourth.subs(c, 6)+12*b**6/343) == 0
    # b^2=log(6) gives k=exp(-u^2/2) cosh(bu). Its Fourier transform
    # is a nonzero Gaussian times cos(bt), with only real zeros.


def test_invalid_enclosure_domains_fail_loudly():
    with pytest.raises(ValueError):
        ratio_ball(41, cutoff=4)
    with pytest.raises(ValueError):
        derivative_polynomial(-1)
    with pytest.raises(ValueError):
        quadratic_form([arb(1)]*24, vector=(0,)*24)


def test_ball_precision_is_restored():
    before = ctx.prec
    ratio_ball(0, bits=128)
    assert ctx.prec == before
