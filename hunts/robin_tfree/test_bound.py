"""Checks for the Robin t-free bound: the identity, the integrals, the inputs, the pins.

Run: .venv/bin/python -m pytest -n0 -q hunts/robin_tfree/test_bound.py

Nothing here replaces a referee: these tests check that the exact identity of
RESULTS.md section 2 holds on real primes, that the closed-form integrals agree
with an independent quadrature, that the bound machinery dominates the true
E(x) where E(x) can be computed, and that a weakened bound is caught.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest
from flint import arb, ctx
from mpmath import mp, mpf, quad

from hunts.robin_tfree import bound as B

HERE = Path(__file__).resolve().parent
EULER_GAMMA = "0.57721566490153286060651209008240243104215933593992"


def _sieve(n: int) -> np.ndarray:
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0]


PRIMES = _sieve(3_000_000)


def _theta_upto(x: float) -> mpf:
    return mp.fsum(mp.log(int(p)) for p in PRIMES[PRIMES <= x])


def _exact_R_integral(x: int, y: int) -> mpf:
    """int_x^y (theta(u) - u) w(u) du with theta exact, using
    int w = -1/(u log u) and int u w = log log u - 1/log u."""
    ps = [int(p) for p in PRIMES if x < p <= y]
    knots = [x] + ps + [y]
    th = _theta_upto(x)
    W = lambda u: -1 / (u * mp.log(u))
    UW = lambda u: mp.log(mp.log(u)) - 1 / mp.log(u)
    total = mpf(0)
    for i, (a, b) in enumerate(zip(knots[:-1], knots[1:])):
        if i > 0:
            th += mp.log(a)  # a is the prime at the left end, theta jumps there
        if b > a:
            total += th * (W(mpf(b)) - W(mpf(a))) - (UW(mpf(b)) - UW(mpf(a)))
    return total


def _g(d: mpf, L: mpf) -> mpf:
    return d / L - mp.log(1 + mp.log(1 + d) / L)


def _E_true(x: int) -> mpf:
    """E(x) = log(e^-gamma prod_{p<=x} p/(p-1) / log theta(x)), from the primes."""
    ps = PRIMES[PRIMES <= x]
    s = mp.fsum(-mp.log(1 - mpf(1) / int(p)) for p in ps)
    return s - mpf(EULER_GAMMA) - mp.log(mp.log(_theta_upto(x)))


# -- 1. the identity ----------------------------------------------------------


@pytest.mark.parametrize("x,y", [(10_007, 99_991), (1_000_003, 2_000_003)])
def test_mertens_partial_summation_with_real_primes(x, y):
    """sum_{x<p<=y} 1/p = loglog y - loglog x + R(y)/(y log y) - R(x)/(x log x)
    + int_x^y R w: the sign convention every later step uses."""
    with mp.workdps(40):
        lhs = mp.fsum(mpf(1) / int(p) for p in PRIMES if x < p <= y)
        R = lambda z: _theta_upto(z) - z
        rhs = (mp.log(mp.log(y)) - mp.log(mp.log(x)) + R(y) / (y * mp.log(y))
               - R(x) / (x * mp.log(x)) + _exact_R_integral(x, y))
        assert abs(lhs - rhs) < mpf("1e-25")
        # the opposite sign on the integral is far off: the check has teeth
        wrong = rhs - 2 * _exact_R_integral(x, y)
        assert abs(lhs - wrong) > mpf("1e-12")


@pytest.mark.parametrize("x,y", [(10_007, 99_991), (1_000_003, 2_000_003)])
def test_E_difference_identity_with_real_primes(x, y):
    """E(y) - E(x) = int_x^y R w + sum_{x<p<=y} h(p) + g(d_y) - g(d_x), the
    difference form of RESULTS.md (2.3), including the cancellation term g."""
    with mp.workdps(40):
        h = mp.fsum(-mp.log(1 - mpf(1) / int(p)) - mpf(1) / int(p) for p in PRIMES if x < p <= y)
        dx = (_theta_upto(x) - x) / x
        dy = (_theta_upto(y) - y) / y
        rhs = (_exact_R_integral(x, y) + h + _g(dy, mp.log(y)) - _g(dx, mp.log(x)))
        assert abs((_E_true(y) - _E_true(x)) - rhs) < mpf("1e-25")


def test_second_order_remainder_lemma():
    """|g(d)| <= d^2/L for |d| <= 1e-6 and L >= 31 (RESULTS.md Lemma 2)."""
    with mp.workdps(60):
        rng = np.random.default_rng(20261004)
        for _ in range(400):
            d = mpf(float(rng.uniform(-1e-6, 1e-6)))
            L = mpf(float(rng.uniform(31, 1e5)))
            assert abs(_g(d, L)) <= d * d / L
        # and it is not much smaller than that: g ~ d^2/(2L) (1 + 1/L)
        d, L = mpf("1e-6"), mpf(31)
        assert _g(d, L) > d * d / (2 * L)


# -- 2. the integrals -----------------------------------------------------------


@pytest.mark.parametrize("alpha", [Fraction(1, 2), Fraction(1, 3), Fraction(1, 5), Fraction(1)])
@pytest.mark.parametrize("a,b", [(31.0, 32.5), (43.75, 45.0), (50.0, 100.0)])
def test_closed_form_integral_against_quadrature(alpha, a, b):
    ctx.prec = 200
    got = B.power_integral(alpha, arb(repr(a)), arb(repr(b)))
    with mp.workdps(40):
        al = mpf(alpha.numerator) / alpha.denominator
        ref = quad(lambda y: mp.e ** ((al - 1) * y) * (1 + y) / y**2, [mpf(repr(a)), mpf(repr(b))])
    assert abs(float(got.mid()) - float(ref)) <= 1e-12 * abs(float(ref))


def test_two_routes_for_the_main_integral():
    """The ball route (E1 closed form) against mpmath quadrature in u, block by block."""
    ctx.prec = 200
    ball = B.main_integral(B.X0)
    with mp.workdps(30):
        extra = B.theta_deficit_terms(B.X_BUTHE)
        w = lambda u: (1 + mp.log(u)) / (u**2 * mp.log(u) ** 2)
        tot = mpf(0)
        for a, b, m in B.table1_blocks(B.X0, B.X_BUTHE):
            f = lambda u, m=m: (mpf(m.numerator) / m.denominator * mp.sqrt(u)
                                + sum(mpf(c.numerator) / c.denominator * u ** (mpf(e.numerator) / e.denominator)
                                      for c, e in extra)) * w(u)
            tot += quad(f, mp.linspace(mpf(a), mpf(b), 8))
    assert abs(float(ball.mid()) - float(tot)) < 1e-12 * float(tot)


# -- 3. inputs -------------------------------------------------------------------


def test_table1_covers_the_range_and_matches_buthe_theorem_2():
    blocks = B.table1_blocks(B.X0, B.X_BUTHE)
    assert blocks[0][0] == B.X0 and blocks[-1][1] == B.X_BUTHE
    assert all(a < b for a, b, _ in blocks)
    assert all(b1 == a2 for (_, b1, _), (a2, _, _) in zip(blocks[:-1], blocks[1:]))
    # Buthe's (1.5) states 0.94 for 11 < x <= 1e19; the table maximum must equal it
    assert max(Fraction(v) for _, v in B.BUTHE_TABLE1_UPPER) == Fraction("0.94")
    # x0 sits in [16e12, 32e12] (M+ = .68); the next block [32e12, 64e12] has .93
    assert blocks[0][2] == Fraction("0.68") + B.TABLE1_MARGIN


def test_table8_rows_increase_and_bound_decreases_past_e100():
    bs = [b for b, _ in B.BKLNW_TABLE8]
    assert bs == sorted(bs) and bs[0] <= 43.749 < bs[1]  # 1e19 = e^43.749 is in the first row
    eps = [Fraction(e) for b, e in B.BKLNW_TABLE8 if b >= 100]
    assert max(eps) == Fraction("2.45299e-12")


def test_buthe_theta_bounds_on_real_primes():
    """Sanity of the inputs where they can be recomputed: 0.05 sqrt(x) < x - theta(x)
    <= 1.95 sqrt(x) (Buthe (1.6)-(1.7)) at sampled x up to 3e6."""
    for x in (1500, 10_000, 123_457, 1_000_000, 2_999_999):
        d = x - float(_theta_upto(x))
        assert 0.05 * math.sqrt(x) < d <= 1.95 * math.sqrt(x)


# -- 4. the bound against the truth where the truth is computable --------------


@pytest.mark.parametrize("x", [100_003, 1_000_003, 2_999_999])
def test_bound_dominates_true_E_and_a_weakened_bound_does_not(x):
    """E(x) <= I(x) + g(d_x) with I(x) the module's integral bound from x upward.
    Below 1e10 the bound uses the global 0.94; above, Buthe's table; past 1e19,
    BKLNW. Then scale I by 0.25 and watch the comparison fail somewhere."""
    ctx.prec = 200
    with mp.workdps(30):
        I = float((B.main_integral(x) + B.tail_integral()).upper().mid())
        dx = (_theta_upto(x) - x) / x
        truth = float(_E_true(x))
        g = float(_g(dx, mp.log(x)))
    assert truth <= I + g
    assert truth > 0  # theta(x) < x here, so the product overshoots log theta


def test_weakened_bound_is_caught():
    """The planted fault: with I scaled by 0.25 the truth exceeds it at some sampled x.
    A comparison that could never fail would not be a check."""
    ctx.prec = 200
    caught = False
    for x in (100_003, 1_000_003, 2_999_999):
        I = float((B.main_integral(x) + B.tail_integral()).upper().mid())
        with mp.workdps(30):
            dx = (_theta_upto(x) - x) / x
            truth = float(_E_true(x))
            g = float(_g(dx, mp.log(x)))
        caught |= truth > 0.25 * I + g
    assert caught


# -- 5. the elementary reductions ------------------------------------------------


def _sigma_table(n: int) -> np.ndarray:
    s = np.zeros(n + 1, dtype=np.int64)
    for d in range(1, n + 1):
        s[d::d] += d
    return s


def test_robin_holds_directly_from_5041_to_13_primorial():
    """Morrill-Platt's Theorem 13 covers this; recheck the bottom of the range directly."""
    n_max = 30030
    sig = _sigma_table(n_max)
    eg = math.exp(float(EULER_GAMMA))
    for n in range(5041, n_max + 1):
        assert sig[n] < eg * n * math.log(math.log(n)) * (1 - 1e-12)


def test_n_over_phi_is_maximized_by_the_primorial_with_the_same_prime_count():
    """omega(n) <= k for n < N_{k+1}, so n/phi(n) <= N_k/phi(N_k): checked to 2e5,
    with the valuation factor sigma(n)/n = (n/phi(n)) prod (1 - q^-(e+1))."""
    n_max = 200_000
    sig = _sigma_table(n_max)
    primes = [int(p) for p in PRIMES[:20]]
    prim, ratio = [1], [Fraction(1)]
    for p in primes:
        prim.append(prim[-1] * p)
        ratio.append(ratio[-1] * Fraction(p, p - 1))
    phi = np.arange(n_max + 1, dtype=np.int64)
    for p in [int(p) for p in PRIMES if p <= n_max]:
        phi[p::p] -= phi[p::p] // p
    for n in range(2, n_max + 1):
        k = max(i for i in range(len(prim)) if prim[i] <= n)
        assert Fraction(n, int(phi[n])) <= ratio[k]
        assert sig[n] * int(phi[n]) < n * n  # sigma(n)/n < n/phi(n)


# -- 6. the pinned outputs ------------------------------------------------------


def test_pinned_results():
    res = B.run()
    a, b = res["route_A_uniform_1.95"], res["route_B_table1"]
    for r in (a, b):
        assert r["max_t_free"] == 25
        assert r["t_verdicts"][25] == "pass" and r["t_verdicts"][26] == "fail"
    assert 2.47e-8 < a["E_star_upper"] < 2.49e-8 and 2.33e-8 < b["E_star_upper"] < 2.35e-8
    assert 4.02e7 < a["Q_star_lower"] < 4.04e7 and 4.26e7 < b["Q_star_lower"] < 4.28e7
    va, vb = a["valuation_max_nu"], b["valuation_max_nu"]
    assert (va["2"], va["3"], va["5"], va["7"], va["11"], va["13"]) == (24, 14, 9, 7, 6, 5)
    assert (vb["2"], vb["3"], vb["5"], vb["7"], vb["11"], vb["13"]) == (24, 14, 9, 8, 6, 5)
    assert a["epsilon_upper"] < 2.49e-8 and b["epsilon_upper"] < 2.35e-8
    on_disk = json.loads((HERE / "results.json").read_text())
    for name in ("route_A_uniform_1.95", "route_B_table1"):
        assert on_disk[name]["max_t_free"] == res[name]["max_t_free"]
        assert on_disk[name]["E_star_upper"] == res[name]["E_star_upper"]


def test_the_conclusion_responds_to_its_inputs():
    """Route B: dropping Table 1's rounding margin keeps t = 25, as does adding 0.5 to
    every entry; adding 0.6 loses it. Route A: replacing 1.95 by 2.6 loses it. The
    margin is real and finite, and the computation moves when its inputs move."""
    ctx.prec = B.PREC
    saved_m, saved_c = B.TABLE1_MARGIN, B.BUTHE_THETA
    try:
        for m, t in ((Fraction(0), 25), (Fraction(1, 2), 25), (Fraction(6, 10), 24)):
            B.TABLE1_MARGIN = m
            assert B.max_tfree(B.e_star(route="table1")["E_star"], B.slack())[0] == t
        B.TABLE1_MARGIN = saved_m
        for c, t in (("1.95", 25), ("2.6", 24)):
            B.BUTHE_THETA = c
            assert B.max_tfree(B.e_star(route="uniform")["E_star"], B.slack())[0] == t
    finally:
        B.TABLE1_MARGIN, B.BUTHE_THETA = saved_m, saved_c


def test_separate_bounding_loses_what_the_cancellation_keeps():
    """The prior-art shape: bound the partial-summation boundary term and the
    log theta denominator separately, each by 1.95/(sqrt(x0) log x0). With route A's
    integral that is enough to lose t = 25 (this is the step RESULTS.md section 2
    removes, and why 25 was out of reach for the separate-terms method at this x0)."""
    ctx.prec = B.PREC
    parts = B.e_star(route="uniform")
    x0 = arb(B.X0)
    sep = 2 * arb("1.95") / (x0.sqrt() * x0.log())
    assert B.max_tfree(parts["E_star"], B.slack())[0] == 25
    assert B.max_tfree(parts["E_star"] + sep, B.slack())[0] == 24
