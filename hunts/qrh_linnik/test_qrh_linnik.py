"""Checks for the qrh_linnik hunt: exponent algebra, proof bookkeeping, least primes.

Every number quoted in RESULTS.md sections 4 to 6 is pinned here.  The exact
route (sympy breakpoints) is compared with an independent float grid, and each
instrument is shown to react to a planted fault.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
import pytest
import sympy as sp

from hunts.qrh_linnik import exponents as ex
from hunts.qrh_linnik import least_primes as lp

R = sp.Rational
HERE = Path(__file__).resolve().parent


# ---------------------------------------------------------------- exponents


@pytest.mark.parametrize(
    "family, L, sigma_star, almost",
    [
        (ex.CLASSICAL, R(12, 5), R(3, 4), R(6, 5)),
        (ex.CGL, R(7, 3), R(5, 7), R(7, 6)),
        (ex.SMOOTH, R(30, 13), R(7, 10), R(15, 13)),
    ],
)
def test_exact_linnik_exponents(family, L, sigma_star, almost):
    value, arg = ex.linnik_exponent(family)
    assert sp.simplify(value - L) == 0
    assert sp.simplify(arg - sigma_star) == 0
    assert sp.simplify(ex.almost_all_exponent(family) - almost) == 0


def test_binding_pieces_cross_at_the_optimum():
    # 7/3: Ingham meets CGL's first term at sigma = 5/7
    s = R(5, 7)
    assert ex.ingham(s) == R(7, 3)
    assert ex.cgl_terms(s)[0] == R(7, 3)
    assert max(ex.cgl_terms(s)[1:]) < R(7, 3)
    # 12/5: Ingham meets Huxley at 3/4; 30/13: Ingham meets 15/(3+5s) at 7/10
    assert ex.ingham(R(3, 4)) == ex.huxley(R(3, 4)) == R(12, 5)
    assert ex.ingham(R(7, 10)) == ex.smooth_terms(R(7, 10))[0] == R(30, 13)


@pytest.mark.parametrize("family", [ex.CLASSICAL, ex.CGL, ex.SMOOTH])
def test_float_grid_agrees_with_exact_route(family):
    value, arg = ex.linnik_exponent(family)
    g_value, g_arg = ex.grid_sup(family)
    assert abs(g_value - float(value)) < 2e-5
    assert abs(g_arg - float(arg)) < 2e-3


def test_theta_profile_seven_eighths_is_not_binding():
    for t in ["1/2", "3/5", "2/3", "7/10"]:
        theta = R(t)
        expected = max(2, ex.ingham(theta))
        assert ex.linnik_exponent(ex.CGL, theta)[0] == expected
    for t in ["5/7", "3/4", "7/8", "11/12", "99/100"]:
        assert ex.linnik_exponent(ex.CGL, R(t))[0] == R(7, 3)


@pytest.mark.parametrize(
    "c, expected",
    [("0", R(30, 13)), ("1/4", R(30, 13)), ("4/13", R(30, 13)),
     ("8/25", R(58, 25)), ("1/3", R(7, 3))],
)
def test_shadow_price_of_the_q1_exponent(c, expected):
    """Door 1: replacing q1^(1/3) by q1^c gives L = max(30/13, 2 + c)."""
    fam = ex.cgl_family(1, c=R(c))
    assert ex.linnik_exponent(fam)[0] == expected
    assert expected == max(R(30, 13), 2 + R(c))


def test_lesion_removing_huxley_moves_the_answer():
    """Huxley's piece carries [0.8, 7/8]; without it the sup jumps to 8/3."""
    assert ex.linnik_exponent(ex.cgl_family(1, huxley_on=False))[0] == R(8, 3)
    assert ex.linnik_exponent(ex.Family("Ingham only", (ex.ingham,)))[0] == R(8, 3)


def test_lesion_wrong_cgl_term_is_detected():
    """A transcription slip (T1 without the 1/3 loss) must change the value."""
    bad = ex.Family(
        "slip", (ex.ingham, ex.huxley),
        (lambda s: [3 / (1 + s)] + ex.cgl_terms(s)[1:],),
    )
    assert ex.linnik_exponent(bad)[0] != R(7, 3)


def test_divisor_profile_and_its_minimiser():
    a_star = ex.ALPHA_STAR
    assert sp.simplify(a_star**2 + 31 * a_star - 30) == 0
    assert sp.simplify(ex.LAMBDA_STAR - (2 + a_star / 3)) == 0
    assert abs(float(ex.LAMBDA_STAR) - 2.3130940742578656) < 1e-15
    assert ex.divisor_profile(1) == R(7, 3)
    assert ex.divisor_profile(R(47, 50)) == R(347, 150)
    for a in ["93/100", "937/1000", "939/1000", "94/100", "95/100", "12/13", "9/10"]:
        assert float(ex.divisor_profile(R(a))) >= float(ex.LAMBDA_STAR) - 1e-12
    for a in ["9390/10000", "9395/10000"]:
        assert float(ex.divisor_profile(R(a))) - float(ex.LAMBDA_STAR) < 5e-4


def test_divisor_window_bound():
    value, _ = ex.linnik_exponent(ex.cgl_family(R(93, 100), R(19, 20)))
    assert sp.simplify(value - (3979 - sp.sqrt(1432441)) / 1200) == 0
    assert 2.3184 < float(value) < 2.3185


@pytest.mark.parametrize(
    "A, theta, eps0",
    [("7/3", "7/8", "1/10"), ("12/5", "7/8", "1/100"), ("30/13", "7/8", "1/3"),
     ("2", "1/2", "1/10"), ("7/3", "99/100", "1/50"), ("7/3", "7/8", "2")],
)
def test_lemma5_bookkeeping_closes(A, theta, eps0):
    b = ex.proof_bookkeeping(R(A), R(theta), R(eps0))
    assert b["kappa"] > 0
    assert b["high"] < 0
    assert b["first"] < 1 - b["kappa"]
    assert b["second"] < 1 - b["kappa"]
    assert b["eta"] <= b["lambda"] / 8


def test_lemma5_bookkeeping_reacts_to_a_bad_parameter():
    """Lesion: with eps0 <= 0 there is no saving left to spend."""
    b = ex.proof_bookkeeping(R(7, 3), R(7, 8), R(0))
    assert b["kappa"] == 0 and b["second"] >= 1 - b["kappa"]


# ------------------------------------------------------------- least primes


def test_least_primes_hand_values():
    P = lp.primes_upto(1000)
    assert lp.least_primes(3, P) == {1: 7, 2: 2}
    assert lp.least_primes(5, P) == {1: 11, 2: 2, 3: 3, 4: 19}
    assert lp.least_primes(7, P)[1] == 29
    assert lp.least_primes(4, P) == {1: 5, 3: 3}


def test_sieve_matches_independent_brute_force():
    P = lp.primes_upto(200_000)
    for q in range(3, 81):
        assert lp.least_primes(q, P) == lp.brute_least_primes(q), q


def test_lesion_dropping_two_is_detected():
    P = lp.primes_upto(10_000)
    assert lp.least_primes(3, P[1:]) != lp.brute_least_primes(3)


def test_short_table_refuses():
    with pytest.raises(ValueError):
        lp.least_primes(101, lp.primes_upto(200))


def test_recorded_table_matches_recomputation():
    data = json.loads((HERE / "least_primes.json").read_text(encoding="utf-8"))
    assert data["row_fields"] == ["q", "M", "a_max", "exp_q50", "exp_q90"]
    rows = {r[0]: r for r in data["rows"]}
    assert len(rows) == data["Q"] - 2
    P = lp.primes_upto(3_000_000)
    for q in list(range(3, 120)) + [461, 997, 2310]:
        s = lp.summarize(q, lp.least_primes(q, P))
        assert rows[q][1] == s["M"] and rows[q][2] == s["a_max"], q
        assert abs(rows[q][4] - s["exp_q90"]) < 1e-4
    exps = [math.log(r[1]) / math.log(r[0]) for r in data["rows"]]
    assert abs(max(exps) - data["max_exp_max_all_q"]) < 1e-12
    assert data["count_exp_max_ge_2"] == sum(e >= 2 for e in exps) == 0
    big = [math.log(r[1]) / math.log(r[0]) for r in data["rows"] if r[0] >= 100]
    assert abs(max(big) - data["max_exp_max_q_ge_100"]) < 1e-12
    assert np.isclose(data["max_exp_max_q_ge_100"], math.log(rows[461][1]) / math.log(461))


@pytest.mark.parametrize("alpha", ["1", "19/20", "47/50", "9/10"])
def test_parse_reproduces_cgl_closed_forms(alpha):
    """Our reading of CGL Theorem 1.2's divisor form must reproduce the closed
    forms CGL state in their (12.6): crossings with Ingham at 2 + a/3,
    3 - 3a/4 and B(a) = (37 + 3a - sqrt(9a^2 + 222a - 71))/12."""
    a = R(alpha)
    s = ex.SIGMA
    t1, t2, t3 = ex.cgl_terms(s, a)[:3]
    i = ex.ingham(s)
    s1 = (3 + 2 * a) / (6 + a)
    assert sp.simplify((t1 - i).subs(s, s1)) == 0 and i.subs(s, s1) == 2 + a / 3
    s2 = 2 * (2 - a) / (4 - a)
    assert sp.simplify((t2 - i).subs(s, s2)) == 0 and i.subs(s, s2) == 3 - 3 * a / 4
    root = (43 - 3 * a - sp.sqrt(9 * a**2 + 222 * a - 71)) / 40
    assert sp.simplify((t3 - i).subs(s, root)) == 0
    assert sp.simplify(i.subs(s, root) - (37 + 3 * a - sp.sqrt(9 * a**2 + 222 * a - 71)) / 12) == 0


# ------------------------------------------------- Lemma 2 calibration (zeta)


def test_lemma2_sign_and_normalisation_for_zeta():
    """Measured: the explicit formula of Lemma 2, truncated at n zeros, closes
    on psi_w(1000) better as n grows, and a flipped zero-sum sign does not."""
    from hunts.qrh_linnik import explicit_check as ec

    r20 = ec.residual(1000, 20)
    r40 = ec.residual(1000, 40)
    flipped = ec.residual(1000, 40, sign=-1)
    assert r40 < r20 < 0.05
    assert flipped > 8 * r40
