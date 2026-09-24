"""Exact local statements at 2 and the refusal gate (mission kill-control 2).

Everything here is exact arithmetic; no tolerance is involved.
"""

from __future__ import annotations

import os
import sys

import pytest
import sympy

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_data as D  # noqa: E402
import ta_local as Lo  # noqa: E402


@pytest.fixture(scope="module")
def rep():
    return Lo.local_report(K=6)


def test_local_fourier_is_an_exact_unitary_involution(rep):
    assert rep["F_unitary"] and rep["F_squared_is_identity"]
    assert rep["F_fixes_one_Z2"] and rep["F_fixes_sigma2"]
    assert rep["F_moves_eps0"]


def test_theory_7_3_item_2_time_and_frequency_limiting_differ(rep):
    """The recheck the brief asked for: P_2 != Phat_2, exactly."""
    assert rep["P2_is_orth_projection"] and rep["Phat2_is_orth_projection"]
    assert rep["P2_equals_Phat2"] is False
    assert rep["P2_Phat2_commute"]
    assert rep["P2_Phat2_is_rank_one_onto_one_Z2"]


def test_local_sonin_space_closed_ball_zero_open_ball_sigma2(rep):
    assert rep["P2_join_Phat2_is_identity"]
    assert rep["closed_ball_sonin_dim"] == 0
    assert rep["open_ball_sonin_dim"] == 1
    assert rep["open_ball_sonin_spanned_by_sigma2"]
    assert rep["norm_sq_sigma2"] == "3/4" and rep["norm_sq_one_Z2"] == "1"


@pytest.mark.parametrize("K", [3, 5, 8])
def test_local_statements_do_not_depend_on_truncation(K):
    r = Lo.local_report(K=K)
    assert r["closed_ball_sonin_dim"] == 0 and r["open_ball_sonin_dim"] == 1
    assert r["P2_equals_Phat2"] is False and r["P2_Phat2_is_rank_one_onto_one_Z2"]


def test_unitary_data_accepted():
    assert D.validate(D.ZETA).alphas == (1,)
    assert D.validate(D.DEDEKIND_Q_SQRT_M23).alphas == (1, 1)
    # Dedekind Q(sqrt -23) tower at 2 (numerics us_check.json): s_k = 2, k = 1..7
    tower = ("tower", {k: 2 for k in range(1, 8)})
    assert D.validate(tower, degree=2).alphas == (1, 1)
    assert D.validate(("satake", (sympy.I,))).alphas == (sympy.I,)


def test_W_a_refused():
    with pytest.raises(D.NonUnitaryLocalData, match="non-unitary"):
        D.validate(D.W_A_QUARTER)
    s1 = sympy.Integer(2) ** sympy.Rational(1, 4) + sympy.Integer(2) ** sympy.Rational(-1, 4)
    s2 = sympy.Integer(2) ** sympy.Rational(1, 2) + sympy.Integer(2) ** sympy.Rational(-1, 2)
    with pytest.raises(D.NonUnitaryLocalData, match=r"\|s_1\(2\)\|"):
        D.validate(("tower", {1: s1, 2: s2}), degree=2)


def test_epstein_tower_refused_and_only_by_the_tower_beyond_the_window():
    with pytest.raises(D.NonUnitaryLocalData, match=r"s_3\(2\)\| = 6 > d = 2"):
        D.validate(D.EPSTEIN_116_TOWER, degree=2)
    # s_1, s_2 alone are those of the unitary pair (1, -1): the window c < 4
    # sees only s_1 (and s_2 enters at c > 4), so it cannot detect Epstein.
    assert set(D.validate(("tower", {1: 0, 2: 2}), degree=2).alphas) == {1, -1}


def test_tower_that_is_not_a_power_sum_refused():
    with pytest.raises(D.NonUnitaryLocalData, match="not a power-sum tower"):
        D.validate(("tower", {1: 0, 2: 2, 3: 1}), degree=2)


def test_float_tolerance_is_explicit():
    ok = D.validate(("satake", (1.0 + 1e-14,)), tol=1e-12)
    assert "tol 1e-12" in ok.checks[0]
    with pytest.raises(D.NonUnitaryLocalData):
        D.validate(("satake", (1.0 + 1e-9,)), tol=1e-12)
