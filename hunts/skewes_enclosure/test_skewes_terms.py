"""Pins for hunt #152: Revers's error terms, the zero sum, and planted faults."""

from __future__ import annotations

import dataclasses
import sys
from pathlib import Path

import pytest

flint = pytest.importorskip("flint")
from flint import arb  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
import skewes_terms as st  # noqa: E402
import zero_layer as zl  # noqa: E402


@pytest.fixture(autouse=True)
def _prec128():
    old = flint.ctx.prec
    flint.ctx.prec = 128
    yield
    flint.ctx.prec = old


def _contains_decimal(ball, printed: str) -> bool:
    """The printed six-digit value is within one unit of its last digit of the ball.

    One unit, not half: the paper's row at eta = 1.58e-5 prints 6.97516e-3 for
    6.9751654e-3, so its printing truncates at least there.
    """
    mant, exp = printed.split("e")
    digits = len(mant.split(".")[1])
    ulp = arb(10) ** (int(exp) - digits)
    return bool(abs(ball - arb(printed)) <= ulp + ball.rad())


# [Rev25] section 4: eta -> printed R, Saouter-Demichel and Chao-Plymen tables.
SD_TABLE = [("0.0000228", "2.79507e-3"), ("0.0000200", "2.79503e-3"),
            ("0.0000180", "2.79500e-3"), ("0.0000160", "2.79527e-3"),
            ("0.0000159", "2.83095e-3"), ("0.0000158", "6.97516e-3")]
CP_TABLE = [("0.0001600", "6.14384e-3"), ("0.0001400", "6.14369e-3"),
            ("0.0001200", "6.14353e-3"), ("0.0001063", "6.20670e-3"),
            ("0.0001061", "6.40600e-3"), ("0.0001060", "6.67779e-3"),
            ("0.0001050", "6.33687e-1")]


@pytest.mark.parametrize("eta,printed", SD_TABLE)
def test_R_reproduces_revers_saouter_demichel_table(eta, printed):
    p = dataclasses.replace(st.SAOUTER_DEMICHEL, eta=eta)
    assert _contains_decimal(st.revers_R(p)["R"], printed)


@pytest.mark.parametrize("eta,printed", CP_TABLE)
def test_R_reproduces_revers_chao_plymen_table(eta, printed):
    p = dataclasses.replace(st.CHAO_PLYMEN, eta=eta)
    assert _contains_decimal(st.revers_R(p)["R"], printed)


def test_revers_row_labelled_1_55e_5_is_the_value_at_1_56e_5():
    """Observation: the table's last row (eta = 0.0000155, R = 5.15554e1) is
    reproduced at eta = 0.0000156; at 0.0000155 the same formula gives 5473.12.
    Both rows are negative lower bounds, so the paper's conclusion is unaffected."""
    at_156 = st.revers_R(dataclasses.replace(st.SAOUTER_DEMICHEL, eta="0.0000156"))["R"]
    at_155 = st.revers_R(dataclasses.replace(st.SAOUTER_DEMICHEL, eta="0.0000155"))["R"]
    assert _contains_decimal(at_156, "5.15554e1")
    assert abs(at_155 - arb("5473.1245")) < arb("1e-3")


def test_hypotheses_hold_at_both_parameter_sets():
    for p in (st.CHAO_PLYMEN, st.SAOUTER_DEMICHEL):
        assert all(st.check_hypotheses(p).values())


def test_hypothesis_check_can_fail():
    bad = dataclasses.replace(st.SAOUTER_DEMICHEL, T="7e7")  # T > A
    assert not st.check_hypotheses(bad)["2 pi e < T <= A"]


def test_float_margin_from_revers_sum():
    """MISSION (c): -1 - S* - R = 1.2787e-4 at eta = 2.28e-5 (before Delta S1)."""
    lb = st.lower_bound_I(arb(st.REVERS_S_STAR["saouter_demichel"]), st.SAOUTER_DEMICHEL)
    assert abs(lb - arb("1.27874e-4")) < arb("1e-9")


def test_planted_fault_dropping_R4_moves_the_bound():
    full = st.revers_R(st.SAOUTER_DEMICHEL)
    dropped = full["R"] - full["R4"]
    assert abs(full["R"] - dropped - arb("3.2021e-5")) < arb("1e-9")


@pytest.fixture(scope="module")
def low_zeros():
    g, _ = zl.arb_zeros(1, 120, batch=120)
    return g


def test_cutoffs_count_exactly_the_intended_zeros():
    """Revers's printed T are truncations: one zero short; ours count exactly n."""
    for key, p in (("chao_plymen", st.CHAO_PLYMEN), ("saouter_demichel", st.SAOUTER_DEMICHEL)):
        assert zl.count_below(p.T) == st.N_ZEROS[key]
        assert zl.count_below(st.REVERS_PRINTED_T[key]) == st.N_ZEROS[key] - 1


def test_zero_count_matches_ground_truth():
    assert zl.count_below("100") == 29
    assert zl.count_below("1000") == 649


def test_zeros_ordered_and_first_known(low_zeros):
    assert zl.check_ordered(low_zeros)
    assert abs(low_zeros[0] - arb("14.134725141734694")) < arb("1e-15")
    assert abs(low_zeros[2] - arb("25.010857580145689")) < arb("1e-15")


def test_sum_agrees_with_mpmath_float_route(low_zeros):
    """The ball sum over 120 zeros agrees with an mpmath float sum over zetazero."""
    import mpmath

    w, al = "727.952018", "1.34e11"
    ball = st.lehman_sum(low_zeros, w, al)
    with mpmath.workdps(40):
        W, AL = mpmath.mpf(w), mpmath.mpf(al)
        s = mpmath.mpf(0)
        for n in range(1, 121):
            g = mpmath.zetazero(n).imag
            rho = mpmath.mpc(0.5, g)
            s += mpmath.re(mpmath.exp(1j * g * W) * (1 / rho + 1 / (W * rho**2))
                           * mpmath.exp(-g * g / (2 * AL)))
        s *= 2
    assert abs(ball - arb(mpmath.nstr(s, 35))) < arb("1e-25")


def test_planted_fault_perturbing_one_zero_moves_the_ball(low_zeros):
    """A 1e-6 shift in gamma_100 moves the sum by ~ |ds/dgamma| 1e-6 and leaves the ball."""
    w, al = "727.952018", "1.34e11"
    ball = st.lehman_sum(low_zeros, w, al)
    bad = list(low_zeros)
    bad[99] = bad[99] + arb("1e-6")
    moved = st.lehman_sum(bad, w, al)
    shift = abs(moved - ball)
    assert not bool(abs(moved - ball) < 10 * (ball.rad() + moved.rad()))
    bound = arb("1508.3") / low_zeros[99] * arb("1e-6")  # [Rev25] RieleS1 bound
    assert bool(shift <= bound)
    assert bool(shift > bound / 1000)


def test_second_order_term_matters(low_zeros):
    w, al = "727.952018", "1.34e11"
    a = st.lehman_sum(low_zeros, w, al)
    b = st.lehman_sum(low_zeros, w, al, second_order=False)
    assert bool(abs(a - b) > arb("1e-6"))
