"""Hunt #150 (rh_moonshot), mechanism probe_tower: the numbers NOTES.md states.

Fast tests re-derive the order-k template in exact rational arithmetic: the
reproduction of the paper at k = 6, the tower's direction, the walls with
their LP dual multipliers, the price of reaching 1/2.  Slow tests evaluate the
distinguishing step (the principal row's reciprocal identity) on the three
rivals with mpmath.  Nothing here writes into the tree.

The first test that could fail is
``test_tower_hypothesis_fails_sigma0_increases_to_one``: the mission asked
whether sigma_0(k) tends to 1/2 as the order k grows; in the template it
increases to 1.
"""

from __future__ import annotations

import os
import random
import sys
from fractions import Fraction as F

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import tower_template as T  # noqa: E402

PAPER = os.environ.get("ZETA_LAB_OPENAI_PAPER", T.PAPER_DEFAULT)


def _random_geometries(n, seed=150, denom=60):
    """Random rational admissible geometries: ell, b >= 0, M >= b, M + ell <= 1."""
    rng = random.Random(seed)
    out = []
    while len(out) < n:
        ell = F(rng.randint(0, denom), denom)
        M = F(rng.randint(0, denom), denom)
        b = F(rng.randint(0, denom), denom)
        if b <= M and M + ell <= 1:
            out.append((ell, M, b))
    return out


# ---------------------------------------------------------------------------
# the source
# ---------------------------------------------------------------------------


def test_citations_sit_on_their_lines():
    if not os.path.isfile(PAPER):
        pytest.skip("pinned paper.tex not present on this machine")
    sha_ok, missing = T.verify_citations(PAPER)
    assert sha_ok, "paper.tex does not have the pinned SHA-256"
    assert missing == [], missing
    assert len(T.CITATIONS) >= 40


# ---------------------------------------------------------------------------
# the template
# ---------------------------------------------------------------------------


def test_template_reproduces_the_paper_at_k6():
    # Part I (lines 190, 509-510, 3717)
    assert T.signal_shift(6, *T.PART_I) == F(-2, 3)
    assert T.low_exponent(6, *T.PART_I) == F(1, 4)
    assert T.target(6, *T.PART_I) == F(11, 12)
    # Part II (lines 191, 514-515, 6860-6864, 8570, 8641-8642)
    assert T.geometry(*T.PART_II) == (F(17, 48), F(23, 48), F(13, 16))
    assert T.signal_shift(6, *T.PART_II) == F(-11, 16)
    assert T.low_exponent(6, *T.PART_II) == F(3, 16)
    assert T.target(6, *T.PART_II) == F(7, 8)
    # the floor rows (lines 15734, 15847)
    assert T.floor_C0(6, *T.PART_II) == F(-1, 48)
    assert T.floor_exponent(6, *T.PART_II, T.FLOOR_BIN) == F(-7, 1200)
    # hunt #134's form 5/6 + (M - 2 ell)/12
    for g in _random_geometries(50):
        assert T.target(6, *g) == F(5, 6) + (g[1] - 2 * g[0]) / 12


def test_two_routes_for_the_signal_agree_for_every_order():
    for k in range(1, 41):
        for g in _random_geometries(25, seed=k):
            assert T.signal_shift_from_weight(k, *g) == T.signal_shift(k, *g)
            assert T.target(k, *g) == T.target_closed(k, *g)


def test_target_is_free_of_the_offset_b():
    """The Gram term counts k-th powers like the pole, so b cancels exactly."""
    for k in (2, 3, 6, 11):
        for ell, M, _ in _random_geometries(20, seed=k):
            vals = {T.target(k, ell, M, b) for b in (F(0), M / 3, M / 2, M)}
            assert len(vals) == 1


def test_line_15729_transcription_matches_line_15732():
    rng = random.Random(15729)
    for _ in range(200):
        delta = F(rng.randint(0, 100), 100)
        q = F(rng.randint(0, 50), 100)
        R = F(rng.randint(0, 100), 100)
        d = F(rng.randint(0, 120), 100)
        lhs = T.high_exponent(6, *T.PART_II, delta, q, R, d)
        assert lhs == T.high_exponent_paper_second_line(delta, q, R, d)


def test_floor_closed_form_matches_the_transcription():
    rng = random.Random(15847)
    for k in (2, 3, 4, 6, 9):
        for g in _random_geometries(20, seed=k):
            d0 = F(rng.randint(0, 20), 200)
            h = T.geometry(*g)[2]
            assert T.high_exponent(k, *g, d0, d0 / 2, 1, h) == T.floor_exponent(k, *g, d0)


def test_symbolic_identities_hold_for_symbolic_k():
    checks = T.symbolic_checks()
    assert all(checks.values()), checks


# ---------------------------------------------------------------------------
# the tower
# ---------------------------------------------------------------------------


def test_tower_hypothesis_fails_sigma0_increases_to_one():
    """The mission's hypothesis: sigma_0(k) -> 1/2 as the order k grows.

    In the template, for every admissible geometry, sigma_0(k + 1) - sigma_0(k)
    = (2 - (M - 2 ell)) / (2k(k + 1)) > 0, and 1 - sigma_0(k) <= 2/k, so the
    tower of growing degree goes to 1, and above 1/2 from k = 5 on.
    """
    for g in _random_geometries(200):
        m = g[1] - 2 * g[0]
        assert m <= 1
        for k in range(1, 65):
            inc = T.tower_increment(k, *g)
            assert inc == (2 - m) / (2 * k * (k + 1))
            assert inc > 0
        for k in (5, 10, 100, 10**4):
            s0 = T.target(k, *g)
            assert 1 - s0 <= F(2, k)
            assert s0 > F(1, 2)
        assert T.target(10**6, *g) > F(999997, 10**6)


def test_k1_endpoint_is_the_moebius_sum():
    """At the formal order k = 1 (no twist), the balanced geometry gives exactly
    1/2: the signal is Z^(s - 1/4) / L, the direct bound Z^(1/4) is square-root
    cancellation in the Moebius sum, i.e. Littlewood's RH-equivalent bound."""
    assert T.signal_shift(1, *T.PART_I) == F(-1, 4)
    assert T.low_exponent(1, *T.PART_I) == F(1, 4)
    assert T.target(1, *T.PART_I) == F(1, 2)


# ---------------------------------------------------------------------------
# the walls
# ---------------------------------------------------------------------------


def test_walls_match_their_closed_forms():
    for k in range(2, 41):
        assert T.wall(k)["sigma0"] == T.wall_dual_closed(k)
        assert T.wall(k, floor=0)["sigma0"] == T.wall_floor_closed(k, 0) == 1 - F(4, 5 * k)
        assert T.wall(k, floor=T.FLOOR_BIN)["sigma0"] == T.wall_floor_closed(k, T.FLOOR_BIN) == 1 - F(25, 32 * k)
        assert T.wall(k, corner=True)["sigma0"] == T.wall_corner_closed(k)
        assert T.wall(k, d0=True)["sigma0"] == 1 - F(4, 5 * k)
        assert T.target(k, *T.PART_I) == T.balanced_closed(k)
        # the floor corner sits at ell = 1/5, M = 4/5, b = 0 for every k
        assert T.wall(k, floor=0)["point"] == (F(1, 5), F(4, 5), F(0))


def test_floor_wall_dual_multipliers():
    """The identity (M - 2 ell) - m* = y1 (-floor) + y2 (1 - M - ell) + y3 b with
    y >= 0 proves the floor wall for every geometry; y3 >= 0 needs k >= 2."""
    for k in range(2, 30):
        for d0 in (F(0), F(1, 50), F(1, 10)):
            y1, y2, y3, mstar = T.floor_dual_multipliers(k, d0)
            assert min(y1, y2, y3) >= 0
            assert T.wall(k, floor=d0)["m"] == mstar
            for ell, M, b in _random_geometries(30, seed=k):
                floor = T.floor_exponent(k, ell, M, b, d0)
                rhs = y1 * (-floor) + y2 * (1 - M - ell) + y3 * b
                assert (M - 2 * ell) - mstar == rhs
    assert T.floor_dual_multipliers(1, 0)[2] < 0  # the k = 1 endpoint is outside it


def test_best_order_is_the_smallest_and_stops_at_three_fifths():
    floors = {k: T.wall_floor_closed(k, 0) for k in range(2, 201)}
    assert min(floors.values()) == F(3, 5) == floors[2]
    assert all(floors[k] < floors[k + 1] for k in range(2, 200))
    assert all(v > F(1, 2) for v in floors.values())
    # the dual-length wall alone: 1/2 exactly at k = 4, above 1/2 from k = 5
    assert T.wall_dual_closed(4) == F(1, 2)
    assert all(T.wall_dual_closed(k) > F(1, 2) for k in range(5, 201))
    # the walls of hunt #136's probe lane at k = 2 and k = 6, recomputed here
    assert (T.balanced_closed(2), T.wall_corner_closed(2), T.wall_floor_closed(2, T.FLOOR_BIN)) == (
        F(3, 4), F(5, 8), F(39, 64))
    assert (T.balanced_closed(6), T.wall_corner_closed(6), T.wall_floor_closed(6, T.FLOOR_BIN),
            T.wall_floor_closed(6, 0)) == (F(11, 12), F(7, 8), F(167, 192), F(13, 15))


def test_price_of_one_half():
    for k in range(2, 13):
        for mode in T.PRICE_MODES:
            lp = T.price_of_one_half(k, mode)
            closed = T.price_closed(k, mode)
            if closed is None:
                assert lp is None
            else:
                assert lp[0] == closed
    assert T.price_of_one_half(2, "common")[0] == F(1, 8)
    assert T.price_of_one_half(2, "floor") == (F(1, 6), (F(1, 3), F(2, 3), F(0), F(1, 6)))
    assert T.price_of_one_half(2, "dual")[0] == F(1, 2)
    assert T.price_of_one_half(6, "common")[0] == F(11, 8)
    assert all(T.price_of_one_half(k, "floor") is None for k in range(5, 13))
    # with the direct bound's loss condition in either reading
    assert T.price_of_one_half(2, "total")[0] == F(2, 7)
    assert T.price_of_one_half(2, "per_summand")[0] == F(1, 2)
    assert T.price_of_one_half(6, "total")[0] == F(22, 7)
    assert T.price_of_one_half(6, "per_summand")[0] == F(9, 2)
    for mode in ("common", "total", "per_summand", "dual"):
        prices = [T.price_closed(k, mode) for k in range(2, 60)]
        assert all(a < b for a, b in zip(prices, prices[1:])), mode


def test_relaxed_walls_price_the_generic_doors():
    """The floor rows gaining Z^g, the dual length growing by Z^e, and the direct
    bound's loss condition, which is tight at the same corner."""
    for k in (2, 3, 6, 12):
        for g in (F(0), F(1, 6), F(1, 2), F(1), F(3, 2)):
            assert T.wall(k, floor=0, floor_relax=g)["sigma0"] == T.wall_floor_gain_closed(k, g)
        for g in (F(0), F(1, 6), F(1), F(2), F(5)):
            got = T.wall(k, floor=0, d0=True, floor_relax=g, loss_relax=g)["sigma0"]
            assert got == T.wall_floor_and_loss_gain_closed(k, g)
        for e in (F(0), F(1, 4), F(1), F(11, 2)):
            assert T.wall(k, floor=0, dual_relax=e)["sigma0"] == T.wall_dual_gain_closed(k, e)
        # with the loss condition in either reading, a floor gain alone moves nothing
        for g in (F(1, 6), F(1), F(10)):
            assert T.wall(k, floor=0, d0=True, floor_relax=g)["sigma0"] == T.wall_floor_closed(k, 0)
            assert T.wall(k, floor=0, corner=True, floor_relax=g)["sigma0"] == T.wall_corner_closed(k)
    # without the loss condition, k = 2 would reach 1/2 at a floor gain of Z^(1/6)
    assert T.wall_floor_gain_closed(2, F(1, 6)) == F(1, 2)
    # at k = 6 nothing in the floor and loss doors gets below the dual-length wall 2/3
    assert T.wall(6, floor=0, d0=True, floor_relax=10, loss_relax=10)["sigma0"] == F(2, 3)
    assert T.wall_floor_and_loss_gain_closed(6, F(1, 6)) == F(17, 20)
    # at k = 6 the dual length alone would have to grow by Z^(11/2)
    assert T.wall_dual_gain_closed(6, F(11, 2)) == F(1, 2)


def test_region_two_holds_the_pole_exactly_up_to_k6():
    assert [k for k in range(1, 30) if T.region_two_contains_pole(k)] == [1, 2, 3, 4, 5, 6]


def test_cubic_twist_signal_cannot_fire():
    """S1 (cubic theta, cubic twist, k = 3): hunt #136's referee computed the
    principal row as L(x, eta)/L(2x, eta^2).  Its poles sit at x = rho/2 with
    real part at most 1/2, below every k = 3 wall, so no zero can be excluded."""
    largest_pole_real_part = F(1, 2)  # rho/2 with Re rho <= 1
    for w in (T.balanced_closed(3), T.wall_corner_closed(3), T.wall_floor_closed(3, 0)):
        assert largest_pole_real_part < w


def test_wa_shift_keeps_its_zeros_out_of_reach():
    """Coefficients of size n^(1/4) lift the template target by 1/4, so W_a's
    zeros at 1/2 + 1/4 are inside reach only if sigma_0 < 1/2."""
    assert T.wa_shifted_floor(2) == F(17, 20)
    assert all(T.wa_shifted_floor(k) > F(3, 4) for k in range(2, 100))
    # W_a's pass is uniform: on Re s >= 3/4 with the primes up to 100 deleted,
    # |H_W - 1| <= exp(c * sum_{n > 100} n^(-3/2)) - 1 with the sum at most 2/sqrt(100)
    import math

    c = 1 / ((1 - 100 ** -0.5) * (1 - 100 ** -1.0))
    assert math.expm1(c * 2 / math.sqrt(100)) < 0.26
    # the principal correction's region of absolute convergence shifts the same way
    assert T.principal_correction_abscissa() == F(2, 3)
    assert T.principal_correction_abscissa(F(1, 4)) == F(11, 12)
    # and the shift is the same for the target: sigma_0 + a against zeros at 1/2 + a
    for g in _random_geometries(20):
        for k in (2, 6):
            assert T.target(k, *g) + F(1, 4) - (F(1, 2) + F(1, 4)) == T.target(k, *g) - F(1, 2)


# ---------------------------------------------------------------------------
# planted faults
# ---------------------------------------------------------------------------


def test_planted_fault_a_wrong_k_reading_passes_k6_but_reverses_the_tower():
    """A pole read as k/36 equals 1/6 at k = 6, so the k = 6 reproduction cannot
    pin the k-dependence; the tower's direction rests on the reading
    'pole = 1/(character order)', which is inferred from lines 3758 and 4045."""
    wrong = lambda k: F(k, 36)  # noqa: E731
    assert T.target(6, *T.PART_I, reading=wrong) == F(11, 12)
    assert T.target(6, *T.PART_II, reading=wrong) == F(7, 8)
    assert T.target(7, *T.PART_II, reading=wrong) < T.target(6, *T.PART_II, reading=wrong)
    assert T.target(7, *T.PART_II) > T.target(6, *T.PART_II)


def test_planted_fault_dropping_the_floor_rows_moves_the_k2_wall():
    assert T.wall(2)["sigma0"] == 0
    assert T.wall(2, floor=0)["sigma0"] == F(3, 5)


def test_planted_fault_a_held_gram_term_makes_b_matter():
    def target_held(k, ell, M, b):
        lx, _, h = T.geometry(ell, M, b)
        return lx / 2 + F(b) / 12 - (lx / 2 - 1 + h / F(k))

    vals = {target_held(3, F(1, 10), F(4, 5), b) for b in (F(0), F(1, 5), F(2, 5))}
    assert len(vals) > 1


def test_planted_fault_wrong_dual_multiplier_breaks_the_identity():
    y1, y2, y3, mstar = T.floor_dual_multipliers(2, 0)
    ell, M, b = F(1, 10), F(3, 5), F(1, 7)
    floor = T.floor_exponent(2, ell, M, b, 0)
    good = y1 * (-floor) + y2 * (1 - M - ell) + y3 * b
    bad = y1 * (-floor) + (y2 + F(1, 100)) * (1 - M - ell) + y3 * b
    assert (M - 2 * ell) - mstar == good
    assert (M - 2 * ell) - mstar != bad


# ---------------------------------------------------------------------------
# the rival gate (mpmath, measured)
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_dh_step_fails_at_its_offline_zero():
    r = T.dh_at_offline_zero(dps=30)
    assert r["abs_dh_direct"] < 1e-30 and r["abs_dh_combo"] < 1e-30
    assert r["abs_L_chi"] > 0.5 and r["abs_L_chibar"] > 0.5
    assert 0.7 < r["abs_probe_reciprocal"] < 0.9  # finite: no pole where the criterion needs one
    assert r["abs_H"] < 1e-30
    assert abs(r["abs_H_minus_1"] - 1) < 1e-20
    assert abs(r["abs_H_closed_minus_1"] - 1) < 1e-20


@pytest.mark.slow
def test_dh_moebius_sum_is_the_linear_combination_not_the_reciprocal():
    r = T.dh_moebius_sum_check(n_max=20000, s_real=2.0)
    assert r["gap_direct_vs_linear"] < r["tail_bound"]
    assert r["gap_direct_vs_reciprocal"] > 100 * r["tail_bound"]
    assert r["zeta_control_gap"] < r["tail_bound"]
    assert abs(r["imag_linear"]) < 1e-15


@pytest.mark.slow
def test_dh_contraction_fails_on_the_seven_eighths_line_without_deletion():
    r = T.dh_contraction_scan(0.875, 80.0, 90.0, 0.5, delete_upto=1, dps=12)
    assert r["max_abs_H_minus_1"] > 1.5
    assert r["points_over_half"] >= 10


@pytest.mark.slow
def test_epstein_step_fails_at_its_offline_zero():
    r = T.epstein_at_offline_zero(dps=25, p_max=3000)
    assert r["abs_Z116"] < 1e-15
    assert r["zeta_K_two_route_gap"] < 1e-15
    assert r["abs_zeta_K_lattice"] > 0.1 and r["abs_L_psi"] > 0.05
    assert r["abs_probe_reciprocal"] < 100
    assert r["abs_H_E"] < 1e-13
    assert abs(r["abs_H_E_minus_1"] - 1) < 1e-12


@pytest.mark.slow
def test_wa_passes_the_step_at_its_offline_zero():
    r = T.wa_at_offline_zero(deletions=(10, 100), p_max=20000, dps=20)
    assert r["abs_W_a"] < 1e-15
    assert r["deletions"]["100"]["abs_H_minus_1"] < 0.5
    assert r["deletions"]["100"]["abs_H"] > 0.5


@pytest.mark.slow
def test_wa_moebius_sum_matches_H_over_W():
    r = T.wa_moebius_sum_check(n_max=20000, s_real=3.0)
    assert r["gap"] < 1e-6


# ---------------------------------------------------------------------------
# the committed report and the prose agree with the code
# ---------------------------------------------------------------------------


def test_results_json_matches_the_code_and_the_notes():
    import json

    path = os.path.join(HERE, "results_probe_tower.json")
    if not os.path.isfile(path):
        pytest.skip("results_probe_tower.json not present")
    with open(path, encoding="ascii") as fh:
        r = json.load(fh)
    assert r["exact"] == json.loads(json.dumps(T.exact_tables()))
    assert all(r["symbolic"].values())
    assert r["citations"] == {"sha256_ok": True, "checked": len(T.CITATIONS), "missing": []}
    with open(os.path.join(HERE, "NOTES.md"), encoding="utf-8") as fh:
        notes = fh.read()
    quoted = {
        f"{r['dh_zero']['abs_probe_reciprocal']:.5f}": "0.77832",
        f"{r['dh_zero']['abs_L_chi']:.5f}": "0.70220",
        f"{r['dh_scan_7_8_deleted_upto_1']['max_abs_H_minus_1']:.2f}": "3.68",
        f"{r['dh_scan_7_8_deleted_upto_3']['max_abs_H_minus_1']:.3f}": "0.276",
        f"{r['dh_scan_7_8_deleted_upto_100']['max_abs_H_minus_1']:.3f}": "0.018",
        f"{r['epstein_zero']['abs_probe_reciprocal']:.5f}": "0.70349",
        f"{r['wa_zero']['deletions']['1']['abs_H_minus_1']:.3f}": "0.236",
        f"{r['wa_zero']['deletions']['10']['abs_H_minus_1']:.4f}": "0.0017",
        f"{r['wa_zero']['deletions']['100']['abs_H_minus_1']:.4f}": "0.0024",
    }
    for computed, written in quoted.items():
        assert computed == written, (computed, written)
        assert written in notes, written
    assert r["dh_scan_7_8_deleted_upto_1"]["points_over_half"] == 572
    assert "572 points" in notes


# ---------------------------------------------------------------------------
# lexical rules for this directory
# ---------------------------------------------------------------------------


def test_files_keep_the_lexical_rules():
    stem = "cert" + "if"
    for name in os.listdir(HERE):
        if not name.endswith((".py", ".md", ".json")):
            continue
        with open(os.path.join(HERE, name), encoding="utf-8") as fh:
            text = fh.read()
        assert stem not in text.lower(), name
        assert chr(0x2014) not in text, name
        assert text.isascii(), name
