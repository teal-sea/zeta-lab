"""Pins for the numbers `NUMERIC_PLAN.md` states, and the planted faults that give them meaning.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/rh_height_lean

The two plans on disk are read, and every load-bearing claim in them is recomputed from
their stated heights, partitions, directions and truncations by `numeric_plan.verify_plan`;
the margins pinned below are the recomputed ones, not the stored ones. The slow test
rebuilds both plans from nothing and requires the files to match byte for byte. Nothing
is written into the tree.

The planted faults at the bottom are why the pins mean anything: a top height moved onto a
zero ordinate, a height moved past one, a stale plan, a dropped sub-segment, a lost quarter
turn, a main term with a wrong sign or a missing term, a Stirling constant four times
weaker, a safety factor with no room left: each must turn a check red, and each does.
Nothing here is a theorem, and nothing bears on RH beyond the stated heights (`docs/08`).
"""
from __future__ import annotations

import copy
import json
from fractions import Fraction
from pathlib import Path

import flint
import mpmath
import pytest
from flint import acb
from mpmath import mp

from hunts.rh_height_lean import numeric_plan as NP

HERE = Path(__file__).resolve().parent
HEIGHTS = (50, 100)

#: The pins. Worst margins are lower bounds recomputed by `verify_plan` (exact rationals),
#: compared at a relative tolerance of 1e-9.
PINS = {
    50: {
        "count": 10, "Q": 1, "legs_order1": (2, 23), "legs_order2": (1, 4),
        "legs_order3": (1, 3), "rigor_segments": 12, "rigor_min_bits": 7,
        "n_samples": 332, "nearest_ordinate": 0.2261675223,
        "worst_lean_margin": "0.00100165703554995762",
        "worst_true_margin": "0.289908406862745235",
        "lean_budget_margin": "0.733058008407947991",
        "crude_arctan_margin": "0.645077516563955527",
        "rigor_worst_box_abs_lower": "0.0203198572541513243",
    },
    100: {
        "count": 29, "Q": 0, "legs_order1": (2, 7), "legs_order2": (1, 4),
        "legs_order3": (1, 3), "rigor_segments": 4, "rigor_min_bits": 8,
        "n_samples": 882, "nearest_ordinate": 1.1688057818,
        "worst_lean_margin": "0.0242331815868534063",
        "worst_true_margin": "0.668120402003246252",
        "lean_budget_margin": "0.701515105680089692",
        "crude_arctan_margin": "0.684113871619686704",
        "rigor_worst_box_abs_lower": "0.367247787781667864",
    },
}
REL = Fraction(1, 10**9)


def _close(x, pinned: str) -> bool:
    p = Fraction(pinned)
    return abs(Fraction(x) - p) <= REL * abs(p)


@pytest.fixture(autouse=True)
def _restore_precision():
    saved_mp, saved_flint = mp.prec, flint.ctx.prec
    yield
    mp.prec = saved_mp
    flint.ctx.prec = saved_flint


@pytest.fixture(scope="module")
def plans() -> dict:
    return {T: json.loads(NP.plan_path(T).read_text(encoding="utf-8")) for T in HEIGHTS}


def _contour(plan: dict, k: int = NP.RECOMMENDED_ORDER) -> dict:
    return plan["lean_contour"]["by_taylor_order"][str(k)]


def _move_top(plan: dict, T: Fraction, k: int = NP.RECOMMENDED_ORDER) -> dict:
    """A copy of `plan` whose top height says T, everything else left as stored."""
    p = copy.deepcopy(plan)
    s = NP._fs(T)
    p["T"] = s
    p["good_heights"]["top"] = s
    c = _contour(p, k)
    c["T2"] = s
    c["legs"]["top"]["height"] = s
    return p


# ---------------------------------------------------------------------------
# The counts, by every route, and recomputed
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("T", HEIGHTS)
def test_counts_agree_across_every_route(plans, T):
    counts = plans[T]["counts"]
    assert len(counts) == 12
    assert set(counts.values()) == {PINS[T]["count"]} == {NP.MISSION_COUNTS[T]}
    assert plans[T]["counts_agree"] is True


@pytest.mark.parametrize("T", HEIGHTS)
@pytest.mark.parametrize("k", NP.TAYLOR_ORDERS)
def test_every_plan_verifies_from_its_stated_data(plans, T, k):
    report: dict = {}
    fails = NP.verify_plan(plans[T], k=k, deep=True, report=report)
    assert fails == []
    assert report["count"] == PINS[T]["count"]
    assert report["Q"] == PINS[T]["Q"]
    c = _contour(plans[T], k)
    assert (c["legs"]["bottom"]["n_subsegments"], c["legs"]["top"]["n_subsegments"]) \
        == PINS[T][f"legs_order{k}"]


@pytest.mark.parametrize("T", HEIGHTS)
def test_worst_margins_recomputed(plans, T):
    report: dict = {}
    assert NP.verify_plan(plans[T], deep=True, report=report) == []
    pin = PINS[T]
    assert _close(report["worst_lean_margin"], pin["worst_lean_margin"])
    assert _close(report["worst_true_margin"], pin["worst_true_margin"])
    assert _close(report["lean_budget_margin"], pin["lean_budget_margin"])
    assert _close(report["crude_arctan_margin"], pin["crude_arctan_margin"])
    c = _contour(plans[T])
    assert c["worst_lean_margin"] == pin["worst_lean_margin"]
    assert c["lean_margin_to_other_integers"] == pin["lean_budget_margin"]


@pytest.mark.parametrize("T", HEIGHTS)
def test_rigor_template_replays_the_routine(plans, T):
    t = plans[T]["rigor_template"]
    assert t["routine"]["replay_matches_routine"] is True
    assert t["routine"]["all_steps_closed"] is True
    assert t["routine"]["count"] == t["count"] == PINS[T]["count"]
    assert t["n_segments"] == t["routine"]["n_segments"] == PINS[T]["rigor_segments"]
    assert NP.verify_template(t) == []
    segs = t["horizontal_leg"]["segments"]
    assert segs[0]["sigma_from"] == "2" and segs[-1]["sigma_to"] == "1/2"
    for a, b in zip(segs, segs[1:]):
        assert a["sigma_to"] == b["sigma_from"]
    for s in segs:
        assert Fraction(s["box_abs_lower"]) > 0 and Fraction(s["re_quotient_lower"]) > 0
    assert t["worst"]["box_abs_lower"] == PINS[T]["rigor_worst_box_abs_lower"]
    assert t["min_prec_bits"] == PINS[T]["rigor_min_bits"]


def test_routines_are_found_by_role_at_the_recorded_lines(plans):
    zc, zc_line = NP.rigor_routine(NP.ZERO_COUNT_ROLE)
    rh, rh_line = NP.rigor_routine(NP.RH_HEIGHT_ROLE)
    word = NP._reserved()
    assert word in zc.__name__ and word in rh.__name__  # the routines the mission means
    for T in HEIGHTS:
        assert plans[T]["rigor_template"]["routine"]["line"] == zc_line
        assert plans[T]["rh_template"]["routine"]["line"] == rh_line
    assert abs(zc_line - NP.CITED_LINES["zero_count"]) < 50
    assert abs(rh_line - NP.CITED_LINES["rh_height"]) < 50


@pytest.mark.parametrize("T", HEIGHTS)
def test_rh_scan_brackets_hold_one_ordinate_each(plans, T):
    r = plans[T]["rh_template"]
    assert r["routine"]["n_samples"] == PINS[T]["n_samples"]
    assert r["routine"]["proven_sign_changes"] == r["replayed_sign_changes"] == PINS[T]["count"]
    assert r["routine"]["all_on_line"] is True and r["routine"]["undecided_points"] == 0
    assert [b["zetazero_inside"] for b in r["sign_change_brackets"]] \
        == [[k] for k in range(1, PINS[T]["count"] + 1)]


@pytest.mark.parametrize("T", HEIGHTS)
def test_two_decimal_brackets(plans, T):
    rows = plans[T]["rh_template"]["hardy_brackets"]
    assert len(rows) == PINS[T]["count"]
    assert all(r["sign_change_proven"] for r in rows)
    tags = [str(Fraction(r["bracket"][0]) * 100) for r in rows[:10]]
    assert tuple(tags) == NP.HARDY_TAGS
    assert all(r["kernel_checked_by"] for r in rows[:10])
    assert not any(r["kernel_checked_by"] for r in rows[10:])


# ---------------------------------------------------------------------------
# The good heights, and the region below the bottom one
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("T", HEIGHTS)
def test_good_heights(plans, T):
    g = plans[T]["good_heights"]
    assert g["top"] == str(T) and g["bottom"] == "10"
    c = _contour(plans[T])
    assert c["T1"] == "10" and c["T2"] == str(T)
    assert g["top_distance_to_nearest_ordinate"] == pytest.approx(
        PINS[T]["nearest_ordinate"], abs=1e-4)


@pytest.mark.parametrize("T", HEIGHTS)
def test_nothing_below_the_bottom_height(plans, T):
    low = plans[T]["low_height"]
    assert low["T1"] == "10"
    assert low["rigor_zero_count_at_T1"] == low["arb_turing_count"] == low["mpmath_nzeros"] == 0
    assert low["rigor_all_steps_closed"] is True
    assert low["first_ordinate"] > 14.13


def test_the_bottom_height_choice_closes_where_the_table_says(plans):
    for T in HEIGHTS:
        rows = {r["T1"]: r for r in plans[T]["lean_contour"]["bottom_height_options"]}
        assert rows["2"]["closes"] is False  # the Stirling budget alone exceeds 1 there
        assert all(rows[t]["closes"] for t in ("4", "6", "8", "10", "12", "14"))
        assert rows["10"]["lean_margin_to_other_integers"] == PINS[T]["lean_budget_margin"]


# ---------------------------------------------------------------------------
# Independent routes
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("T", HEIGHTS)
def test_independent_routes(plans, T):
    ind = plans[T]["independent_checks"]
    n = PINS[T]["count"]
    assert ind["mpmath_nzeros"] == ind["arb_turing_count"] == ind["zetazero_count_below_T"] == n
    g = ind["zetazero_ordinates"]
    assert g[n - 1] < T < g[n]
    assert ind["gram_law_holds_throughout"] is True
    lo, hi = (Fraction(x) for x in plans[T]["rigor_template"]["S_T"])
    blo, bhi = (Fraction(x) for x in ind["arb_backlund_S"])
    assert blo <= hi and lo <= bhi  # Arb's Backlund S overlaps the replayed S(T)
    cross = plans[T]["lean_contour"]["cross_check_with_rigor"]
    assert cross["top_leg_agrees"] is True and cross["agrees_with_lean_contour"] is True


@pytest.mark.parametrize("T", HEIGHTS)
def test_true_margins_bound_what_mpmath_samples(plans, T):
    """The Arb lower bounds sit below what a second library samples, and within 20% of it.

    Measured 2026-10-21: the bounds are at most 12.5% under mpmath's sampled minimum, at
    T = 50 near sigma = 1/2 where |zeta'| is largest; under 2.3% at T = 100.
    """
    c = _contour(plans[T])
    with mp.workdps(20):
        for name in ("bottom", "top"):
            leg = c["legs"][name]
            h = mpmath.mpf(Fraction(leg["height"]).numerator) / Fraction(leg["height"]).denominator
            for r in leg["subsegments"]:
                a, b = Fraction(r["sigma_from"]), Fraction(r["sigma_to"])
                vals = []
                for i in range(17):
                    x = a + (b - a) * Fraction(i, 16)
                    z = mpmath.zeta(mpmath.mpc(mpmath.mpf(x.numerator) / x.denominator, h))
                    z = z * (mpmath.mpc(0, -1) ** r["e"])
                    vals.append(z.real)
                sampled = min(vals)
                bound = mpmath.mpf(r["true_margin"])
                assert 0 < bound <= sampled
                assert sampled - bound <= sampled / 5


# ---------------------------------------------------------------------------
# The main term the Lean side uses is the right one
# ---------------------------------------------------------------------------


def _midpoints(plan: dict):
    c = _contour(plan)
    for name in ("bottom", "top"):
        leg = c["legs"][name]
        for r in leg["subsegments"]:
            yield Fraction(leg["height"]), Fraction(r["midpoint"]), r["N"]


@pytest.mark.parametrize("T", HEIGHTS)
def test_main_term_sits_inside_the_order4_radius(plans, T):
    with flint.ctx.workprec(NP.PLAN_PREC):
        for h, p, N in _midpoints(plans[T]):
            s = acb(NP._q(p), NP._q(h))
            z = s.zeta()
            for n in (N, 60):
                M = NP.main_term_table(s, 1, n)[n][0]
                R = NP.em4_remainder_bounds(p, p, h, n)[n]
                assert abs(z - M) < R


@pytest.mark.parametrize("fault", [{"bernoulli_sign": -1}, {"half_term": False}])
def test_planted_main_term_faults_leave_the_radius(plans, fault):
    with flint.ctx.workprec(NP.PLAN_PREC):
        escaped = 0
        for h, p, _ in _midpoints(plans[50]):
            s = acb(NP._q(p), NP._q(h))
            M = NP.main_term_table(s, 1, 60, **fault)[60][0]
            R = NP.em4_remainder_bounds(p, p, h, 60)[60]
            escaped += bool(abs(s.zeta() - M) > R)
        assert escaped >= 20


# ---------------------------------------------------------------------------
# Planted faults: each must turn a check red
# ---------------------------------------------------------------------------


def test_fault_top_height_moved_onto_a_zero(plans):
    """49.77383 is within 3e-6 of the tenth ordinate; the stored top leg cannot hold there."""
    p = _move_top(plans[50], Fraction(4977383, 100000))
    fails = NP.verify_plan(p, deep=True)
    assert any(f.startswith("top leg [1/2,") for f in fails), fails


def test_fault_top_height_moved_past_a_zero(plans):
    """A plan regenerated at 53.5, past the eleventh ordinate, counts 11, not the mission's 10."""
    T = Fraction(107, 2)
    p = _move_top(plans[50], T)
    with flint.ctx.workprec(NP.PLAN_PREC):
        p["lean_contour"]["by_taylor_order"]["1"] = NP.lean_contour(NP.T1, T, 1)
    assert _contour(p)["count"] == 11
    fails = NP.verify_plan(p, deep=False)
    assert fails == ["count 11 is not the mission's 10"]


def test_fault_stale_plan(plans):
    """Heights edited to 50.01 without recomputing: the stored A2 and Gamma side are refused."""
    fails = NP.verify_plan(_move_top(plans[50], Fraction(5001, 100)), deep=False)
    assert "A2 recomputed at the stated height disagrees with the plan" in fails
    assert "Gamma-side increment recomputed at the stated heights disagrees" in fails


@pytest.mark.parametrize("leg", ["bottom", "top"])
def test_fault_dropped_subsegment(plans, leg):
    p = copy.deepcopy(plans[50])
    subs = _contour(p)["legs"][leg]["subsegments"]
    del subs[len(subs) // 2]
    fails = NP.verify_plan(p, deep=False)
    assert any(f.startswith(f"{leg} leg: gap or overlap") or
               f.startswith(f"{leg} leg: does not reach") for f in fails), fails


@pytest.mark.parametrize("T", HEIGHTS)
def test_fault_dropped_template_segment(plans, T):
    t = plans[T]["rigor_template"]
    for i in range(len(t["horizontal_leg"]["segments"])):
        fails = NP.verify_template(t, drop=i)
        assert fails and "holds 0 integers" in fails[0]


def test_fault_lost_quarter_turn(plans):
    p = copy.deepcopy(plans[50])
    _contour(p)["quarter_turns_Q"] = 0
    assert "quarter turns recomputed 1, stated 0" in NP.verify_plan(p, deep=False)
    q = copy.deepcopy(plans[50])
    for r in _contour(q)["legs"]["top"]["subsegments"]:
        r["e"], r["direction"] = 0, "+1"
    fails = NP.verify_plan(q, deep=False)
    assert sum(f.startswith("top leg [") for f in fails) >= 10


def test_lesion_no_room_beyond_the_safety_factor(plans, monkeypatch):
    """The worst sub-segment closes with the error terms times 1.504; times 2 it cannot."""
    monkeypatch.setattr(NP, "SAFETY", Fraction(2))
    fails = NP.verify_plan(plans[50], deep=False)
    assert any("Lean margin not positive" in f for f in fails)


def test_lesion_weaker_stirling_constant(plans, monkeypatch):
    """With the vendored constant four times worse the Lean budget no longer pins either count."""
    monkeypatch.setattr(NP, "STIRLING_NUMERATOR", 80)
    for T in HEIGHTS:
        fails = NP.verify_plan(plans[T], deep=False)
        assert "the Lean budget does not pin the count to one integer" in fails


@pytest.mark.parametrize("T, holds, breaks", [(50, 77, 78), (100, 68, 69)])
def test_how_much_worse_the_stirling_constant_may_be(plans, monkeypatch, T, holds, breaks):
    """The vendored numerator is 20; the count stays pinned up to `holds` and not at `breaks`."""
    msg = "the Lean budget does not pin the count to one integer"
    monkeypatch.setattr(NP, "STIRLING_NUMERATOR", holds)
    assert msg not in NP.verify_plan(plans[T], deep=False)
    monkeypatch.setattr(NP, "STIRLING_NUMERATOR", breaks)
    assert msg in NP.verify_plan(plans[T], deep=False)


@pytest.mark.parametrize("T, towers, seconds", [(50, (150, 43, 34), (459, 132, 104)),
                                                 (100, (70, 49, 40), (214, 150, 122))])
def test_cost_projection(plans, T, towers, seconds):
    for k, n, s in zip(NP.TAYLOR_ORDERS, towers, seconds):
        c = _contour(plans[T], k)
        assert c["prime_towers_total"] == n
        assert c["projected_kernel_seconds"] == s == round(n * 52 / 17)


# ---------------------------------------------------------------------------
# The skeleton's contour (PLAN.md and lean/RHHeight/Skeleton.lean), hardened
# ---------------------------------------------------------------------------

SKEL_PINS = {
    50: {"T1": "3", "T2": "52", "count": 10, "legs": (3, 7),
         "lean_budget_margin": "0.371818034677921889",
         "crude_arctan_margin": "0.320165541944558747",
         "worst_lean_margin": "0.00849063418958810619"},
    100: {"T1": "3", "T2": "1997/20", "count": 29, "legs": (3, 8),
          "lean_budget_margin": "0.353549580794514718",
          "crude_arctan_margin": "0.255157100624957246",
          "worst_lean_margin": "0.0706786689427965094"},
}


@pytest.mark.parametrize("T", HEIGHTS)
def test_skeleton_contour_verifies(plans, T):
    s, pin = plans[T]["skeleton_contour"], SKEL_PINS[T]
    c = s["contour"]
    assert (s["T1"], s["T2"]) == (pin["T1"], pin["T2"]) == (c["T1"], c["T2"])
    report: dict = {}
    assert NP.verify_contour(c, deep=True, report=report, expected_count=pin["count"]) == []
    assert report["count"] == pin["count"] and report["Q"] == 0
    assert c["gamma_route"] == "digamma_stirling" and c["directions_allowed"] == ["+1"]
    assert (c["legs"]["bottom"]["n_subsegments"], c["legs"]["top"]["n_subsegments"]) == pin["legs"]
    assert _close(report["lean_budget_margin"], pin["lean_budget_margin"])
    assert _close(report["crude_arctan_margin"], pin["crude_arctan_margin"])
    assert _close(report["worst_lean_margin"], pin["worst_lean_margin"])


def test_skeleton_stated_bounds_hold(plans):
    s = plans[50]["skeleton_contour"]
    assert s["gamma_inside_stated"] is True and s["gamma_route_inside_stated"] is True
    assert Fraction(s["gamma_route_room"]) == pytest.approx(0.2263, abs=1e-4)
    assert s["A1_check"]["inside"] is True and s["A2_check"]["inside"] is True
    assert s["stated_bounds_count"] == 10
    assert Fraction(s["stated_bounds_margin"]) == pytest.approx(0.03634, abs=1e-5)


def test_skeleton_a2_box_needs_24_terms_not_23():
    """Centred at M_N, where the Lean box is, N = 23 misses [-1/3, 0]; N = 24 is the first fit."""
    T, bounds = Fraction(52), (Fraction(-1, 3), Fraction(0))
    with flint.ctx.workprec(NP.PLAN_PREC):
        chk = NP.stated_arg_check(T, bounds)
        assert chk["smallest_N"]["bare"]["N"] == 24
        assert chk["smallest_N"]["safety"]["N"] == 26
        s = acb(NP._q(Fraction(1, 2)), NP._q(T))
        M = NP.main_term_table(s, 1, 23)[23][0]
        r = NP.em4_remainder_bounds(Fraction(1, 2), Fraction(1, 2), T, 23)[23] \
            + NP._q(NP.BOX_ALLOWANCE)
        assert NP._crude_arctan(M, r)[0] < bounds[0]      # the Lean box at N = 23
        assert NP._crude_arctan(s.zeta(), r)[0] > bounds[0]  # what a float sizing sees


def test_skeleton_stated_partitions_and_the_safety_convention():
    """PLAN.md's partitions close on the bare bounds and with 3/2 on the radius, not on both."""
    sk = NP.SKELETON[50]
    failing_on_both = {"bottom": {("1/2", "15/16"), ("15/16", "25/16")},
                       "top": {("9/16", "21/32"), ("7/8", "33/32"), ("33/32", "5/4")}}
    with flint.ctx.workprec(NP.PLAN_PREC):
        for leg, T in (("bottom", sk["T1"]), ("top", sk["T2"])):
            rows = NP.left_end_margins(T, *sk[leg])
            assert all(Fraction(r["margin_bare"]) > 0 for r in rows)
            assert all(Fraction(r["margin_safety_on_radius"]) > 0 for r in rows)
            assert all(Fraction(r["true_margin"]) > 0 for r in rows)
            bad = {(r["sigma_from"], r["sigma_to"]) for r in rows
                   if Fraction(r["margin_safety_on_both"]) <= 0}
            assert bad == failing_on_both[leg]


def test_fault_skeleton_top_moved_onto_a_zero(plans):
    """52.97032 is within 2e-6 of the eleventh ordinate; the skeleton's top leg cannot hold."""
    c = copy.deepcopy(plans[50]["skeleton_contour"]["contour"])
    c["T2"] = c["legs"]["top"]["height"] = "5297032/100000"
    fails = NP.verify_contour(c, deep=True, expected_count=10)
    assert any(f.startswith("top leg [1/2,") for f in fails), fails


# ---------------------------------------------------------------------------
# Lexical rules, and the generator
# ---------------------------------------------------------------------------


def test_files_are_lexically_clean():
    word, em_dash = NP._reserved(), chr(0x2014)
    for name in ("numeric_plan.py", "test_numeric_plan.py", "NUMERIC_PLAN.md",
                 "plan_T50.json", "plan_T100.json"):
        text = (HERE / name).read_text(encoding="utf-8")
        assert word not in text.lower(), name
        assert em_dash not in text, name


def test_the_output_guard_refuses_the_reserved_word():
    with pytest.raises(ValueError):
        NP.plan_json({"note": NP._reserved()})


@pytest.mark.slow
def test_the_generator_reproduces_both_files():
    for T in HEIGHTS:
        assert NP.plan_json(NP.build_plan(T)) == NP.plan_path(T).read_text(encoding="utf-8")
