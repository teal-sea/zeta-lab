"""Pins for the numbers hunt #119's `RESULTS.md` section 8 states (resumed 2026-10-26).

Run from the repository root:

    .venv/bin/python -m pytest -q -n0 hunts/lambda_dh_exact              # both tiers
    .venv/bin/python -m pytest -q -n0 -m "not slow" hunts/lambda_dh_exact

Three kinds of test, each naming the artifact it reads:

1. **Artifact pins.** Every number section 8 calls decided or measured,
   read back from the committed JSON it came from, and every prediction and
   kill-condition verdict of section 8.7 and 8.8 re-derived from those numbers
   (not from the prose).
2. **Recomputations.** One low-screen zero decided again on both backends
   (seconds), the |t| <= 8 rectangle of the kill-condition-2 count and a
   five-unit window around the zero at gamma = 2442.53 recomputed on Arb
   (seconds), and, in the slow tier, the whole lowest left-edge shard of that
   count compared with its recorded arg-variation ball (about 2 minutes).
3. **Planted faults.** Each comparison goes through a checker in this file,
   and each checker is also fed a faulted input that it must reject: a zero
   shifted past its interval, a count off by one, a landing nudged above the
   floor. Setting ``LDH_PLANT_FAULT=1`` injects the same faults into the
   comparisons themselves, so the recomputation tests go red; that run is
   recorded in `RUNS.md` (Run 13).
4. **Review corrections** (section 12, 2026-10-26): every decided interval the
   record quotes contains its artifact's exact interval; the Arb-versus-iv
   cross-check compares exact endpoints; the Euler-Maclaurin constant is
   covered by the rounding fudge; the registered text is as registered; and
   two known limits of the census evaluation are shown, with their absence
   from the recorded runs.

Grades are those of `RESULTS.md`: the two counts are decided, the landings
are measured. Nothing here bears on RH (`docs/08`).
"""
from __future__ import annotations

import importlib.util
import json
import math
import os
import re
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

PLANT = os.environ.get("LDH_PLANT_FAULT") == "1"
FLOOR_MEASURED = 0.05765184034869543      # gamma = 240.4046 landing, measured
FLOOR_DECIDED = Fraction(36, 625)          # Hunt #61, decided
ODE_BAND = 0.0004                          # ODE vs Xi-plane, 0.04 percent


def load(name: str) -> dict:
    with open(HERE / name) as fh:
        return json.load(fh)


def _theory():
    spec = importlib.util.spec_from_file_location("ldh_theory", HERE / "theory.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------------------
# checkers (each one is also fed a planted fault below)
# ---------------------------------------------------------------------------

def interval_inside(inner: tuple[Fraction, Fraction], outer: tuple[Fraction, Fraction]) -> bool:
    return outer[0] <= inner[0] and inner[1] <= outer[1]


def count_matches(recomputed: int | None, recorded: int) -> bool:
    return recomputed is not None and recomputed == recorded


def balls_intersect(a_lo: float, a_hi: float, b_lo: float, b_hi: float) -> bool:
    return a_lo <= b_hi and b_lo <= a_hi


def none_beats_floor(landings: list[float]) -> bool:
    return all(t <= FLOOR_MEASURED * (1 + ODE_BAND) for t in landings)


def _maybe_plant_count(n):
    return n + 1 if (PLANT and n is not None) else n


def floor_dp(x: Fraction, d: int) -> str:
    """x rounded down to d decimals, as a string (the outward lower end)."""
    return _dp(math.floor(x * 10**d), d)


def ceil_dp(x: Fraction, d: int) -> str:
    """x rounded up to d decimals, as a string (the outward upper end)."""
    return _dp(math.ceil(x * 10**d), d)


def _dp(n: int, d: int) -> str:
    """The integer n / 10^d written exactly with d decimals (no float)."""
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n // 10**d}.{n % 10**d:0{d}d}"


# ---------------------------------------------------------------------------
# 1a. step 1: the height-1e6 zero (decide_deep_zero.json)
# ---------------------------------------------------------------------------

def test_deep_zero_decided_count_one_on_both_backends():
    """decide_deep_zero.json: count 1 on python-flint and on mpmath.iv."""
    d = load("decide_deep_zero.json")
    for name in ("python-flint", "mpmath.iv"):
        r = d["routes"][name]
        assert r["status"] == "decided" and r["count"] == 1, name
        assert r["prec_bits"] == 128
        assert r["winding_lo"] <= 1 <= r["winding_hi"] and r["winding_hi"] - r["winding_lo"] < 1e-12
        assert r["worst_clearance_over_tube"] > 1
    assert round(d["routes"]["python-flint"]["worst_clearance_over_tube"]) == 1420
    assert round(d["routes"]["mpmath.iv"]["worst_clearance_over_tube"]) == 174151
    assert d["routes"]["mpmath.iv"]["N"] == 199153 and d["routes"]["mpmath.iv"]["p"] == 293


def test_deep_zero_depth_interval():
    """decide_deep_zero.json: y0 in [0.3583118516, 0.3583118666] (outward), right of the line."""
    d = load("decide_deep_zero.json")
    lo, hi = (Fraction(x) for x in d["depth_y0_enclosure"])
    assert lo == Fraction(393968047217, 2**40) and hi == Fraction(393968063601, 2**40)
    assert interval_inside((lo, hi), (Fraction("0.35831185"), Fraction("0.35831187")))
    # quoted rounded outward (2026-10-26 in review; to nearest, the upper end was 0.3583118665 < hi)
    assert floor_dp(lo, 10) == "0.3583118516" and ceil_dp(hi, 10) == "0.3583118666"
    assert interval_inside((lo, hi), (Fraction("0.3583118516"), Fraction("0.3583118666")))
    assert d["rectangle_right_of_half_line"] is True and d["float_datum_inside"] is True
    sl, sh = (Fraction(x) for x in d["rectangle"]["sigma"])
    assert sl > Fraction(1, 2) and sh - sl == Fraction(2, 2**27)


def _shift_box(box: dict, part: str = "re", widths: int = 2) -> dict:
    """The box moved along one part by `widths` times its own width there."""
    lo, hi = box[part]
    w = hi - lo
    out = dict(box)
    out[part] = (lo + widths * w, hi + widths * w)
    return out


def test_deep_zero_planted_faults_and_cross_check():
    """decide_deep_zero.json: the faults decide 0; Arb and iv enclosures intersect on exact endpoints.

    `cross_check_exact` (Run 22, 2026-10-26 in review) stores every endpoint as an
    exact rational; the intersection is recomputed here from those endpoints with
    no slack. The recorded float-midpoint `cross_check` could not fail and is
    no longer read. Planted: the iv enclosure moved by twice its width.
    """
    import decide_deep_zero as dd
    d = load("decide_deep_zero.json")
    f = d["faults"]
    assert f["python-flint"]["kappa_plus_1e-3"]["count"] == 0
    assert f["python-flint"]["rectangle_shifted_4_half_widths"]["count"] == 0
    assert f["mpmath.iv"]["rectangle_shifted_4_half_widths"]["count"] == 0
    xs = d["cross_check_exact"]
    assert [x["s"] for x in xs] == [x["s"] for x in d["cross_check"]] and len(xs) == 3
    run = d["cross_check_exact_run"]
    assert run["all_intersect"] is True and run["iv_N"] == 199153 and run["iv_p"] == 293
    for x in xs:
        a, b = dd.box_from_json(x["arb"]), dd.box_from_json(x["iv"])
        if PLANT:
            b = _shift_box(b)                     # planted: one enclosure moved past itself
        assert dd.enclosures_intersect(a, b) and x["intersect"] is True
        for k in ("re", "im"):                    # the stored widths are the exact ones
            assert math.isclose(x["parts"][k]["width_iv"], float(b[k][1] - b[k][0]), rel_tol=1e-12)
            assert x["parts"][k]["midpoint_gap"] < 3e-33 < x["parts"][k]["width_iv"]


def test_planted_fault_cross_check_shift_is_caught():
    """enclosures_intersect rejects the recorded iv box moved by twice its width, in either part."""
    import decide_deep_zero as dd
    x = load("decide_deep_zero.json")["cross_check_exact"][2]
    a, b = dd.box_from_json(x["arb"]), dd.box_from_json(x["iv"])
    assert dd.enclosures_intersect(a, b)
    assert not dd.enclosures_intersect(a, _shift_box(b, "re"))
    assert not dd.enclosures_intersect(a, _shift_box(b, "im"))
    assert not dd.enclosures_intersect(a, _shift_box(b, "re", -2))
    # the recorded float check passes the same shifted box: why it was replaced
    assert _old_float_check(a, _shift_box(b, "re"))


def _old_float_check(a: dict, b: dict) -> bool:
    """The comparison `decide_deep_zero.py` recorded before 2026-10-26: float64
    midpoints within radii + 1e-30.  Kept here only to show that it cannot fail."""
    ok = True
    for k in ("re", "im"):
        am, bm = float((a[k][0] + a[k][1]) / 2), float((b[k][0] + b[k][1]) / 2)
        ar, br = float(a[k][1] - a[k][0]) / 2, float(b[k][1] - b[k][0]) / 2
        ok = ok and abs(am - bm) <= ar + br + 1e-30
    return ok


# ---------------------------------------------------------------------------
# 1b. step 2: the low screen, screen_hi
# ---------------------------------------------------------------------------

LOW_TABLE = {   # RESULTS.md section 8.3, gamma (4 dp) -> y0 enclosure (10 dp, rounded outward)
    "240.4047": ("0.3695305721", "0.3695305871"), "783.6530": ("0.3530014426", "0.3530014576"),
    "857.2959": ("0.3561094084", "0.3561094234"), "1092.4545": ("0.3546296114", "0.3546296264"),
    "2442.5303": ("0.3977501475", "0.3977501625"), "2887.9392": ("0.3604422749", "0.3604422899"),
    "3059.5187": ("0.3678568615", "0.3678568765"), "3214.1444": ("0.3612643315", "0.3612643465"),
    "3294.6092": ("0.3603604982", "0.3603605132"), "4237.9692": ("0.3576562360", "0.3576562510"),
    "4392.3764": ("0.3535286435", "0.3535286585"), "4935.6178": ("0.3551060612", "0.3551060763"),
    "5090.3177": ("0.3663990726", "0.3663990877"), "5833.2823": ("0.3740914934", "0.3740915084"),
    "5913.7059": ("0.3594353089", "0.3594353239"), "6113.9288": ("0.3581936446", "0.3581936596"),
    "7011.5119": ("0.3662883173", "0.3662883323"), "7909.4450": ("0.3545747216", "0.3545747366"),
    "8235.5925": ("0.3753363088", "0.3753363238"), "8561.5942": ("0.3836407511", "0.3836407661"),
    "9694.5786": ("0.3516309902", "0.3516310052"),
}


def test_low_screen_located_21_one_per_window():
    """deep_zeros_locate_20261026.json: 21 zeros, unit winding, one per flagged window."""
    z = load("deep_zeros_locate_20261026.json")["zeros"]
    assert len(z) == 21 and {q["winding"] for q in z} == {1}
    assert len({tuple(q["screen_window"]) for q in z}) == 21
    assert all(q["beta"] > 0.85 and q["gamma"] < 10000 for q in z)


def test_low_zeros_decided_on_both_backends_match_table():
    """decide_low_zeros.json: all 21 count 1 on both backends; y0 table of section 8.3."""
    d = load("decide_low_zeros.json")
    assert d["all_decided"] is True and len(d["rows"]) == 21
    got = {}
    for r in d["rows"]:
        assert r["python-flint"]["count"] == 1 and r["mpmath.iv"]["count"] == 1
        lo, hi = (Fraction(x) for x in r["y0_enclosure"])
        assert hi - lo == Fraction(2, 2**27)
        got[f"{r['gamma_float']:.4f}"] = (floor_dp(lo, 10), ceil_dp(hi, 10))   # outward
    assert got == LOW_TABLE
    assert max(Fraction(r["y0_enclosure"][1]) for r in d["rows"]) < Fraction(2, 5)


def test_screen_hi_superseded_and_complete():
    """deep_zeros.json (recorded, complete False) vs deep_zeros_hi_20261026.json (complete, 111)."""
    rec = load("deep_zeros.json")["screen_hi"]
    assert rec["complete"] is False and rec["boundaries"][-1][0] == 82480.0
    new = load("deep_zeros_hi_20261026.json")
    s = new["screen_hi"]
    assert s["complete"] is True and s["t0"] == 10000.0 and s["t1"] == 100000.0
    assert s["boundaries"][-1][0] == 100000.0
    z = new["zeros"]
    assert len(z) == 111 and len({round(q["gamma"], 3) for q in z}) == 111
    assert {q["winding"] for q in z} == {1}
    deepest = max(z, key=lambda q: q["y0"])
    assert round(deepest["y0"], 6) == 0.437058 and round(deepest["gamma"], 2) == 49688.34
    assert sum(q["y0"] > 0.40 for q in z) == 9


# ---------------------------------------------------------------------------
# 1c. kill condition 2 by the decided count (decide_kc2.json, kc2/)
# ---------------------------------------------------------------------------

def test_kc2_zero_free_count_decided():
    """decide_kc2.json + kc2/below8.json: no zero with beta >= 0.90 for |t| <= 1e4."""
    d = load("decide_kc2.json")
    assert d["status"] == "decided" and d["count"] == 0 and d["backend"] == "python-flint"
    assert d["rectangle"] == [["9/10", "41/20"], ["8", "10000"]]
    assert d["winding"]["lo"] < 0 < d["winding"]["hi"] and d["winding"]["hi"] - d["winding"]["lo"] < 1e-10
    assert d["left_edge_point_evals"] == 448092 and d["left_edge_min_margin"] > 1
    b = load("kc2/below8.json")
    assert b["count"] == 0 and b["rectangle"] == [["9/10", "41/20"], ["-8", "8"]]


def test_kc2_shards_tile_the_left_edge():
    """kc2/left_*_of_8.json: the eight shards tile 0.90 + i[8, 1e4] exactly, top to bottom."""
    ends = []
    for i in range(8):
        sh = load(f"kc2/left_{i}_of_8.json")
        assert sh["from"][0] == sh["to"][0] == "9/10"
        ends.append((Fraction(sh["from"][1]), Fraction(sh["to"][1])))
    assert ends[0][0] == 10000 and ends[-1][1] == 8
    assert all(ends[i][1] == ends[i + 1][0] for i in range(7))


def test_kc2_right_edge_bound_and_faults():
    """kc2/short_edges.json, kc2/faults.json: S < 1 decided; faults give 1 and 0."""
    s = load("kc2/short_edges.json")
    assert s["right"]["S_bound"]["hi"] < 1
    assert round(float(s["right"]["S_bound"]["mid"]), 10) == 0.2459783663
    f = load("kc2/faults.json")
    assert f["edge_0.89_t2400_2500_expect_1"]["count"] == 1
    assert f["edge_0.90_t2400_2500_expect_0"]["count"] == 0


# ---------------------------------------------------------------------------
# 1d. the landings (census_1e4.json, census_deep4_1e5.json)
# ---------------------------------------------------------------------------

def test_census_below_1e4_21_of_21_none_beats_floor():
    """census_1e4.json: 21 windows accounted and landed; control within band; floor not beaten."""
    rows = load("census_1e4.json")["rows"]
    assert len(rows) == 21
    assert all(r["accounting_ok"] and r["offline_located_ok"] and r["self_found"] for r in rows)
    land = [r["landing_ode"] for r in rows]
    assert all(t is not None for t in land)
    ctrl = min(rows, key=lambda r: abs(r["gamma"] - 240.4047))
    assert abs(ctrl["landing_ode"] / FLOOR_MEASURED - 1) < ODE_BAND
    assert round(100 * (ctrl["landing_ode"] / FLOOR_MEASURED - 1), 3) == 0.024
    assert none_beats_floor(land)
    deepest = max(rows, key=lambda r: r["y0"])
    assert round(deepest["gamma"], 2) == 2442.53 and round(deepest["landing_ode"], 6) == 0.055865
    shaves = [r["shave_percent"] for r in rows]
    assert round(min(shaves), 1) == 15.5 and round(max(shaves), 1) == 55.8


def test_targeted_check_above_1e4_8_of_9():
    """census_deep4_1e5.json: nine pairs with y0 > 0.40 attempted, eight landed, one open."""
    rows = load("census_deep4_1e5.json")["rows"]
    assert len(rows) == 9 and all(r["y0"] > 0.40 for r in rows)
    landed = [r for r in rows if r["landing_ode"] is not None]
    assert len(landed) == 8
    (open_,) = [r for r in rows if r["landing_ode"] is None]
    assert round(open_["gamma"], 2) == 88167.40 and open_["accounting_ok"] is False
    assert open_["n_strip"] == 142 and open_["n_right_beta_gt_0.505"] == 6
    assert none_beats_floor([r["landing_ode"] for r in landed])
    assert round(max(r["landing_ode"] for r in landed), 5) == 0.04902
    sh = [r["shave_percent"] for r in landed]
    assert round(min(sh), 1) == 38.8 and round(max(sh), 1) == 71.0


# ---------------------------------------------------------------------------
# 1e. every verdict of RESULTS.md sections 8.4 to 8.8, re-derived
# ---------------------------------------------------------------------------

def _all_landed():
    a = load("census_1e4.json")["rows"]
    b = [r for r in load("census_deep4_1e5.json")["rows"] if r["landing_ode"] is not None]
    return a, b


def test_verdict_P2_refuted_decided():
    """decide_low_zeros.json + decide_kc2.json: y_max(1e4) in [0.39775014, 0.40) (lower end outward)."""
    low = load("decide_low_zeros.json")["rows"]
    best_lo = max(Fraction(r["y0_enclosure"][0]) for r in low)
    assert best_lo >= Fraction("0.39775014") and load("decide_kc2.json")["count"] == 0
    assert not (Fraction(2, 5) <= best_lo <= Fraction(13, 25))   # outside [0.40, 0.52]


def test_verdict_KC2_fires_and_stage6_law_overpredicts():
    """theory_results.json criterion.sup: all four exponents predict y_max(1e4) > observed."""
    sup = load("theory_results.json")["criterion"]["sup"]
    observed_hi = max(Fraction(r["y0_enclosure"][1]) for r in load("decide_low_zeros.json")["rows"])
    preds = {p: v["y_max_1e4"] for p, v in sup.items()}
    assert {p: round(v, 4) for p, v in preds.items()} == {"0.5": 0.4125, "1.0": 0.4481, "1.5": 0.4776, "2.0": 0.5021}
    assert all(v > float(observed_hi) for v in preds.values())


def test_verdict_KC5_branch_p05_below_decided_floor():
    """theory_results.json: the p = 0.5 sup 0.05574992... is below 36/625 (recorded 2026-09-12)."""
    sup = load("theory_results.json")["criterion"]["sup"]
    assert sup["0.5"]["sup"] < float(FLOOR_DECIDED) and sup["0.5"]["consistent"] is False
    assert all(sup[p]["sup"] > float(FLOOR_DECIDED) for p in ("1.0", "1.5", "2.0"))


def test_verdict_P3_holds_KC1_does_not_fire():
    """census_1e4.json + census_deep4_1e5.json against theory.t_star_gap."""
    th = _theory()
    a, b = _all_landed()
    ratios = {round(r["gamma"], 2): r["landing_ode"] / float(th.t_star_gap(r["y0"], r["gamma"])) for r in a + b}
    p3 = ratios[2442.53]
    assert 0.85 <= p3 <= 1.25 and round(p3, 3) == 0.986          # P3 holds
    assert max(ratios.values()) < 1.25 and max(ratios.values()) < 1.0   # KC1 does not fire
    small = sorted(g for g, q in ratios.items() if q < 0.7)
    assert small == [4935.62, 49688.34, 74189.64, 77163.41]
    dh = {round(r["gamma"], 2): r["gap_ratio_d_over_h"] for r in a + b}
    assert all(dh[g] < 0.123 for g in small) and round(max(dh[g] for g in small), 4) == 0.1223


def test_verdict_P4_not_raised_within_coverage():
    """census_1e4.json: the best landing below 1e4 is the floor pair itself.

    P4 is *unresolved, evidence against* (RESULTS.md 8.7, relabelled 2026-10-26 in
    review): its antecedent, a complete census to 1e4, was not run (y0 in
    (0.3396, 0.35] not landed), so this shows only that, within coverage
    y0 > 0.35, the best landing is not raised.
    """
    assert all(r["y0"] > 0.35 for r in load("census_1e4.json")["rows"])     # the coverage
    a, _ = _all_landed()
    best = max(a, key=lambda r: r["landing_ode"])
    assert round(best["gamma"], 2) == 240.40
    assert none_beats_floor([r["landing_ode"] for r in a if r is not best])


def test_verdict_P6_refuted():
    """census_1e4.json: d/h of the 20 new pairs, 10 of 20 in [1.1, 1.8], mean 0.947."""
    a, _ = _all_landed()
    new = [r["gap_ratio_d_over_h"] for r in a if abs(r["gamma"] - 240.4047) > 0.01]
    assert len(new) == 20
    assert sum(1.1 <= g <= 1.8 for g in new) == 10
    mean = sum(new) / 20
    sd = math.sqrt(sum((g - mean) ** 2 for g in new) / 19)
    assert round(mean, 3) == 0.947 and round(sd, 3) == 0.317
    assert round(min(new), 3) == 0.101 and round(max(new), 3) == 1.329


def test_verdict_P8_not_observed():
    """census_1e4.json: within P8's registered scope, pairs below 1e4, 0 of 21 land later than y0^2/2.

    The 8 targeted pairs (and the 170 census pairs) above 1e4 lie outside that
    scope and are checked only as a description (restricted 2026-10-26 in review;
    this test used to pool them as 0 of 29).
    """
    a, b = _all_landed()
    assert len(a) == 21 and all(r["gamma"] < 1e4 for r in a)
    assert not any(r["later_than_naive"] for r in a)
    assert all(r["landing_ode"] < r["landing_naive"] for r in a)
    assert len(b) == 8 and all(r["gamma"] > 1e4 for r in b)                  # outside P8's scope
    assert not any(r["later_than_naive"] for r in b)


def test_verdict_P5_and_KC4_per_decade_maxima_fall():
    """census_1e4.json + census_deep4_1e5.json: per-decade measured maxima fall."""
    a, b = _all_landed()
    dec = lambda lo, hi: max(r["landing_ode"] for r in a + b if lo <= r["gamma"] < hi)
    m2, m3, m4 = dec(1e2, 1e3), dec(1e3, 1e4), dec(1e4, 1e5)
    assert (round(m2, 5), round(m3, 5), round(m4, 5)) == (0.05767, 0.05586, 0.04902)
    assert m2 > m3 > m4                  # KC4 does not fire on what was measured
    best = max(a + b, key=lambda r: r["landing_ode"])
    assert best["gamma"] < 1e3 and best["y0"] < 0.40   # outside both of P5's ranges


# ---------------------------------------------------------------------------
# 2. recomputations, fast tier
# ---------------------------------------------------------------------------

def _low_row(gamma4: str) -> dict:
    return next(r for r in load("decide_low_zeros.json")["rows"] if f"{r['gamma_float']:.4f}" == gamma4)


def _decide_low(row, shift: Fraction = Fraction(0)):
    import decide_deep_zero as dd
    sl, sh = (Fraction(x) for x in row["rectangle_sigma"])
    tl, th = (Fraction(x) for x in row["rectangle_t"])
    half = (sh - sl) / 2
    centre = ((sl + sh) / 2 + shift, (tl + th) / 2)
    R = Fraction(1, 2**13)
    arb = dd.count_zeros(dd.ArbRoute(prec=128), centre, half, R)
    ivr = dd.IvRoute(prec=128, centre=centre, radius=Fraction(1, 2**12), K=14, log_every=0)
    ivc = dd.count_zeros(ivr, centre, half, R)
    y0 = (centre[0] - half - Fraction(1, 2), centre[0] + half - Fraction(1, 2))
    return arb.get("count"), ivc.get("count"), y0


def test_recompute_one_low_zero_on_both_backends():
    """decide_low_zeros.json, gamma = 240.4047: recount 1 on Arb and iv, same y0 interval."""
    row = _low_row("240.4047")
    shift = Fraction(4, 2**27) if PLANT else Fraction(0)   # planted: the zero pushed past its interval
    n_arb, n_iv, y0 = _decide_low(row, shift)
    recorded = tuple(Fraction(x) for x in row["y0_enclosure"])
    assert count_matches(n_arb, 1) and count_matches(n_iv, 1)
    assert interval_inside(y0, recorded)


def test_planted_fault_zero_past_its_interval_is_caught():
    """The same recount with the rectangle moved four half-widths: both backends see 0."""
    row = _low_row("240.4047")
    n_arb, n_iv, y0 = _decide_low(row, Fraction(4, 2**27))
    assert not count_matches(n_arb, 1) and not count_matches(n_iv, 1)
    assert n_arb == 0 and n_iv == 0
    assert not interval_inside(y0, tuple(Fraction(x) for x in row["y0_enclosure"]))


def test_recompute_kc2_below8_slice():
    """kc2/below8.json: [0.90, 2.05] x [-8, 8] recounted on Arb, count 0, winding balls intersect."""
    import decide_deep_zero as dd
    import decide_kc2 as kc
    rec = load("kc2/below8.json")
    got = kc.count_rect(dd.ArbRoute(prec=kc.PREC), kc.SIG_L, kc.SIG_R, Fraction(-8), Fraction(8))
    assert count_matches(_maybe_plant_count(got["count"]), rec["count"])
    assert balls_intersect(got["winding"]["lo"], got["winding"]["hi"], rec["winding"]["lo"], rec["winding"]["hi"])


def test_recompute_kc2_edge_sensitivity_at_2442():
    """[0.89 vs 0.90, 2.05] x [2440, 2445] on Arb: 1 and 0, the zero at beta 0.89775 seen once."""
    import decide_deep_zero as dd
    import decide_kc2 as kc
    r = dd.ArbRoute(prec=kc.PREC)
    a = kc.count_rect(r, Fraction(89, 100), kc.SIG_R, Fraction(2440), Fraction(2445))
    b = kc.count_rect(r, kc.SIG_L, kc.SIG_R, Fraction(2440), Fraction(2445))
    assert count_matches(_maybe_plant_count(a["count"]), 1)
    assert count_matches(b["count"], 0)


def test_planted_fault_count_off_by_one_is_caught():
    """count_matches and balls_intersect reject a recorded count or ball that is off by one."""
    rec = load("kc2/below8.json")
    assert not count_matches(rec["count"] + 1, rec["count"])
    assert not count_matches(None, rec["count"])
    w = rec["winding"]
    assert not balls_intersect(w["lo"] + 1, w["hi"] + 1, w["lo"], w["hi"])


def test_planted_fault_landing_above_floor_is_caught():
    """none_beats_floor rejects the census with one landing nudged 0.1 percent above the floor."""
    rows = load("census_1e4.json")["rows"]
    land = [r["landing_ode"] for r in rows] + [FLOOR_MEASURED * 1.001]
    assert not none_beats_floor(land)


def test_planted_fault_interval_checker():
    """interval_inside rejects a recorded y0 interval shifted by one width."""
    lo, hi = (Fraction(x) for x in _low_row("2442.5303")["y0_enclosure"])
    w = hi - lo
    assert interval_inside((lo, hi), (lo, hi))
    assert not interval_inside((lo + w, hi + w), (lo, hi))


# ---------------------------------------------------------------------------
# 2b. recomputation, slow tier
# ---------------------------------------------------------------------------

@pytest.mark.slow
def test_recompute_kc2_lowest_shard_matches_record():
    """kc2/left_7_of_8.json: arg variation down 0.90 + i[8, 1257] recomputed on Arb (~2 min)."""
    import decide_deep_zero as dd
    import decide_kc2 as kc
    from flint import arb
    rec = load("kc2/left_7_of_8.json")
    pa = (Fraction(rec["from"][0]), Fraction(rec["from"][1]))
    pb = (Fraction(rec["to"][0]), Fraction(rec["to"][1]))
    var, st = kc.edge_variation(dd.ArbRoute(prec=kc.PREC), pa, pb)
    lo, hi = float(var.lower()), float(var.upper())
    if PLANT:
        lo, hi = lo + 2 * math.pi, hi + 2 * math.pi   # one extra winding on the slice
    assert balls_intersect(lo, hi, rec["variation"]["lo"], rec["variation"]["hi"])
    assert st["segments"] == rec["stats"]["segments"]
    assert arb(rec["variation_arb"]).overlaps(var) or PLANT


# ---------------------------------------------------------------------------
# 4. the transcription slips, corrected in this hunt (RESULTS.md section 8.9)
# ---------------------------------------------------------------------------

SLIPS = {   # gamma: (old, corrected), flow_repair/NOTES.md section 1 vs results.json
    114.1633: (0.1508270, 0.1508301), 166.4793: (0.0743505, 0.0743561),
    176.7025: (0.2242763, 0.2242577), 240.4046: (0.3695261, 0.3695306),
}


def _flow_repair_polished() -> dict:
    """hunts/flow_repair/results.json (read-only): polished y0 of pairs 2 to 5."""
    d = json.load(open(HERE.parent / "flow_repair" / "results.json"))
    out = {}
    for key in ("survey_2_3", "survey_4_5"):
        for pk, v in d[key].items():
            if pk.startswith("pair") and isinstance(v, dict) and "polished" in v:
                out[round(float(v["polished"]["gamma"]), 4)] = float(v["polished"]["y0"])
    return out


def test_slips_corrected_against_flow_repair_results():
    """theory.NINE and landing.json carry flow_repair/results.json's y0 to 7 dp, not NOTES.md's."""
    pol = _flow_repair_polished()
    th = _theory()
    nine = {g: y for g, y, _ in th.NINE}
    lj = load("landing.json")["census_1_2_3_4_5_6_7_8_9"]
    for (g, (old, new)), k in zip(sorted(SLIPS.items()), ("pair2", "pair3", "pair4", "pair5")):
        match = [v for gg, v in pol.items() if abs(gg - g) < 0.01]
        assert len(match) == 1 and round(match[0], 7) == new
        assert nine[g] == new and lj[k]["y0"] == new


def test_flow_repair_notes_still_carries_the_old_values():
    """hunts/flow_repair/NOTES.md is untouched: its section-1 table still has the slipped y0."""
    notes = (HERE.parent / "flow_repair" / "NOTES.md").read_text()
    for old, _ in SLIPS.values():
        assert f"{old:.7f}" in notes


def test_slip_effect_is_below_every_reported_digit():
    """slip_effect.json: stage 5 mean d/h 1.42844 -> 1.42519, stage 6 moves at most 4e-6."""
    e = load("slip_effect.json")
    # the recomputed old-value calibration reproduces the recorded artifact (to 1e-15)
    assert abs(e["recorded"]["d_over_h_mean"] - load("theory_results.json")["calibration"]["mean"]) < 1e-12
    assert round(e["recorded"]["d_over_h_mean"], 5) == 1.42844
    assert round(e["corrected"]["d_over_h_mean"], 5) == 1.42519
    for p in ("0.5", "1.0", "1.5", "2.0"):
        for k in ("y_max_1e4", "sup"):
            assert abs(e["corrected"]["sup"][p][k] - e["recorded"]["sup"][p][k]) < 4e-6
    assert e["corrected"]["sup"]["0.5"]["sup"] < float(FLOOR_DECIDED)   # KC5 branch unchanged


# ---------------------------------------------------------------------------
# 5. the per-pair d/h refit (refit_dh.json)
# ---------------------------------------------------------------------------

def test_refit_dh_plugin_is_worse_inverse_tracks_measured():
    """refit_dh.json: plug-in rms 0.393 vs frozen 0.160; inverse d/h vs measured r = 0.967."""
    d = load("refit_dh.json")
    assert d["n"] == 29 and d["DBAR"] == 1.4284
    assert round(d["frozen"]["rms_dev_from_1"], 3) == 0.160
    assert round(d["plugin"]["rms_dev_from_1"], 3) == 0.393
    assert d["plugin_ratio_above_1"] == 28 and round(d["plugin"]["max"], 3) == 2.088
    iv = d["inverse_vs_measured"]
    assert iv["n"] == 29 and round(iv["pearson_r"], 3) == 0.967
    lf = iv["linear_fit"]
    assert (round(lf["a"], 3), round(lf["b"], 3), round(lf["rms_resid"], 3)) == (0.567, 0.674, 0.071)


def test_refit_dh_recomputes_from_the_census():
    """refit_dh.py's frozen ratios equal the census ratios of section 8.7 (same model, same rows)."""
    th = _theory()
    d = {round(r["gamma"], 2): r for r in load("refit_dh.json")["rows"]}
    r = d[2442.53]
    assert abs(r["model_frozen_dbar"] - float(th.t_star_gap(r["y0"], r["gamma"]))) < 1e-12
    assert abs(float(th.t_star_gap(r["y0"], r["gamma"], dfac=r["d_over_h_inverse"])) - r["landing_ode"]) < 1e-7


# ---------------------------------------------------------------------------
# 6. the two-sided local gap, PREREG RESULTS.md section 8.10 (twosided.json)
# ---------------------------------------------------------------------------

def test_twosided_prereg_verdict_improves_not_pass():
    """twosided.json: gate clean; rms 0.112 (frozen 0.160, pass bar 0.080); 26 of 29 in band."""
    d = load("twosided.json")
    assert d["n"] == 29 and d["gate_ok"] is True and d["max_gate_defect"] < 1e-9
    assert round(d["rms_dev_from_1"], 3) == 0.112
    assert d["n_in_band"] == 26 and d["n_second_nearest_same_side"] == 1
    assert (round(d["min_ratio"], 3), round(d["max_ratio"], 3)) == (0.981, 1.339)
    import twosided as ts
    assert ts.rule(d["rms_dev_from_1"], [r["ratio"] for r in d["rows"]]) == d["verdict"] == "IMPROVES"
    out = sorted(round(r["gamma"], 2) for r in d["rows"] if r["ratio"] > 1.25)
    assert out == [4935.62, 49688.34, 77163.41]
    assert all(min(r["d_L_over_h"], r["d_R_over_h"]) < 0.123 for r in d["rows"] if r["ratio"] > 1.25)


def test_twosided_rule_is_the_preregistered_one():
    """twosided.rule: PASS, IMPROVES and FAIL at the thresholds written in section 8.10."""
    import twosided as ts
    assert ts.rule(0.080, [1.0] * 29) == "PASS"
    assert ts.rule(0.050, [1.0] * 28 + [1.26]) == "IMPROVES"   # band fails, rms passes
    assert ts.rule(0.159, [1.0] * 29) == "IMPROVES"
    assert ts.rule(0.160, [1.0] * 29) == "FAIL"


def test_recompute_twosided_control_window():
    """twosided.json, gamma = 240.4047: line scan and t*_2 recomputed; same d_L, d_R and ratio."""
    import twosided as ts
    import census_1e4 as cz
    rec = next(r for r in load("twosided.json")["rows"] if abs(r["gamma"] - 240.4047) < 0.01)
    g, h = rec["gamma"], rec["h"]
    reals = cz.line_zeros(g - 4 * h, g + 4 * h)
    d_l = g - max(x for x in reals if x < g)
    d_r = min(x for x in reals if x > g) - g
    if PLANT:
        d_l += 0.05 * h          # planted: the lower neighbour misplaced by 5 percent of a gap
    assert abs(d_l / h - rec["d_L_over_h"]) < 1e-9 and abs(d_r / h - rec["d_R_over_h"]) < 1e-9
    t2 = ts.t_star_two(rec["y0"], d_l, d_r, h)
    assert abs(rec["landing_ode"] / t2 - rec["ratio"]) < 1e-9


def test_twosided_reduces_to_the_frozen_model():
    """t_star_two(d_L = d_R = DBAR h) equals theory.t_star_gap exactly (2442.53)."""
    import twosided as ts
    th = _theory()
    g, y0 = 2442.5303, 0.3977501
    h = ts.h_mean(g)
    assert ts.t_star_two(y0, th.DBAR * h, th.DBAR * h, h) == float(th.t_star_gap(y0, g))


def test_twosided_comparison_table_of_section_8_11():
    """refit_dh.json + twosided.json: in-band counts 25 / 22 / 26; the 25 non-collision ratios."""
    f = load("refit_dh.json")["rows"]
    t = load("twosided.json")["rows"]
    band = lambda q: 0.85 <= q <= 1.25
    assert sum(band(r["ratio_frozen"]) for r in f) == 25
    assert sum(band(r["ratio_plugin"]) for r in f) == 22
    assert sum(band(r["ratio"]) for r in t) == 26
    assert round(max(1 / r["ratio_frozen"] for r in f), 1) == 1.9
    rest = [r["ratio"] for r in t if min(r["d_L_over_h"], r["d_R_over_h"]) >= 0.123]
    assert len(rest) == 25 and (round(min(rest), 3), round(max(rest), 2)) == (0.981, 1.11)
    r74 = next(r for r in t if round(r["gamma"], 2) == 74189.64)
    assert round(r74["ratio"], 3) == 1.173


# ---------------------------------------------------------------------------
# 7. the 1e5 census, prepared for Actions and not triggered
# ---------------------------------------------------------------------------

WORKFLOW = HERE.parents[1] / ".github" / "workflows" / "lambda-dh-census.yml"
PLAN_SHA = "461079f90cf78f9c635b44ab365d9cf956cbe8bce23532fc55c6d4eef226eaa9"


def test_census_plan_is_the_generated_one_and_hash_pinned():
    """census_plan_1e5.json: 36 shards of 2500 tiling [1e4, 1e5]; sha256 pinned in RUNS.md."""
    import census_shard as cs
    plan = load("census_plan_1e5.json")
    assert plan == cs.plan_obj()
    assert cs.plan_sha(str(HERE / "census_plan_1e5.json")) == PLAN_SHA
    sh = plan["shards"]
    assert len(sh) == 36 and sh[0][0] == 10000 and sh[-1][1] == 100000
    assert all(a[1] == b[0] and a[1] - a[0] == 2500 for a, b in zip(sh, sh[1:]))
    assert plan["sigma_c"] == 0.82 and plan["min_y0"] == 0.3396
    assert plan["min_y0"] ** 2 / 2 > FLOOR_MEASURED > 0.3395 ** 2 / 2


def test_census_request_valid_and_workflow_guard_rails():
    """RUN_REQUEST.json, when present (pushed only after the coordinator's go), names this plan
    and a known mode; the workflow triggers only on it, with the agreed limits."""
    yaml = pytest.importorskip("yaml")
    req_path = HERE / "RUN_REQUEST.json"
    if req_path.exists():
        req = json.loads(req_path.read_text())
        assert req["mode"] in ("calibrate", "full") and isinstance(req["attempt"], int)
        assert req["plan_sha256"] == PLAN_SHA
    w = yaml.safe_load(WORKFLOW.read_text())
    on = w.get("on", w.get(True))
    assert list(on) == ["push"]
    assert on["push"]["branches"] == ["hunt/lambda-dh-exact-resume"]
    assert on["push"]["paths"] == ["hunts/lambda_dh_exact/RUN_REQUEST.json"]
    assert w["permissions"] == {"contents": "read"}
    assert w["concurrency"]["group"] == "lambda-dh-census"
    assert w["defaults"]["run"]["shell"] == "bash"     # pipefail: a failing calib | tee fails its step
    for name, job in w["jobs"].items():
        assert job["timeout-minutes"] <= 350, name
        mp = job.get("strategy", {}).get("max-parallel")
        assert mp is None or mp <= 4, name
    text = WORKFLOW.read_text()
    assert "attempt${{ github.run_attempt }}" in text and "-r${{ needs.plan.outputs.req }}-" in text
    assert "census_shard.py\" preflight" in text and "census_constraints.txt" in text


def test_census_pins_match_the_versions_that_made_the_artifacts():
    """census_constraints.txt: exact pins, equal to this environment's (which made census_1e4)."""
    from importlib.metadata import version
    import census_shard as cs
    pins = cs._pins()
    assert set(pins) == {"mpmath", "numpy", "python-flint", "scipy"}
    if PLANT:
        pins["numpy"] = "0.0.0"      # planted: a drifted pin must be noticed
    assert all(version(n) == v for n, v in pins.items())


def test_census_gather_picks_the_most_advanced_copy(tmp_path):
    """census_shard.gather: a complete later copy beats a stale partial one, whatever the order."""
    import census_shard as cs
    plan = tmp_path / "plan.json"
    plan.write_text(json.dumps({**cs.plan_obj(), "shards": [[10000, 10040]]}))
    old, new = tmp_path / "prior" / "a2", tmp_path / "prior" / "a1"   # names sort the stale one last
    old.mkdir(parents=True), new.mkdir(parents=True)
    (old / "screen_0.json").write_text(json.dumps({"partial": True}))
    (new / "screen_0.json").write_text(json.dumps({"screen_c82": {"complete": True}}))
    (new / "census_0.json").write_text(json.dumps({"rows": [{"gamma": 1.0}]}))
    (new / "shard_0.json").write_text(json.dumps({"screen_complete": True, "runs": 1}))
    saved = cs.PLAN
    try:
        cs.PLAN = str(plan)
        cs.stage_gather(str(tmp_path / "prior"), str(tmp_path / "out"))
    finally:
        cs.PLAN = saved
    got = json.loads((tmp_path / "out" / "screen_0.json").read_text())
    assert got == {"screen_c82": {"complete": True}}


def test_census_preflight_refuses_a_wrong_plan_hash(tmp_path):
    """census_shard.py preflight exits non-zero before any computation when the hash is wrong."""
    import subprocess
    req = tmp_path / "req.json"
    req.write_text(json.dumps({"mode": "calibrate", "attempt": 1, "plan_sha256": "0" * 64}))
    r = subprocess.run([sys.executable, str(HERE / "census_shard.py"), "preflight", "--request", str(req)],
                       capture_output=True, text=True, cwd=HERE.parents[1])
    assert r.returncode != 0 and "plan_sha256 does not match" in (r.stderr + r.stdout)


def test_census_records_peak_rss_and_calib_reports_it(tmp_path):
    """census_shard: peak_rss_gb() covers child processes; calib reports 4 x peak against 13 GB."""
    import subprocess
    import census_shard as cs
    subprocess.run([sys.executable, "-c", "x = bytearray(64 * 2**20)"], check=True)   # a 64 MiB child
    r = cs.peak_rss_gb()
    assert r["children_gb"] >= 64 / 1024 and r["peak_gb"] == max(r["self_gb"], r["children_gb"])
    plan = tmp_path / "plan.json"
    plan.write_text(json.dumps({**cs.plan_obj(), "shards": [[55000, 57500]]}))
    peak = 0.25 if not PLANT else 3.5           # planted: a runner-busting peak must fail the 13 GB check
    (tmp_path / "shard_0.json").write_text(json.dumps({
        "interval": [55000, 57500], "n_screen_windows": 125, "n_candidates": 4,
        "cpu_seconds": {"screen": 50.0, "locate": 10.0, "census": 1200.0},
        "peak_rss": {"self_gb": 0.02, "children_gb": peak, "peak_gb": peak}}))
    saved = cs.PLAN
    try:
        cs.PLAN = str(plan)
        cs.stage_calib(str(tmp_path), 0)
    finally:
        cs.PLAN = saved
    cal = json.loads((tmp_path / "calibration.json").read_text())
    assert cal["peak_rss_gb"] == peak and cal["four_x_peak_rss_gb"] == 4 * peak
    assert cal["four_x_peak_rss_ok_13gb"] is True
    assert cal["cpu_s_per_census_window"] == 300.0 and cal["cpu_s_per_screen_window"] == 60.0 / 125


# ---------------------------------------------------------------------------
# 8. the census run (RESULTS.md section 8.13): void by K-d
# ---------------------------------------------------------------------------

CENSUS_SHA = "84e8ec88a7dcc75d33318edba9a8fa9b99fbc106efaa61df6238f6135331af72"


def test_census_merged_artifact_hash_and_shape():
    """census_runs/full_r1/census_1e5.json: the merge job's sha256; 36 shards, 162 rows, 161 landed."""
    import hashlib
    raw = (HERE / "census_runs" / "full_r1" / "census_1e5.json").read_bytes()
    if PLANT:
        raw = raw + b" "        # planted: one byte appended to the merged census
    assert hashlib.sha256(raw).hexdigest() == CENSUS_SHA
    c = json.loads(raw)
    assert c["plan_sha256"] == PLAN_SHA and len(c["shards"]) == 36
    assert sorted(s["shard"] for s in c["shards"]) == list(range(36))
    assert len(c["rows"]) == 162 and sum(r["landing_ode"] is not None for r in c["rows"]) == 161
    cpu = sum(sum(s["cpu_seconds"].values()) for s in c["shards"]) / 3600
    assert round(cpu, 2) == 11.05 and cpu <= 30
    assert max(s["peak_rss"]["peak_gb"] for s in c["shards"]) < 0.26


def _kd(rows, deep):
    out = []
    for d in deep:
        if d["landing_ode"] is None:
            continue
        m = [r for r in rows if abs(r["gamma"] - d["gamma"]) < 1e-3]
        out.append((round(d["gamma"], 2), (abs(m[0]["landing_ode"] / d["landing_ode"] - 1) if m else None)))
    return out


def test_census_K_d_fails_exactly_at_20011():
    """census_1e5.json vs census_deep4_1e5.json, recomputed here: 7 of 8 replicate, 20011.16 missing."""
    rows = load("census_runs/full_r1/census_1e5.json")["rows"]
    deep = load("census_deep4_1e5.json")["rows"]
    if PLANT:   # planted: pretend the missing pair was landed; the K-d failure must then vanish
        d = next(x for x in deep if abs(x["gamma"] - 20011.16) < 0.01)
        rows = rows + [d]
    kd = dict(_kd(rows, deep))
    assert len(kd) == 8 and kd[20011.16] is None
    assert all(v is not None and v < 1e-11 for g, v in kd.items() if g != 20011.16)


def test_census_evaluation_void_with_values_kept():
    """census_runs/full_r1/evaluation.json: K-a..K-e as recorded; every verdict void; values kept."""
    e = load("census_runs/full_r1/evaluation.json")
    if PLANT:
        e["K_d_ok"] = True      # planted: an evaluation that let K-d pass
    assert e["K_b_ok"] and e["K_c_ok"] and e["K_e_ok"] and not e["K_d_ok"] and not e["census_valid"]
    assert e["n_unaccounted"] == 1 and e["unaccounted_gammas"] == [88167.4]
    for k in ("verdict_floor", "verdict_KC4", "verdict_P5", "verdict_P8", "verdict_two_sided_oos"):
        assert e[k].startswith("void (K_d_ok failed)"), k
    assert e["floor_beaten_by"] == [] and round(e["m4"], 5) == 0.04877
    assert round(e["m4_at"]["gamma"], 2) == 24415.48 and e["P8_count"] == 0
    assert round(e["P5_argmax"]["gamma"], 2) == 240.40
    t = e["two_sided_oos"]
    assert t["n"] == 154 and t["n_in_band"] == 126 and round(t["rms"], 3) == 0.158


def test_mislocated_roots_lie_outside_their_boxes_and_relocate():
    """mislocated.json + relocated.json: 17 windows; each true root is inside its box; 8 census misses."""
    mis = load("census_runs/full_r1/mislocated.json")["rows"]
    rel = load("census_runs/full_r1/relocated.json")
    assert len(mis) == 17 and sum(m["source"].startswith("census") for m in mis) == 16
    assert all(m["wrong_root"]["beta"] <= m["sigma_c"] for m in mis)
    rows = rel["rows"]
    assert rel["n_ok"] == 17 and all(r["count_in_box"] == 1 and len(r["found"]) == 1 for r in rows)
    sig = {tuple(r["window"]): r["sigma_c"] for r in rows}
    for r in rows:
        f = r["found"][0]
        bad = PLANT and r["source"] == "census shard 4"     # planted: pretend the wrong root was kept
        beta = r["wrong_root"]["beta"] if bad else f["beta"]
        assert beta > r["sigma_c"] and r["window"][0] < f["gamma"] < r["window"][1]
    cen = [r["found"][0] for r in rows if r["source"].startswith("census")]
    assert sum(f["y0"] > 0.3396 for f in cen) == 8
    assert round(max(f["y0"] for f in cen), 4) == 0.4002


def test_screen_hi_correction_leaves_the_y0_above_040_selection_unchanged():
    """deep_zeros_hi_20261026.json with its one mislocated root replaced: still 9 zeros above 0.40."""
    hi = load("deep_zeros_hi_20261026.json")["zeros"]
    rel = load("census_runs/full_r1/relocated.json")["rows"]
    fix = next(r for r in rel if r["source"].startswith("screen_hi"))
    assert fix["window"] == [16620.0, 16640.0] and round(fix["found"][0]["y0"], 4) == 0.3742
    wrong = [z for z in hi if z["beta"] <= 0.85]
    assert len(wrong) == 1 and round(wrong[0]["gamma"], 2) == 16637.67
    true_y0 = fix["found"][0]["y0"] + (0.05 if PLANT else 0.0)   # planted: the true zero 0.05 deeper
    fixed = [z["y0"] for z in hi if z["beta"] > 0.85] + [true_y0]
    assert len(fixed) == 111
    assert sum(y > 0.40 for y in fixed) == 9 and round(max(fixed), 6) == 0.437058


# ---------------------------------------------------------------------------
# 9. the stage_locate box guard (unit 4; deep_zeros.locate_part)
# ---------------------------------------------------------------------------

def _guarded(monkeypatch, sigma_c, a, b, first=None):
    import deep_zeros as dz
    monkeypatch.setattr(dz, "SIGMA_C", sigma_c)
    if PLANT:   # planted: the guard switched off, every root accepted wherever it lands
        monkeypatch.setattr(dz, "in_box", lambda rho, ta, tb: True)
    return dz.locate_part(a, b, 1, first=first)


def test_guard_refuses_a_planted_outside_start_and_relocates(monkeypatch):
    """[12460, 12480] at sigma_c 0.82: a planted start at beta 0.8027 is refused; the box search
    returns the zero relocated.json records (gamma 12468.3898)."""
    rel = next(r for r in load("census_runs/full_r1/relocated.json")["rows"] if r["window"] == [12460.0, 12480.0])
    w = rel["wrong_root"]
    got, refused = _guarded(monkeypatch, 0.82, 12460.0, 12480.0, first=complex(w["beta"], w["gamma"]))
    assert refused is not None and abs(refused["beta"] - w["beta"]) < 1e-12
    assert len(got) == 1 and got[0].real > 0.82
    assert abs(got[0].imag - rel["found"][0]["gamma"]) < 1e-6


def test_guard_accepts_an_in_box_start(monkeypatch):
    """The same window with the true root as the start: accepted, nothing refused."""
    import deep_zeros as dz
    monkeypatch.setattr(dz, "SIGMA_C", 0.82)
    rel = next(r for r in load("census_runs/full_r1/relocated.json")["rows"] if r["window"] == [12460.0, 12480.0])
    f = rel["found"][0]
    got, refused = dz.locate_part(12460.0, 12480.0, 1, first=complex(f["beta"], f["gamma"]))
    assert refused is None and len(got) == 1 and abs(got[0] - complex(f["beta"], f["gamma"])) < 1e-12


def _known_windows():
    return load("census_runs/full_r1/relocated.json")["rows"]


def test_guard_fixes_the_three_lowest_known_windows(monkeypatch):
    """Three of the 17 affected windows: unguarded locate lands outside, guarded lands inside."""
    import deep_zeros as dz
    for r in sorted(_known_windows(), key=lambda r: r["window"][0])[:3]:
        a, b = r["window"]
        got, refused = _guarded(monkeypatch, r["sigma_c"], a, b)
        assert refused is not None
        assert len(got) == 1 and got[0].real > r["sigma_c"] and a <= got[0].imag <= b
        assert abs(got[0].imag - r["found"][0]["gamma"]) < 1e-6


@pytest.mark.slow
def test_guard_fixes_all_17_known_windows(monkeypatch):
    """All 17 affected windows (16 census, 1 screen_hi): every guarded root is in its box."""
    rows = _known_windows()
    assert len(rows) == 17
    for r in rows:
        a, b = r["window"]
        got, refused = _guarded(monkeypatch, r["sigma_c"], a, b)
        assert refused is not None, r["window"]
        assert len(got) == 1 and got[0].real > r["sigma_c"] and a <= got[0].imag <= b, r["window"]
        assert abs(got[0].imag - r["found"][0]["gamma"]) < 1e-6, r["window"]


# ---------------------------------------------------------------------------
# 10. the audit under the guard, and the window at gamma = 88167.40 (unit 4)
# ---------------------------------------------------------------------------

def test_audit_low_and_1e6_roots_unchanged_under_the_guard():
    """census_runs/audit_u4/guarded_locate.json: low 21 identical, 1e6 within 1e-12, nothing refused."""
    a = load("census_runs/audit_u4/guarded_locate.json")
    key = lambda z: complex(z["beta"], z["gamma"])
    for name, rec, tol in (("low", "deep_zeros_locate_20261026.json", 0.0),
                           ("1e6", "deep_zeros_1e6.json", 1e-12)):
        new = a[name]["zeros"]
        old = load(rec)["zeros"]
        if PLANT and name == "low":
            new = new[:-1]           # planted: one root lost by the guard
        assert len(new) == len(old) and a[name]["unlocated"] == []
        assert not any(z["guard"]["first_root_refused"] for z in new)
        assert max(min(abs(key(o) - key(n)) for n in new) for o in old) <= tol


def test_audit_screen_hi_exactly_one_root_replaced():
    """guarded_locate.json screen_hi: 110 roots identical; 16637.67 (beta 0.7132) -> 16620.3825 (y0 0.3742)."""
    a = load("census_runs/audit_u4/guarded_locate.json")["screen_hi"]
    old = load("deep_zeros_hi_20261026.json")["zeros"]
    new = a["zeros"]
    key = lambda z: complex(z["beta"], z["gamma"])
    gone = [o for o in old if min(abs(key(o) - key(n)) for n in new) > 1e-9]
    came = [n for n in new if min(abs(key(o) - key(n)) for o in old) > 1e-9]
    if PLANT:
        came = came + [dict(came[0], gamma=50000.0)]   # planted: a second change
    assert len(new) == 111 and a["unlocated"] == []
    assert [round(g["gamma"], 2) for g in gone] == [16637.67]
    assert [(round(c["gamma"], 4), round(c["y0"], 4)) for c in came] == [(16620.3825, 0.3742)]
    assert came[0]["guard"]["first_root_refused"]["beta"] < 0.85
    assert min(z["beta"] for z in new) > 0.85
    assert sum(z["y0"] > 0.40 for z in new) == 9 and round(max(z["y0"] for z in new), 6) == 0.437058


def test_window_88167_closes_with_the_fallback():
    """census_runs/audit_u4/w88167_relanded.json: 142 = 128 + 2 x 7 at sigma_in 0.5005; landing 0.04012."""
    e = load("census_runs/audit_u4/w88167_relanded.json")
    fb = e["accounting_fallback"]
    n_right = fb["n_right"] + (1 if PLANT else 0)    # planted: one zero too many in the fallback count
    assert e["n_strip"] == e["n_line"] + 2 * n_right == 142
    assert e["n_line"] == 128 and e["n_right_beta_gt_0.505"] == 6 and e["sig_in_used"] == 0.5005
    assert e["accounting_ok"] and e["offline_located_ok"] and e["self_found"]
    assert round(e["landing_ode"], 5) == 0.04012 and e["landing_ode"] < FLOOR_MEASURED
    shallow = [p for p in e["other_pairs"] if p[1] < 0.005]
    assert len(shallow) == 1 and round(shallow[0][0], 2) == 88132.18 and round(shallow[0][1], 4) == 0.0048


@pytest.mark.slow
def test_fallback_search_finds_the_near_line_zero():
    """census_1e4.offline_zeros below SIG_IN: the beta 0.50479 zero at 88132.18 is found; at SIG_IN it is not."""
    import census_1e4 as cz
    a, b = 88131.9, 88132.5
    near = cz.offline_zeros(a, b, 1, sig_in=cz.SIG_FALLBACK if not PLANT else cz.SIG_IN)
    assert any(abs(z.imag - 88132.1802) < 1e-3 and 0.5005 < z.real < 0.505 for z in near)
    assert not any(z.real < cz.SIG_IN for z in cz.offline_zeros(a, b, 1))


# ---------------------------------------------------------------------------
# 11. the census, attempt 2 on the guarded code (RESULTS.md section 8.15)
# ---------------------------------------------------------------------------

CENSUS2_SHA = "3787b389cf4c3c09365e3d3211dbb525c8be9528c773502c58871c14645d643e"
R2 = "census_runs/full_r2/"


def test_census2_merged_artifact_hash_and_shape():
    """census_runs/full_r2/census_1e5.json: the merge job's sha256; 36 shards, 170 rows, all landed."""
    import hashlib
    raw = (HERE / R2 / "census_1e5.json").read_bytes()
    if PLANT:
        raw = raw.replace(b"170", b"171", 1)     # planted: one digit changed
    assert hashlib.sha256(raw).hexdigest() == CENSUS2_SHA
    c = json.loads(raw)
    assert c["plan_sha256"] == PLAN_SHA and sorted(s["shard"] for s in c["shards"]) == list(range(36))
    assert len(c["rows"]) == 170 and all(r["landing_ode"] is not None for r in c["rows"])
    assert all(r["accounting_ok"] for r in c["rows"])
    cpu = sum(sum(s["cpu_seconds"].values()) for s in c["shards"]) / 3600
    assert round(cpu, 2) == 13.16 and cpu <= 15
    assert sum(s["n_unlocated"] for s in c["shards"]) == 0
    assert sum(s["n_relocated_by_guard"] for s in c["shards"]) == 16


def test_census2_kill_conditions_and_verdicts_recomputed():
    """census_runs/full_r2/census_1e5.json + census_1e4.json: K-b..K-e and the five 8.12 items, here."""
    rows = load(R2 + "census_1e5.json")["rows"]
    if PLANT:
        rows = rows + [dict(rows[0], landing_ode=0.0600, gamma=60000.0)]   # planted: a landing above the floor
    deep = load("census_deep4_1e5.json")["rows"]
    kd = dict(_kd(rows, deep))
    assert len(kd) == 8 and all(v is not None and v < 1e-11 for v in kd.values())        # K-d
    assert sum(not r["accounting_ok"] for r in rows) == 0                                  # K-c
    assert none_beats_floor([r["landing_ode"] for r in rows])                              # floor
    m4 = max(r["landing_ode"] for r in rows)
    m4row = max(rows, key=lambda r: r["landing_ode"])
    assert round(m4, 5) == 0.04902 and round(m4row["gamma"], 2) == 20011.16
    assert m4 < 0.05586                                                                    # KC4 does not fire
    low = [r for r in load("census_1e4.json")["rows"]]
    best = max(low + rows, key=lambda r: r["landing_ode"])
    assert best["gamma"] < 1e3                                                             # P5 refuted up to 1e5
    assert not any(r["later_than_naive"] for r in rows)   # 0 of 170 above 1e4: outside P8's registered scope, a description


def test_census2_evaluation_record():
    """census_runs/full_r2/evaluation.json: valid; verdicts as recorded; two-sided OOS rms 0.154."""
    e = load(R2 + "evaluation.json")
    if PLANT:
        e["K_d_ok"] = False      # planted: a failed replication
    assert e["census_valid"] and e["K_b_ok"] and e["K_c_ok"] and e["K_d_ok"] and e["K_e_ok"]
    assert e["verdict_floor"] == "no pair with y0 > 0.3396 in [1e4, 1e5] beats it"
    assert e["verdict_KC4"] == "does not fire up to 1e5" and e["m4_gt_m2"] is False
    assert e["verdict_P5"] == "refuted up to 1e5" and e["verdict_P8"] == "not observed"
    t = e["two_sided_oos"]
    assert t["n"] == 162 and t["n_in_band"] == 134 and round(t["rms"], 3) == 0.154
    assert e["verdict_two_sided_oos"] == "expectation met (rms < 0.160)"
    assert e["n_accounting_fallback"] == 1 and e["n_unlocated_windows"] == 0


def test_census2_extends_attempt1_by_exactly_the_missed_windows():
    """Attempt 2 contains attempt 1's 161 landings (to 1e-11) plus exactly the 9 recovered windows."""
    r1 = {round(r["gamma"], 2): r["landing_ode"] for r in load("census_runs/full_r1/census_1e5.json")["rows"]
          if r["landing_ode"] is not None}
    r2 = {round(r["gamma"], 2): r["landing_ode"] for r in load(R2 + "census_1e5.json")["rows"]}
    if PLANT:
        r2.pop(24415.48)         # planted: one attempt-1 landing lost
    assert set(r1) <= set(r2)
    assert max(abs(r2[g] / r1[g] - 1) for g in r1) < 1e-11
    assert sorted(set(r2) - set(r1)) == [15442.11, 16620.38, 20011.16, 54447.38, 65942.07,
                                         74280.37, 86726.64, 88167.4, 90724.37]
    w = load("census_runs/audit_u4/w88167_relanded.json")["landing_ode"]
    assert abs(r2[88167.4] / w - 1) < 1e-12


def test_census2_closest_to_the_floor_statement():
    """RESULTS 8.15: nothing in [1e4, 1e5] within 10 percent of the floor; the closest below 1e5 is 2442.53."""
    rows = load(R2 + "census_1e5.json")["rows"]
    low = [r for r in load("census_1e4.json")["rows"] if abs(r["gamma"] - 240.4047) > 0.01]
    if PLANT:
        rows = rows + [dict(rows[0], landing_ode=0.053)]    # planted: a decade landing within 10 percent
    assert all(r["landing_ode"] < 0.9 * FLOOR_MEASURED for r in rows)
    best = max(low + rows, key=lambda r: r["landing_ode"])
    assert round(best["gamma"], 2) == 2442.53 and round(100 * (1 - best["landing_ode"] / FLOOR_MEASURED), 1) == 3.1


# ---------------------------------------------------------------------------
# 12. review corrections (RESULTS.md section 8.16, 2026-10-26)
# ---------------------------------------------------------------------------

_NUM = r"-?\d+\.\d+"
_QUOTED = re.compile(rf"\[({_NUM}), ({_NUM})([\]\)])")


def _decided_intervals() -> list:
    """Every decided interval the record quotes, exact, from its artifact: (name, (lo, hi), closed)."""
    out = []
    d = load("decide_deep_zero.json")
    out.append(("1e6 sigma", tuple(Fraction(x) for x in d["rectangle"]["sigma"]), True))
    out.append(("1e6 t", tuple(Fraction(x) for x in d["rectangle"]["t"]), True))
    out.append(("1e6 y0", tuple(Fraction(x) for x in d["depth_y0_enclosure"]), True))
    best = None
    for r in load("decide_low_zeros.json")["rows"]:
        iv = tuple(Fraction(x) for x in r["y0_enclosure"])
        out.append((f"y0 {r['gamma_float']:.4f}", iv, True))
        best = iv if best is None or iv[0] > best[0] else best
    # P2: y_max(1e4) lies in [lower end of the deepest decided rectangle, 2/5), open at the
    # top, because decide_kc2.json + kc2/below8.json decide no zero with beta >= 0.90
    assert load("decide_kc2.json")["count"] == 0 and load("kc2/below8.json")["count"] == 0
    out.append(("y_max(1e4)", (best[0], Fraction(2, 5)), False))
    return out


def _quoted_intervals(text: str):
    """Bracketed decimal intervals with at least 8 decimals at one end: ((lo, hi, closed), raw)."""
    for m in _QUOTED.finditer(text):
        a, b, close = m.groups()
        if max(len(a.split(".")[1]), len(b.split(".")[1])) < 8:
            continue
        yield (Fraction(a), Fraction(b), close == "]"), m.group(0)


def _quote_contains(q: tuple, d: tuple) -> bool:
    """The quoted interval q contains the decided interval d (each (lo, hi, closed at the top))."""
    (qlo, qhi, qclosed), (dlo, dhi, dclosed) = q, d
    return qlo <= dlo and (dhi < qhi or (dhi == qhi and (qclosed or not dclosed)))


def _check_quotes(text: str):
    """Match each quoted interval to the decided interval it quotes (nearest, within 1e-6)."""
    decided = _decided_intervals()
    matched, bad = [], []
    for q, raw in _quoted_intervals(text):
        name, d, closed = min(decided, key=lambda x: abs(q[0] - x[1][0]) + abs(q[1] - x[1][1]))
        if abs(q[0] - d[0]) + abs(q[1] - d[1]) > Fraction(1, 10**6):
            continue                                     # not a quotation of a decided interval
        matched.append(name)
        if not _quote_contains(q, (d[0], d[1], closed)):
            bad.append((raw, name))
    return matched, bad


def test_quoted_decided_intervals_contain_the_artifact_intervals():
    """RESULTS.md and the #119 case log in hunts/README.md: every quoted decided interval is an enclosure.

    Each bracketed decimal interval that quotes a decided one (sections 8.1, 8.2,
    the 21 rows of 8.3, 8.4, the P2 row of 8.7; the case log's 1e6 depth and P2)
    must contain the exact interval in its artifact. Until 2026-10-26 (review)
    they were rounded to nearest and every one failed on at least one side.
    Planted: the 8.3 row for gamma = 240.4047 given one inward digit.
    """
    results = (HERE / "RESULTS.md").read_text()
    readme = (HERE.parent / "README.md").read_text()
    entry = readme[readme.index("**Resumed 2026-10-26 (compute sweep"):]
    entry = entry[: entry.index("\n### ")]
    if PLANT:
        row = "| 240.4047 | [0.3695305721,"
        assert row in results
        results = results.replace(row, "| 240.4047 | [0.3695305722,", 1)     # planted: one inward digit
    for text, n in ((results, 27), (entry, 2)):
        matched, bad = _check_quotes(text)
        assert not bad, bad
        assert len(matched) == n, matched
    m = re.search(r"y_max\(10\^4\) >= (\d+\.\d+)", results)     # section 8.5's one-sided bound
    assert m and Fraction(m.group(1)) <= _decided_intervals()[-1][1][0]


def test_planted_fault_quoted_interval_checker():
    """_quote_contains rejects an interval quoted to nearest where that rounds inward."""
    decided = {name: (iv, closed) for name, iv, closed in _decided_intervals()}
    (lo, hi), _ = decided["y0 240.4047"]
    assert _quote_contains((Fraction("0.3695305721"), Fraction("0.3695305871"), True), (lo, hi, True))
    assert not _quote_contains((Fraction("0.3695305722"), Fraction("0.3695305871"), True), (lo, hi, True))
    (lo, hi), _ = decided["y_max(1e4)"]
    assert _quote_contains((Fraction("0.39775014"), Fraction("0.40"), False), (lo, hi, False))
    assert not _quote_contains((Fraction("0.39775015"), Fraction("0.40"), False), (lo, hi, False))


def test_em_remainder_constant_is_covered_by_the_fudge():
    """decide_deep_zero.py docstring: the remainder constant C_p = 4 (1 - 2^-2p) zeta(2p) and the fudge.

    For the Euler-Maclaurin sum through k = p - 1 the remainder weight is
    B_2p - B~_2p(x), whose peak is (2 - 2^(1-2p)) |B_2p| (checked on a grid for
    p = 1..5). The code's constant 4 falls short of C_p at p = 293 by under 1e-279
    relative, inside the net 2^-50 - 2^-52 margin of `_upper`. Planted: the
    constant the old text cited, 2 zeta(2p), in place of the code's 4.
    """
    from mpmath import iv, mp
    import decide_deep_zero as dd
    with mp.workdps(40):
        for p in range(1, 6):
            b = mp.bernoulli(2 * p)
            peak = max(abs(mp.bernpoly(2 * p, mp.mpf(i) / 2000) - b) for i in range(2001))
            assert mp.almosteq(peak, (2 - mp.mpf(2) ** (1 - 2 * p)) * abs(b), 1e-30)
            lhs = (2 - mp.mpf(2) ** (1 - 2 * p)) * abs(b) * (2 * mp.pi) ** (2 * p) / mp.factorial(2 * p)
            assert mp.almosteq(lhs, 4 * (1 - mp.mpf(2) ** (-2 * p)) * mp.zeta(2 * p), 1e-30)
    p = int(math.ceil((128 * math.log(2) + 40) / (2 * math.log(1.25)))) + 4     # IvRoute at 128 bits
    assert p == 293 == load("decide_deep_zero.json")["routes"]["mpmath.iv"]["p"]
    with mp.workdps(700):
        cp = 4 * (1 - mp.mpf(2) ** (-2 * p)) * mp.zeta(2 * p)
        used = 2 * mp.zeta(2 * p) if PLANT else mp.mpf(4)          # planted: the old text's constant
        short = cp / used - 1
        assert short < mp.mpf(2) ** -50 - mp.mpf(2) ** -52
        assert 0 < short < mp.mpf(10) ** -279
    assert dd._upper(iv.mpf(1)) >= 1 + 2.0 ** -50 - 2.0 ** -52


def test_registered_text_keeps_the_slip_and_8_9_points_at_it():
    """MISSION.md (2026-08-18) and RESULTS.md (2026-09-12) read as registered; section 8.9 points at each.

    The in-place corrections of the y0 slip inside registered text were reverted
    on 2026-10-26 (review). The registered sentences still read 0.3695261, and
    RESULTS.md section 8.9 names each one with its correction. Planted: the P2
    edit put back.
    """
    mission = (HERE / "MISSION.md").read_text()
    results = (HERE / "RESULTS.md").read_text()
    reg_m = mission.split("\n## 8. Resumption")[0]
    reg_r = results.split("\n## 8. Resumption")[0]
    if PLANT:   # planted: the reverted in-place edit put back into the registered P2 sentence
        reg_m = reg_m.replace("For scale: `y_max(600) = 0.3695261` today,",
                              "For scale: `y_max(600) = 0.3695306` today (corrected\n  2026-10-26 from 0.3695261),")
    for s in ("best measured landing 0.05765184035 at gamma = 240.4046, y0 = 0.3695261\n",
              "| best measured landing | `0.05765184035` at `gamma = 240.4046`, `y0 = 0.3695261` | measured |",
              "anchored at\n`y_max(600) = 0.3695261`, and maximize",
              "For scale: `y_max(600) = 0.3695261` today, and the strip ceiling is"):
        assert s in reg_m, s
    for s in ("| 240.4046 | 0.3695261 | hunts/flow_repair, hunts/lambda_dh_bounds |",
              "| the depth-law anchor | y_max(600) = 0.3695261 | stage 6, sets c_p |"):
        assert s in reg_r, s
    assert "0.3695306" not in reg_m + reg_r and "2026-10-26" not in reg_m + reg_r
    s89 = results.split("### 8.9 ")[1].split("### 8.10 ")[0]
    for pointer in ("huntspec `frontier:` line", "section 0 table", "section 5.2, C3",
                    'P2, its "For scale" sentence', "section 4 table", "the depth-law anchor"):
        assert pointer in s89, pointer


def _fake_window(cz, monkeypatch, gamma: float, y0: float, tstar):
    """census_one's float instruments replaced by a closed, consistent window (4 line zeros, 1 pair)."""
    reals = [gamma - 30, gamma - 1, gamma + 1, gamma + 30]
    monkeypatch.setattr(cz, "line_zeros", lambda a, b, per_gap=60: list(reals))
    monkeypatch.setattr(cz, "count_float",
                        lambda sig_c, a, b, pts_per_unit=32: (1, 0.0) if sig_c > 0 else (len(reals) + 2, 0.0))
    monkeypatch.setattr(cz, "offline_zeros", lambda a, b, want, sig_in=None: [complex(0.5 + y0, gamma)])
    monkeypatch.setattr(cz.probe, "ode_null_control",
                        lambda *a, **k: {"tstar_ode": tstar, "slope0_ode": -1.0, "n_reals": 4, "n_pairs": 1,
                                         "window": 40.0, "rho": 1.0, "tail_term_vs_mirror": 0.0,
                                         "trajectory_Q": []})


def test_known_limit_no_crossing_reads_as_not_beating_the_floor(monkeypatch):
    """census_1e4.census_one, known limit 1 (RESULTS.md 8.16): no ODE crossing by t_end reads as not beating.

    A pair that has not landed by t_end = 1.25 y0^2/2 (above the floor for
    y0 > 0.3396) gets landing_ode None and beats_floor False. The logic is left as
    it is; the recorded censuses never hit it (every accounted row landed).
    Planted: one accounted row of attempt 2 with its landing removed.
    """
    import census_1e4 as cz
    g, y0 = 50000.0, 0.42
    assert 1.25 * y0 * y0 / 2 > FLOOR_MEASURED
    _fake_window(cz, monkeypatch, g, y0, None)
    e = cz.census_one(g, y0)
    assert e["accounting_ok"] and e["offline_located_ok"] and e["self_found"]
    assert e["landing_ode"] is None and e["beats_floor"] is False and e["later_than_naive"] is False
    _fake_window(cz, monkeypatch, g, y0, 0.03)                     # the same window with a crossing
    assert cz.census_one(g, y0)["landing_ode"] == 0.03
    rows = (load("census_1e4.json")["rows"] + load(R2 + "census_1e5.json")["rows"]
            + load("census_deep4_1e5.json")["rows"])
    if PLANT:
        rows = rows + [dict(rows[0], landing_ode=None)]            # planted: an accounted row unlanded
    assert all(r["landing_ode"] is not None for r in rows if r["accounting_ok"])


def test_known_limit_evaluation_drops_unlanded_and_unlocated(monkeypatch, tmp_path):
    """evaluate_census.main, known limits 1 and 2 (RESULTS.md 8.16), on a synthetic merged census.

    An accounted but unlanded row leaves the floor verdict at "no pair beats it"
    and passes every kill condition; an unlocated window enters none. Attempt 2
    had neither (170 of 170 landed, 0 unlocated). Planted: attempt 2 given one
    unlanded row.
    """
    import evaluate_census as ec
    deep = [r for r in load("census_deep4_1e5.json")["rows"] if r["landing_ode"] is not None]
    oos = dict(deep[0], gamma=60000.0, landing_ode=0.03)
    unlanded = dict(deep[0], gamma=70000.0, y0=0.42, landing_ode=None, accounting_ok=True)
    shards = [{"shard": i, "screen_complete": True, "n_unlocated": 1 if i == 0 else 0,
               "n_relocated_by_guard": 0, "cpu_seconds": {"census": 1.0}, "peak_rss": {"peak_gb": 0.1}}
              for i in range(36)]
    (tmp_path / "census_1e5.json").write_text(
        json.dumps({"plan_sha256": PLAN_SHA, "shards": shards, "rows": deep + [oos, unlanded]}))
    monkeypatch.setattr(ec, "RUN", str(tmp_path))
    monkeypatch.setattr(ec, "two_sided_ratio", lambda r: {"gamma": r["gamma"], "ratio": 1.0, "gate_defect": 0.0,
                                                          "d_L_over_h": 1.0, "d_R_over_h": 1.0})
    ec.main()
    e = json.loads((tmp_path / "evaluation.json").read_text())
    assert e["n_rows"] == 10 and e["n_landed"] == 9 and e["n_unaccounted"] == 0
    assert e["K_c_ok"] and e["census_valid"]
    assert e["verdict_floor"] == "no pair with y0 > 0.3396 in [1e4, 1e5] beats it"     # limit 1
    assert e["n_unlocated_windows"] == 1                                                # limit 2
    rec, merged = load(R2 + "evaluation.json"), load(R2 + "census_1e5.json")
    rows = merged["rows"] + ([dict(merged["rows"][0], landing_ode=None)] if PLANT else [])
    assert rec["n_landed"] == rec["n_rows"] == len(rows)
    assert all(r["landing_ode"] is not None for r in rows) and rec["n_unlocated_windows"] == 0
