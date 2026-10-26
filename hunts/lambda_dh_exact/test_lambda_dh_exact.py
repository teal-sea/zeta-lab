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

Grades are those of `RESULTS.md`: the two counts are decided, the landings
are measured. Nothing here bears on RH (`docs/08`).
"""
from __future__ import annotations

import importlib.util
import json
import math
import os
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
    """decide_deep_zero.json: y0 in [0.3583118516, 0.3583118665], right of the line."""
    d = load("decide_deep_zero.json")
    lo, hi = (Fraction(x) for x in d["depth_y0_enclosure"])
    assert lo == Fraction(393968047217, 2**40) and hi == Fraction(393968063601, 2**40)
    assert interval_inside((lo, hi), (Fraction("0.35831185"), Fraction("0.35831187")))
    assert f"{float(lo):.10f}" == "0.3583118516" and f"{float(hi):.10f}" == "0.3583118665"
    assert d["rectangle_right_of_half_line"] is True and d["float_datum_inside"] is True
    sl, sh = (Fraction(x) for x in d["rectangle"]["sigma"])
    assert sl > Fraction(1, 2) and sh - sl == Fraction(2, 2**27)


def test_deep_zero_planted_faults_and_cross_check():
    """decide_deep_zero.json: the faults decide 0, and Arb and iv enclosures intersect."""
    d = load("decide_deep_zero.json")
    f = d["faults"]
    assert f["python-flint"]["kappa_plus_1e-3"]["count"] == 0
    assert f["python-flint"]["rectangle_shifted_4_half_widths"]["count"] == 0
    assert f["mpmath.iv"]["rectangle_shifted_4_half_widths"]["count"] == 0
    assert len(d["cross_check"]) == 3 and all(x["intersect"] for x in d["cross_check"])


# ---------------------------------------------------------------------------
# 1b. step 2: the low screen, screen_hi
# ---------------------------------------------------------------------------

LOW_TABLE = {   # RESULTS.md section 8.3, gamma (4 dp) -> y0 enclosure (10 dp)
    "240.4047": ("0.3695305722", "0.3695305871"), "783.6530": ("0.3530014427", "0.3530014576"),
    "857.2959": ("0.3561094084", "0.3561094233"), "1092.4545": ("0.3546296115", "0.3546296264"),
    "2442.5303": ("0.3977501475", "0.3977501624"), "2887.9392": ("0.3604422750", "0.3604422899"),
    "3059.5187": ("0.3678568616", "0.3678568765"), "3214.1444": ("0.3612643316", "0.3612643465"),
    "3294.6092": ("0.3603604983", "0.3603605132"), "4237.9692": ("0.3576562361", "0.3576562510"),
    "4392.3764": ("0.3535286436", "0.3535286585"), "4935.6178": ("0.3551060613", "0.3551060762"),
    "5090.3177": ("0.3663990727", "0.3663990876"), "5833.2823": ("0.3740914934", "0.3740915083"),
    "5913.7059": ("0.3594353089", "0.3594353238"), "6113.9288": ("0.3581936447", "0.3581936596"),
    "7011.5119": ("0.3662883174", "0.3662883323"), "7909.4450": ("0.3545747216", "0.3545747365"),
    "8235.5925": ("0.3753363089", "0.3753363238"), "8561.5942": ("0.3836407511", "0.3836407660"),
    "9694.5786": ("0.3516309903", "0.3516310052"),
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
        got[f"{r['gamma_float']:.4f}"] = (f"{float(lo):.10f}", f"{float(hi):.10f}")
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
    """decide_low_zeros.json + decide_kc2.json: y_max(1e4) in [0.39775015, 0.40)."""
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


def test_verdict_P4_raises_clause_fails():
    """census_1e4.json: the best landing below 1e4 is the floor pair itself."""
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
    """census_1e4.json + census_deep4_1e5.json: 0 of 29 land later than y0^2/2."""
    a, b = _all_landed()
    assert len(a) + len(b) == 29
    assert not any(r["later_than_naive"] for r in a + b)
    assert all(r["landing_ode"] < r["landing_naive"] for r in a + b)


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
