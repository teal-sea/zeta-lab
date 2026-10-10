"""Pins for the numbers `li_dh_onset`'s `RESULTS.md`, `MISSION.md` and `RUNS.md` state.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/li_dh_onset

Written 2026-10-10, when the hunt was landed on main as #128. Until then nothing
pinned these numbers: the scripts wrote artifacts and the page quoted them. Here
the cheap ones are recomputed live (the first four coefficients, the half-plane
sum, the radius rectangles and their argument-principle counts, the xi control
and the route `scripts/18_dh_li_coefficients.py` uses at small n, the background
fit, the onset scan and the cost model off the committed tables), and the
expensive ones (the n <= 5000 tables, the zero-side box counts, the dominance
wedge) are read from the artifacts, which the 2026-10-10 reproduction recorded in
`RUNS.md` regenerated and compared. Where a stated number did not reproduce, the
test pins what does and the page says so at the point of use.

Nothing writes into the tree: the two scripts whose whole output is compared here
run with their artifact directory redirected to a temporary one.

Nothing here is evidence about the Riemann Hypothesis (`docs/08`).
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import pytest
from mpmath import mp

from hunts.li_dh_onset import ceiling as C
from hunts.li_dh_onset import defect_check as D
from hunts.li_dh_onset import dhli
from hunts.li_dh_onset import dominance as DOM
from hunts.li_dh_onset import onset as O
from hunts.li_dh_onset import radius_scan as RS
from hunts.li_dh_onset import zero_side as Z
from zeta.epstein import completed_dh, count_zeros_box, dh_mean_value_defect, dh_theta
from zeta.li import _roots_of_unity, _unwrapped_log

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ART = HERE / "artifacts"

T2000 = ART / "lambda_dh_n2000_r0.9.json"
T5000 = ART / "lambda_dh_n5000_r0.95.json"
TXI = ART / "lambda_xi_n2000_r0.9.json"
XI_REFERENCE = ROOT / "data" / "li_lambda_dps25_methodcauchy_n400_radius0.5.json"

#: RESULTS.md, "the first four coefficients, at dps 25".
FIRST_FOUR = (
    "0.09763614680951967118155",
    "0.3888255141255960075677",
    "0.8684689300375514689369",
    "1.528259116943152270966",
)


@pytest.fixture(autouse=True)
def _restore_mpmath_precision():
    """`dhli._worker_init` sets `mp.dps` globally when it samples in-process
    (processes = 1), as the hunt's scripts do; put it back after every test so
    no test reads another's precision."""
    saved = mp.prec
    yield
    mp.prec = saved


def _json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _text(name: str) -> str:
    return (HERE / name).read_text(encoding="utf-8")


def _table(path: Path) -> list[str]:
    return _json(path)["lambda"]


def _close(a, b, rel: float = 1e-9) -> bool:
    """Recursive comparison of two JSON trees: ints and strings exact, floats to rel."""
    if isinstance(a, dict):
        return isinstance(b, dict) and a.keys() == b.keys() and all(
            _close(a[k], b[k], rel) for k in a
        )
    if isinstance(a, list):
        return isinstance(b, list) and len(a) == len(b) and all(
            _close(x, y, rel) for x, y in zip(a, b)
        )
    if isinstance(a, float) or isinstance(b, float):
        if a is None or b is None:
            return a is b
        return math.isclose(float(a), float(b), rel_tol=rel, abs_tol=1e-12)
    return a == b


# --- the first coefficients, recomputed -------------------------------------


def test_first_four_coefficients_recomputed_by_the_cauchy_route():
    lam = dhli.li_coefficients_cauchy("dh", 4, dps=25, radius="0.5", processes=1)
    got = tuple(mp.nstr(v, 22) for v in lam)
    assert got == FIRST_FOUR
    rows = _json(ART / "definition_defect.json")["rows"]
    assert tuple(r["cauchy"] for r in rows) == FIRST_FOUR
    text = _text("RESULTS.md")
    for n, value in enumerate(FIRST_FOUR, start=1):
        assert f"lambda_{n}(DH) = {value}" in text


def _script_18_route(n_max: int = 24, dps: int = 15, radius: str = "0.4") -> list:
    """`scripts/18_dh_li_coefficients.py`'s contour_lambdas, with the reference
    evaluator `zeta.epstein.completed_dh` rather than `dhli.completed_dh_fast`.

    That script has computed lambda_n(DH) for n <= 24 on main since 2026-08-05,
    so this is both the evaluator cross-check and the comparison with the tree's
    earlier numbers that RESULTS.md's 2026-10-10 note records.
    """
    guard = 10
    decay = float(mp.log10(1 / mp.mpf(radius)))
    work = int(dps + 2 * guard + n_max * decay)
    with mp.workdps(work):
        R = mp.mpf(radius)
        n_points = int(mp.ceil(work * mp.log(10) / mp.log(1 / R))) + n_max + 8
        w = _roots_of_unity(n_points)
        vals = _unwrapped_log([completed_dh(1 / (1 - R * wj), dps=30) for wj in w])
        out = []
        for n in range(1, n_max + 1):
            acc = mp.fsum(vals[j] * w[(-(j * n)) % n_points] for j in range(n_points))
            out.append(n * mp.re(acc * mp.power(R, -n) / n_points))
    return out


def test_the_reference_evaluator_and_the_script_18_route_agree_with_the_table():
    mine = _script_18_route()
    table = _table(T2000)
    with mp.workdps(30):
        worst = max(abs(mine[i] - mp.mpf(table[i])) / mp.mpf(table[i]) for i in range(24))
    assert worst < mp.mpf("1e-12"), worst


def test_xi_positive_control_at_small_n_and_its_docstring_values():
    lam = dhli.li_coefficients_cauchy("xi", 60, dps=25, radius="0.9", processes=1)
    ref = _json(XI_REFERENCE)["values"]
    with mp.workdps(35):
        worst = max(abs(mp.mpf(lam[i]) - mp.mpf(ref[i])) / max(abs(mp.mpf(ref[i])), 1)
                    for i in range(60))
    assert worst < mp.mpf("1e-26"), worst
    assert mp.nstr(lam[0], 22) == "0.02309570896612103381431"
    assert mp.nstr(lam[49], 16) == "43.53109648837402"
    radii = _json(ART / "controls.json")["xi_positive_control"]["radii"]
    assert [(r["radius"], r["work_digits"], r["n_points"]) for r in radii] == [
        ("0.5", 166, 960), ("0.9", 64, 1807)]
    assert {r["worst_relative_vs_committed_table"] for r in radii} == {"4.4174238e-28"}
    assert {r["lambda_300"] for r in radii} == {"519.7019656192496"}
    assert "λ_300 = 519.7019656192" in (ROOT / "zeta" / "li.py").read_text(encoding="utf-8")


def test_fast_evaluator_matches_the_reference_on_the_contour():
    R = mp.mpf("0.9")
    with mp.workdps(45):
        for j in (0, 1, 3, 6):
            s = 1 / (1 - R * mp.expjpi(mp.mpf(2 * j) / 12))
            fast, ref = dhli.completed_dh_fast(s), completed_dh(s, 45)
            assert abs(fast - ref) / abs(ref) < mp.mpf("1e-40")
    # round-off level, history dependent (RESULTS.md note): magnitude only
    assert abs(dh_mean_value_defect(mp.mpf("1.001"), "0.25", 30)) < mp.mpf("1e-49")
    ev = _json(ART / "controls.json")["evaluator_control"]
    assert ev["worst_relative_fast_vs_reference"] == pytest.approx(6.64806e-46)
    assert ev["functional_equation_defects_dps40"] == ["0.0"] * 4
    assert ev["mean_value_defect_at_1.001_dps30"] == "1.33641e-51"


@pytest.mark.slow
def test_lambda_1_by_the_closed_form_route():
    """The third route, about 20 s: -log(pi/5)/2 - euler/2 + f'(1)/f(1)."""
    cf = D.closed_form_lambda1(30)
    with mp.workdps(40):
        assert abs(mp.re(cf) - mp.mpf(FIRST_FOUR[0])) < mp.mpf("1e-22")
    assert _json(ART / "definition_defect.json")["lambda_1_closed_form_defect"] == "2.04931e-28"


def test_literal_definition_defects_as_recorded():
    rows = _json(ART / "definition_defect.json")["rows"]
    assert [r["abs_defect"] for r in rows] == ["2.04931e-28", "2.34049e-27",
                                              "4.25078e-27", "3.69223e-27"]
    assert all(r["literal_definition"] == r["cauchy"] for r in rows)
    assert max(float(r["abs_defect"]) for r in rows) < 4.3e-27


# --- the radius ---------------------------------------------------------------


def test_half_plane_sum_and_where_it_reaches_one():
    stored = {row["sigma"]: row for row in _json(ART / "radius_scan.json")["half_plane"]}
    for sigma in (2.0, 1.5):
        live = RS.half_plane_bound(sigma)
        for key in ("tail_hurwitz", "tail_partial_sum_to_4000", "margin"):
            assert live[key] == stored[sigma][key], (sigma, key)
    assert stored[2.0]["tail_hurwitz"] == "0.2666639461309748574"
    assert stored[2.0]["tail_partial_sum_to_4000"] == "0.26653553822880422209"
    # The door's "the cap could come down to about 1.55": 1.55 is admissible,
    # but the sum reaches 1 only at sigma = 1.3951 (RESULTS.md, 2026-10-10 note).
    with mp.workdps(30):
        root = mp.findroot(lambda s: mp.mpf(RS.half_plane_bound(s, 30)["tail_hurwitz"]) - 1, 1.3)
    assert 1.395 < root < 1.396
    assert float(RS.half_plane_bound(1.55)["tail_hurwitz"]) < 1


def test_apollonius_geometry_and_the_rectangles():
    assert dhli.apollonius_disc(0.9) == pytest.approx((5.263157894736842, 4.736842105263158))
    assert dhli.apollonius_disc(0.95) == pytest.approx((10.256410256410254, 9.74358974358974))
    assert dhli.modulus_floor_for_radius(0.9) == pytest.approx(10.0)
    legs = {leg["radius"]: leg for leg in _json(ART / "radius_scan.json")["radius_legs"]}
    for r, rect in ((0.9, (0.5203, 3.5036)), (0.95, (0.50682, 5.2439))):
        left, right, half = dhli.disc_bounding_box(r, sigma_cap=2.0)
        assert legs[r]["disc_box_with_re_le_2"] == pytest.approx([left, right, half])
        assert round(left - 0.006, len(str(rect[0])) - 2) == rect[0]
        assert round(half + 0.07, 4) == rect[1]
        assert legs[r]["scanned"]["zeros"] == 0 and legs[r]["admissible"]
    # MISSION.md: "[0.526, 2] x [-3.44, 3.44]" for r = 0.9, before padding
    left, _, half = dhli.disc_bounding_box(0.9)
    assert (round(left, 3), round(half, 2)) == (0.526, 3.43)


def test_both_radius_rectangles_hold_no_zero_by_the_argument_principle():
    for leg in _json(ART / "radius_scan.json")["radius_legs"]:
        lo_s, hi_s, lo_t, hi_t = leg["scanned"]["rect"]
        assert count_zeros_box(mp.mpc(lo_s, lo_t), mp.mpc(hi_s, hi_t), dps=20) == 0


def test_the_recorded_scans_are_empty_where_the_page_says():
    scan = _json(ART / "radius_scan.json")
    assert [r["rect"][:2] for r in scan["tall_scan"]] == [[1.0001, 4.0]] * 6
    assert scan["tall_scan"][-1]["rect"][3] == 120.0
    assert all(r["zeros"] == 0 for r in scan["tall_scan"])
    census = scan["offline_census"]
    assert [c["excess"] for c in census] == [0] * 8 + [2]
    assert (census[-1]["t_lo"], census[-1]["t_hi"]) == (80.0, 90.0)


# --- the tables -----------------------------------------------------------------


def test_tables_are_positive_and_bit_identical_over_their_common_range():
    a, b = _json(T2000), _json(T5000)
    assert a["lambda"] == b["lambda"][:2000]
    for blob, n, work, nodes in ((a, 2000, 142, 5112), (b, 5000, 162, 12281)):
        assert len(blob["lambda"]) == n
        assert (blob["work_digits"], blob["n_points"]) == (work, nodes)
        assert dhli.work_digits(n, 30, blob["radius"]) == work
        assert dhli.node_count(n, work, blob["radius"]) == nodes
        values = [float(v) for v in blob["lambda"]]
        assert min(values) > 0 and values.index(min(values)) == 0
        assert blob["all_positive"] and blob["min_index"] == 1
    assert (a["seconds_sampling"], a["seconds_extraction"]) == (502.6, 124.1)
    assert (b["seconds_sampling"], b["seconds_extraction"]) == (1006.9, 464.6)
    assert round(b["seconds_sampling"] + b["seconds_extraction"]) == 1472
    text = _text("RESULTS.md")
    assert "lambda_2000(DH) = " + a["lambda"][-1] in text
    assert "lambda_5000(DH) = " + b["lambda"][-1] in text
    assert "lambda_200(DH)  = 467.6848865502381460808" in text
    with mp.workdps(30):
        assert mp.nstr(mp.mpf(b["lambda"][199]), 22) == "467.6848865502381460808"


def test_radius_independence_as_recorded():
    ri = _json(ART / "controls.json")["radius_independence"]
    assert ri["passed"] and {p["worst_relative"] for p in ri["pairwise"]} == {"0.0"}
    assert set(ri["lambda_n_max_by_radius"].values()) == {"467.6848865502381460808"}
    par = _json(ART / "controls.json")["parallel_identity"]
    assert par["samples_bit_identical"] and par["coefficients_bit_identical"]


def test_the_conductor_shows_up_in_the_xi_difference():
    dh, xi = _table(T2000), _table(TXI)
    diff = [float(dh[i]) - float(xi[i]) - (i + 1) / 2 * math.log(5) for i in range(2000)]
    assert round(min(diff), 2) == -16.89
    assert round(max(diff), 2) == 21.83
    assert round(sum(diff) / len(diff), 2) == -1.54


# --- the background and the onset ---------------------------------------------


def test_onset_script_reproduces_onset_json(tmp_path, monkeypatch):
    monkeypatch.setattr(O, "ART", str(tmp_path))
    monkeypatch.setattr(sys, "argv", ["onset.py", "--table", str(T5000), "--n-hi", "3000000"])
    O.main()
    live = json.loads((tmp_path / "onset.json").read_text(encoding="utf-8"))
    stored = _json(ART / "onset.json")
    live.pop("generated"), stored.pop("generated")
    assert _close(live, stored, rel=1e-9)


def test_the_background_fit_numbers_on_the_page():
    fit = _json(ART / "onset.json")["background_fit"]
    assert fit["window"] == [2500, 5000]
    assert round(fit["a_pinned_half"]["b"], 5) == -0.32530
    assert O.B_PREDICTED == pytest.approx(-0.32561174453685604, abs=1e-15)
    assert round(fit["a_pinned_half"]["b"] - O.B_PREDICTED, 5) == 0.00031
    assert round(fit["a_pinned_half"]["rms_residual"], 2) == 6.69
    assert round(fit["free"]["a"], 6) == 0.501894
    assert round(O.B_ZETA, 4) == -1.1303
    assert round(O.B_PREDICTED - O.B_ZETA, 3) == 0.805
    envelope = _json(ART / "onset.json")["residual_envelope_vs_fitted_background"][-1]
    assert (round(envelope["min"], 2), round(envelope["max"], 2)) == (-18.88, 18.42)


def test_first_negative_index_and_its_variants():
    on = _json(ART / "onset.json")["onset"]
    for key in ("measured_background_all_quadruples",
                "measured_background_dominant_quadruple_only",
                "measured_background_lower_fit_window",
                "derived_background_all_quadruples"):
        assert on[key]["first_negative_n"] == 328997, key
    assert on["zeta_shaped_background_all_quadruples"]["first_negative_n"] == 325229
    top = on["measured_background_all_quadruples"]
    assert round(top["value_there"], 1) == -2216.9
    assert round(top["background_there"], 1) == 1982732.9
    assert round(100 * on["dip_depth_as_fraction_of_background"], 3) == 0.112
    assert round(328997 / 5000) == 66


def test_sensitivity_and_what_533_measures():
    sens = _json(ART / "onset.json")["sensitivity"]
    by_b = {r["delta_b"]: r["first_negative_n"] for r in sens if "delta_b" in r}
    assert by_b == {-0.05: 328469, -0.02: 328995, 0.02: 328999, 0.05: 329002}
    # "moves by at most 533": 533 is the spread of the two extremes; the largest
    # single displacement from 328997 is 528 (RESULTS.md, 2026-10-10 note).
    assert max(by_b.values()) - min(by_b.values()) == 533
    assert max(abs(v - 328997) for v in by_b.values()) == 528
    by_a = sorted(r["first_negative_n"] for r in sens if "delta_a" in r)
    assert by_a == [328996, 328998]
    by_r = sorted(r["first_negative_n"] for r in sens
                  if "relative_delta_log_R_of_dominant_pair" in r)
    assert by_r == [321997, 336005]


def test_against_the_prior_datum():
    """RESULTS.md says the estimate moves by 1.2 per cent from jensen_clock's.

    jensen_clock recorded 330342 (`results.json`, rounded to 3.3e5 on its page);
    328997 is 0.41 per cent below that. The 1.2 per cent is the gap to this hunt's
    own zeta-shaped variant, 325229. Pinned both ways; the page carries the note.
    """
    prior = _json(ROOT / "hunts" / "jensen_clock" / "results.json")
    found = []

    def walk(node):
        if isinstance(node, dict):
            for k, v in node.items():
                if k == "dh_pair1_predicted_onset_n":
                    found.append(v)
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(prior)
    assert found == [330342]
    assert round(100 * (330342 - 328997) / 330342, 2) == 0.41
    assert round(100 * (328997 - 325229) / 325229, 2) == 1.16


def test_quadruple_identity_and_growth_table():
    pair1 = Z.offline_quadruples()[0]
    with mp.workdps(40):
        rho = mp.mpc(mp.mpf(pair1["beta"]), mp.mpf(pair1["gamma"]))
        sig = 1 - rho
        assert abs((1 - 1 / rho) * (1 - 1 / sig) - 1) < mp.mpf("1e-38")
        g = Z.quadruple_growth(pair1["beta"], pair1["gamma"])
        n = 1000
        four = sum(1 - mp.power(1 - 1 / z, n) for z in (rho, mp.conj(rho), sig, mp.conj(sig)))
        closed = 4 - 2 * (g["R"] ** n + g["R"] ** -n) * mp.cos(n * g["psi"])
        assert abs(mp.re(four) - closed) < mp.mpf("1e-30")
    rows = {r["label"]: r for r in _json(ART / "onset.json")["quadruples_by_growth"]}
    assert len(rows) == 15
    for label, rm1, psi, period in (("pair1", 4.2006164e-05, -0.0116684165, 538.5),
                                    ("pair2", 1.1572523e-05, -0.0087593078, 717.3),
                                    ("pair4", 7.1822338e-06, -0.0056592065, 1110.3),
                                    ("pair5", 6.3938591e-06, -0.0041596371, 1510.5)):
        assert float(f"{rows[label]['R_minus_1']:.7e}") == rm1
        assert round(rows[label]["psi"], 10) == psi
        assert round(rows[label]["period_in_n"], 1) == period
    ranked = _json(ART / "onset.json")["quadruples_by_growth"]
    assert ranked[0]["label"] == "pair1"


def test_dominance_arithmetic():
    dom = _json(ART / "dominance.json")
    rows = sorted(
        (Z.quadruple_growth(q["beta"], q["gamma"]) for q in Z.offline_quadruples()),
        key=lambda g: -float(g["R_minus_1"]))
    R1 = float(rows[0]["R"])
    k = R1 * R1 - 1.0
    assert math.sqrt(3.0 / k) == pytest.approx(dom["gamma_above_which_the_strip_bound_suffices"])
    assert round(math.sqrt(3.0 / k), 2) == 188.97
    for row in dom["threshold_curve"]:
        assert DOM.threshold_beta(row["gamma"], k) == pytest.approx(row["threshold_beta"])
    assert round(DOM.threshold_beta(90, k), 4) == 0.8403
    assert dom["wedge_clear"] and len(dom["wedge_boxes"]) == 5
    assert dom["wedge_boxes"][0]["rect"][:3] == [0.83, 2.0, 90.0]
    assert dom["wedge_boxes"][-1]["rect"][3] == 190.0


# --- the cost model ------------------------------------------------------------------


def test_ceiling_script_reproduces_ceiling_json(tmp_path, monkeypatch):
    monkeypatch.setattr(C, "ART", str(tmp_path))
    C.main()
    live = json.loads((tmp_path / "ceiling.json").read_text(encoding="utf-8"))
    stored = _json(ART / "ceiling.json")
    live.pop("generated"), stored.pop("generated")
    assert _close(live, stored, rel=1e-12)


def test_the_cost_numbers_on_the_page():
    assert round(C.best_radius(20000, [0.8, 0.85, 0.9, 0.95, 0.97, 0.98, 0.99])["total_h"], 1) == 3.7
    onset = C.predict(328997, 0.99)
    assert (onset["work"], onset["nodes"]) == (1487, 669685)
    assert round(onset["total_h"], -3) == 20000
    assert round(C.predict(5000, 0.99)["total_h"], 2) == 0.24
    assert round(C.predict(5000, 0.95)["total_h"], 2) == 0.59
    # Not reproduced, recorded in RESULTS.md and RUNS.md on 2026-10-10:
    assert round(C.predict(5000, 0.9)["total_h"], 2) == 1.45   # page: "model 0.99 h"
    w = 162
    assert math.ceil(w * math.log(10) / math.log(1 / 0.95)) == 7273   # page: 7227
    full = C.predict(5000, 0.95)["sampling_s"]
    L = math.log10(1 / 0.95)
    w15 = math.ceil(15 + 20 + 5000 * L)
    n15 = math.ceil(w15 * math.log(10) / math.log(1 / 0.95)) + 5008
    saved = 1 - n15 * C.C_REF * (w15 / C.W_REF) ** C.C_EXP / full
    assert round(100 * saved) == 22                                  # page: "about 9 per cent"
    tenk = C.predict(10000, 0.95)["total_h"]
    assert (round(tenk, 2), round(tenk / 3, 2)) == (3.52, 1.17)     # RUNS.md: "3 h", "1.1 h"
    # The calibration's own two points give an exponent of 1.85, not 1.97.
    assert round(math.log(0.3226 / 0.0924) / math.log(279 / 142), 2) == 1.85
    # "Doubling n_max at fixed r costs about eightfold" is the asymptote; the model:
    for r, factor in ((0.95, 6.0), (0.9, 7.0)):
        assert round(C.predict(10000, r)["total_h"] / C.predict(5000, r)["total_h"], 1) == factor


# --- the zero side --------------------------------------------------------------------


def test_zero_side_completeness_and_the_smooth_count():
    zs = _json(ART / "zero_side.json")
    assert zs["n_line_ordinates"] == 313 and len(zs["quadruples"]) == 15
    rows = {c["t_max"]: c for c in zs["completeness"]}
    for t, box, line, quads in ((100.0, 54, 52, 1), (200.0, 130, 122, 4),
                                (300.0, 214, 204, 5), (430.0, 331, 313, 9)):
        c = rows[t]
        assert (c["box"], c["line_found"], c["offline_quadruples_below"]) == (box, line, quads)
        assert c["unaccounted"] == 0 and c["accounted"] == line + 2 * quads == box
        with mp.workdps(30):
            smooth = float(dh_theta(t, 30) / mp.pi)
        assert smooth == pytest.approx(c["smooth_count_theta_over_pi"], rel=1e-12)
    assert [round(rows[t]["measured_minus_smooth"], 3) for t in (100.0, 200.0, 300.0, 430.0)] == [
        0.133, 0.327, 0.193, -0.040]
    assert [round(rows[t]["smooth_count_theta_over_pi"], 3) for t in (100.0, 200.0, 300.0, 430.0)] == [
        53.867, 129.673, 213.807, 331.040]


def test_zero_side_against_the_cauchy_table():
    zs = _json(ART / "zero_side.json")["zero_side"]["values"]
    cauchy = _table(T2000)
    rel = {n: abs(float(cauchy[n - 1]) - float(zs[str(n)])) / float(cauchy[n - 1])
           for n in (1, 4, 8, 12)}
    assert {n: float(f"{v:.2e}") for n, v in rel.items()} == {
        1: 9.37e-09, 4: 9.58e-09, 8: 1.03e-08, 12: 1.14e-08}
    assert max(rel.values()) < 1.15e-8


def test_the_first_line_ordinates_recomputed():
    """The ten ordinates zero_side.json stores, by sign change and bisection.

    The full list to height 430 took 29 minutes in the 2026-10-10 re-run and is
    checked there (`RUNS.md`); here only the stored head, with a scan that stops
    at 28.5 and so uses a finer step than the full run, which is why the match is
    to 1e-12 and not to the 20 printed digits.
    """
    stored = _json(ART / "zero_side.json")["first_line_ordinates"]
    live = Z.line_ordinates(28.5)
    assert len(live) == 10
    for g, ref in zip(live, stored):
        assert abs(g - mp.mpf(ref)) < mp.mpf("1e-12") * mp.mpf(ref)


# --- planted faults: each check above can go red ----------------------------------


def test_planted_fault_wrong_conductor_moves_lambda_1(monkeypatch):
    """A completion with pi/4 in place of pi/5 is a neighbouring normalisation the
    zero-free contour would not notice; the pinned lambda_1 does."""
    def wrong(s):
        return mp.power(mp.pi / 4, -(s + 1) / 2) * mp.gamma((s + 1) / 2) * dhli._dh_raw(s)

    monkeypatch.setitem(dhli.EVALUATORS, "dh", wrong)
    lam = dhli.li_coefficients_cauchy("dh", 2, dps=20, radius="0.5", processes=1)
    assert abs(lam[0] - mp.mpf(FIRST_FOUR[0])) > mp.mpf("1e-3")


def test_planted_fault_the_scan_floor_is_what_stops_a_sign_change_at_n_1():
    """The degeneracy onset.py guards against: a fitted background read at n = 1."""
    rows = O.growths(Z.offline_quadruples())
    unguarded = O.first_negative(O.B_ZETA, 1.0, rows, 10, n_lo=1)
    assert unguarded["first_negative_n"] == 1
    guarded = O.first_negative(O.B_ZETA, 1.0, rows, 10000, n_lo=5000)
    assert guarded["first_negative_n"] is None


def test_planted_fault_the_xi_control_rejects_the_wrong_function():
    lam = dhli.li_coefficients_cauchy("dh", 4, dps=25, radius="0.5", processes=1)
    ref = _json(XI_REFERENCE)["values"]
    assert abs(lam[0] - mp.mpf(ref[0])) > mp.mpf("0.07")
