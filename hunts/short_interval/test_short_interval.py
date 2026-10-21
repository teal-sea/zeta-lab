"""The numbers hunt #141 (`short_interval/`) states, pinned so a drift is seen.

Runs beside the hunt, one pytest process per directory
(`scripts/run_hunt_tests.py`). Nothing here is a result and nothing here
bears on RH (`docs/08`). Every check reads or recomputes; none writes into
the tree, so `enclose_theta.py`'s artifact is re-evaluated, never rewritten.

What is pinned, and at what grade:

1. `verify.py`: the constants of Wang arXiv:2609.07918 and Lamzouri
   arXiv:2609.02882 that the hunt cites (float grade; the script raises on any
   drift), and the copy of `hunts/frontier_map/frontier.py:zeta_H_closed`
   inside it, which its docstring asks this file to compare with the source.
2. `enclose_theta.py`: each lower bound in `artifacts/enclose-theta.json`,
   re-evaluated in exact rational arithmetic from its committed rational
   window, plus the run's controls (hardened grade: exact rationals and a
   proved series tail; ball arithmetic only for Wang's transcendental
   `c(theta)` in the zeta control).
3. `landscape.py`: the float-grade landscape table, the Alpoge-Furman
   calibration, the vacuity thresholds, every cell of the band-edge price
   table, and the method-error and derived figures that `MISSION.md` and the
   case log quote.
4. `ceiling_theta.py`: the cheapest rung recomputed and compared with the
   committed checkpoint, and the ladder values `RESULTS.md` section 8 quotes.
5. Two figures that were quoted wrong and corrected on 2026-10-21 (the series
   tail constant `rho_M` in `RESULTS.md` section 9, and the band-edge gain in
   the case log), read from the documents themselves so the corrected value
   stays the one printed; and the `2 * T` count in the bridge that finding two
   quotes.

Counts and figures the hunt quotes from its audits, its search logs, papers
or other hunts are cited, not recomputed, and are not pinned here.
"""

from __future__ import annotations

import importlib.util
import json
import re
import sys
from fractions import Fraction
from math import e, exp, sqrt, tan
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ARTIFACTS = HERE / "artifacts"

#: The bandwidth-one configuration ceiling and the Montgomery-Taylor optimum,
#: as quoted (the ceiling from `Zeta23/PairCeiling/`, not recomputed here).
CEILING_ONE = 0.6818286874638
MT_OPTIMUM = 0.6725007036794116


def _load(name: str, path: Path):
    """Import a file under a unique module name, so no hunt's `verify` collides."""
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


verify = _load("short_interval_verify", HERE / "verify.py")
landscape = _load("short_interval_landscape", HERE / "landscape.py")
enclose = _load("short_interval_enclose_theta", HERE / "enclose_theta.py")

ENCLOSE = json.loads((ARTIFACTS / "enclose-theta.json").read_text(encoding="utf-8"))
ROWS = ENCLOSE["rows"]


def _row(theta: str, kernel: str) -> dict:
    (row,) = [r for r in ROWS if r["theta"] == theta and r["kernel"] == kernel]
    return row


def _case_log_entry() -> str:
    """This hunt's entry in `hunts/README.md`, found by directory, not number."""
    text = (ROOT / "hunts" / "README.md").read_text(encoding="utf-8")
    (entry,) = [s for s in text.split("\n### ")
                if s.startswith("Hunt #") and "(`short_interval/`" in s.splitlines()[0]]
    return entry


@pytest.fixture(scope="module")
def forms():
    return enclose.build_forms()


# ---------------------------------------------------------------------------
# 1. verify.py
# ---------------------------------------------------------------------------


def test_verify_reproduces_every_constant_the_papers_print(capsys) -> None:
    verify.main()  # raises SystemExit naming the drift
    assert "all cross-checks passed" in capsys.readouterr().out


@pytest.fixture(scope="module")
def frontier():
    return _load("frontier_map_frontier", ROOT / "hunts" / "frontier_map" / "frontier.py")


@pytest.mark.parametrize("lam", [0.50, 0.55, 0.60, 0.75, 0.90, 1.00])
def test_the_landscape_copy_in_verify_still_matches_frontier_py(lam: float, frontier) -> None:
    assert abs(verify.lab_landscape(lam) - frontier.zeta_H_closed(lam)) <= 1e-15
    assert abs(frontier.zeta_H_closed(lam) - verify.c_simple(lam)) <= 1e-14


def test_the_bridge_diagnostic_of_finding_two() -> None:
    """`Phi_3` in the coordinate `R = 2 - c`: `R -> 1.001343 R - 0.002019`.

    A relative 0.134% of the second moment against a fixed absolute gain,
    break-even at `R = 1.5037`, that is `theta = 0.8082` (MISSION.md section 4).
    """
    slope = verify.bridge("Phi_3", 1.0) - verify.bridge("Phi_3", 0.0)
    intercept = verify.bridge("Phi_3", 0.0)
    assert abs(slope - 1.001343) <= 5e-7
    assert abs((2 - 2 * slope - intercept) - (-0.002019)) <= 1e-6
    breakeven = -intercept / (slope - 1)
    assert abs((2 - breakeven) - 1.5037) <= 5e-5
    theta = verify._bisect(lambda t: verify.c_simple(t) - breakeven, 0.56, 0.999)
    assert abs(theta - 0.8082) <= 5e-5


def test_the_shadow_price_of_bandwidth_at_one() -> None:
    """`c'(1) = (1/2) cot^2(1/sqrt 2) = (3/2 - H)^2`, MISSION.md section 13."""
    h = verify.c_simple(1.0)
    assert abs(verify.c_prime(1.0) - (1.5 - h) ** 2) <= 1e-12
    assert abs(verify.c_prime(1.0) - 0.6847550854111) <= 1e-12


# ---------------------------------------------------------------------------
# 2. enclose_theta.py
# ---------------------------------------------------------------------------


def test_the_artifact_records_a_passing_run_over_ten_bandwidths() -> None:
    assert ENCLOSE["all_controls_pass"] is True
    assert len(ROWS) == 20
    assert {r["kernel"] for r in ROWS} == {"zeta", "xiprime"}


def test_the_exact_moments_agree_with_sympy(forms) -> None:
    checks = enclose.sympy_selfcheck(*forms)
    assert checks and all(c["agrees_with_sympy"] for c in checks)


@pytest.mark.parametrize("row", ROWS, ids=lambda r: f"{r['kernel']}-{r['theta']}")
def test_each_bound_re_evaluates_exactly_from_its_committed_window(row: dict, forms) -> None:
    P, b, G = forms
    theta = Fraction(row["theta"])
    window = [Fraction(x) for x in row["window_coefficients_s_monomials"]]
    R, tail = enclose.exact_R(theta, row["kernel"], window, P, b, G)
    bound = 2 - R - tail
    assert enclose.frac_str(R) == row["R_exact_truncated_series"]
    assert enclose.frac_str(tail) == row["tail_upper_bound"]
    assert enclose.frac_str(bound) == row["lower_bound_exact"]
    assert enclose.trunc_down(bound) == row["lower_bound_truncated_down"]


def test_the_flat_window_gives_the_closed_form_for_zeta_exactly(forms) -> None:
    P, b, G = forms
    for row in ROWS:
        lam = Fraction(row["theta"])
        R, tail = enclose.exact_R(lam, "zeta", enclose.FLAT, P, b, G)
        assert R == 1 / lam + lam / 3 and tail == 0


@pytest.mark.parametrize("theta", sorted({r["theta"] for r in ROWS}))
def test_the_zeta_bound_sits_below_wang_and_within_6e_12(theta: str) -> None:
    """Control (i): a one-window bound can never exceed the optimum c(theta).

    Also the stored enclosure width, `1e-30`, that RESULTS.md section 9 quotes:
    both ends are kept to thirty decimals, the upper one padded upward.
    """
    row = _row(theta, "zeta")
    bound = Fraction(row["lower_bound_exact"])
    lo, hi, _backend = enclose.wang_enclosure(Fraction(theta))
    assert bound <= lo
    assert hi - bound <= Fraction(61, 10**13)
    stored = row["control_wang"]
    stored_lo = Fraction(stored["c_theta_enclosure_lower"])
    stored_hi = Fraction(stored["c_theta_enclosure_upper"])
    assert stored_lo <= lo and hi <= stored_hi
    assert stored_hi - stored_lo == Fraction(1, 10**30)


def test_the_published_windows_at_bandwidth_one_reproduce(forms) -> None:
    """Control (ii): Alpoge-Furman Remark 7.1, quartic 0.86864 and flat 0.85838.

    The twelve-decimal values are the ones RESULTS.md section 9 prints.
    """
    P, b, G = forms
    for window, published, printed in ((enclose.QUARTIC, enclose.AF_QUARTIC, "0.868640515166"),
                                       (enclose.FLAT, enclose.AF_FLAT, "0.858384054709")):
        R, tail = enclose.exact_R(Fraction(1), "xiprime", window, P, b, G)
        assert 2 - R - tail >= published
        assert enclose.trunc_down(2 - R - tail) == printed


def test_the_float_landscape_lies_above_the_enclosed_bounds() -> None:
    """Control (iii), and the gaps RESULTS.md section 9 quotes."""
    expected_gap = {Fraction(55, 100): 3.7e-6, Fraction(60, 100): 4.4e-6,
                    Fraction(80, 100): 9.9e-6}
    for theta, value in enclose.LANDSCAPE_XIPRIME.items():
        bound = Fraction(_row(enclose.frac_str(theta), "xiprime")["lower_bound_exact"])
        gap = float(Fraction(value) - bound)
        assert gap > 0
        assert abs(gap - expected_gap[theta]) <= 1e-7


def test_the_quoted_xiprime_bounds_and_tail() -> None:
    """The two end rows the case log quotes, and the series tail RESULTS.md quotes."""
    top, bottom = _row("1/1", "xiprime"), _row("11/20", "xiprime")
    assert top["lower_bound_truncated_down"] == "0.868641500514"
    assert bottom["lower_bound_truncated_down"] == "0.130258286830"
    assert 1.5e-20 < top["tail_upper_bound_float"] < 1.7e-20
    assert 1.0e-31 < bottom["tail_upper_bound_float"] < 1.2e-31
    assert Fraction(top["lower_bound_exact"]) <= Fraction(enclose.LAB_H_STAR)
    # "sits 1.6e-11 below the laboratory's full-window H*" (RESULTS.md section 9)
    assert abs((enclose.LAB_H_STAR - float(Fraction(top["lower_bound_exact"]))) - 1.6e-11) <= 5e-13


#: The first transcription of rho_M in RESULTS.md section 9, which lost 18
#: digits of its denominator. It stays visible beside its dated correction.
_RHO_SUPERSEDED = Fraction(45088768, 2828846926)


def test_the_series_tail_constant_results_quotes_is_the_one_the_code_uses() -> None:
    """`rho_M` as RESULTS.md section 9 prints it, against the artifact and the code.

    Every `rho_M = p/q` in RESULTS.md must be the constant `tail_bound(M)`
    computes and the artifact stores, except the superseded transcription,
    which may appear only in the original sentence and in the 2026-10-21 note
    that corrects it. The constant must also majorize the series tail it
    stands for, summed exactly here to k = 200 with a geometric remainder.
    """
    rho = enclose.tail_bound(enclose.M)
    assert ENCLOSE["tail_bound"].endswith(f"rho_M = {enclose.frac_str(rho)}")
    assert 1.5e-20 < float(rho) < 1.7e-20  # the "about 1.6e-20" printed beside it

    results = (HERE / "RESULTS.md").read_text(encoding="utf-8")
    quoted = [Fraction(int(p), int(q)) for p, q in re.findall(r"rho_M = (\d+)/(\d+)", results)]
    assert rho in quoted
    assert set(quoted) <= {rho, _RHO_SUPERSEDED}
    assert quoted.count(_RHO_SUPERSEDED) <= 2
    if _RHO_SUPERSEDED in quoted:
        assert "**Corrected 2026-10-21, on landing.** The fraction printed above" in results

    K = 200
    tail = sum(enclose.a_coeff(k) for k in range(enclose.M + 1, K + 1))
    ratio = Fraction(2 * (K + 1), (K + 2) * (2 * K + 3))
    tail_upper = tail + enclose.a_coeff(K + 1) / (1 - ratio)
    assert tail_upper <= rho
    assert abs(float(tail) - 1.593747e-20) <= 5e-27      # "1.593747e-20" in the note
    assert abs(float((rho - tail_upper) / tail_upper) - 9.1e-5) <= 5e-7  # "slack 9.1e-5"


# ---------------------------------------------------------------------------
# 3. landscape.py (float grade, discretization error about 1e-5)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "lam, zeta, xiprime",
    [(1.00, 0.672513, 0.868660), (0.80, 0.486277, 0.682554),
     (0.60, 0.134562, 0.281718), (0.55, -0.000570, 0.130262),
     (0.50, -0.165957, -0.052054)],
)
def test_the_landscape_table_of_mission_section_6(lam: float, zeta: float, xiprime: float) -> None:
    z = 2 - landscape.R_optimal(lam, landscape.F_zeta)
    x = 2 - landscape.R_optimal(lam, landscape.F_xiprime)
    assert abs(z - zeta) <= 5.1e-7
    assert abs(x - xiprime) <= 5.1e-7
    # the zeta control carries the method error that every xi' value inherits
    exact = 2 - (lam / 2 + (1 / sqrt(2)) / tan(lam / sqrt(2)))
    assert abs(z - exact) <= 2e-5


def test_the_flat_window_identity_and_the_xiprime_calibration() -> None:
    for lam in (0.6, 1.0):
        assert abs(landscape.R_flat(lam, landscape.F_zeta) - (1 / lam + lam / 3)) <= 1e-6
    r = landscape.R_flat(1.0, landscape.F_xiprime)
    assert abs((2 - r) - 0.85838) <= 5e-6
    assert abs((3 - r) / 2 - 0.92919) <= 5e-6
    # the six-decimal values MISSION.md section 6 and the case log print beside them
    assert abs((2 - r) - 0.858384) <= 5e-7
    assert abs((3 - r) / 2 - 0.929192) <= 5e-7
    assert abs((3 - sqrt(6)) - 0.5505102572) <= 1e-10


@pytest.mark.parametrize("lam, gap", [(0.6, 0.00122), (1.0, 0.00583)])
def test_flat_minus_optimal_is_about_lambda_cubed_over_180(lam: float, gap: float) -> None:
    """Finding three: the whole value of window shape, against `lambda^3/180`."""
    measured = landscape.R_flat(lam, landscape.F_zeta) - landscape.C_wang(lam)
    assert abs(measured - gap) <= 5e-6
    assert abs(measured - lam ** 3 / 180) <= 0.1 * lam ** 3 / 180


def test_the_vacuity_thresholds() -> None:
    zt = landscape._bisect(lambda t: 2 - landscape.R_optimal(t, landscape.F_zeta, 120), 0.40, 0.70)
    xt = landscape._bisect(lambda t: 2 - landscape.R_optimal(t, landscape.F_xiprime, 120), 0.40, 0.70)
    assert abs(zt - 0.55019) <= 5e-6
    assert abs(xt - 0.51332) <= 5e-6


#: MISSION.md section 8, every cell, keyed by (B, L). `None` is a cell the
#: table prints as "sign-changing": the minimizer leaves Lamzouri's class, so
#: its value is not a bound.
_PRICE_TABLE = {
    (2.0, 1.05): 0.702950, (2.0, 1.10): 0.726768, (2.0, 1.20): 0.760859,
    (3.0, 1.05): 0.701549, (3.0, 1.10): 0.721863, (3.0, 1.20): 0.746779,
    (6.0, 1.05): 0.697810, (6.0, 1.10): 0.710023, (6.0, 1.20): 0.718168,
    (20.0, 1.05): 0.686561, (20.0, 1.10): None, (20.0, 1.20): None,
}


@pytest.mark.parametrize("B, L", sorted(_PRICE_TABLE), ids=lambda x: f"{x:g}")
def test_the_band_edge_price_table(B: float, L: float) -> None:
    """MISSION.md section 8: a measured price, not a bound that exists."""
    value, ok = landscape.bound_with_outband_cap(L, B)
    expected = _PRICE_TABLE[(B, L)]
    if expected is None:
        assert not ok, "a sign-changing minimizer is outside Lamzouri's class and is not a bound"
    else:
        assert ok and abs(value - expected) <= 5e-7


def test_the_band_edge_baseline_and_the_gain_the_case_log_quotes() -> None:
    """Baseline `0.672508`; `B = 20` on a sliver of width `0.05` gains `0.0141`.

    The case log first printed `0.0142`, from the source branch; the gain is
    `0.01405` against this baseline and `0.01406` against the exact optimum,
    and it exceeds the bandwidth-one headroom either way. The corrected figure
    is read from the entry so it stays the one printed (2026-10-21).
    """
    base, ok = landscape.bound_with_outband_cap(1.0, 0.0)
    assert ok and abs(base - 0.672508) <= 5e-7
    value, ok = landscape.bound_with_outband_cap(1.05, 20.0)
    assert ok
    assert abs((value - base) - 0.01405) <= 5e-6
    assert abs((value - MT_OPTIMUM) - 0.01406) <= 5e-6
    assert round(value - base, 4) == round(value - MT_OPTIMUM, 4) == 0.0141
    assert value - base > CEILING_ONE - MT_OPTIMUM
    entry = _case_log_entry()
    assert "still gains `0.0142`" in entry  # the original, kept visible
    assert "(**corrected 2026-10-21**: `0.0141`;" in entry


def test_the_method_error_mission_section_6_quotes() -> None:
    """The zeta control's `+1.2e-5` at bandwidth one, and the xi' solve's `+1.9e-5` over H*.

    Both at the settings of the section 6 table; the second is method error,
    not a gain, because the first is.
    """
    z = 2 - landscape.R_optimal(1.0, landscape.F_zeta)
    x = 2 - landscape.R_optimal(1.0, landscape.F_xiprime)
    exact = 2 - (0.5 + (1 / sqrt(2)) / tan(1 / sqrt(2)))
    assert abs((z - exact) - 1.2e-5) <= 5e-7
    assert abs((x - enclose.LAB_H_STAR) - 1.9e-5) <= 5e-7


def test_the_derived_figures_the_hunt_quotes() -> None:
    """Small figures in MISSION.md sections 5 to 8 and the case log, from pinned inputs."""
    theta_0 = verify._bisect(verify.c_simple, 0.5, 0.6)
    # section 5: the whole value of window shape is 3.2e-4 of threshold
    assert abs(((3 - sqrt(6)) - theta_0) - 3.2e-4) <= 5e-6
    # section 5: at theta = 0.55 the window-shape game is worth about 9e-4
    game_055 = landscape.R_flat(0.55, landscape.F_zeta) - landscape.C_wang(0.55)
    game_one = landscape.R_flat(1.0, landscape.F_zeta) - landscape.C_wang(1.0)
    assert round(game_055, 4) == 0.0009
    # section 5: "an n-point family whose bandwidth-one share of it is 2.4e-4 is worth
    # roughly 4e-5". The text does not say where 2.4e-4 comes from; it matches the
    # Phi_3 bridge's gain over the window optimum at bandwidth one (2.37e-4), and the
    # 4e-5 is that share scaled by the window-shape game from bandwidth one to 0.55.
    h = verify.c_simple(1.0)
    assert round(verify.bridge("Phi_3", h) - h, 5) == 0.00024
    assert round(2.4e-4 * game_055 / game_one, 5) == 0.00004
    # section 6.2: the zeta constant 1/c*_1 = 2 - H at bandwidth one
    assert abs((2 - MT_OPTIMUM) - 1.3274992963205884) <= 1e-15
    # section 7: the bandwidth-one headroom 0.00933, and the ladder 0.0078 short of the ceiling
    assert abs((CEILING_ONE - MT_OPTIMUM) - 0.00933) <= 5e-6
    assert round(CEILING_ONE - 0.6740762, 4) == 0.0078
    # section 6.1: Rezvyakova's simple on-line proportion at k = 1 is about 0.413
    assert round(1 - (e ** 2 + 2) / 16, 3) == 0.413
    # section 8: at alpha = 1.05, log T = 100, c = 2 the residual is already 1.4 times the main term
    assert 1.4 < exp(100 * 0.05) / 100 < 1.5


# ---------------------------------------------------------------------------
# 4. ceiling_theta.py
# ---------------------------------------------------------------------------


def test_the_ladders_quoted_in_results_section_8_match_the_checkpoints() -> None:
    one = json.loads((ARTIFACTS / "ceiling-theta-1.00.json").read_text(encoding="utf-8"))
    low = json.loads((ARTIFACTS / "ceiling-theta-0.55.json").read_text(encoding="utf-8"))
    quoted_one = [0.6793882, 0.6775676, 0.6768963, 0.6764627, 0.6759394, 0.6756339]
    assert [round(r["value"], 7) for r in one["rungs"]] == quoted_one
    assert round(one["extrapolated_value"], 7) == 0.6740762
    assert round(low["rungs"][-1]["value"], 7) == 0.0103512
    assert abs(low["extrapolated_value"] - 0.000689) <= 5e-7
    assert one["landscape_violations"] == [] and low["landscape_violations"] == []


def test_the_dyadic_count_in_the_bridge_that_finding_two_quotes() -> None:
    """`2 * T` in the bridge's `Main.lean`: 21 lines, 28 occurrences.

    Finding two first wrote "21 occurrences"; 21 counts lines, and the
    correction (2026-10-21) gives both. The file is read as it stands, so an
    edit to the bridge that changes the count shows up here.
    """
    main = ROOT / "lean" / "bridge" / "Zeta23Ext" / "Bridge" / "Main.lean"
    text = main.read_text(encoding="utf-8")
    assert sum("2 * T" in line for line in text.splitlines()) == 21
    assert text.count("2 * T") == 28


def test_the_cheapest_rung_reproduces_and_reduces_to_bandwidth_one() -> None:
    pytest.importorskip("scipy")
    ceiling = _load("short_interval_ceiling_theta", HERE / "ceiling_theta.py")
    v_original, v_here, diff = ceiling.test_reduces_to_bandwidth_one(40.0, 200)
    assert diff <= 1e-12
    first = json.loads((ARTIFACTS / "ceiling-theta-1.00.json").read_text(encoding="utf-8"))["rungs"][0]
    assert (first["X"], first["J"]) == (40.0, 200)
    assert abs(v_here - first["value"]) <= 1e-9
    assert abs(v_original - ceiling.recorded_inband_ladder()[40.0]) <= 1e-9
