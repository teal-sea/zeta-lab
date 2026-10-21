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
   calibration, the vacuity thresholds and the band-edge price cells that
   `MISSION.md` quotes.
4. `ceiling_theta.py`: the cheapest rung recomputed and compared with the
   committed checkpoint, and the ladder values `RESULTS.md` section 8 quotes.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from fractions import Fraction
from math import sqrt, tan
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ARTIFACTS = HERE / "artifacts"


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
    """Control (i): a one-window bound can never exceed the optimum c(theta)."""
    bound = Fraction(_row(theta, "zeta")["lower_bound_exact"])
    lo, hi, _backend = enclose.wang_enclosure(Fraction(theta))
    assert bound <= lo
    assert hi - bound <= Fraction(61, 10**13)


def test_the_published_windows_at_bandwidth_one_reproduce(forms) -> None:
    """Control (ii): Alpoge-Furman Remark 7.1, quartic 0.86864 and flat 0.85838."""
    P, b, G = forms
    for window, published in ((enclose.QUARTIC, enclose.AF_QUARTIC),
                              (enclose.FLAT, enclose.AF_FLAT)):
        R, tail = enclose.exact_R(Fraction(1), "xiprime", window, P, b, G)
        assert 2 - R - tail >= published


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


def test_the_band_edge_price_cells() -> None:
    """MISSION.md section 8: a measured price, not a bound that exists."""
    base, ok = landscape.bound_with_outband_cap(1.0, 0.0)
    assert ok and abs(base - 0.672508) <= 5e-7
    value, ok = landscape.bound_with_outband_cap(1.20, 2.0)
    assert ok and abs(value - 0.760859) <= 5e-7
    value, ok = landscape.bound_with_outband_cap(1.05, 20.0)
    assert ok and abs(value - 0.686561) <= 5e-7
    _value, ok = landscape.bound_with_outband_cap(1.10, 20.0)
    assert not ok, "a sign-changing minimizer is outside Lamzouri's class and is not a bound"


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


def test_the_cheapest_rung_reproduces_and_reduces_to_bandwidth_one() -> None:
    pytest.importorskip("scipy")
    ceiling = _load("short_interval_ceiling_theta", HERE / "ceiling_theta.py")
    v_original, v_here, diff = ceiling.test_reduces_to_bandwidth_one(40.0, 200)
    assert diff <= 1e-12
    first = json.loads((ARTIFACTS / "ceiling-theta-1.00.json").read_text(encoding="utf-8"))["rungs"][0]
    assert (first["X"], first["J"]) == (40.0, 200)
    assert abs(v_here - first["value"]) <= 1e-9
    assert abs(v_original - ceiling.recorded_inband_ladder()[40.0]) <= 1e-9
