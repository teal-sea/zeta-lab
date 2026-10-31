"""Pins for the independent de_branges rival challenge."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest
from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
for entry in (str(HERE), str(ROOT)):
    if entry not in sys.path:
        sys.path.insert(0, entry)

import rival_gate as R  # noqa: E402


@pytest.fixture(scope="module")
def payload():
    return R.report()


def test_zeta_control_has_the_hermite_biehler_sign(payload):
    assert mp.mpf(payload["zeta_control"]["defect"]) < 0


@pytest.mark.parametrize(
    "kind",
    ["davenport_heilbronn", "epstein_1_1_6", "W_1_4", "zeta_shift_delta_0_1"],
)
def test_each_off_line_rival_flips_the_defect_at_the_predicted_offset(payload, kind):
    row = payload["rivals"][kind]
    assert mp.mpf(row["failure_defect"]) > 1
    assert mp.mpf(row["control_defect"]) < -1


def test_three_centered_rivals_meet_the_fixed_functional_equation(payload):
    rows = payload["rivals"]
    for kind in ("davenport_heilbronn", "epstein_1_1_6", "W_1_4"):
        assert mp.mpf(rows[kind]["symmetry_defects"]["fixed_half"]) < mp.mpf("1e-35")


def test_shifted_zeta_has_only_its_shifted_symmetry(payload):
    row = payload["rivals"]["zeta_shift_delta_0_1"]["symmetry_defects"]
    assert mp.mpf(row["fixed_half"]) > mp.mpf("1e-3")
    assert mp.mpf(row["actual_center_0_6"]) < mp.mpf("1e-35")


def test_off_line_zero_residuals_are_small_at_the_stated_precision(payload):
    rows = payload["rivals"]
    assert mp.mpf(rows["davenport_heilbronn"]["zero_residual"]) < mp.mpf("1e-40")
    assert mp.mpf(rows["epstein_1_1_6"]["zero_residual"]) < mp.mpf("1e-9")
    assert mp.mpf(rows["W_1_4"]["zero_residual"]) < mp.mpf("1e-30")
    assert mp.mpf(rows["zeta_shift_delta_0_1"]["zero_residual"]) < mp.mpf("1e-30")


def test_challenge_is_independent_and_obeys_lexical_rules():
    source = (HERE / "rival_gate.py").read_text(encoding="utf-8")
    for forbidden_import in ("dbr_common", "dbr_grid"):
        assert forbidden_import not in source
    for path in HERE.iterdir():
        if path.is_file() and path.suffix in {".py", ".md", ".json"}:
            text = path.read_text(encoding="utf-8").lower()
            assert ("cert" + "if") not in text
            assert chr(0x2014) not in text
