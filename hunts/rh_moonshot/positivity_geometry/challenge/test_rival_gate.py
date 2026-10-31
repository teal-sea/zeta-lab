"""Pins for the independent positivity_geometry rival challenge."""

from __future__ import annotations

import sys
from pathlib import Path

from mpmath import mp
import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
for entry in (str(HERE), str(ROOT)):
    if entry not in sys.path:
        sys.path.insert(0, entry)

import rival_gate as R  # noqa: E402


@pytest.fixture(scope="module")
def payload():
    return R.report(n_max=60, dps=45)


def test_rival_arithmetic_is_recomputed_without_mechanism_imports(payload):
    rows = payload["arithmetic"]
    assert rows["zeta"]["first_negative"] is None
    assert rows["zeta"]["first_non_prime_power"] is None
    assert rows["davenport_heilbronn"]["first_negative"][0] == 3
    assert rows["davenport_heilbronn"]["first_non_prime_power"][0] == 6
    assert rows["epstein_1_1_6"]["first_negative"][0] == 48
    assert rows["epstein_1_1_6"]["first_non_prime_power"][0] == 6
    assert rows["W_1_4"]["first_negative"] is None
    assert rows["W_1_4"]["first_non_prime_power"] is None
    assert rows["zeta_shift_delta_0_1"]["first_negative"] is None
    assert rows["zeta_shift_delta_0_1"]["first_non_prime_power"] is None


def test_shifted_zeta_passes_prime_data_but_fails_fixed_normalization(payload):
    row = payload["shifted_zeta_normalization"]
    assert mp.mpf(row["actual_symmetry_defect"]) < mp.mpf("1e-40")
    assert mp.mpf(row["fixed_half_symmetry_defect"]) > mp.mpf("1e-10")
    assert row["actual_center"] == "0.6"
    assert row["pole"] == "1.1"


def test_all_four_rivals_really_have_the_stated_off_line_zero(payload):
    residuals = payload["zero_residuals"]
    assert mp.mpf(residuals["davenport_heilbronn"]) < mp.mpf("1e-30")
    assert mp.mpf(residuals["epstein_1_1_6"]) < mp.mpf("1e-8")
    assert mp.mpf(residuals["W_1_4"]) < mp.mpf("1e-30")
    assert mp.mpf(residuals["zeta_shift_delta_0_1"]) < mp.mpf("1e-30")


def test_golden_fake_exact_arithmetic_and_refusal():
    fake = R.golden_fake(80)
    assert fake["points_1_to_6"] == [1, 11, 76, 451, 2501, 13376]
    assert fake["places_1_to_6"] == [1, 5, 25, 110, 500, 2215]
    assert fake["minimum_place_count_to_n_max"] > 0
    assert fake["castelnuovo_severi_margin_n1"] == -5
    with mp.workdps(50):
        ratios = [mp.mpf(x) for x in fake["normalized_root_moduli"]]
        phi = (1 + mp.sqrt(5)) / 2
        assert abs(ratios[0] - phi) < mp.mpf("1e-25")
        assert abs(ratios[1] - 1 / phi) < mp.mpf("1e-25")


def test_challenge_files_obey_lexical_rules():
    for path in HERE.iterdir():
        if path.is_file() and path.suffix in {".py", ".md", ".json"}:
            text = path.read_text(encoding="utf-8").lower()
            assert ("cert" + "if") not in text
            assert chr(0x2014) not in text
