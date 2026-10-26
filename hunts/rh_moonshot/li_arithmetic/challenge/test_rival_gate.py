"""Pins for the independent li_arithmetic rival challenge."""

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


def test_small_li_coefficients_are_recomputed_independently(payload):
    zeta_values = [mp.mpf(value) for value in payload["small_li"]["zeta"]]
    dh_values = [mp.mpf(value) for value in payload["small_li"]["davenport_heilbronn"]]
    assert all(value > 0 for value in zeta_values + dh_values)
    assert abs(zeta_values[0] - mp.mpf("0.0230957089661210338")) < mp.mpf("1e-17")
    assert abs(dh_values[0] - mp.mpf("0.0976361468095196712")) < mp.mpf("1e-17")


def test_wa_negative_li_value_is_reproduced_from_zeros(payload):
    row = payload["W_1_4_li"]
    assert row["n"] == 8260
    assert row["zero_count"] == 1000
    assert abs(mp.mpf(row["value"]) - mp.mpf("-122.315821669551207")) < mp.mpf("1e-12")
    assert mp.mpf(row["value"]) < -100
    assert mp.mpf(payload["zero_residuals"]["W_1_4"]) < mp.mpf("1e-30")


def test_log_derivative_coefficients_separate_the_rivals(payload):
    rows = payload["coefficient_gate"]
    assert rows["zeta"]["first_negative"] is None
    assert rows["zeta"]["first_non_prime_power"] is None
    assert rows["W_1_4"]["first_negative"] is None
    assert rows["W_1_4"]["first_non_prime_power"] is None
    assert rows["zeta_shift_delta_0_1"]["first_negative"] is None
    assert rows["zeta_shift_delta_0_1"]["first_non_prime_power"] is None
    assert rows["davenport_heilbronn"]["first_negative"][0] == 3
    assert rows["davenport_heilbronn"]["first_non_prime_power"][0] == 6
    assert rows["epstein_1_1_6"]["first_negative"][0] == 48
    assert rows["epstein_1_1_6"]["first_non_prime_power"][0] == 6
    assert mp.mpf(payload["zero_residuals"]["davenport_heilbronn"]) < mp.mpf("1e-40")
    assert mp.mpf(payload["zero_residuals"]["epstein_1_1_6"]) < mp.mpf("1e-9")


def test_shifted_zeta_passes_prime_sign_but_loses_fixed_normalization(payload):
    row = payload["shifted_zeta"]
    assert row["actual_center"] == "0.6"
    assert mp.mpf(row["local_modulus_at_2"]) > 1
    assert mp.mpf(row["actual_defect"]) < mp.mpf("1e-40")
    assert mp.mpf(row["fixed_center_defect"]) > mp.mpf("1e-3")
    assert mp.mpf(row["zero_residual"]) < mp.mpf("1e-30")


def test_challenge_is_independent_and_obeys_lexical_rules():
    source = (HERE / "rival_gate.py").read_text(encoding="utf-8")
    for forbidden_import in ("li_arith_split", "li_arith_prime", "li_arith_wa"):
        assert forbidden_import not in source
    for path in HERE.iterdir():
        if path.is_file() and path.suffix in {".py", ".md", ".json"}:
            text = path.read_text(encoding="utf-8").lower()
            assert ("cert" + "if") not in text
            assert chr(0x2014) not in text
