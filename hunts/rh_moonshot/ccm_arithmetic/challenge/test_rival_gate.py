"""Pins for the independent ccm_arithmetic rival challenge."""

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


def _cell(payload, kind, c):
    return next(row for row in payload["cells"] if row["kind"] == kind and row["c"] == c)


def test_dh_capture_breaks_after_the_negative_window(payload):
    at31 = _cell(payload, "dh", "31")
    at33 = _cell(payload, "dh", "33")
    assert mp.mpf(at31["lambda_1"]) < 0
    assert mp.mpf(at33["lambda_1"]) < 0
    assert mp.mpf(at31["radical_misfit"]) < mp.mpf("0.001")
    assert mp.mpf(at33["radical_misfit"]) > mp.mpf("0.999")
    # Ordinary double precision is many orders too coarse at this scale.
    assert abs(mp.mpf(at31["lambda_1_numpy"])) > 10**10 * abs(mp.mpf(at31["lambda_1"]))


def test_epstein_sign_change_is_seen_by_two_numeric_routes(payload):
    at29 = _cell(payload, "epstein", "29")
    at295 = _cell(payload, "epstein", "29.5")
    assert mp.mpf(at29["lambda_1"]) > 0
    assert mp.mpf(at295["lambda_1"]) < 0
    assert abs(mp.mpf(at29["lambda_1"]) - mp.mpf(at29["lambda_1_numpy"])) < mp.mpf("1e-15")
    assert abs(mp.mpf(at295["lambda_1"]) - mp.mpf(at295["lambda_1_numpy"])) < mp.mpf("1e-14")


def test_shifted_product_loses_capture_with_the_sign(payload):
    at2 = _cell(payload, "wa", "2")
    at3 = _cell(payload, "wa", "3")
    assert mp.mpf(at2["lambda_1"]) > 0
    assert mp.mpf(at3["lambda_1"]) < 0
    assert mp.mpf(at2["radical_misfit"]) < mp.mpf("0.19")
    assert mp.mpf(at3["radical_misfit"]) > mp.mpf("0.998")
    assert abs(mp.mpf(at3["lambda_1"]) - mp.mpf(at3["lambda_1_numpy"])) < mp.mpf("1e-14")


def test_shifted_zeta_lacks_the_fixed_even_normalization(payload):
    row = payload["shifted_zeta_normalization"]
    assert row["actual_center"] == "0.6"
    assert mp.mpf(row["actual_defect"]) < mp.mpf("1e-40")
    assert mp.mpf(row["fixed_center_defect"]) > mp.mpf("1e-3")


def test_challenge_is_independent_and_obeys_lexical_rules():
    source = (HERE / "rival_gate.py").read_text(encoding="utf-8")
    for forbidden_import in ("ccm_common", "wp_common", "enclosures", "galerkin"):
        assert forbidden_import not in source
    for path in HERE.iterdir():
        if path.is_file() and path.suffix in {".py", ".md", ".json"}:
            text = path.read_text(encoding="utf-8").lower()
            assert ("cert" + "if") not in text
            assert chr(0x2014) not in text
