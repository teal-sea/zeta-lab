"""Pins for the independent spectral_operator rival challenge."""

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


def _cell(payload, kind):
    return next(row for row in payload["cells"] if row["kind"] == kind)


@pytest.mark.parametrize("kind", ["dh", "epstein", "wa", "zeta_shift_recentered"])
def test_each_operator_is_even_simple_and_self_adjoint_on_its_cell(payload, kind):
    row = _cell(payload, kind)
    assert mp.mpf(row["even_gap"]) > 0
    assert mp.mpf(row["commutator_defect"]) < mp.mpf("1e-35")
    assert mp.mpf(row["max_abs_spectrum_imag"]) < mp.mpf("1e-8")


@pytest.mark.parametrize(
    "kind,offset",
    [("dh", "0.308517182456637386"), ("epstein", "0.4532604748"), ("wa", "0.25")],
)
def test_real_spectrum_cannot_reach_each_off_line_zero(payload, kind, offset):
    row = _cell(payload, kind)
    assert abs(mp.mpf(row["off_line_zero_real_offset"]) - mp.mpf(offset)) < mp.mpf("1e-12")
    assert mp.mpf(row["distance_to_off_line_zero"]) >= mp.mpf(offset)


def test_shifted_zeta_is_zeta_after_recentering(payload):
    row = _cell(payload, "zeta_shift_recentered")
    assert row["symmetry_center"] == "0.6"
    assert mp.mpf(row["off_line_zero_real_offset"]) == 0
    assert mp.mpf(payload["shifted_zeta"]["recentered_matrix_defect"]) < mp.mpf("1e-50")
    assert mp.mpf(payload["shifted_zeta"]["fixed_half_symmetry_defect"]) > mp.mpf("1e-3")


def test_challenge_is_independent_and_obeys_lexical_rules():
    source = (HERE / "rival_gate.py").read_text(encoding="utf-8")
    for forbidden_import in ("spo_common", "ccm_common", "enclosures", "wp_common"):
        assert forbidden_import not in source
    for path in HERE.iterdir():
        if path.is_file() and path.suffix in {".py", ".md", ".json"}:
            text = path.read_text(encoding="utf-8").lower()
            assert ("cert" + "if") not in text
            assert chr(0x2014) not in text
