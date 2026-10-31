"""Pins for the independent probe_tower rival challenge."""

from __future__ import annotations

import random
import sys
from fractions import Fraction as F
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
    return R.report(dps=45)


def _geometries(count: int, seed: int = 150):
    rng = random.Random(seed)
    rows = []
    while len(rows) < count:
        ell = F(rng.randrange(61), 60)
        total = F(rng.randrange(61), 60)
        offset = F(rng.randrange(61), 60)
        if offset <= total and total + ell <= 1:
            rows.append((ell, total, offset))
    return rows


def test_tower_direction_is_recomputed_exactly():
    for ell, total, _ in _geometries(200):
        m = total - 2 * ell
        for k in range(2, 65):
            assert R.tower_increment(k, ell, total) == (2 - m) / (2 * k * (k + 1))
            assert R.tower_increment(k, ell, total) > 0
        assert R.sigma0(10**6, ell, total) > F(999_997, 1_000_000)
    assert R.sigma0(6, F(1, 6), F(5, 6)) == F(7, 8)
    assert R.tower_increment(6, F(1, 6), F(5, 6)) == F(1, 56)


def test_floor_wall_and_its_dual_identity_are_exact():
    assert min(R.floor_wall(k) for k in range(2, 201)) == F(3, 5)
    assert R.floor_wall(6) == F(13, 15)
    assert R.dual_length_wall(6) == F(2, 3)
    for k in range(2, 20):
        for delta0 in (F(0), F(1, 50), F(1, 10)):
            for ell, total, offset in _geometries(20, seed=k):
                left, right, multipliers = R.floor_dual_identity(
                    k, delta0, ell, total, offset
                )
                assert left == right
                assert min(multipliers[:3]) >= 0


def test_dh_and_epstein_fail_before_the_complete_hypotheses(payload):
    dh = payload["davenport_heilbronn"]
    assert mp.mpf(dh["row_to_constituents_gap"]) < mp.mpf("1e-6")
    assert mp.mpf(dh["row_to_scalar_reciprocal_gap"]) > mp.mpf("0.02")
    assert mp.mpf(dh["zero_residual"]) < mp.mpf("1e-30")
    assert abs(mp.mpf(dh["H_minus_1_at_zero"]) - 1) < mp.mpf("1e-10")
    epstein = payload["epstein_1_1_6"]
    assert mp.mpf(epstein["coefficient_defect_2_3"]) == 2
    assert mp.mpf(epstein["zero_residual"]) < mp.mpf("1e-8")


def test_euler_product_rivals_lack_unitarity(payload):
    shifted = payload["zeta_shift_delta_0_1"]
    assert mp.mpf(shifted["truncation_gap"]) < mp.mpf("1e-4")
    assert mp.mpf(shifted["local_modulus_at_2"]) > 1
    assert shifted["actual_symmetry_center"] == "0.6"
    assert mp.mpf(shifted["zero_residual"]) < mp.mpf("1e-30")
    wa = payload["W_1_4"]
    roots = [mp.mpf(x) for x in wa["local_root_moduli_at_2"]]
    assert roots[0] > 1 > roots[1]
    assert mp.mpf(wa["correction_minus_1_at_zero"]) < mp.mpf("0.3")
    assert mp.mpf(wa["zero_residual"]) < mp.mpf("1e-30")


def test_challenge_files_obey_lexical_rules():
    for path in HERE.iterdir():
        if path.is_file() and path.suffix in {".py", ".md", ".json"}:
            text = path.read_text(encoding="utf-8").lower()
            assert ("cert" + "if") not in text
            assert chr(0x2014) not in text
