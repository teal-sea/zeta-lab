"""Pins for the circularity challenge of positivity_geometry (hunt #150).

Every number quoted in CHALLENGE_circularity.md is asserted here, from
``circ_positivity.py``, which shares no code with the construction. Writes nothing.
"""
from __future__ import annotations

import re
import random
import sys
from fractions import Fraction
from pathlib import Path

from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
for _p in (str(HERE), str(ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import circ_positivity as cp  # noqa: E402

_RESERVED = "cert" + "ified"
_EM_DASH = chr(0x2014)


def test_golden_fake_closed_points_nonnegative_to_degree_300():
    b = cp.closed_points(300)
    assert b[:8] == [1, 5, 25, 110, 500, 2215, 10000, 45100]
    assert min(b) == 1


def test_golden_fake_quadratic_split_matches_notes_and_holds_to_300():
    s, i = cp.quadratic_split(300)
    assert all(x.denominator == 1 and x >= 0 for x in s + i)
    assert [int(x) for x in s[:8]] == [0, 0, 12, 50, 250, 1094, 5000, 22500]
    assert [int(x) for x in i[:8]] == [5, 10, 27, 100, 374, 1486, 6160, 26250]


def test_planted_fault_other_ramification_configurations_fail():
    for ram in ({1: 4}, {1: 2, 2: 1}, {2: 2}, {4: 1}):
        s, i = cp.quadratic_split(10, ram=ram)
        assert any(x.denominator != 1 or x < 0 for x in s + i), ram


def test_window_2g_lemma_on_arbitrary_closed_multisets():
    rng = random.Random(150)
    for g in (2, 3):
        for off in (False, True):
            for _ in range(8):
                us = cp.random_closed_multiset(g, off, rng)
                ev = cp.toeplitz_min_eig(us, 2 * g)
                assert (ev < -mp.mpf(10) ** -15) == off


def test_window_sharpness_genus2_fake_by_independent_route():
    # P = (1 + 3T + 5T^2)(1 - 5T + 5T^2): inverse roots / sqrt 5
    with mp.workdps(30):
        us = []
        for a in (-3, 5):
            r = mp.polyroots([1, -a, 5])
            us += [x / mp.sqrt(5) for x in r]
        assert cp.toeplitz_min_eig(us, 3) > -mp.mpf(10) ** -20
        assert cp.toeplitz_min_eig(us, 4) < -mp.mpf(10) ** -3


def test_shifted_zeta_passes_g1_and_g2():
    for delta in (mp.mpf(1) / 10, mp.mpf(1) / 4):
        r = cp.shifted_zeta_g1(delta)
        assert r["first_negative"] == [] and r["first_off_prime_power"] == []
        assert abs(r["residue"] - 1) < mp.mpf(10) ** -10


def test_dh_lambda6_closed_form():
    with mp.workdps(30):
        l2, l3, l6, cf, kappa = cp.dh_lambda6()
        assert abs(l2 - kappa * mp.log(2)) < mp.mpf(10) ** -25
        assert abs(l3 + kappa * mp.log(3)) < mp.mpf(10) ** -25
        assert abs(l6 - cf) < mp.mpf(10) ** -25


def test_lexical_rules_and_manifest():
    for path in sorted(HERE.iterdir()):
        if path.suffix in {".py", ".md"}:
            text = path.read_text(encoding="utf-8")
            assert _RESERVED not in text.lower(), path.name
            assert _EM_DASH not in text, path.name
    sys.path.insert(0, str(ROOT / "tests"))
    try:
        import test_huntspec as hs
    finally:
        sys.path.remove(str(ROOT / "tests"))
    text = (HERE / "CHALLENGE_circularity.md").read_text(encoding="utf-8")
    blocks = re.findall(r"```runmanifest\n(.*?)```", text, re.DOTALL)
    assert blocks
    for block in blocks:
        assert hs.validate_runmanifest(hs.parse_huntspec(block)) == ()
