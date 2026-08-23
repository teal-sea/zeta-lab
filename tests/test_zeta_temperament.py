"""Pins for hunt #76 (`hunts/zeta_temperament/`): the Riemann zeros in tuning units.

theta = gamma ln2 / 2pi is a zero's ordinate in steps per octave. Landau's
formula says the mean over zeros of n^{i gamma} is -Lambda(n)/sqrt(n) divided
by the mean of log(gamma/2pi), up to O(log T / N). In these units that is the
Fourier coefficient of the zeros mod 1 at frequency log2 n. The always-on
check uses the laboratory's own 2000 cached zeros (independent of Odlyzko's
table); the 100,000-zero checks run when `data/odlyzko/zeros1` is present.
"""

from __future__ import annotations

import json
import sys
from math import log, sqrt
from pathlib import Path

import numpy as np
import pytest

_ROOT = Path(__file__).resolve().parents[1]
_HUNT = _ROOT / "hunts" / "zeta_temperament"
if str(_HUNT) not in sys.path:
    sys.path.insert(0, str(_HUNT))

import probe_landau_edo as pl  # noqa: E402

LN2 = log(2.0)


def _own_zeros():
    from zeta.explicit import first_zeros

    g = first_zeros(2000)
    if len(g) < 2000:
        pytest.skip("fewer than 2000 cached zeros")
    return g


def test_von_mangoldt():
    assert [pl.lam(n) for n in (2, 3, 4, 6, 8, 9, 12)] == pytest.approx(
        [log(2), log(3), log(2), 0.0, log(2), log(3), 0.0])


def test_landau_in_tuning_units_on_own_zeros():
    """Prime powers carry Landau's coefficient to within 6 percent on 2000
    zeros; composites sit within three random-points standard errors of zero."""
    g = _own_zeros()
    th = g * LN2 / (2 * np.pi)
    L = np.mean(np.log(g / (2 * np.pi)))
    se = 1 / sqrt(2 * len(g))
    for n in (2, 3, 4, 5, 7, 8, 9, 11, 13):
        c = np.mean(np.exp(2j * np.pi * th * np.log2(n))).real
        pred = -pl.lam(n) / sqrt(n) / L
        assert abs(c - pred) < 0.06 * abs(pred), (n, c, pred)
    for n in (6, 10, 12, 15):
        c = np.mean(np.exp(2j * np.pi * th * np.log2(n)))
        assert abs(c) < 3 * se, (n, c)


def test_zeros_avoid_integer_temperaments_on_own_zeros():
    g = _own_zeros()
    th = g * LN2 / (2 * np.pi)
    frac = th - np.round(th)
    L = np.mean(np.log(g / (2 * np.pi)))
    measured = pl.box_density(frac)
    predicted = pl.predicted_box_density(L, 2)
    assert measured < 0.75
    assert abs(measured - predicted) < 0.05
    assert np.mean(np.abs(frac) < 0.05) < 0.07  # uniform would give 0.10


def test_planted_fault_is_caught():
    """Shift every zero by half a step: the integer deficit must disappear."""
    g = _own_zeros()
    th = g * LN2 / (2 * np.pi) + 0.5
    frac = th - np.round(th)
    assert pl.box_density(frac) > 1.0


def _odlyzko_results():
    path = _HUNT / "results_landau.json"
    if not path.is_file():
        pytest.skip("results_landau.json not generated")
    return json.loads(path.read_text())["odlyzko"]


def test_odlyzko_table_matches_landau_to_four_decimals():
    r = _odlyzko_results()
    assert r["zeros"] == 100_000
    for c in r["coefficients"]:
        if c["prime_power"]:
            assert abs(c["measured_re"] - c["predicted"]) < 0.0015, c
        else:
            assert abs(c["measured_re"]) < 0.0005 and abs(c["measured_im"]) < 0.0005, c
    assert r["density_integer"] == pytest.approx(0.801, abs=0.003)
    assert r["density_integer_predicted"] == pytest.approx(0.800, abs=0.003)
    assert r["density_fifth_perfect"] == pytest.approx(0.762, abs=0.003)
    assert r["density_composite6_control"] == pytest.approx(1.0, abs=0.01)
    dens = [b["measured"] for b in r["bands"]]
    assert dens == sorted(dens)  # the deficit shrinks with height, as 1/log t


def test_peaks_calibration_reproduces_the_known_ranking():
    path = _HUNT / "results_peaks.json"
    if not path.is_file():
        pytest.skip("results_peaks.json not generated")
    r = json.loads(path.read_text())
    assert r["spearman_by_prime_set"]["3,5,7,11,13"]["raw"] < -0.7
    assert r["null_abs_spearman_p999"] < 0.3
    assert r["classic_in_top24"] >= 6
    assert r["classic_ranks_of_396"]["311"] == 1
    twelve = next(h for h in r["horizon"] if h["x"] == 12)
    assert twelve["N"] == 4
    assert abs(twelve["remainder"]) < 0.35
