"""Tests for zeta.detector, off-line zeros found without solving for them.

Every literal was measured in this environment before being asserted.

    zeta, max |residue| over c = 20, 45, 60, 100      1.6e-15   (float noise)
    DH,   max |residue| over c = 40, 60, 100          8.0e-15   (quiet)
    DH,   residue at c = 85.6993484853776             4.096324360133627
    predicted contribution of the known quadruple     4.096324360133638
    agreement                                         1.1e-14
    |beta-1/2| recovered from the peak height         0.30851718245662
    true |beta-1/2|                                   0.30851718245664

The ζ row is the real test.  It is a three-way agreement between a digamma
integral, a prime sum and a zero list that share no code, so its vanishing
simultaneously validates the archimedean convention, the sign of the prime
term, and the Fourier pair.  A sign-flipped prime term (met during
development) leaves ζ residues of order 1 that read as a genuine signal.
"""

from __future__ import annotations

import pytest
from mpmath import mp

from zeta.detector import (
    DEFAULT_WIDTH,
    arithmetic_side,
    bump_pair,
    detector_battery,
    offline_residue,
    online_list_is_complete,
    online_zero_side,
    recover_distance_from_line,
    residue_scan,
)


def test_fourier_pair_is_exact():
    """g must be (1/2π)∫h(r)e^{−iru}dr for the shifted-Gaussian h."""
    c, a = mp.mpf(7), DEFAULT_WIDTH
    h, g = bump_pair(c, a)
    for u in (0.0, 0.4, 1.1):
        numeric = mp.quad(
            lambda r: h(r) * mp.e ** (-mp.mpc(0, 1) * r * mp.mpf(u)),
            [-40, -float(c), 0, float(c), 40],
        ) / (2 * mp.pi)
        assert mp.re(numeric) == pytest.approx(float(g(u)), abs=1e-12)


def test_h_accepts_complex_argument():
    """The whole point: off-line zeros are evaluated off the real axis."""
    h, _ = bump_pair(10.0)
    val = h(mp.mpc(10.0, -0.3))
    assert abs(mp.im(val)) < 1e-12          # symmetric pair keeps it real
    assert float(mp.re(val)) > 1.0          # amplified above the on-line value


def test_zeta_residue_is_float_noise():
    """All zeta zeros are on the line, so the on-line list must account for
    the entire explicit formula."""
    for c in (20.0, 45.0, 60.0, 100.0):
        r = offline_residue(c, "zeta")
        assert abs(r["residue"]) < 1e-11, c


def test_dh_is_quiet_away_from_its_offline_zero():
    for c in (40.0, 60.0, 100.0):
        assert abs(offline_residue(c, "dh")["residue"]) < 1e-9, c


def test_dh_residue_equals_the_known_quadruple():
    """The headline: the residue reproduces zeros nothing in it knew about."""
    b = detector_battery()
    assert b["dh_peak_residue"] == pytest.approx(4.0963243601, abs=1e-9)
    assert b["peak_match_error"] < 1e-11
    assert b["separates"] is True


def test_peak_height_recovers_distance_from_the_line():
    b = detector_battery()
    assert b["recovered_distance"] == pytest.approx(0.3085171824, abs=1e-9)
    assert b["recovery_error"] < 1e-11


def test_recovery_returns_zero_when_nothing_is_off_line():
    assert recover_distance_from_line(4.0) == 0.0
    assert recover_distance_from_line(2.5) == 0.0


def test_online_list_completeness_guard():
    """The residue cannot tell an off-line zero from a missing on-line one,
    so the guard is load-bearing, not decorative."""
    out = online_list_is_complete(80.0, 92.0)
    assert out["complete"] is True
    assert out["cached_count"] == out["reference_count"] == 6


def test_scan_localizes_the_offline_zero():
    scan = residue_scan([83.0, 84.0, 85.0, 86.0, 87.0, 88.0], "dh")
    assert 84.5 < scan["argmax_c"] < 86.5
    assert scan["max_abs_residue"] > 3.5


def test_arithmetic_side_uses_no_zeros():
    """Sanity that the arithmetic side is computable at a c where we hold no
    zero data at all, it depends only on coefficients and the gamma factor."""
    val = arithmetic_side(300.0, "dh")
    assert mp.isfinite(val)


@pytest.mark.slow
def test_verdict_states_the_limits():
    v = detector_battery()["verdict"]
    assert "NOT a proof" in v and "NOT certified" in v
    assert "missing on-line" in v
