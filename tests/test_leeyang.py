"""Tests for zeta.leeyang — the Lee–Yang / GHS reading of Φ.

Every literal was measured in this environment before being asserted.

1. The free-energy normalization is *derived*: ∫Φ(u)e^{hu}du = ¼·ξ(½+h/2),
   with the ratio constant to machine zero across h.  That constancy is the
   whole content — a fitted constant that drifted with h would mean the
   identity is wrong.
2. Two independent routes to G‴(w) agree to ~5e-5 relative: a stencil on ξ
   itself, and the RH-assuming Hadamard zero-sum.  This cross-check is what
   caught a sign-flipped stencil during development, so it is pinned.
3. ``mp.diff`` on ξ returns ~0 — the same internal-rounding trap as ``dh_f``.
   Pinned as a regression so the hand-rolled stencil is never "simplified"
   back to it.
4. The verdict: GHS holds for ζ *and* for Davenport–Heilbronn, so the
   inequality separates nothing (docs/09 gate #3).
"""

from __future__ import annotations

import pytest
from mpmath import mp

from zeta.leeyang import (
    DEFAULT_PROBES,
    free_energy_normalization,
    ghs_battery,
    ghs_defect,
    ghs_scan,
    ghs_zero_sum,
    log_xi_third_derivative,
    phi_log_concavity,
)


def test_free_energy_normalization_is_one_quarter():
    n = free_energy_normalization()
    assert n["matches_quarter"]
    assert n["constant"] == pytest.approx(0.25, abs=1e-12)
    assert n["spread"] < 1e-12          # constant across h, not fitted


@pytest.mark.slow
def test_two_routes_to_third_derivative_agree():
    # Marked slow 2026-08-23: measured at 631s in CI, over half the fast tier's
    # entire wall time. Under `-n auto` a single test of that length sets the
    # floor for the whole run, so the tier drifted to 19 minutes against the
    # ~115s CLAUDE.md documents, and the next pull request to add any work
    # tipped it past the 30-minute job cap. The cross-check itself is unchanged
    # and still runs — in the slow tier, which is where a three-point
    # high-precision stencil sweep belongs.
    for w in (1.0, 5.0, 20.0):
        a = log_xi_third_derivative(w)
        b = ghs_zero_sum(w)
        assert a == pytest.approx(b, rel=2e-4)
        assert a < 0 and b < 0          # sign convention pinned by agreement


def test_mp_diff_on_xi_is_the_documented_trap():
    """Regression: the obvious derivative silently vanishes."""
    from zeta.core import xi

    with mp.workdps(30):
        bad = mp.diff(lambda x: mp.log(xi(mp.mpf(0.5) + x)), mp.mpf(5), 3)
    assert abs(bad) < 1e-40             # ~1e-47 measured; the true value is 1.65e-3
    assert abs(ghs_zero_sum(5.0)) > 1e-4


def test_ghs_holds_for_zeta():
    s = ghs_scan(DEFAULT_PROBES, source="zeta")
    assert s["ghs_holds_on_probes"]
    assert s["violations"] == []
    assert s["max_defect"] < 0


def test_phi_is_positive_and_log_concave():
    lc = phi_log_concavity()
    assert lc["log_concave"]
    assert lc["max_value"] < -70.0      # measured -74.93 at u = 0


def test_zero_sum_truncation_bias_is_conservative():
    """More zeros must make the sum MORE negative, never less — the omitted
    terms have sign -12w/gamma^4, so truncation cannot manufacture a pass."""
    few = ghs_zero_sum(5.0, n_zeros=200)
    many = ghs_zero_sum(5.0, n_zeros=2000)
    assert many <= few


@pytest.mark.slow
def test_battery_ghs_distinguishes_nothing():
    b = ghs_battery()
    assert b["zeta"]["ghs_holds_on_probes"]
    assert b["dh"]["ghs_holds_on_probes"]
    assert b["separates"] is False
    assert b["max_route_gap"] < 1e-3
    assert "distinguishes nothing" in b["verdict"]
