"""Tests for zeta.synthesis — the mean power of the prime signal.

Every literal was measured in this environment before being asserted.
Measured at N = 10⁶ with 1000 cached zeros:

    closed form  2 + γ_Euler − log 4π   = 0.04619142
    zero side    partial + tail          = 0.04619200  (gap 5.8e-7)
    prime side   window u ≥ 6            = 0.04693046  (gap 7.4e-4)
    RMS amplitude √P                     = 0.2149

The prime-side window approaches P *from above* as the start moves up
(0.0831 → 0.0531 → 0.0469 → 0.0454 at u₀ = 2, 4, 6, 8), which is the
dropped archimedean and trivial-zero content thinning out.  That monotone
approach is asserted, because a prime-side average that converged from
below would mean the signal was being normalised wrong.
"""

from __future__ import annotations

import pytest

from zeta.synthesis import (
    MEAN_POWER_CLOSED_FORM,
    closed_form_power,
    mean_power_prime_side,
    mean_power_zero_side,
    power_report,
)


def test_closed_form_matches_pinned_constant():
    assert closed_form_power() == pytest.approx(MEAN_POWER_CLOSED_FORM, rel=1e-14)
    assert closed_form_power() == pytest.approx(0.0461914179, abs=1e-10)


def test_zero_side_reproduces_closed_form():
    z = mean_power_zero_side(1000)
    assert z["total"] == pytest.approx(closed_form_power(), abs=2e-6)
    # the tail is a real contribution, not a rounding nudge
    assert z["tail_estimate"] > 1e-3
    assert z["tail_is_estimate_not_bound"] is True


def test_zero_side_partial_sum_is_below_total():
    """Every omitted zero adds positive weight, so truncation under-counts."""
    z_small = mean_power_zero_side(200)
    z_big = mean_power_zero_side(1000)
    assert z_small["partial_sum"] < z_big["partial_sum"] < closed_form_power()


def test_prime_side_converges_from_above():
    p = mean_power_prime_side(N=10**6, n_samples=100_000)
    conv = p["convergence"]
    starts = sorted(conv)
    vals = [conv[s] for s in starts]
    assert all(a > b for a, b in zip(vals, vals[1:]))   # monotone decreasing
    assert vals[-1] == pytest.approx(closed_form_power(), abs=5e-3)


def test_rms_amplitude():
    r = power_report(N=10**6, n_samples=100_000)
    assert r["rms_amplitude"] == pytest.approx(0.2149, abs=1e-4)
    assert r["zero_gap"] < 1e-5
    assert r["prime_gap"] < 5e-3
    assert "not evidence" in r["note"] or "not RH" in r["note"]


@pytest.mark.slow
def test_prime_side_improves_with_range():
    """A decade more sieve must move the window average toward P."""
    small = mean_power_prime_side(N=10**6, n_samples=200_000, u_start=8.0)
    big = mean_power_prime_side(N=10**7, n_samples=400_000, u_start=8.0)
    target = closed_form_power()
    assert abs(big["mean_power"] - target) < abs(small["mean_power"] - target)
