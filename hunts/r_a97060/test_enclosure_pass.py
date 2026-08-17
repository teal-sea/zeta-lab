"""Pins for the enclosure pass over the k=2 tau-table.

Fast tier only: everything here avoids building the 1.9M-cell field envelope
(22 s, and its cache is a gitignored `.npz`).  The full table is `probe.py`
run end to end; what is pinned here is that the enclosure layer agrees with
the double-precision field it is hardening, that the pieces which do not need
the envelope reproduce their published values, and that the depth row's
`u -> 0` corner really is closed.
"""
from __future__ import annotations

import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import pytest

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))
sys.path.insert(0, str(_HERE.parent / "frontier_math"))

import ball_field as BF          # noqa: E402
import k2_closure as K           # noqa: E402
import probe as P                # noqa: E402


ULP = 1e-14   # the measured pass's own double-precision noise, not the ball's


@pytest.mark.parametrize("x", [3.0, 6.5, 12.4, 31.5, 50.0, 100.0])
def test_ball_agrees_with_the_double_precision_field(x):
    """The enclosure must contain what the measured pass computed, or one of
    the two is wrong.  This is the kill condition the HuntSpec names.

    The comparison carries a relative `1e-14` because the ball is the tighter
    object: `k2_closure._D` is a chain of complex `numpy` operations and lands
    a couple of ulps off the true value, while the ball's radius here is
    ~1e-29.  So this pins agreement to double precision, which is all the
    scan-grade side can support -- not containment of the ball by the float.
    """
    e = BF.D_enclosure(0.5, 0.5, x, x)
    v = float(K._D(0.5, x))
    tol = ULP * max(1.0, abs(v))
    assert float(e.lower()) - tol <= v <= float(e.upper()) + tol
    assert abs(float(e.mid()) - v) < tol


def test_ball_agrees_with_kpair():
    for u in (0.5, 3.0, 6.33, 20.0):
        e = BF.kpair_enclosure(u, u)
        v = float(K._kpair(np.array([u]))[0])
        tol = ULP * max(1.0, abs(v))
        assert float(e.lower()) - tol <= v <= float(e.upper()) + tol


def test_phi_series_branch_covers_the_removable_singularity():
    """`ghat` divides by `(z -+ i sqrt2)/2`, which the box `u in [0,U1]`,
    `tau ~ sqrt2` contains.  The scan dodged the point; the enclosure cannot."""
    e = BF.D_enclosure(0.0, 0.02, 1.40, 1.43)
    assert np.isfinite(float(e.upper())) and np.isfinite(float(e.lower()))
    assert float(e.rad()) < 1.0


def test_depth_linear_term_vanishes():
    """`ghat` is even with real Taylor coefficients, so `Re ghat'(i tau) = 0`
    and `D(u,tau) = -G^2 + O(u^2)`.  This is what closes the `u -> 0` corner
    of the depth supremum, and no scan can check it."""
    for tau in (6.33, 6.63, 12.85, 40.0):
        g0 = float(BF.kpair_enclosure(tau, tau).mid())
        for u in (0.01, 0.02, 0.04):
            resid = float(BF.D_enclosure(u, u, tau, tau).mid()) + g0
            # quadratic, not linear: halving u must quarter the residual
            assert abs(resid) < 0.6 * u ** 2 + 1e-12
        r1 = float(BF.D_enclosure(0.02, 0.02, tau, tau).mid()) + g0
        r2 = float(BF.D_enclosure(0.04, 0.04, tau, tau).mid()) + g0
        assert abs(r2 / r1 - 4.0) < 0.05


def test_far_total_exact_matches_the_measured_float_row():
    for ta in (0.0, 30.0, 66.0, 120.0):
        assert abs(float(P.far_total_exact(F(ta).limit_denominator()))
                   - K.far_total(ta)) < 1e-12


def test_budget_floor_is_the_kernel_checked_O8_constant():
    assert P.BUDGET0 == F(51944, 100000) / 2
    assert abs(float(P.BUDGET0) - K.BUDGET0) < 1e-15


def test_c1_enclosure_brackets_the_measured_depth_scan():
    """At the binding cells the enclosure's lower witness must not exceed the
    measured 18-point y-grid value, and its upper bound must not fall below."""
    for i in (316, 331, 642):
        upper, lower, _, _ = P.c1_upper(i)
        ts = np.linspace(i * P.CELL, (i + 1) * P.CELL, 7)
        scan = max(float(np.max(K._dam(2 * y, ts))) / y ** 2 for y in K._YGRID)
        assert lower <= scan + 1e-12
        assert upper >= scan
        assert upper < 2.0 * max(scan, 1e-6)   # and it is not wildly loose


def test_c1_closes_the_cell_that_stalled_a_pure_branch_and_bound():
    """`tau in [6.62,6.64]` sits on a root of `G`, where the direct box bound
    `4 sup D / a^2` stalls at 0.114 against a true value near 0.067.  The
    second-order bound is what brings it down; if it regresses, the whole
    table reports a false nonpositive cell."""
    upper = P.c1_upper(331)[0]
    assert upper < 0.075, f"depth row regressed at the G-root cell: {upper}"


def test_kpair_charge_is_a_lower_bound_without_a_monotonicity_assumption():
    rmin = np.minimum.accumulate(
        [BF.kpair_lower(j * 0.01, (j + 1) * 0.01) for j in range(400)])
    us = np.linspace(0.0, 4.0, 4001)
    true = K._kpair(us)
    for d in (0.5, 1.5, 2.5, 3.9):
        bound = float(rmin[min(399, int(d / 0.01))])
        assert bound <= float(true[us <= d].min()) + 1e-12
