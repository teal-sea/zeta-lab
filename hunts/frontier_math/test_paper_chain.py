"""Controls for paper_chain.py (the band-lattice dual at the paper field).

Fast versions: the dual instances here use G = 120 (vs the audit's 400) so
the whole file stays in seconds; the tail majorant grows ~3x, which only
tightens every inequality being tested.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import (  # noqa: E402
    A,
    PaperBandDual,
    PaperChain,
    derivative_pin_control,
    explicit_single_pair_adversary,
    kernel_identity_control,
    phipap,
    series_pin_control,
)


@pytest.fixture(scope="module")
def bd() -> PaperBandDual:
    return PaperBandDual(G=120.0)


def test_kernel_identity_is_mt_g():
    """(phihat_mt(2 pi u)/A)^2 == g_kernel(u) to 1e-12: this field's
    incidence weight IS the Montgomery-Taylor kernel."""
    assert kernel_identity_control() < 1e-12


def test_normalisation_matches_closed_form():
    s2 = math.sqrt(2.0)
    assert abs(A - 2 * math.sin(s2 / 2) / s2) < 1e-14
    assert abs(complex(phipap(0j)).real - A) < 1e-14


def test_derivative_pins():
    """Closed-form d1/d2 vs central differences at 20 scattered points."""
    rec = derivative_pin_control()
    assert rec["d1_worst"] < 1e-6
    assert rec["d2_worst"] < 1e-6


def test_series_fallback_joins_closed_form():
    """The Taylor branch and the closed form agree at the threshold."""
    rec = series_pin_control()
    worst = max(v for r in rec.values() for v in r.values())
    assert worst < 1e-7


def test_no_missed_band_clears(bd):
    """Completeness: off-band curvature test clears with worst ratio
    > 100 at every probe depth (no allowance term enters the cap)."""
    for y in (0.02, 0.1, 0.3, 0.49):
        rec = bd.no_missed_band(y)
        assert rec["clear"], f"y={y}: completeness did not clear"
        assert rec["worst_ratio"] > 100, (
            f"y={y}: worst ratio {rec['worst_ratio']:.1f} <= 100")


def test_cross_band_drop_is_one_sided(bd):
    """omega^2 >= 0 (a square): dropping cross-band charges cannot help."""
    rs = np.arange(0.0, 120.0, 0.02)
    assert float(np.min(bd.pc.omega2(rs.astype(complex)))) >= 0.0


def test_theta_one_diverges(bd):
    """At theta = 1 the internal charge vanishes and stacking is
    unbounded: the cap must be infinite."""
    rec = bd.cap(1.0, 0.49)
    assert not math.isfinite(rec["cap"])


def test_theta_star_holds_and_next_grid_point_fails(bd):
    """cap <= slack at theta = 0.995 at every probe depth; the next grid
    theta (0.999) fails at the deep end."""
    for y in (0.02, 0.1, 0.3, 0.49):
        rec = bd.cap(0.995, y)
        assert rec["cap"] <= bd.pc.slack(y), f"y={y}"
    rec = bd.cap(0.999, 0.49)
    assert rec["cap"] > bd.pc.slack(0.49)


def test_adversary_stays_inside_cap(bd):
    """The measured greedy adversary (primal) stays strictly inside the
    dual cap at the reported theta."""
    theta = 0.995
    for y in (0.3, 0.49):
        rec = explicit_single_pair_adversary(bd.pc, y, theta=theta,
                                             halfrange=120.0)
        measured = rec["D"] - (1 - theta) * rec["R"]
        cap = bd.cap(theta, y)["cap"]
        assert measured < cap, f"y={y}: {measured} !< {cap}"


def test_free_ratio_below_half(bd):
    """The whole band sum granted free stays under half the slack."""
    for y in (0.02, 0.49):
        assert bd.free_ratio(y) < 0.5


def test_paper_field_differs_from_t1_field():
    """The two incidence kernels genuinely differ (this module is not a
    re-run of the same numbers): W at the first T1 band centre."""
    from mt_chain import MTChain
    pc, mt = PaperChain(), MTChain()
    gs = np.array([6.95])
    assert abs(float(pc.W(gs, 0.3)[0]) - float(mt.W(gs, 0.3)[0])) > 1e-3
