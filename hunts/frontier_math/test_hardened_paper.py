"""Controls for hardened_paper.py (the ball-arithmetic pass at the paper
field).

Fast versions: the hardened instance here uses the coarse resolution
rung (coarse 0.05, fine 0.002, k_step 0.005) and G = 120 (vs the
audit's 400), so the file stays in seconds.  A cover-based bound only
moves by the interval overestimation the finer rungs remove, and the
float comparison is run against paper_chain at the same G.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

flint = pytest.importorskip("flint", reason="ball arithmetic needs python-flint")

from hardened_paper import (  # noqa: E402
    A_BALL,
    HardenedPaper,
    cross_backend_spot_check,
    interval_amplification,
    singular_branch_vs_mpmath,
    theta_one_must_fail,
)


@pytest.fixture(scope="module")
def hb() -> HardenedPaper:
    return HardenedPaper(coarse=0.05, fine=0.002, k_step=0.005, G=120.0)


def test_normalisation_ball_matches_closed_form():
    s2 = math.sqrt(2.0)
    a = 2 * math.sin(s2 / 2) / s2
    assert abs(float(A_BALL.mid()) - a) < 1e-15
    assert float(A_BALL.rad()) < 1e-30


def test_singular_branch_pin_vs_mpmath():
    """The Taylor branch of s, s', s'' vs mpmath at high dps: the
    reference value must sit INSIDE every ball (enclosure, not
    estimate), including at points crossing the removable singularity."""
    rows = singular_branch_vs_mpmath()
    assert len(rows) == 27  # 9 points x 3 orders
    for r in rows:
        assert r["inside"], (
            f"mpmath reference outside the ball at u={r['u']} "
            f"({r['which']}): defect {r['defect']:.2e} > rad {r['rad']:.2e}"
        )
    # and the balls are tight, not vacuous
    assert max(r["rad"] for r in rows) < 1e-30


def test_interval_amplification_is_modest():
    """The measurement that admits the interval-argument route: the
    hunt window amplified input radii ~1.8e5; the paper field must stay
    O(1) at the first band and decay with g."""
    prof = interval_amplification()
    amps = {g: amp for g, _, amp in prof}
    assert amps[1.05] < 2.0
    assert amps[300.0] < 0.01
    assert amps[300.0] < amps[1.05]  # decaying with g


def test_no_missed_band_directed_endpoints(hb):
    """Every unflagged coarse cell has f <= 0 THROUGHOUT the cell (the
    cover statement, off-band allowance exactly 0), and the independent
    directed-endpoint curvature witness clears at its own step."""
    for y in (0.1, 0.49):
        rec = hb.scan(y)
        assert rec["off_band_allowance"] == 0.0
        assert rec["n_flagged"] > 0
        cw = hb.curvature_witness(y)
        assert cw["clear"], (
            f"curvature witness at y={y}: worst ratio {cw['worst_ratio']}"
        )
        assert cw["worst_ratio"] > 1.0


def test_hardened_vs_float_cap(hb):
    """Hardened cap vs paper_chain's float cap at matched (theta, y, G).

    Tighter-than-float is the T1 experience (the cover removes the
    float pass's blanket Lipschitz margins) and is NOT required; but a
    hardened cap more than 5% above float would suggest a defect, and
    any loosening at all is quantified in the failure message."""
    from paper_chain import PaperBandDual

    bd = PaperBandDual(G=120.0)
    for y in (0.1, 0.3, 0.49):
        cf = bd.cap(0.99, y)["cap"]
        ch = hb.cap_up(0.99, y)["cap"]
        assert ch <= cf * 1.05, (
            f"hardened cap LOOSER than float at y={y}: {ch:.6e} vs "
            f"{cf:.6e} (ratio {ch / cf:.4f}) — more than 5%; a large "
            f"loosening suggests a defect, not a rounding cost"
        )


def test_hardened_cap_stays_below_enclosed_slack(hb):
    """The per-depth verdict at theta = 0.99, both sides one-sided:
    cap rounded up, slack rounded down."""
    for y in (0.1, 0.3, 0.49):
        r = hb.verdict(0.99, y)
        assert r["closes"], (
            f"y={y}: cap {r['cap_up']:.6e} > slack {r['slack_lo']:.6e}"
        )
        assert r["slack_lo"] > 0.0


def test_theta_one_diverges(hb):
    """No charge, unbounded multiplicity: the cap must be infinite."""
    assert not math.isfinite(theta_one_must_fail(hb))


def test_cross_backend_spot_check(hb):
    """flint enclosure midpoints vs mpmath dps 40 at three (band, depth)
    points: disagreement beyond the enclosure radius is a critical
    defect and must fail here, never be widened away."""
    rows = cross_backend_spot_check(hb)
    assert len(rows) == 3
    for r in rows:
        assert r["inside"], (
            f"CRITICAL DEFECT: flint vs mpmath disagree at g={r['g']}, "
            f"y={r['y']}: defect {r['defect']:.2e} > rad {r['rad']:.2e}"
        )
        assert r["rad"] < 1e-30  # the enclosures are tight


def test_band_charge_is_directed_down(hb):
    """The hardened repulsion floor must not exceed the float one
    (float band_charge already subtracts a Lipschitz margin; the ball
    minimum over an interval cover sits at or below the true min)."""
    from paper_chain import PaperBandDual

    bd = PaperBandDual()
    for width in (0.4, 0.8):
        assert hb.band_charge_lo(width) <= bd.band_charge(width) + 1e-12
        assert hb.band_charge_lo(width) > 0.0
