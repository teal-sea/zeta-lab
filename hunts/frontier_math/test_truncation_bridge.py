"""Controls for truncation_bridge.py, the two-sided finite-to-infinite estimate.

What a reader must be able to check without rerunning the audit:

(a) **the rate**.  ``b_m -> b_inf``, and the discrepancy is
    ``(a + b log m)/m`` rather than a pure ``1/m``: the naive power-law
    exponent is pinned (~0.72-0.86 over m in [8, 256], NOT 1), and the
    fitted ``log m / m`` coefficient is pinned against the DERIVED one
    from the corner of c2 at the origin.  The derived coefficient also
    predicts the SIGN, which flips between resonant and non-resonant
    spacings, the mechanism behind the crossing that rules out a
    one-sided lemma;
(b) **E bounds the measured discrepancy** on the full grid
    (m in {2..64}, s in [0.3, 20] mean gaps including the resonances,
    y in {0.02, 0.1, 0.3, 0.49}), with the worst ratio and the headroom
    pinned for both the fully symbolic and the sharpened estimate;
(c) **the reused constant**: C_T is `cluster_universal`'s, re-checked
    both against its recorded value and against its own measurement;
(d) **m0 and the small-m region**: the m0 values are pinned, and the
    finite clusters below m0 are put through the finite instrument
    directly, including the point where that comes back NEGATIVE;
(e) **the planted control**: inflating the discrepancy past the measured
    headroom must break the estimate, or the check has no power.

The identity (*) of the module docstring is checked separately against
the O(m^2) instrument, so the collapse to an O(m) difference sum is not
taken on trust.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import MEAN_GAP, PaperChain  # noqa: E402
from truncation_bridge import (  # noqa: E402
    D_SPLIT, RHO_SUP, E_crude, E_hybrid, b_finite, b_finite_via_instrument,
    b_limit, b_limit_direct, bridge_grid, c_t_reuse_check, cap_side_probe,
    discrepancy, discrepancy_via_identity, harmonic, inverse_square_tail_bound,
    is_resonant, leading_coefficient, m0_uniform, pair_term, rate_record,
    small_m_ladder,
)


# ---------------------------------------------------------------------------
# 0. the two sides are the objects they claim to be
# ---------------------------------------------------------------------------


def test_pair_term_is_the_instruments_T() -> None:
    pc = PaperChain()
    for dt in (0.7, 3.0, 12.566, 41.0):
        for y in (0.02, 0.3, 0.49):
            assert float(pair_term(dt, y)) == pytest.approx(pc.T(dt, y, y),
                                                            abs=1e-13)


def test_the_finite_budget_collapse_matches_the_o_m2_instrument() -> None:
    """b_finite is PaperJoint.budget/m, translation invariance used."""
    for m in (2, 5, 9):
        for x, y in ((1.0, 0.49), (2.05, 0.1)):
            s = x * MEAN_GAP
            assert b_finite(m, s, y) == pytest.approx(
                b_finite_via_instrument(m, s, y), abs=1e-12)


def test_the_poisson_closed_form_matches_direct_summation() -> None:
    """The infinite side: finite Bragg sum vs 20000 direct interactions."""
    for x, y in ((0.5, 0.49), (1.0, 0.3), (2.0, 0.49), (5.0, 0.02)):
        s = x * MEAN_GAP
        assert b_limit(s, y) == pytest.approx(b_limit_direct(s, y), abs=2e-4)


def test_the_difference_identity_reproduces_the_discrepancy() -> None:
    """(*): b_m - b_inf = -(2/m) sum_{d<m} d T(ds) - 2 sum_{d>=m} T(ds)."""
    for m in (2, 8, 32):
        for x, y in ((1.0, 0.49), (2.05, 0.49), (0.3, 0.1)):
            s = x * MEAN_GAP
            assert discrepancy(m, s, y) == pytest.approx(
                discrepancy_via_identity(m, s, y), abs=3e-4)


# ---------------------------------------------------------------------------
# (a) the rate, and the structural story behind it
# ---------------------------------------------------------------------------


def test_the_finite_budget_converges_to_the_limit() -> None:
    for x, y in ((0.3, 0.02), (1.0, 0.49), (2.0, 0.49), (2.05, 0.49),
                 (7.0, 0.3)):
        s = x * MEAN_GAP
        ds = [abs(discrepancy(m, s, y)) for m in (4, 16, 64, 256)]
        assert all(ds[i] > ds[i + 1] for i in range(len(ds) - 1)), (
            f"discrepancy not decreasing at s={x}, y={y}: {ds}")
        assert ds[-1] < 0.08 * max(ds[0], 1e-12)


#: naive power-law exponents of |b_m - b_inf| over m in [8, 256].  They
#: sit BELOW 1 because the decay is (a + b log m)/m, not C/m, the log
#: comes from the corner of c2 at the origin, which contributes a
#: non-oscillating 1/d^2 piece to T(ds).  Pinned so the reading cannot
#: drift into being reported as "1/m".
RATE_RECORD = {
    (2.0, 0.49): 0.810, (2.05, 0.49): 0.722, (1.0, 0.49): 0.815,
    (3.0, 0.3): 0.807, (5.0, 0.1): 0.796, (0.3, 0.02): 0.860,
}


def test_the_convergence_exponent_is_pinned_and_is_not_one() -> None:
    for (x, y), expected in RATE_RECORD.items():
        r = rate_record(x * MEAN_GAP, y)
        assert r["exponent"] == pytest.approx(expected, abs=0.01), (
            f"exponent at s={x}, y={y} moved: {r['exponent']:.4f}")
        assert r["exponent"] < 0.95, (
            "a pure 1/m boundary term would read ~1.0 here; it does not")


def test_the_log_coefficient_matches_the_derived_one() -> None:
    """The sharp test of the boundary story: the fitted coefficient of
    log m / m against the one derived from h'(0+) and h'(1-)."""
    worst = 0.0
    for x, y in list(RATE_RECORD) + [(20.0, 0.49), (1.5, 0.3)]:
        r = rate_record(x * MEAN_GAP, y)
        worst = max(worst, abs(r["fit_over_derived"] - 1.0))
    assert worst < 0.01, f"derived log coefficient off by {worst:.4f}"


def test_the_sign_of_the_discrepancy_flips_with_resonance() -> None:
    """Why no one-sided lemma exists: at commensurate spacing the finite
    budget sits ABOVE the limit, off resonance BELOW.  Derived from the
    sign of L = h'(0+) - h'(1-) [resonant] vs h'(0+) [generic]."""
    for x in (1.0, 2.0, 3.0, 5.0):
        s = x * MEAN_GAP
        assert is_resonant(s)
        assert leading_coefficient(s, 0.49)["L"] > 0
        assert discrepancy(32, s, 0.49) > 0
    for x in (0.3, 1.5, 2.05, 3.05):
        s = x * MEAN_GAP
        assert not is_resonant(s)
        assert leading_coefficient(s, 0.49)["L"] < 0
        assert discrepancy(32, s, 0.49) < 0


# ---------------------------------------------------------------------------
# (c) the reused constant
# ---------------------------------------------------------------------------


def test_the_reused_T_decay_constant_still_holds() -> None:
    rec = c_t_reuse_check()
    assert rec["matches_pinned"], f"C_T moved to {rec['C_T']}"
    assert rec["holds"], (
        f"cluster_universal's own |T| dt^2 measurement now exceeds C_T "
        f"(worst quotient {rec['worst_quotient']})")
    assert rec["worst_quotient"] == pytest.approx(0.6181, abs=1e-3)


def test_the_elementary_tail_bound_is_a_bound() -> None:
    """sum_{d>=m} 1/d^2 <= 1/(m-1/2), the telescoping estimate that keeps
    the statement free of special functions."""
    for m in (1, 2, 5, 40):
        exact = sum(1.0 / d**2 for d in range(m, 200000))
        assert exact <= inverse_square_tail_bound(m)
        assert inverse_square_tail_bound(m) < exact * 1.35


def test_harmonic_numbers() -> None:
    assert harmonic(0) == 0.0
    assert harmonic(4) == pytest.approx(25 / 12)


# ---------------------------------------------------------------------------
# (b) E bounds the measured discrepancy, with pinned headroom
# ---------------------------------------------------------------------------

#: worst measured |b_m - b_inf| / E over the full grid (504 points), and
#: where it happens.  Both estimates hold; the sharpened one is tight
#: enough that its headroom is only x1.22.
GRID_RECORD = {
    "n": 504,
    "worst_crude": 0.3544, "at_crude": (0.3, 0.02, 2),
    "worst_hybrid": 0.8166, "at_hybrid": (0.5, 0.02, 2),
}


def test_E_bounds_the_discrepancy_on_the_whole_grid() -> None:
    g = bridge_grid()
    assert g["n"] == GRID_RECORD["n"]
    assert g["crude_holds"], (
        f"E_crude fails at {g['worst_crude']['s_gaps']} gaps, "
        f"y={g['worst_crude']['y']}, m={g['worst_crude']['m']}")
    assert g["hybrid_holds"], (
        f"E_hybrid fails at {g['worst_hybrid']['s_gaps']} gaps, "
        f"y={g['worst_hybrid']['y']}, m={g['worst_hybrid']['m']}")
    wc, wh = g["worst_crude"], g["worst_hybrid"]
    assert wc["ratio"] == pytest.approx(GRID_RECORD["worst_crude"], abs=2e-3)
    assert wh["ratio"] == pytest.approx(GRID_RECORD["worst_hybrid"], abs=2e-3)
    assert (wc["s_gaps"], wc["y"], wc["m"]) == GRID_RECORD["at_crude"]
    assert (wh["s_gaps"], wh["y"], wh["m"]) == GRID_RECORD["at_hybrid"]
    assert g["headroom_crude"] == pytest.approx(2.82, abs=0.05)
    assert g["headroom_hybrid"] == pytest.approx(1.22, abs=0.02)


def test_E_is_depth_free_and_decreasing_in_m() -> None:
    s = 2.0 * MEAN_GAP
    assert E_crude(8, s, 0.02) == E_crude(8, s, 0.49)
    for x in (0.3, 2.0, 20.0):
        s = x * MEAN_GAP
        vals = [E_crude(m, s) for m in (2, 4, 8, 16, 32, 64, 256)]
        assert all(vals[i] > vals[i + 1] for i in range(len(vals) - 1))
        vals = [E_hybrid(m, s, 0.49) for m in (2, 4, 8, 16, 32, 64, 256)]
        assert all(vals[i] > vals[i + 1] for i in range(len(vals) - 1))


def test_the_sharpened_estimate_is_the_tighter_one() -> None:
    for x, y in ((0.3, 0.02), (1.0, 0.49), (2.0, 0.3), (10.0, 0.49)):
        s = x * MEAN_GAP
        for m in (2, 8, 64):
            assert E_hybrid(m, s, y, D_SPLIT) <= E_crude(m, s)


# ---------------------------------------------------------------------------
# (e) the planted control: the check must be able to fail
# ---------------------------------------------------------------------------


def test_inflating_the_discrepancy_breaks_the_estimate() -> None:
    """Power of the control in (b): scale the measured discrepancy just
    past the measured headroom and both estimates must reject it."""
    g = bridge_grid()
    for key, hold in (("hybrid", "hybrid_holds"), ("crude", "crude_holds")):
        factor = 1.05 / g[f"worst_{key}"]["ratio"]
        gi = bridge_grid(inflate=factor)
        assert not gi[hold], (
            f"E_{key} still bounds a discrepancy inflated by {factor:.3f}, "
            "the grid check has no power")
    # and it must NOT reject just below the headroom
    gj = bridge_grid(inflate=0.95 / g["worst_hybrid"]["ratio"])
    assert gj["hybrid_holds"]


# ---------------------------------------------------------------------------
# (d) m0, and the region below it
# ---------------------------------------------------------------------------

#: m0 against the UNIFORM room (1 - sup rho) b_inf at y = 0.49, sup rho =
#: 0.9286 from cluster_universal.RHO_SUP_RECORD.  These are the numbers
#: that say the bridge is NOT single-digit everywhere: it is m0 = 2 in
#: the sparse regime and O(10^2) near the resonance, O(10^3) at the
#: budget floor s = 1 mean gap where b_inf = 0.0245.
M0_UNIFORM_RECORD = {
    0.3: (152, 101), 1.0: (8454, 6157), 1.5: (110, 69), 2.0: (287, 162),
    2.002: (282, 159), 3.0: (95, 43), 5.0: (26, 2), 10.0: (4, 2),
    20.0: (2, 2),
}


def test_m0_against_the_uniform_room_is_pinned() -> None:
    assert RHO_SUP == 0.9286
    for x, (mc, mh) in M0_UNIFORM_RECORD.items():
        r = m0_uniform(x, 0.49)
        assert (r["m0_crude"], r["m0_hybrid"]) == (mc, mh), (
            f"m0 at s={x} gaps moved to "
            f"({r['m0_crude']}, {r['m0_hybrid']})")


def test_m0_is_not_uniformly_small() -> None:
    """The honest negative: no single-digit m0 covers the family."""
    assert max(mh for _, mh in M0_UNIFORM_RECORD.values()) > 100


@pytest.mark.slow
def test_the_small_m_region_goes_through_the_finite_instrument() -> None:
    """m < m0 by direct finite verdict, and the two points where that
    verdict is what it is.

    At s = 1.0 and s = 2.0 mean gaps, y = 0.49, every rung of the ladder
    closes with a positive per-pair margin.  At the argmax of the rho map
    (s = 2.002 gaps, y = 0.4999) the finite instrument returns a NEGATIVE
    per-pair margin from m = 24 on.  That is recorded, not tuned away,
    and it is gap (G1) rather than a failure of the estimate: the budget
    side of those rungs falls to b_inf exactly as the estimate says
    (0.150154 -> 0.130079 at m = 2 -> 64, b_inf = 0.129891), while the
    finite per-pair CAP rises past the limit instrument's value
    (0.124864 -> 0.136926 against cap_inf = 0.125799 at matched step).
    """
    for x, y in ((1.0, 0.49), (2.0, 0.49)):
        lad = small_m_ladder(x, y, ms=(2, 4, 8, 16, 32))
        assert lad["all_close"], (
            f"a finite rung fails at s={x}, y={y}: {lad['rows']}")
        assert lad["min_margin_pp"] > 0.0
    hard = small_m_ladder(2.002, 0.4999, ms=(2, 8, 24, 32))
    assert not hard["all_close"], (
        "the coarse instrument now closes the argmax family, the recorded "
        "negative rung has moved and the record needs rewriting")
    assert hard["rows"][-1]["margin_pp"] < 0.0
    # and the budget side of those same rungs is the exact one
    for r in hard["rows"]:
        assert r["budget_pp"] == pytest.approx(
            b_finite(r["m"], 2.002 * MEAN_GAP, 0.4999), abs=1e-12)


@pytest.mark.slow
def test_the_cap_side_is_a_named_gap_not_a_result() -> None:
    """(G1) measured: the finite per-pair cap does NOT sit below the
    periodic-limit cap on this grid, so the budget bridge alone does not
    transfer a verdict.  The test pins the failure, not a hope."""
    rec = cap_side_probe(2.0, 0.49, ms=(4, 8, 16))
    assert rec["step"] == 0.005, "the two caps must be read at one step"
    assert not rec["all_below_limit"]
    assert rec["worst_excess"] > 0.0
    caps = [r["cap_pp"] for r in rec["rows"]]
    assert all(caps[i] < caps[i + 1] for i in range(len(caps) - 1)), (
        "the finite per-pair cap at the resonance rises with m; if that "
        "reverses the gap statement needs re-measuring")
    # the shielded spacing: the limit instrument says 0, the finite one
    # does not get there
    sh = cap_side_probe(1.0, 0.49, ms=(4, 16, 32))
    assert sh["cap_inf"] == 0.0
    assert min(r["cap_pp"] for r in sh["rows"]) > 0.03
    # (G3) the limit cap at the argmax, read at the coarse step: below 1
    # but well above its step-0.002 value, and below the finite caps
    arg = cap_side_probe(2.002, 0.4999, ms=(4, 32))
    assert arg["rho_inf"] == pytest.approx(0.9685, abs=3e-3)
    assert arg["rho_inf"] > RHO_SUP
    assert arg["rows"][-1]["cap_pp"] > arg["cap_inf"]
