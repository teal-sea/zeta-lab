"""Controls for negative_margin_probe.py, the crossing that was not there.

`truncation_bridge.py` gap (G1)/(G3) reports a per-pair margin going
negative at the rho argmax (s = 2.002 mean gaps, y = 0.4999) from
m = 24, which read at face value would kill the ``theta = 0.995``
verdict at that configuration.  The probe module answers it; this file
is what a reader checks instead of rerunning the ~40 minutes of grid.

Five controls, one per claim the module makes:

(a) **the reproduction is exact**.  At `truncation_bridge`'s own
    settings, ``PaperJoint(step=0.005, G=60.0)``, theta = 0.995, the
    default delta ladder, no slicing, the ladder comes back to the last
    recorded digit, crossing included.  A probe that could not reproduce
    the finding would have no standing to explain it away;
(b) **the refinement trend is pinned, with its direction**.  The margin
    is monotone INCREASING as the grid step falls and as the resolved
    window grows, at fixed m; the crossing point m* moves OUT under step
    refinement (24 / 48 / 64 / beyond 64 at step 0.005 / 0.002 / 0.001 /
    0.0005) and disappears from the ladder entirely once the window is
    widened.  Both directions are measured here, not asserted, as is
    the negative half: at G = 60 the m -> infinity margin stays below
    zero at every step measured, and that is pinned too;
(c) **the hardened reading, including where it does not bracket**.
    Every ball band height dominates the float instrument's raw grid
    maximum on the same band (a one-sided relation, and it holds), and
    the one-sided margin lower bound at the crossing configuration is
    positive, so the ball instrument decides the case the coarse float
    instrument reported as failing.  The budget comparison comes out the
    other way and is recorded as such: the float lands 6 ulp OUTSIDE the
    ball, which is the float's own accumulation error and is pinned at
    the ulp scale rather than hidden in a loose tolerance;
(d) **the diagnosis is a measurement**.  The cap splits exactly into
    interior + exterior + tail; the interior channel is invariant under
    the window knob, the tail channel is invariant under the step knob
    and under m, the band counts are what the story says they are
    (m-1 interior, 18 exterior at G = 60, 62 at G = 200), and the
    interior per-band sequence rises and decelerates;
(e) **theta = 1 still diverges** on this configuration, in both
    instruments: no charge, so an unbounded multiplicity stack is free
    and the cap must be infinite.  A cap instrument that returned a
    finite number there would be broken in a way that makes every other
    number here meaningless.

Plus one planted control: the attribution has power only if putting a
channel back breaks the refined verdict, so the tail term of the narrow
window is added back to a refined cap and must drive the margin
negative again.

Nothing here computes a proportion and nothing here is evidence about
RH.  The slow tier is marked; the fast tier keeps m <= 16.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import MEAN_GAP  # noqa: E402
from paper_joint import PaperJoint  # noqa: E402
from cluster_universal import b_infty  # noqa: E402
from negative_margin_probe import (  # noqa: E402
    B_INF, BRIDGE_CAPS, BRIDGE_G, BRIDGE_LADDER, BRIDGE_STEP,
    EXTERIOR_TOTAL, HARDENED_RECORD, INTERIOR_LARGE_M, INTERIOR_PER_BAND,
    HARDENED_INSTRUMENT, REFINEMENT_RECORD, S_GAPS, TAIL_PER_PAIR, THETA, Y,
    asymptotic_margin, cap_split, config_pairs, crossing_m,
    hardened_brackets_float, partition_and_multiplicity,
    hardened_margin, interior_limit, interior_saturates, ladder,
    monotone_in_step, monotone_in_window, tail_per_pair, theta_one_diverges,
    theta_one_diverges_hardened, theta_probe,
)

flint = pytest.importorskip("flint", reason="the ball instrument needs acb")


# ---------------------------------------------------------------------------
# (a) the reproduction, at the reporting instrument's own settings
# ---------------------------------------------------------------------------


def test_the_settings_are_stated_and_are_not_the_instrument_defaults():
    """The whole finding is a settings difference, so it must be visible.

    `truncation_bridge.small_m_ladder` and `.cap_side_probe` construct
    ``PaperJoint(step=0.005, G=60.0)``; `paper_joint.PaperJoint`'s own
    defaults are 0.001 and 200.0.  Five times the grid step and a third
    of the window.
    """
    assert (BRIDGE_STEP, BRIDGE_G) == (0.005, 60.0)
    default = PaperJoint()
    assert default.step == 0.001 and default.G == 200.0
    assert BRIDGE_STEP == 5 * default.step
    assert BRIDGE_G < default.G


def test_reproduction_matches_the_reported_ladder_small_m():
    """m <= 16 of the recorded ladder, exactly (fast tier)."""
    lad = ladder((2, 4, 8, 16), BRIDGE_STEP, BRIDGE_G)
    for r in lad["rows"]:
        assert r["margin_pp"] == pytest.approx(BRIDGE_LADDER[r["m"]],
                                               abs=1e-12)
        assert r["cap_pp"] == pytest.approx(BRIDGE_CAPS[r["m"]], abs=1e-12)
    assert lad["crossing_m"] is None, "no crossing yet at m <= 16"


@pytest.mark.slow
def test_reproduction_matches_the_reported_ladder_and_its_crossing():
    """The whole ladder, including the sign change the report is about."""
    lad = ladder(tuple(sorted(BRIDGE_LADDER)), BRIDGE_STEP, BRIDGE_G)
    for r in lad["rows"]:
        assert r["margin_pp"] == pytest.approx(BRIDGE_LADDER[r["m"]],
                                               abs=1e-12)
    assert lad["crossing_m"] == 24
    assert lad["min_margin_pp"] == pytest.approx(-0.00684659255326997,
                                                 abs=1e-12)


def test_the_budget_side_is_not_the_cause():
    """The budget falls toward b_inf exactly as the bridge's estimate
    says; only the cap side moves the sign."""
    lad = ladder((2, 16), BRIDGE_STEP, BRIDGE_G)
    b2, b16 = (r["budget_pp"] for r in lad["rows"])
    assert b2 == pytest.approx(0.150154, abs=5e-7)
    assert b_infty(S_GAPS * MEAN_GAP, Y) == pytest.approx(B_INF, rel=1e-12)
    assert b16 > B_INF > 0.1298
    # the budget is step- and window-free: it is exact arithmetic
    other = ladder((16,), 0.002, 200.0)["rows"][0]
    assert other["budget_pp"] == pytest.approx(b16, rel=1e-14)


# ---------------------------------------------------------------------------
# (b) the refinement trend, in both knobs, with its direction pinned
# ---------------------------------------------------------------------------


def test_margin_increases_as_the_grid_refines():
    """Direction stated: a coarser grid inflates the cap, so refining can
    only move the margin UP.  Measured at m = 16 over three steps."""
    rec = monotone_in_step(16, steps=(0.005, 0.002, 0.001), G=BRIDGE_G)
    assert rec["increasing_as_step_falls"], rec["rows"]
    assert rec["total_move"] > 0.005
    got = {r["step"]: r["margin_pp"] for r in rec["rows"]}
    for step in (0.005, 0.002, 0.001):
        assert got[step] == pytest.approx(REFINEMENT_RECORD[(16, step, 60.0)],
                                          abs=1e-9)


def test_margin_increases_as_the_window_widens():
    """The dominant knob: the window, at fixed grid step."""
    rec = monotone_in_window(16, Gs=(30.0, 60.0, 120.0), step=0.002)
    assert rec["increasing_as_window_grows"], rec["rows"]
    got = {r["G"]: r["margin_pp"] for r in rec["rows"]}
    for G in (30.0, 60.0, 120.0):
        assert got[G] == pytest.approx(REFINEMENT_RECORD[(16, 0.002, G)],
                                       abs=1e-9)
    # the window moves the margin further than the step does
    assert got[120.0] - got[30.0] > 0.04


def test_the_narrow_window_is_where_the_sign_lives():
    """At G = 30 the ladder is negative from m = 16, the same instrument
    with the window halved fails at a cluster size that closes at G = 60.
    A verdict that flips under a window change is a window measurement."""
    lad = ladder((16,), 0.002, 30.0)
    assert lad["rows"][0]["margin_pp"] < 0
    assert ladder((16,), 0.002, 60.0)["rows"][0]["margin_pp"] > 0


@pytest.mark.slow
def test_the_crossing_point_moves_out_under_step_refinement():
    """m* = 24 / 48 / 64 / beyond 64 at step 0.005 / 0.002 / 0.001 /
    0.0005: the crossing is not a fixed feature of the configuration.
    The live check is the first two; the rest is the pinned record,
    which the other refinement tests re-measure."""
    assert crossing_m(ladder((16, 24, 32), 0.005, BRIDGE_G)["rows"]) == 24
    assert crossing_m(ladder((16, 24, 32), 0.002, BRIDGE_G)["rows"]) is None
    assert crossing_m(ladder((48,), 0.002, BRIDGE_G)["rows"]) == 48
    ms = (2, 4, 8, 16, 24, 32, 48, 64)
    for step, expected in ((0.005, 24), (0.002, 48), (0.001, 64)):
        rows = [{"m": m, "margin_pp": REFINEMENT_RECORD[(m, step, 60.0)]}
                for m in ms if (m, step, 60.0) in REFINEMENT_RECORD]
        assert crossing_m(rows) == expected, step
    assert REFINEMENT_RECORD[(64, 0.0005, 60.0)] > 0


@pytest.mark.slow
def test_no_crossing_survives_the_refined_corner():
    """step 0.001, G = 200: the ladder is positive with room at every m
    that was negative at (0.005, 60)."""
    lad = ladder((24, 48), 0.001, 200.0)
    for r in lad["rows"]:
        assert r["margin_pp"] > 0.015, r
        assert BRIDGE_LADDER[r["m"]] < 0, "these are the m that went negative"
    assert lad["crossing_m"] is None


def test_the_refinement_record_is_the_measurement_it_claims_to_be():
    """Spot-check of the pinned table against a live run (fast entries)."""
    for key in ((2, 0.002, 60.0), (8, 0.002, 60.0), (16, 0.002, 200.0)):
        m, step, G = key
        got = ladder((m,), step, G)["rows"][0]["margin_pp"]
        assert got == pytest.approx(REFINEMENT_RECORD[key], abs=1e-9), key


# ---------------------------------------------------------------------------
# (c) the ball-arithmetic reading
# ---------------------------------------------------------------------------


def test_the_ball_budget_does_not_quite_bracket_the_float_budget():
    """A negative result, recorded rather than widened away.

    The arb ball for the m = 8 budget has width ~4e-16 around the exact
    value; ``PaperJoint.budget`` sums the same 28 pair terms in double
    precision and lands 6 ulp BELOW the ball's lower endpoint.  So the
    bracket FAILS, and what it exposes is the float instrument's own
    accumulation error, not a defect in the ball.  Pinned at the ulp
    scale so that a real disagreement (anything above ~1e-12 relative)
    would break this test instead of hiding inside a loose tolerance.
    """
    rec = hardened_brackets_float(m=8, G=BRIDGE_G)
    assert rec["budget_bracketed"] is False
    assert abs(rec["float_defect_ulp"]) <= 32, rec["float_defect_ulp"]
    assert rec["float_agrees_to_1e14"], rec
    assert rec["budget_ball_width"] < 1e-14


def test_every_ball_band_height_dominates_the_float_grid_maximum():
    """The float ``max f`` over grid points is a lower bound on the true
    band maximum; the ball ``F`` is an upper bound on it.  So the ball
    heights must dominate, band by band."""
    rec = hardened_brackets_float(m=8, G=BRIDGE_G)
    assert rec["heights_dominate"], rec["worst_float_minus_hardened_F"]
    assert rec["n_bands_hardened"] >= 20


@pytest.mark.slow
def test_the_ball_instrument_decides_the_crossing_configuration_positive():
    """The headline, hardened: m = 24 at G = 60, the very configuration
    the coarse float instrument reported at -0.00264, has a strictly
    positive one-sided margin lower bound under ball arithmetic.

    ``margin_lo_pp`` is one-sided: positive means this instrument closes
    the configuration; a value straddling zero would mean the cover does
    not decide it, which is reported as such rather than resolved (see
    the m = 64 case below).
    """
    rec = hardened_margin(m=24, G=BRIDGE_G, coarse=0.02, fine=0.002)
    assert rec["decided"] is True
    assert rec["margin_lo_pp"] > 0.003
    assert rec["margin_lo_pp"] == pytest.approx(
        HARDENED_RECORD[(24, 60.0, 0.002)]["margin_lo_pp"], abs=1e-8)
    assert BRIDGE_LADDER[24] < 0 < rec["margin_lo_pp"]


def test_the_ball_instrument_leaves_m64_at_the_narrow_window_undecided():
    """The honest half of the hardening, pinned from the record.

    At m = 64, G = 60, cover 0.02/0.002 the one-sided margin lower bound
    is -0.000211: the ball instrument does NOT decide that cluster at
    the reported window.  That is "undecided at this cover", not a
    counterexample, refining the cover to 0.001 turns it positive
    (+0.000345), and the float readings around it straddle zero too
    (-0.000569 at step 0.001, +0.000191 at step 0.0005).  The same m at
    G = 200 is decided positive by a wide margin.
    """
    narrow = HARDENED_RECORD[(64, 60.0, 0.002)]
    assert narrow["decided"] is False
    assert -1e-3 < narrow["margin_lo_pp"] < 0
    finer = HARDENED_RECORD[(64, 60.0, 0.001)]
    assert finer["decided"] and 0 < finer["margin_lo_pp"] < 1e-3
    assert REFINEMENT_RECORD[(64, 0.001, 60.0)] < 0
    assert REFINEMENT_RECORD[(64, 0.0005, 60.0)] > 0
    wide = HARDENED_RECORD[(64, 200.0, 0.002)]
    assert wide["decided"] and wide["margin_lo_pp"] > 0.018


@pytest.mark.slow
def test_the_ball_cap_sits_between_the_coarse_and_fine_float_caps():
    """Consistency reading, not a theorem: both are upper bounds on the
    same supremum, computed differently (a cover owes no slope margin, a
    point grid does).  The ball cap landing between the float caps at
    step 0.002 and step 0.0005 is what that predicts, and is pinned so a
    drift in either instrument shows up."""
    rec = hardened_margin(m=8, G=BRIDGE_G, coarse=0.02, fine=0.002)
    coarse = ladder((8,), 0.002, BRIDGE_G)["rows"][0]["cap_pp"]
    fine = ladder((8,), 0.0005, BRIDGE_G)["rows"][0]["cap_pp"]
    assert fine < rec["cap_up_pp"] < coarse, (fine, rec["cap_up_pp"], coarse)


def test_the_hardened_record_names_its_instrument():
    """An enclosure without its cover settings is not a statement."""
    for key in ("theta", "coarse", "fine", "k_step", "prec_bits"):
        assert key in HARDENED_INSTRUMENT
    from flint import ctx

    assert ctx.prec == HARDENED_INSTRUMENT["prec_bits"]
    assert HARDENED_INSTRUMENT["theta"] == THETA
    # every row carries its own (m, G, fine) and a decided flag that is
    # the sign of the one-sided bound, never a judgement call
    for (m, G, fine), rec in HARDENED_RECORD.items():
        assert isinstance(m, int) and isinstance(G, float)
        assert fine in (0.001, 0.002)
        assert rec["decided"] == (rec["margin_lo_pp"] > 0), (m, G, fine)
    assert any(not r["decided"] for r in HARDENED_RECORD.values()), (
        "a hardened record with no undecided row would mean the cover "
        "was chosen after seeing the answer")


# ---------------------------------------------------------------------------
# (d) the diagnosis, as measurements
# ---------------------------------------------------------------------------


def test_the_split_reproduces_the_instrument_exactly():
    """The decomposition is the cap, not a model of it."""
    for m in (2, 8, 16):
        d = cap_split(m, 0.002, BRIDGE_G)
        pj = PaperJoint(step=0.002, G=BRIDGE_G)
        cap = pj.cap(config_pairs(m), THETA)["cap"] / m
        assert d["cap_pp"] == pytest.approx(cap, rel=1e-12), m
        assert d["interior_pp"] + d["exterior_pp"] + d["tail_pp"] == \
            pytest.approx(cap, rel=1e-12)
        assert d["off_band_allowance"] == 0.0


def test_the_band_counts_are_what_the_story_says():
    """Claim: m-1 interior bands, and an exterior count set by the window
    alone (18 at G = 60, 62 at G = 200).  Pinned, not asserted."""
    for m in (2, 8, 16):
        assert cap_split(m, 0.002, BRIDGE_G)["n_interior"] == m - 1
        assert cap_split(m, 0.002, BRIDGE_G)["n_exterior"] == 18
    assert cap_split(8, 0.002, 200.0)["n_exterior"] == 62


def test_the_interior_channel_is_invariant_under_the_window():
    """If the window knob acted on the interior bands the diagnosis would
    be wrong.  It does not: the interior totals at G = 60 and G = 200
    agree to 6e-12 relative, which is grid alignment, not structure."""
    a = cap_split(8, 0.002, BRIDGE_G)
    b = cap_split(8, 0.002, 200.0)
    # not bit-identical: the field grid starts at min(t) - G, so the
    # sample points inside the bands shift.  6e-12 relative, measured.
    assert a["interior_pp"] == pytest.approx(b["interior_pp"], rel=1e-9)
    assert a["interior_pp"] != b["interior_pp"]
    assert a["n_interior"] == b["n_interior"]
    assert b["exterior_pp"] > a["exterior_pp"]  # more bands resolved
    assert b["tail_pp"] < a["tail_pp"]          # less charged to the tail


def test_the_tail_channel_is_invariant_under_m_and_under_the_step():
    """The term that carries the comparison: charged per pair, so it is
    the same number for every cluster size and every grid step, and it
    is what the periodic instrument does not pay at all."""
    for m in (2, 8, 16):
        for step in (0.005, 0.002):
            d = cap_split(m, step, BRIDGE_G)
            assert d["tail_pp"] == pytest.approx(TAIL_PER_PAIR[60.0],
                                                 rel=1e-12), (m, step)
    for G in (60.0, 200.0, 400.0):
        assert tail_per_pair(G) == pytest.approx(TAIL_PER_PAIR[G], rel=1e-12)
    # at the reported window it is a fifth of the whole budget
    assert TAIL_PER_PAIR[60.0] / B_INF == pytest.approx(0.2086, abs=2e-4)
    # and it is bigger than the deficit it is being blamed for
    assert TAIL_PER_PAIR[60.0] > abs(BRIDGE_LADDER[64])


def test_the_rival_explanations_are_ruled_out_by_numbers():
    """Candidates (i) and (ii) for the cap's m-dependence, measured.

    (i) *more, narrower bands at the cluster ends*: bands per pair FALL
        with m (1 + 17/m at G = 60), and the interior bands are NARROWER
        than the periodic instrument's single band, narrower means a
        higher repulsion floor and a cheaper completion, so this channel
        pushes the wrong way to be the cause.
    (ii) *the completion multiplicity m* rises*: it does, but only from
        3.886 to 4.657 over m = 2 -> 16 (integer m* = 4 -> 5), and it
        rises because F rises, ``m* = (F + cK)/(2cK)``, so it is
        downstream of the interior channel rather than beside it.
    """
    small = partition_and_multiplicity(2, 0.002, BRIDGE_G)
    big = partition_and_multiplicity(16, 0.002, BRIDGE_G)
    assert small["n_bands"] == 2 + 17 and big["n_bands"] == 16 + 17
    assert big["bands_per_pair"] < small["bands_per_pair"]
    assert big["interior_width_max"] < big["periodic_width"], (
        big["interior_width_max"], big["periodic_width"])
    assert big["periodic_bands"] == 1
    assert 3.5 < small["m_star_max"] <= big["m_star_max"] < 6
    assert big["interior_F_max"] > small["interior_F_max"]


def test_the_interior_channel_rises_and_decelerates():
    """The one genuine m-effect, measured: per-interior-band completion
    rises with cluster size and its increments shrink."""
    for m, v in INTERIOR_PER_BAND.items():
        if m > 16:
            continue
        d = cap_split(m, 0.002, BRIDGE_G)
        assert d["interior_per_band"] == pytest.approx(v, rel=1e-9), m
    seq = [INTERIOR_PER_BAND[m] for m in sorted(INTERIOR_PER_BAND)]
    incs = [seq[i + 1] - seq[i] for i in range(len(seq) - 1)]
    assert all(i > 0 for i in incs), incs
    assert all(incs[i + 1] < incs[i] for i in range(len(incs) - 1)), incs


def test_the_exterior_channel_is_a_one_over_m_term():
    """Its TOTAL barely moves with m, so per pair it decays like 1/m,
    which is why it cannot be what makes the cap rise."""
    tot = [EXTERIOR_TOTAL[m] for m in sorted(EXTERIOR_TOTAL)]
    assert max(tot) / min(tot) < 1.25
    for m in (2, 8, 16):
        d = cap_split(m, 0.002, BRIDGE_G)
        assert d["exterior_pp"] * m == pytest.approx(EXTERIOR_TOTAL[m],
                                                     rel=1e-9), m


@pytest.mark.slow
def test_the_interior_limit_stays_under_the_periodic_instrument():
    """Channel 1 saturates below `cluster_universal.periodic_cap`'s own
    per-period number, so it cannot on its own carry the finite cap past
    the infinite-lattice cap."""
    rec = interior_saturates(ms=(2, 4, 8, 16, 24, 32), step=0.002)
    assert rec["rising"] and rec["decelerating"]
    assert rec["periodic_bands"] == 1
    assert rec["below_periodic"], (rec["extrapolated_limit"],
                                   rec["periodic_cap"])
    assert rec["extrapolated_limit"] < 0.11


def test_the_attribution_has_power():
    """Planted control.  If the tail channel is not what carries the
    reported deficit, putting the narrow window's tail back onto a
    refined cap should leave the margin positive.  At m = 32 it does
    not: adding ``tail_pp(60) - tail_pp(200)`` back to the (0.002, 200)
    margin drives it negative again, so the attribution is doing work
    rather than describing.

    At m = 24 the same penalty leaves +0.00126, the configuration is
    close enough to the boundary at G = 60 that one channel does not
    account for the whole deficit there, which is why the m -> infinity
    reading is used for the general statement rather than a single m.
    """
    penalty = TAIL_PER_PAIR[60.0] - TAIL_PER_PAIR[200.0]
    at32 = REFINEMENT_RECORD[(32, 0.002, 200.0)]
    assert at32 > 0
    assert at32 - penalty < 0, (at32, penalty)
    at24 = REFINEMENT_RECORD[(24, 0.002, 200.0)]
    assert 0 < at24 - penalty < 0.002, at24 - penalty
    # and the penalty alone cannot rescue the already-negative coarse
    # row, so the control is not vacuous in the other direction
    assert REFINEMENT_RECORD[(24, 0.005, 60.0)] + penalty > 0


def test_the_asymptotic_reading_is_two_sided_and_agrees_in_sign():
    """The m -> infinity statement, both readings, at both windows.

    At G = 60 both readings are negative at every measured step: the
    reported window does not close unbounded clusters here, and that is
    recorded rather than extrapolated away.  At G >= 120 both are
    positive.  Where the two readings disagreed in sign nothing would be
    claimed.
    """
    narrow = asymptotic_margin(0.001, 60.0)
    assert narrow["sign_agrees"] and not narrow["closes_for_all_m"]
    assert narrow["margin_pp_optimistic"] < 0
    assert narrow["margin_pp_optimistic"] == pytest.approx(-0.000785,
                                                           abs=1e-5)
    for G in (120.0, 200.0, 400.0):
        wide = asymptotic_margin(0.001, G)
        assert wide["sign_agrees"] and wide["closes_for_all_m"], G
        assert wide["margin_pp_pessimistic"] > 0.013, G
    # and refining the step moves the narrow-window limit UP, as the
    # step channel says it must
    assert (asymptotic_margin(0.001, 60.0)["margin_pp_optimistic"]
            > asymptotic_margin(0.002, 60.0)["margin_pp_optimistic"])


def test_the_interior_sequence_is_measured_not_modelled():
    """The limit statements rest on this sequence; it is pinned, and its
    increments are pinned collapsing, out to m = 128."""
    seq = INTERIOR_LARGE_M[0.001]
    ms = sorted(seq)
    assert ms[-1] == 128
    incs = [seq[ms[i + 1]] - seq[ms[i]] for i in range(len(ms) - 1)]
    assert all(i > 0 for i in incs), incs
    assert incs[-1] < incs[-2] / 5, incs[-2:]
    lim = interior_limit(seq)
    assert lim["last"] < lim["richardson"], lim
    assert lim["richardson"] - lim["last"] < 2e-4, lim


# ---------------------------------------------------------------------------
# (e) theta = 1 must still diverge on this configuration
# ---------------------------------------------------------------------------


def test_theta_one_diverges_in_the_float_instrument():
    rec = theta_one_diverges(m=4, step=0.002, G=BRIDGE_G)
    assert rec["float_infinite"]
    assert rec["float_cap"] == math.inf


def test_theta_one_diverges_in_the_ball_instrument():
    rec = theta_one_diverges_hardened(m=2, G=BRIDGE_G)
    assert rec["hardened_infinite"]
    assert rec["hardened_cap"] == math.inf


def test_theta_below_one_is_finite_and_ordered():
    """Sanity on the retention knob: a smaller theta is a larger internal
    charge, hence a smaller cap and a larger margin."""
    pj = PaperJoint(step=0.002, G=BRIDGE_G)
    pairs = config_pairs(8)
    caps = [pj.cap(pairs, th)["cap"] for th in (0.9, 0.99, 0.995)]
    assert all(math.isfinite(c) for c in caps)
    assert caps[0] < caps[1] < caps[2]


@pytest.mark.slow
def test_the_configuration_closes_at_the_retention_of_record():
    """What retention this configuration actually permits at the refined
    instrument.  The crossing was not real, so this is room rather than
    a bound: 0.995 closes, with the margin ordered in theta."""
    rec = theta_probe(m=16, thetas=(0.9, 0.99, 0.995), step=0.001, G=200.0)
    assert rec["largest_closing_theta"] == 0.995
    margins = [r["margin_pp"] for r in rec["rows"]]
    assert margins[0] > margins[1] > margins[2] > 0
