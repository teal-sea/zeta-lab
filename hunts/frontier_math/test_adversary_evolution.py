"""Controls for adversary_evolution.py, the adversarial global search.

The module's claim is a NEGATIVE: a global search over finite pair
configurations at theta = 0.995 reached no configuration whose margin
stayed nonpositive at the promotion instrument.  A negative is worth
exactly as much as the instrument and the search behind it, so these are
the checks a reader needs:

(a) **the search works**, from RANDOM starts the optimiser walks back
    to the regime `cluster_universal.py` already knows binds: the deep
    edge, spacings in the coupled band, and a score at or below the best
    resonant lattice at that k.  Load-bearing: if it cannot rediscover a
    known hard configuration, its failure to find a new one measures
    nothing;
(b) **the search has detector power**, with the damage field inflated
    by a planted factor the same search finds a negative margin, and
    finds it in the first handful of scores;
(c) **the instrument is honest**, the one-pass evaluator with the exact
    tail reproduces `PaperJoint.cap` to 1e-12, the conservative tail is
    one-sided (never smaller), and refining the instrument raises the
    margin, so a positive search margin is a positive fine margin;
(d) theta = 1 diverges (no internal charge, unbounded multiplicity
    stack);
(e) the recorded worst configuration reproduces from its recorded
    parameters at BOTH instruments, and every recorded near miss
    reproduces its margin.

Plus the m-scaling record: the per-pair margin ladder at the resonance,
the fitted law, and the crossing verdict, with a synthetic control that
the crossing detector is not vacuous.  The ladder to m = 64, the
rediscovery control and the campaign are marked slow.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from adversary_evolution import (  # noqa: E402
    CAMPAIGN_RECORD, Evaluator, FAST_G, FAST_STEP, InflatedEvaluator,
    M_SCALING_RECORD, NEAR_MISS_REL, P_CONSERVATIVE, PROMOTE_G,
    PROMOTE_STEP, RESONANCES, THETA_FULL, WORST_FOUND, Book,
    build_config, campaign, cmaes_lite, commensurate, coordinate_polish,
    depth_gradient_lattice,
    fit_m_law, free_bounds, free_pack, free_unpack, jittered_lattice,
    lattice, m_ladder, phipap_trio, planted_detection_control,
    primal_check, primal_sweep, promote, rediscovery_control,
    resolution_ladder, run_differential_evolution, structured_seeds,
    theta_one_control, two_scale,
)
from paper_chain import (  # noqa: E402
    MEAN_GAP, PaperBandDual, phipap, phipap_d1, phipap_d2,
)
from paper_joint import PaperJoint  # noqa: E402

#: one shared coarse instrument, so the K_of and band caches are warm
EV = Evaluator()
PJ = PaperJoint(step=FAST_STEP, G=FAST_G)


# ---------------------------------------------------------------------------
# (c) the instrument
# ---------------------------------------------------------------------------


def test_trio_matches_paper_chain():
    """The shared-trigonometry kernel is the same closed form.

    Probes cross the |u| < 1e-4 series threshold at both singular points
    z = +-sqrt2, which is where a shared-subexpression rewrite would
    break if it broke anywhere.
    """
    S2 = math.sqrt(2.0)
    zs = np.concatenate([
        np.linspace(-60.0, 60.0, 2001),
        np.array([0.0, 1e-9, 1e-5, 1e-3]),
        S2 + np.array([0.0, 1e-9, 1e-5, 1e-3, -1e-5]),
        -S2 + np.array([0.0, 1e-9, 1e-5, -1e-3]),
    ]).astype(complex)
    for y in (0.0, 0.1, 0.4999):
        z = zs + 1j * y
        v, v1, v2 = phipap_trio(z)
        for got, want in ((v, phipap(z)), (v1, phipap_d1(z)),
                          (v2, phipap_d2(z))):
            # absolute 1e-12 with a 1e-11 relative allowance: the two
            # routes differ only in the order of the same floating-point
            # operations, and the worst measured defect is ~2e-14
            # absolute, in Phi2'' just past the series threshold
            assert np.all(np.abs(got - want)
                          <= 1e-12 + 1e-11 * np.abs(want))


CAP_BATTERY = [
    lattice(2.002, 0.4999, 2),
    lattice(2.002, 0.4999, 5),
    lattice(1.0, 0.3, 4),
    lattice(4.0, 0.2, 3),
    jittered_lattice(2.002, 0.45, 4, 0.6, 3),
    depth_gradient_lattice(2.05, 4, 0.05, 0.4999),
    commensurate(2.002, 4, 4.004, 2, 0.4999),
    [(0.0, 0.4999), (0.4, 0.1), (11.0, 0.35)],
]


@pytest.mark.parametrize("pairs", CAP_BATTERY)
def test_exact_tail_evaluator_reproduces_paper_joint(pairs):
    """(c) One field pass, three field passes: the same cap.

    This is what licenses using the fast evaluator for tens of thousands
    of scores, it is `PaperJoint.cap` with the arithmetic reordered, not
    a second instrument.
    """
    want = PJ.cap(pairs, THETA_FULL)["cap"]
    got = Evaluator(tail_mode="exact").verdict(pairs, THETA_FULL)["cap"]
    assert abs(got - want) <= 1e-12 * max(abs(want), 1.0)


def test_budget_matches_paper_joint():
    """The budget side is exact and instrument-free; the fast route must
    agree with `PaperJoint.budget` on the same battery."""
    for pairs in CAP_BATTERY:
        got = EV.verdict(pairs, THETA_FULL)["budget"]
        assert abs(got - PJ.budget(pairs)) <= 1e-10 * max(abs(got), 1.0)


def test_conservative_band_period_is_one_sided():
    """(c) P_CONSERVATIVE is below every band period the module's own
    instrument reports on (0, 1/2], so the conservative tail is larger,
    the cap larger, and the margin smaller.  One-sided against the
    defender, which is the only direction an adversarial search may
    round."""
    bd = PaperBandDual()
    for y in (0.02, 0.1, 0.25, 0.4, 0.49, 0.4999):
        assert P_CONSERVATIVE <= bd.band_period_lower(y) + 1e-12


@pytest.mark.parametrize("pairs", CAP_BATTERY[:5])
def test_conservative_cap_never_below_module_cap(pairs):
    """(c) The search instrument never reports a smaller cap than the
    module's, so a margin it calls positive is positive there too."""
    cons = EV.verdict(pairs, THETA_FULL)["cap"]
    assert cons >= PJ.cap(pairs, THETA_FULL)["cap"] - 1e-12


@pytest.mark.parametrize("pairs", [
    lattice(2.002, 0.4999, 2),
    lattice(2.002, 0.4999, 4),
    lattice(1.0, 0.4999, 4),
    jittered_lattice(2.002, 0.4999, 4, 0.6, 1),
])
def test_refining_the_instrument_raises_the_margin(pairs):
    """(c) The direction that makes the whole search meaningful: a finer
    step and a longer resolved half-range can only shrink the cap, so the
    margin is nondecreasing down the ladder.  Tolerance 1e-9 absolute,
    the ladder is a monotonicity claim, not an equality."""
    rows = resolution_ladder(pairs, THETA_FULL,
                             rungs=((0.01, 40.0), (FAST_STEP, FAST_G),
                                    (0.002, 100.0)))
    for a, b in zip(rows, rows[1:]):
        assert b["margin"] >= a["margin"] - 1e-9
    assert all(r["completeness"] > 1.0 for r in rows)


def test_completeness_clears_on_the_battery():
    """No band thinner than the grid, on every battery member: the cap is
    void without it and a violated completeness criterion would show up
    as a spurious negative margin."""
    for pairs in CAP_BATTERY:
        rec = EV.verdict(pairs, THETA_FULL)
        assert rec["completeness"] > 1.0
        assert rec["off_band_allowance"] == 0.0


# ---------------------------------------------------------------------------
# parameterisation round trip
# ---------------------------------------------------------------------------


def test_free_parameterisation_round_trip():
    for pairs in (lattice(2.002, 0.4999, 5), lattice(0.5, 0.2, 3)):
        x = free_pack(pairs)
        back = free_unpack(x, len(pairs))
        for (t1, y1), (t2, y2) in zip(pairs, back):
            assert abs(t1 - t2) < 1e-9 and abs(y1 - y2) < 1e-9
        assert len(x) == 2 * len(pairs) - 1
        assert len(free_bounds(len(pairs))) == len(x)


def test_structured_seeds_are_well_formed():
    seeds = list(structured_seeds(ms=(2, 4)))
    assert len(seeds) > 60
    for name, pairs in seeds:
        assert len(pairs) >= 2
        assert all(0.0 < y <= 0.5 for _, y in pairs)
        assert all(pairs[i][0] <= pairs[i + 1][0] + 1e-12
                   for i in range(len(pairs) - 1)) or "two-scale" in name


# ---------------------------------------------------------------------------
# (a) rediscovery, load-bearing
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_optimiser_rediscovers_the_binding_family():
    """(a) THE control that makes the negative result readable.

    Random starts, no hint of the answer: the optimiser must end up in
    the regime the rho map already flags, the deep end of the depth
    range, spacings in the coupled band around the resonances
    (`RESONANCES`), scoring at or below the best resonant lattice at the
    same k.  A failure here invalidates the negative result rather than
    the verdict.

    Why not "the spacing equals two mean gaps": at k = 3 and k = 4 the
    three lowest resonances are nearly degenerate on this instrument
    (relative margins 0.162 / 0.176 / 0.179 at s = 2 / 3 / 1, with
    everything off-resonance above 0.30), and the search does better than
    any of them, it lands on unequal-gap configurations in the same
    coupled band.  So the control asks for the three things a working
    search must deliver: the deep edge, the coupled band, and a score at
    or below the lattice reference.
    """
    rc = rediscovery_control(n_starts=4, k=3, seed=21, iters=30, lam=12)
    assert rc["frac_deep"] >= 0.75, rc
    assert rc["frac_in_coupled_band"] >= 0.75, rc
    assert rc["frac_beating_the_lattice"] >= 0.5, rc
    assert rc["best_rel_margin"] <= rc["lattice_reference_rel_margin"], rc


def test_the_optimiser_makes_progress_from_a_random_start():
    """The cheap half of (a): the evolution strategy must actually
    descend.  One random start, 15 generations, and the relative margin
    must fall well below where it began.

    Deliberately NOT an assertion about where a single start lands: three
    seeds measured (77 / 78 / 79) all find a resonant spacing but only
    one of the three reaches the deep edge in that budget, so a
    single-start landing claim would be a coin flip dressed as a control.
    The multi-start version above is the real one.
    """
    ev = Evaluator()
    book = Book()
    bounds = np.array(free_bounds(3), float)
    lo, hi = bounds[:, 0], bounds[:, 1]
    rng = np.random.default_rng(77)
    x0 = lo + rng.random(len(lo)) * (hi - lo)
    start = ev.rel_margin(free_unpack(x0, 3))
    rec = cmaes_lite(ev, book, 3, x0, sigma0=1.0, iters=15, lam=10, seed=77)
    assert rec["fun"] < start - 0.1, (rec["fun"], start)
    assert rec["fun"] < 0.5


# ---------------------------------------------------------------------------
# (b) detector power, the planted counterexample
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("inflate", [1.5, 2.0, 4.0])
def test_planted_inflation_is_found(inflate):
    """(b) Inflate the damage field (the budget is untouched) and the
    same search must produce a negative margin.  A search that never
    finds a planted violation could not have found a real one."""
    rec = planted_detection_control(inflate=inflate, k=3)
    assert rec["found"], rec
    assert rec["n_negative"] >= 1
    assert rec["best_rel_margin"] < 0.0


def test_planted_inflation_is_found_quickly():
    """Detector power with a budget: a strong planted fault must be
    caught inside the first handful of scores, not eventually."""
    rec = planted_detection_control(inflate=4.0, k=3)
    assert rec["found"]
    assert rec["first_negative_at"] <= 20, rec
    assert rec["n_scored"] <= 200, rec


def test_honest_instrument_finds_no_violation_on_the_same_budget():
    """The specificity half of (b): the same optimiser, same evaluation
    budget, on the UNINFLATED instrument, must not report a negative
    margin.  A detector that fires on everything is not a detector."""
    ev = Evaluator()
    book = Book()
    x0 = free_pack(lattice(2.002, 0.4999, 3))
    cmaes_lite(ev, book, 3, x0, sigma0=0.8, iters=8, lam=8, seed=41)
    assert book.n_negative == 0, book.summary()["worst"]


# ---------------------------------------------------------------------------
# (d) theta = 1
# ---------------------------------------------------------------------------


def test_theta_one_diverges():
    """(d) At theta = 1 there is no internal charge, an unbounded
    multiplicity stack costs nothing, and the cap must say so."""
    rec = theta_one_control()
    assert rec["diverges"] and rec["cap"] == math.inf
    for pairs in (lattice(1.0, 0.3, 2), [(0.0, 0.4999)]):
        assert Evaluator().verdict(pairs, 1.0)["cap"] == math.inf


# ---------------------------------------------------------------------------
# (e) the record reproduces
# ---------------------------------------------------------------------------


def test_worst_found_reproduces_at_the_search_instrument():
    """(e) The reported worst configuration, re-scored from its recorded
    coordinates on the recorded search instrument.  Tolerance 1e-8: this
    is a determinism check on recorded data, not a tolerance for drift."""
    rec = EV.verdict(WORST_FOUND["pairs"], WORST_FOUND["theta"])
    want = WORST_FOUND["search"]
    for key in ("budget", "cap", "margin", "rel_margin"):
        assert abs(rec[key] - want[key]) <= 1e-8 * max(abs(want[key]), 1.0), \
            (key, rec[key], want[key])


@pytest.mark.slow
def test_worst_found_reproduces_at_the_promotion_instrument():
    """(e) and the headline in one: the same configuration at step
    0.001, G = 400 reproduces its recorded numbers, its margin is
    POSITIVE, and it stays positive for every larger resolved half-range
    (the per-pair margin clears the residual closed-form tail).

    A future run that breaks this test is reporting a counterexample,
    which is the outcome this module was built to find.
    """
    got = promote(WORST_FOUND["pairs"], WORST_FOUND["theta"])
    want = WORST_FOUND["promoted"]
    for key in ("budget", "cap", "margin", "rel_margin",
                "margin_per_pair", "headroom_per_pair"):
        assert abs(got[key] - want[key]) <= 1e-8 * max(abs(want[key]), 1.0), \
            (key, got[key], want[key])
    assert got["margin"] > 0
    assert got["headroom_per_pair"] > 0
    assert (got["step"], got["G"]) == (PROMOTE_STEP, PROMOTE_G)


def test_the_search_instrument_negatives_are_recorded_as_such():
    """The honesty check on the headline: the campaign DID reach negative
    margins at the search instrument, the record says how many, and the
    record also says that none of them survived promotion.  A campaign
    that quietly reported only the promoted numbers would be hiding the
    interesting half."""
    assert CAMPAIGN_RECORD["n_negative_search_instrument"] > 0
    assert CAMPAIGN_RECORD["n_negative_promoted"] == 0
    assert CAMPAIGN_RECORD["worst_promoted_rel_margin"] > 0


def test_campaign_record_is_self_consistent():
    """The recorded campaign: its evaluation count is the sum of its own
    per-method counts, and it reached the budget it claims."""
    assert CAMPAIGN_RECORD["n_evals"] >= 20000
    assert sum(CAMPAIGN_RECORD["by_method"].values()) \
        == CAMPAIGN_RECORD["n_evals"]
    assert abs(CAMPAIGN_RECORD["worst_search_rel_margin"]
               - WORST_FOUND["search"]["rel_margin"]) <= 1e-9
    assert CAMPAIGN_RECORD["n_instrument_failure"] == 0


def test_recorded_near_misses_reproduce():
    """Every DISTINCT family the record keeps under the near-miss
    threshold, rebuilt from its ``build`` spec and re-scored at the
    search instrument.  These are the ones an independent reader would
    re-examine first, so their numbers must not drift."""
    nm = CAMPAIGN_RECORD["near_misses"]
    assert nm, "the campaign recorded no near miss; the threshold record " \
               "is then the finding, not this list"
    for row in nm:
        pairs = build_config(row["build"])
        assert len(pairs) == row["k"], row["name"]
        rec = EV.verdict(pairs, THETA_FULL)
        assert abs(rec["rel_margin"] - row["search_rel_margin"]) <= 1e-8, \
            (row["name"], rec["rel_margin"])
        assert rec["rel_margin"] < NEAR_MISS_REL, row["name"]


@pytest.mark.slow
def test_every_recorded_near_miss_promotes_positive():
    """The table that decides the headline: each distinct near miss, at
    the promotion instrument.  Positive margin AND positive headroom (the
    per-pair margin above the residual tail, so it stays positive at every
    larger resolved half-range).

    Twelve of the fourteen are NEGATIVE at the search instrument.  If a
    future run turns one of them negative here, that is the
    counterexample.
    """
    for row in CAMPAIGN_RECORD["near_misses"]:
        got = promote(build_config(row["build"]))
        assert abs(got["rel_margin"] - row["promoted_rel_margin"]) <= 1e-8, \
            (row["name"], got["rel_margin"])
        assert abs(got["headroom_per_pair"]
                   - row["headroom_per_pair"]) <= 1e-8, row["name"]
        assert got["margin"] > 0, row["name"]
        assert got["headroom_per_pair"] > 0, row["name"]


# ---------------------------------------------------------------------------
# the m-scaling law
# ---------------------------------------------------------------------------


def test_m_ladder_at_the_resonance_reproduces():
    """The open bridge, measured: per-pair margins along m at the
    resonance spacing on the search instrument, against the record.

    Only the cheap rungs are re-run here (m <= 16); the full ladder to
    m = 64 is the slow test below.
    """
    ms = [m for m in M_SCALING_RECORD["ms"] if m <= 16]
    want = M_SCALING_RECORD["margin_pp"]["2.002"][:len(ms)]
    rows = m_ladder(2.002, M_SCALING_RECORD["y"], tuple(ms), ev=EV)
    for r, w in zip(rows, want):
        assert abs(r["margin_pp"] - w) <= 1e-6, (r["m"], r["margin_pp"], w)
        assert r["completeness"] > 1.0
    # the shape claim: decreasing, and it does cross zero on this
    # instrument (which is what the promotion ladder then resolves)
    assert M_SCALING_RECORD["shape"]["2.002"] == "decreasing"
    assert min(M_SCALING_RECORD["margin_pp"]["2.002"]) < 0


def test_m_law_fit_reproduces_and_states_its_verdict():
    """The fitted law and its extrapolation, at BOTH instruments.

    On the search instrument the two-mean-gap fits have negative limits;
    on the promotion instrument every fitted limit is positive, above the
    residual tail, and no fit crosses zero.  If a future run turns a
    promotion-instrument crossing from None into a finite m, that is a
    PREDICTED counterexample and this test is where it surfaces.
    """
    for s in ("1.0", "2.0", "2.002", "2.05", "3.0"):
        fit = fit_m_law([{"m": m, "margin_pp": v}
                         for m, v in zip(M_SCALING_RECORD["ms"],
                                         M_SCALING_RECORD["margin_pp"][s])])
        assert fit["shape"] == M_SCALING_RECORD["shape"][s], s
        # the record stores the ladder rounded to 1e-6, so the refit
        # reproduces the limit to about that, not to machine precision
        assert abs(fit["a+b/m"]["limit_a"]
                   - M_SCALING_RECORD["search_limit_two_term"][s]) <= 1e-5, s
        rec = M_SCALING_RECORD["search_zero_crossing"][s]
        for key, name in (("two_term", "a+b/m"),
                          ("three_term", "a+b/m+c log m/m")):
            got = fit[name]["zero_crossing_m"]
            if rec[key] is None:
                assert got is None, (s, name, got)
            else:
                assert got == pytest.approx(rec[key], rel=1e-9), (s, name)

    tail = M_SCALING_RECORD["tail_per_pair"]["G=400"]
    for s in ("1.0", "2.0", "2.002"):
        fit = fit_m_law([{"m": m, "margin_pp": v}
                         for m, v in
                         zip(M_SCALING_RECORD["promote_ms"][s],
                             M_SCALING_RECORD["promote_margin_pp"][s])])
        assert abs(fit["a+b/m"]["limit_a"]
                   - M_SCALING_RECORD["promote_limit_two_term"][s]) <= 1e-5
        assert abs(fit["a+b/m+c log m/m"]["limit_a"]
                   - M_SCALING_RECORD["promote_limit_three_term"][s]) <= 1e-5
        assert fit["a+b/m"]["zero_crossing_m"] is None, s
        assert fit["a+b/m+c log m/m"]["zero_crossing_m"] is None, s
        # the limits clear the only thing left to recover as G grows
        assert fit["a+b/m+c log m/m"]["limit_a"] > tail, s


def test_the_two_term_extrapolation_is_not_conservative():
    """The honest caveat, as an assertion: the m = 96 measurement at
    s = 2.002 sits BELOW the two-term fit's own extrapolated limit, so
    the two-term limit may not be read as a floor.  The three-term fit
    (an order of magnitude better residual) is not violated by it."""
    ms = M_SCALING_RECORD["promote_ms"]["2.002"]
    v = M_SCALING_RECORD["promote_margin_pp"]["2.002"]
    assert ms[-1] == 96
    short = fit_m_law([{"m": m, "margin_pp": x}
                       for m, x in zip(ms[:-1], v[:-1])])
    assert v[-1] < short["a+b/m"]["limit_a"]
    assert v[-1] > short["a+b/m+c log m/m"]["limit_a"]
    assert (short["a+b/m+c log m/m"]["max_resid"]
            < short["a+b/m"]["max_resid"] / 5)


def test_m_law_fit_would_flag_a_crossing():
    """The extrapolation machinery is not vacuous: fed a ladder whose
    per-pair margin decays to a NEGATIVE limit, it reports a finite
    crossing.  Without this, `zero_crossing_m is None` would be
    unfalsifiable."""
    rows = [{"m": m, "margin_pp": -0.01 + 0.2 / m}
            for m in (2, 4, 8, 16, 32, 64)]
    fit = fit_m_law(rows)
    assert fit["a+b/m"]["limit_a"] < 0
    # the fitted curve is already nonpositive at the end of the ladder,
    # so the reported crossing sits at the ladder's last rung
    assert fit["a+b/m"]["zero_crossing_m"] is not None
    assert fit["a+b/m"]["zero_crossing_m"] <= 64.0 + 1e-6

    # and a ladder that decays to a positive floor must report no crossing
    rows = [{"m": m, "margin_pp": 0.02 + 0.2 / m}
            for m in (2, 4, 8, 16, 32, 64)]
    assert fit_m_law(rows)["a+b/m"]["zero_crossing_m"] is None
    rows = [{"m": m, "margin_pp": 0.002 + 0.2 / m - 0.05 * math.log(m) / m}
            for m in (2, 4, 8, 16, 32, 64)]
    fit = fit_m_law(rows)
    assert fit["a+b/m+c log m/m"]["limit_a"] > 0


@pytest.mark.slow
def test_m_ladder_out_to_64_crosses_at_the_search_instrument():
    """The bridge, pushed past `cluster_universal`'s m = 32, and the
    honest half of the answer.

    At the SEARCH instrument the decreasing sequence does cross zero, and
    this test pins that it does: the per-pair tail handicap at G = 60 is
    0.02733 and the quantity being measured is smaller than that.  A
    reader who takes a search-instrument number for a verdict would
    conclude the opposite of the truth, so the crossing is recorded here
    rather than smoothed over.
    """
    rows = m_ladder(2.002, 0.4999, ms=(2, 16, 32, 64), ev=Evaluator())
    v = [r["margin_pp"] for r in rows]
    assert v[0] > 0 and v[-1] < 0, v
    assert all(v[i] > v[i + 1] for i in range(len(v) - 1)), v
    assert all(r["completeness"] > 1.0 for r in rows)


@pytest.mark.slow
def test_m_ladder_out_to_64_stays_positive_where_it_counts():
    """And the half that decides: the same ladder at the promotion
    instrument stays positive, stays above the residual tail, and
    reproduces the record."""
    ev = Evaluator(step=PROMOTE_STEP, G=PROMOTE_G)
    ms = (2, 16, 64)
    rows = m_ladder(2.002, 0.4999, ms=ms, ev=ev)
    want = dict(zip(M_SCALING_RECORD["promote_ms"]["2.002"],
                    M_SCALING_RECORD["promote_margin_pp"]["2.002"]))
    tail = M_SCALING_RECORD["tail_per_pair"]["G=400"]
    for r in rows:
        assert abs(r["margin_pp"] - want[r["m"]]) <= 1e-6, r
        assert r["margin_pp"] > tail, r
        assert r["completeness"] > 1.0


# ---------------------------------------------------------------------------
# the campaign runs
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_quick_campaign_runs_and_promotes_its_candidates():
    """A short campaign end to end: the machinery runs, counts its own
    evaluations, and every candidate it promotes comes back with a
    positive margin.  The search-instrument negatives are expected (see
    the module docstring); what must not happen is one of them
    surviving promotion."""
    rec = campaign(quick=True, verbose=False)
    assert rec["n_evals"] > 500
    assert sum(rec["by_method"].values()) == rec["n_evals"]
    assert rec["n_instrument_failure"] == 0
    prom = rec["promotion"]
    assert prom["n"] >= 1
    assert prom["n_negative_promoted"] == 0, prom["worst"]
    assert prom["n_negative_headroom"] == 0, prom["worst"]


def test_primal_stays_within_budget_at_the_worst_find():
    """A cap crossing would be an instrument statement; only the PRIMAL
    crossing the budget would touch the E-form itself.  The distinction
    is kept on disk with numbers."""
    pr = primal_check(WORST_FOUND["pairs"])
    assert pr["primal_within_budget"], pr


@pytest.mark.slow
def test_primal_sweep_stays_within_budget():
    """The sup over the on-line set X, measured by the same greedy the
    joint layer uses, against the exact budget, on the families the cap
    finds hardest.  Room here is what says a cap crossing (if one ever
    appeared) would be an instrument failure rather than an E-form
    failure."""
    ps = primal_sweep()
    assert ps["all_within_budget"], [r for r in ps["rows"]
                                     if not r["primal_within_budget"]]
    assert ps["worst_ratio"] < 1.0


def test_book_records_negatives_and_near_misses():
    """The bookkeeping the whole report rests on, exercised directly."""
    book = Book()
    book.absorb({"margin": -1.0, "rel_margin": -0.5, "pairs": [],
                 "budget": 2.0, "cap": 3.0, "completeness": 5.0}, "x")
    book.absorb({"margin": 1.0, "rel_margin": 0.5, "pairs": [],
                 "budget": 2.0, "cap": 1.0, "completeness": 5.0}, "y")
    s = book.summary()
    assert s["n_negative"] == 1
    assert s["worst"]["rel_margin"] == -0.5
    assert s["n_near_miss"] == 1
    assert s["by_method"] == {"x": 1, "y": 1}
