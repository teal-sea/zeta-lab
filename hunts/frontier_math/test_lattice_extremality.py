"""Pins for the lattice-extremality attack.

The load-bearing test here is not "no counterexample was found". That is a
fact about a search.  It is `test_the_objective_has_power`: a search that
cannot tell configurations apart would also find no counterexample, and the
two are only distinguishable by measuring the discrimination.
"""

import math

import pytest

from lattice_extremality import (
    SEARCH_RECORD, TWOPI, alternating_gap_cost, calibration_error,
    g4_pattern_cost, per_centre_cost, per_centre_cost_raw, vacancy_cost,
    vectorisation_defect,
)
from two_species import centre_gas_row_closed


def test_the_vectorised_kernel_matches_the_scalar_path():
    """The search reimplements `gram_form._ghat` for speed. Measured against
    the original rather than asserted equal."""
    assert vectorisation_defect() < 1e-15


def test_the_objective_reproduces_the_closed_form_on_the_lattice():
    """Calibration. `per_centre_cost` at m=1, P=2*pi must be the closed form;
    everything the search says is trustworthy only to this residual."""
    assert abs(calibration_error()) < 1e-7


def test_the_truncated_sum_approaches_the_limit_from_below():
    """`f` decays like 1/s^2, so truncation always undershoots. If a raw
    reading ever exceeded the limit the Richardson step would be masking a
    sign error rather than a tail."""
    exact = centre_gas_row_closed()
    for N in (500, 2000, 8000):
        assert per_centre_cost_raw([0.0], TWOPI, N) < exact


def test_the_objective_has_power():
    """The negative result is only worth as much as this.

    Perturbations the optimiser resolves at 1e-6 must move the objective by
    orders more than that, or "found nothing" would be indistinguishable from
    "cannot see anything"."""
    base = centre_gas_row_closed()
    assert base - alternating_gap_cost(0.95) > 1e-2
    assert base - alternating_gap_cost(0.90) > 5e-2
    assert base - vacancy_cost(4) > 1e-2
    assert base - per_centre_cost([0.0, 0.5], 2 * TWOPI) > 1.0


def test_the_lattice_is_a_strict_symmetric_maximum_of_the_gap_family():
    base = centre_gas_row_closed()
    assert abs(alternating_gap_cost(1.0) - base) < 1e-7
    for frac in (0.90, 0.95, 1.05, 1.10, 1.20):
        assert alternating_gap_cost(frac) < base
    for lo, hi in ((0.90, 1.10), (0.95, 1.05)):
        assert abs(alternating_gap_cost(lo) - alternating_gap_cost(hi)) < 1e-9


def test_no_structured_family_beats_the_lattice():
    base = centre_gas_row_closed()
    assert g4_pattern_cost() < base
    for slots in (4, 6, 9, 13):
        assert vacancy_cost(slots) < base
    for d in (0.5, 2.0, 4.0, 6.0):
        assert per_centre_cost([0.0, d], 2 * TWOPI) < base


def test_the_g4_pattern_reading_is_recorded_with_its_disagreement():
    """L5. This module reads the pattern as 0.0666, the withdrawal note as
    ~0.0602. Both far below the lattice; the gap between them is the finite
    chain's boundary effect and is recorded rather than reconciled away."""
    got = g4_pattern_cost()
    assert abs(got - SEARCH_RECORD["structured_families"]["g4_pattern"]) < 1e-6
    assert got < 0.7 * centre_gas_row_closed()


def test_the_search_record_does_not_claim_a_proof():
    from lattice_extremality import NAMED_GAPS
    joined = " ".join(NAMED_GAPS)
    assert "L1" in NAMED_GAPS[0] and "not discharged" in joined
    assert "NOT covered" in joined            # L2 names the family's limit
    assert "evidence about RH" in joined      # L6
    for gap in NAMED_GAPS:
        assert "certif" not in gap.lower()


def test_the_free_search_record_is_internally_consistent():
    rec = SEARCH_RECORD["free_search"]
    base = SEARCH_RECORD["lattice_closed_form"]
    assert base == pytest.approx(centre_gas_row_closed(), abs=1e-15)
    assert rec["restarts"] == 300
    for m, val in rec["best_by_m"].items():
        assert val < base                       # nothing beat the lattice
        assert base - val < 1e-5                # and everything came back to it
    assert rec["worst_shortfall"] == pytest.approx(
        min(v - base for v in rec["best_by_m"].values()), abs=1e-8)


# --------------------------------------------------------------------------
# The frequency route.  LATTICE-EXTREMALITY-ROUTE.md carries the argument;
# these pin the steps that argument actually depends on.
# --------------------------------------------------------------------------

def test_the_structure_factor_identity_holds_off_the_lattice_too():
    """Section 1, and the load-bearing step of the whole route.

    An infinite sum over space equals a finite sum over frequency. Checked on
    non-lattice configurations, because holding only at the extremiser would
    make it a coincidence rather than an identity."""
    from lattice_extremality import TWOPI, structure_factor_defect
    cases = [([0.0], TWOPI),
             ([0.0], 2.6 * math.pi),
             ([0.0, 0.8 * TWOPI], 2 * TWOPI),
             ([0.0, 0.55 * TWOPI, 1.7 * TWOPI], 3 * TWOPI),
             ([0.0, 1.3 * TWOPI], 3.4 * TWOPI)]
    for a, P in cases:
        assert abs(structure_factor_defect(a, P, N=1500)) < 1e-7, (a, P)


def test_kappa_hat_has_the_three_properties_the_argument_uses():
    """Section 2. Compact support, non-negativity, and a zero at the
    endpoints. The third is what the lattice's reciprocal frequency lands on."""
    from lattice_extremality import kappa_hat, c2
    assert kappa_hat(1.0) == 0.0 and kappa_hat(-1.0) == 0.0       # (c)
    assert kappa_hat(1.0001) == 0.0 and kappa_hat(37.0) == 0.0    # (a)
    for x in (0.0, 0.1, 0.35, 0.5, 0.75, 0.9, 0.99):              # (b)
        assert kappa_hat(x) > 0.0
        assert kappa_hat(x) == pytest.approx(kappa_hat(-x))


def test_c2_positivity_has_a_reason_not_just_a_measurement():
    """Section 2(b). c2 is the autocorrelation of g(u) = cos(sqrt2 u) on
    |u| <= 1/2, and sqrt2/2 < pi/2, so g is strictly positive on its whole
    support. That is why c2 > 0 on (-1,1), and the test pins the inequality
    the proof rests on rather than only the numbers it produces."""
    from lattice_extremality import c2
    assert math.sqrt(2) / 2 < math.pi / 2
    assert math.cos(math.sqrt(2) / 2) > 0
    assert min(c2(w) for w in (0.0, 0.25, 0.5, 0.75, 0.9, 0.99)) > 0.0
    assert c2(1.0) == pytest.approx(0.0, abs=1e-12)


def test_the_lp_bound_is_tight_at_the_critical_density_and_decreasing():
    """Section 3. Tight exactly at rho = 1/(2*pi), and monotone, which is what
    closes the dense side."""
    from lattice_extremality import TWOPI, lp_bound
    from two_species import centre_gas_row_closed
    assert lp_bound(1 / TWOPI) == pytest.approx(centre_gas_row_closed(), abs=1e-14)
    prev = None
    for r in (0.5, 0.8, 1.0, 1.2, 1.7, 2.5):
        got = lp_bound(r / TWOPI)
        if prev is not None:
            assert got < prev
        prev = got


def test_the_dense_side_is_closed_by_the_bound():
    """Section 3. For rho >= 1/(2*pi) the bound already sits at or below the
    lattice value, so no dense configuration can beat it."""
    from lattice_extremality import TWOPI, lp_bound
    from two_species import centre_gas_row_closed
    lat = centre_gas_row_closed()
    for r in (1.0, 1.05, 1.4, 2.0, 3.0):
        assert lp_bound(r / TWOPI) <= lat + 1e-14


def test_equal_spacing_zeroes_exactly_the_constrained_modes():
    """Section 4. At rho = 1/(2*pi) the modes with 0 < |j| < m are the ones
    kappa_hat weights, and equal spacing kills precisely those. Perturbing
    switches them on and the value drops strictly."""
    import numpy as np
    from lattice_extremality import TWOPI, per_centre_cost
    from two_species import centre_gas_row_closed
    lat = centre_gas_row_closed()
    for m in (2, 3, 4):
        P = m * TWOPI
        even = np.array([i * TWOPI for i in range(m)])
        for j in range(1, m):
            assert abs(np.exp(2j * math.pi * j * even / P).sum()) < 1e-9
        assert per_centre_cost(even, P, N=2000) == pytest.approx(lat, abs=1e-6)
        pert = even.copy()
        pert[-1] += 0.35
        assert any(abs(np.exp(2j * math.pi * j * pert / P).sum()) > 1e-3
                   for j in range(1, m))
        assert per_centre_cost(pert, P, N=2000) < lat - 1e-3


def test_hypothesis_H2_holds_for_the_extremiser():
    """Section 5. The rectification never fires at a lattice difference, which
    is why the bound is attained there rather than merely approached."""
    from lattice_extremality import clip_is_idle_on_lattice
    assert clip_is_idle_on_lattice(2000) < 0.0


def test_gap_B_is_real_and_is_not_understated():
    """Section 6, gap B. The clip bonus is zero on the lattice and NOT small
    elsewhere. A test that only checked the lattice would make the gap look
    like a technicality."""
    from lattice_extremality import TWOPI, clip_bonus
    assert clip_bonus([0.0], TWOPI, N=800) == pytest.approx(0.0, abs=1e-12)
    assert clip_bonus([0.0, 0.8 * TWOPI], 2 * TWOPI, N=800) > 1e-2


def test_gap_A_is_real_and_is_not_understated():
    """Section 6, gap A. On the sparse side the bound is not merely loose, it
    is above the lattice value, so it protects nothing there."""
    from lattice_extremality import TWOPI, lp_bound, per_centre_cost
    from two_species import centre_gas_row_closed
    lat = centre_gas_row_closed()
    for r in (0.4, 0.6, 0.8, 0.9):
        assert lp_bound(r / TWOPI) > lat            # bound is vacuous, and
        assert per_centre_cost([0.0], TWOPI / r, N=2000) < lat   # truth is not


def test_the_route_document_states_its_own_limits():
    from pathlib import Path
    raw = (Path(__file__).resolve().parent / "LATTICE-EXTREMALITY-ROUTE.md").read_text()
    doc = " ".join(raw.split())          # line wraps must not hide a claim
    assert "not a completed proof" in doc
    assert "T1 is not discharged" in doc
    assert "evidence about RH" in doc
    for gap in ("Gap A", "Gap B", "Gap C", "Gap D"):
        assert gap in doc
    assert "certif" not in raw.lower()          # the reserved word, banned here


# --------------------------------------------------------------------------
# Gap B, closed.  Section 5a of the route document.
# --------------------------------------------------------------------------

def test_the_fejer_ansatz_has_all_four_required_properties():
    """Section 5a. Non-negative, vanishing on the punctured lattice, a
    triangular transform supported on [-1,1], and int s = 2*pi*s(0), which is
    the tightness condition the first draft of the route missed."""
    import numpy as np
    from lattice_extremality import TWOPI, fejer
    xs = np.linspace(-200, 200, 200001)
    assert (fejer(xs) >= 0).all()
    for n in range(1, 40):
        assert abs(float(fejer(np.array([n * TWOPI]))[0])) < 1e-20
        assert abs(float(fejer(np.array([-n * TWOPI]))[0])) < 1e-20
    assert float(fejer(np.array([0.0]))[0]) == 1.0
    grid = np.linspace(-3000, 3000, 3000001)
    vals = fejer(grid)
    assert np.trapezoid(vals, grid) == pytest.approx(TWOPI, rel=1e-3)   # int s
    for xi, want in ((0.3, TWOPI * 0.7), (0.7, TWOPI * 0.3), (1.4, 0.0)):
        got = np.trapezoid(vals * np.cos(xi * grid), grid)
        assert got == pytest.approx(want, abs=2e-3)


def test_the_obvious_ansatz_is_ruled_out_by_the_tightness_condition():
    """Why `(1 - cos x)*psi` cannot work: it vanishes at the origin, so
    tightness would force int v = 0 against v >= K_1^+ >= 0. Pinned so the
    dead end is not re-entered."""
    assert (1 - math.cos(0.0)) == 0.0


def test_gap_B_is_feasible_with_margin():
    """Section 5a, the whole point. Both one-dimensional inequalities hold at
    once, so an admissible multiplier exists."""
    from lattice_extremality import MAJORANT_RECORD, majorant_multiplier_range
    lo, hi = majorant_multiplier_range(xmax=800.0, npts=80000)
    assert lo <= hi
    assert hi - lo > 0.5
    assert lo == pytest.approx(MAJORANT_RECORD["c_lower"], abs=1e-5)
    assert hi == pytest.approx(MAJORANT_RECORD["c_upper"], abs=1e-12)


def test_the_admissible_multiplier_keeps_the_bound_tight_and_decreasing():
    """LP_v agrees with the lattice value at the critical density for ANY
    admissible c, and stays decreasing because every admissible c is below
    2*c2(0)."""
    from lattice_extremality import (MAJORANT_RECORD, TWOPI, c2,
                                     lp_bound_with_majorant)
    from two_species import centre_gas_row_closed
    lat = centre_gas_row_closed()
    lo, hi = MAJORANT_RECORD["c_lower"], MAJORANT_RECORD["c_upper"]
    assert hi < 2 * c2(0.0)                       # slope stays negative
    for c in (lo, 0.5 * (lo + hi), hi):
        assert lp_bound_with_majorant(1 / TWOPI, c) == pytest.approx(lat, abs=1e-12)
        prev = None
        for r in (1.0, 1.3, 1.8, 2.4):
            got = lp_bound_with_majorant(r / TWOPI, c)
            assert got <= lat + 1e-12
            if prev is not None:
                assert got < prev
            prev = got


def test_H2_holds_on_the_lattice_for_a_reason_not_by_luck():
    """The closed form for the tail constant, and the single inequality it
    turns on. K_1(2*pi*n)*(2*pi*n)^2 -> 2*cos^2(sqrt2/2)*(1 - cosh 1), which is
    negative exactly because cosh 1 > 1."""
    import gram_form as gf
    from lattice_extremality import TWOPI, lattice_tail_constant
    assert math.cosh(1.0) > 1.0
    tc = lattice_tail_constant()
    assert tc < 0
    assert tc == pytest.approx(-0.6277706355638578, abs=1e-12)
    for n in (500, 2000, 5000):
        x = n * TWOPI
        assert gf.kernel(1.0, x) * x * x == pytest.approx(tc, rel=2e-3)
        assert gf.kernel(1.0, x) < 0


def test_the_route_records_gap_B_as_closed_without_overclaiming():
    from pathlib import Path
    from lattice_extremality import MAJORANT_RECORD
    raw = (Path(__file__).resolve().parent / "LATTICE-EXTREMALITY-ROUTE.md").read_text()
    doc = " ".join(raw.split())
    assert "Gap B, the rectification. CLOSED" in doc
    assert "not enclosed" in doc            # the honest limit of the closure
    assert "not a completed proof" in doc   # and the honest limit overall
    assert "T1 is not discharged" in doc
    assert "Gap A" in doc and "where the work is" in doc
    assert "not enclosed" in MAJORANT_RECORD["grade"]
    assert "certif" not in raw.lower()


# --------------------------------------------------------------------------
# Gap A.  Section 6a: narrowed, not closed.
# --------------------------------------------------------------------------

def test_gap_A_has_exactly_one_possible_route():
    """Section 6a. ghat(0) = 0 is forced: the bound is linear in rho, so a
    density-independent bound needs a non-negative slope, and ghat <= 0
    permits only zero."""
    from lattice_extremality import density_independent_target
    from two_species import centre_gas_row_closed
    t = density_independent_target()
    assert t["ghat0_required"] == 0.0
    assert t["g0_required"] == pytest.approx(-centre_gas_row_closed() / 2, abs=1e-15)
    assert t["uhat0_required"] == pytest.approx(t["u0_required"] * 2 * math.pi,
                                                rel=1e-12)


def test_gap_A_is_infeasible_at_bandwidth_one_and_not_narrowly():
    """Section 6a. The rigidity collapses the admissible set to multiples of
    the same Fejer kernel gap B used, and the cap falls 29% short."""
    from lattice_extremality import (GAP_A_RECORD, bandwidth_one_ceiling,
                                     density_independent_target)
    need = density_independent_target()["uhat0_required"]
    ceil = bandwidth_one_ceiling()
    assert ceil < need
    assert (need - ceil) / need > 0.25          # short by a lot, not a whisker
    assert ceil == pytest.approx(GAP_A_RECORD["bandwidth_one_ceiling"], abs=1e-6)
    assert need == pytest.approx(GAP_A_RECORD["uhat0_required"], abs=1e-6)


def test_the_failed_LP_method_is_recorded_with_its_witness():
    """A method that silently gives wrong answers is worth more written down
    than forgotten. The sampled-positivity LP returns a value above a proved
    ceiling, which is how we know it is unsound rather than merely loose."""
    from lattice_extremality import GAP_A_RECORD, bandwidth_one_ceiling
    m = GAP_A_RECORD["method_that_does_not_work"]
    assert "4.908534" in m and "3.507678" in m      # the number and the ceiling
    assert "BETWEEN its own sample points" in m     # where it cheats
    assert 4.908534 > bandwidth_one_ceiling()       # and that it really is above
    assert "Fejer-Riesz" in GAP_A_RECORD["right_tool"]


def test_gap_A_is_not_described_as_closed_anywhere():
    from pathlib import Path
    from lattice_extremality import GAP_A_RECORD
    raw = (Path(__file__).resolve().parent / "LATTICE-EXTREMALITY-ROUTE.md").read_text()
    doc = " ".join(raw.split())
    assert "Gap A, the sparse side. NARROWED, not closed" in doc
    assert "This is where the work is" in doc
    assert "open" in GAP_A_RECORD
    assert "not a proof either way" in GAP_A_RECORD["open"]
