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
