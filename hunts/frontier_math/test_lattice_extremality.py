"""Pins for the lattice-extremality attack.

The load-bearing test here is not "no counterexample was found" — that is a
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
