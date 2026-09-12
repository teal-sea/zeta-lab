"""Tests for zeta.relations: PSLQ probes of ℚ-linear independence.

Every literal here was computed in this environment before being asserted.
The instrument's history is part of its documentation: the first n=20 run
(guard = 20 digits) terminated on a pigeonhole accident with coefficients
~7·10⁵ and residual 4.4·10⁻¹⁰⁴, which recomputation at dps 300 refuted,
exactly the failure mode the residual gate and the 40-digit guard now
foreclose.  These tests pin (a) the planted-relation sanity check, (b) a
fast clean exclusion, (c) the junk-candidate refutation path, and (d) the
underpowered-run refusal.
"""

from __future__ import annotations

import pytest

from zeta.relations import (
    confirm_relation,
    constants_relation_search,
    pslq_sanity,
    zero_relation_search,
)

# The junk vector from the first (guard=20) n=20 run, kept as a regression
# fixture: it must never be accepted as a relation.
JUNK_N20 = [
    -384552, -325047, 93956, -119872, 229124, -69246, -377716, -178870,
    714732, -159056, 52334, 324528, -211407, 194285, -23226, 10695,
    344366, -102784, -469505, 63097,
]


def test_pslq_recovers_planted_relation():
    out = pslq_sanity(dps=60)
    assert out["passed"]
    assert out["found"] and out["nontrivial"]
    # The residual of an exact relation sits at the rounding floor.
    assert out["residual"] < 1e-45


def test_small_batch_exclusion_is_clean():
    out = zero_relation_search(n_zeros=8, max_coeff=10**4)
    assert out["status"] == "excluded"
    assert out["excluded"] is True
    assert out["relation"] is None
    assert out["floor_ratio"] >= 1.0


def test_underpowered_run_refused():
    with pytest.raises(ValueError):
        zero_relation_search(n_zeros=12, max_coeff=10**6, dps=50)


def test_junk_candidate_refuted_at_double_precision():
    out = confirm_relation(JUNK_N20, n_zeros=20, dps=200)
    assert out["confirmed"] is False
    # The residual is the pigeonhole floor, not a rounding artifact: it is
    # stable under precision increase (4.43e-104 at dps 140, 300, and here).
    assert 1e-105 < out["residual"] < 1e-103


def test_constants_search_excludes():
    out = constants_relation_search(n_zeros=4, max_coeff=10**3)
    assert out["status"] == "excluded"
    assert out["excluded"] is True


@pytest.mark.slow
def test_headline_exclusion_first_20_zeros():
    """The record this module exists to produce, at its fast end.

    No integer relation with max|aᵢ| ≤ 10⁶ among the first 20 ordinates
    (bounded search; the n=30/dps=280 run is recorded in docs, too slow
    for the suite).
    """
    out = zero_relation_search(n_zeros=20, max_coeff=10**6)
    assert out["status"] == "excluded"


@pytest.mark.slow
def test_floor_noise_is_classified_not_reported():
    """At dps exactly n·log10(B), PSLQ may terminate on an accident; the
    gate must classify it as noise, never as a candidate or an exclusion."""
    out = zero_relation_search(n_zeros=30, max_coeff=10**6, dps=220)
    assert out["status"] in ("inconclusive_floor_noise", "excluded")
    if out["status"] == "inconclusive_floor_noise":
        assert out["excluded"] is False
        assert out["relation"] is not None
        assert out["residual"] > 1e-205  # far above an exact relation's floor
