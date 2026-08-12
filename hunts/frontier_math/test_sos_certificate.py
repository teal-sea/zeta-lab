"""Controls for ``sos_certificate.py``.

Five families, in the order the module's claims are made:

(a) the matrix form against the existing evaluators of
    ``joint_universal.py``, on eight mixed configurations;
(b) the ``n = 0`` special case, where the cone's minimum must be the
    kernel-checked ``4k`` --- and the degree-2 lift's FAILURE to reproduce
    it at ``k >= 2`` is pinned as a number, not hidden;
(c) planted infeasibility: at the one size the relaxation solves tightly,
    a constant pushed above the true optimum must be rejected;
(d) CLARABEL against SCS;
(e) the rational cone violator, re-checked in exact ``fractions``.

The slow marks are on the SDP families; the exact and matrix-form
families are fast.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from sos_certificate import (  # noqa: E402
    CONE_RECORD, DIAG_CAP, PHI_MIN, PSI_HALF, SDP_RECORD, THETA_FULL,
    VALIDATION_CONFIGS, atoms, cone_local_min, cone_violator,
    cone_violator_exact, inertia_bound, inertia_defect, lift_index,
    matrix_form_defect, qmat, relax, structural_equalities,
    structural_facts, target_from_Q, target_from_config, target_terms,
    weight_matrix,
)


# ---------------------------------------------------------------------------
# (a) the matrix form
# ---------------------------------------------------------------------------


def test_matrix_form_matches_existing_evaluators():
    """(a) The Gram form of the obligation against
    ``joint_universal.verdict_fourier_gap`` on eight mixed configurations
    (n from 0 to 6, k from 0 to 4, depths 0.02..0.49, spacings from a
    0.16-tight cluster to 27 units)."""
    rows = matrix_form_defect(n_quad=1600001)
    assert len(rows) >= 6
    worst = max(r["defect"] for r in rows)
    assert worst <= 1e-10, [(r["name"], r["defect"]) for r in rows]


def test_matrix_form_block_decomposition():
    """The three blocks add up to the whole, and each is the object the
    prose names it: budget >= 0, on-line block = (1-theta) R >= 0."""
    for _, on, pr in VALIDATION_CONFIGS:
        t = target_terms(on, pr)
        total = (t["pair_block"] + t["cross_block"] + t["online_block"]
                 - 4 * t["k"])
        assert abs(total - t["target"]) < 1e-12
        assert t["budget"] >= -1e-9           # PairEnergy.lean
        assert t["online_block"] >= -1e-12    # (1-theta) R, R >= 0


def test_weight_matrix_is_the_stated_block_pattern():
    _, _, kinds = atoms([0.0, 1.0], [(0.0, 0.3)])
    c = weight_matrix(kinds, THETA_FULL)
    assert c[0, 0] == 0.0 and c[1, 1] == 0.0          # on-line diagonal
    assert abs(c[0, 1] - (1 - THETA_FULL)) < 1e-15    # on-line off-diagonal
    assert c[2, 2] == 1.0 and c[0, 2] == 1.0          # pair and cross


def test_structural_facts_hold_on_real_configurations():
    """(Q1)-(Q5) measured, not assumed."""
    for _, on, pr in VALIDATION_CONFIGS:
        f = structural_facts(on, pr)
        if f["N"] == 0:
            continue
        assert f["Q1_min_eig"] > -1e-9
        assert f["Q1_hermitian_defect"] < 1e-12
        assert f["Q2_involution_defect"] < 1e-12
        assert f["Q3_symmetry_defect"] < 1e-12
        assert f["Q4_min_diag"] > 1 - 1e-12
        assert f["Q4_online_diag_defect"] < 1e-12
        assert f["Q5_worst_cauchy_schwarz"] < 1e-12
        assert f["online_block_imag"] < 1e-14
        assert f["max_pair_diag"] <= DIAG_CAP + 1e-12


def test_derived_ranges_are_where_the_module_says():
    assert 1.0 < PSI_HALF < DIAG_CAP
    assert PSI_HALF ** 2 <= DIAG_CAP + 1e-12      # log-convexity of Psi
    assert -0.19 < PHI_MIN < -0.17


def test_inertia_bound_on_the_combined_atom_set():
    """``sum Q^2 >= (n+2k)^2/(n+k)``, and the trace identity it rests on."""
    for _, on, pr in VALIDATION_CONFIGS:
        d = inertia_defect(on, pr)
        if d["n"] + d["k"] == 0:
            continue
        assert d["slack"] >= -1e-9, d
        assert d["tr_identity_defect"] < 1e-9
        assert abs(d["tr_QP"] - 2 * (d["n"] + 2 * d["k"])) < 1e-9


def test_inertia_bound_reduces_to_pair_energy_at_n_zero():
    for k in range(1, 7):
        assert abs(inertia_bound(0, k) - 4 * k) < 1e-12


def test_inertia_bound_is_short_of_the_obligation():
    """It never closes: the shortfall is exactly ``nk/(n+k)`` at R = 0."""
    for n in (1, 3, 8):
        for k in (1, 2, 5):
            assert (inertia_bound(n, k) - (n + 4 * k)
                    + n * k / (n + k)) == pytest.approx(0.0, abs=1e-12)


# ---------------------------------------------------------------------------
# (e) the exact rational cone violator
# ---------------------------------------------------------------------------


def test_cone_violator_is_exact_and_violates():
    """(e) The witness satisfies every cone constraint in exact rational
    arithmetic and has ``Xi < 0``: the hypotheses of
    ``PairEnergy.four_n_le_sum_sq``, extended to an involution with fixed
    points, do NOT imply the obligation."""
    for n, t, want in ((3, Fraction(1, 2), Fraction(-47, 100)),
                       (4, Fraction(1, 2), Fraction(-36, 25)),
                       (6, Fraction(1), Fraction(-157, 20))):
        r = cone_violator_exact(n, t)
        assert r["hermitian"] and r["Q1_psd"]
        assert r["Q2_involution"] and r["Q3_symmetry"]
        assert r["Q4_diag"] and r["Q5_cauchy_schwarz"]
        assert r["Xi"] == want
        assert r["violates"]
        assert isinstance(r["Xi"], Fraction)


def test_cone_violator_closed_form_and_float_agreement():
    for n in (2, 3, 4, 5, 6, 9):
        for t in (Fraction(1, 4), Fraction(1, 2), Fraction(1)):
            r = cone_violator_exact(n, t)
            assert r["Xi"] == r["closed_form"]
            re_, im_ = cone_violator(n, t)
            N = n + 2
            Q = np.array([[float(re_[a][b]) + 1j * float(im_[a][b])
                           for b in range(N)] for a in range(N)])
            L = lift_index(n, 1)
            assert target_from_Q(Q, L.kinds, THETA_FULL, 1) == pytest.approx(
                float(r["Xi"]), abs=1e-9)


def test_cone_violator_is_small_at_n_two_and_negative_from_three():
    assert cone_violator_exact(2, Fraction(1, 2))["Xi"] > 0
    for n in (3, 4, 5, 6, 10):
        best = min(cone_violator_exact(n, Fraction(m, 4))["Xi"]
                   for m in range(1, 4 * n))
        assert best < 0


def test_exact_psd_test_rejects_a_non_psd_matrix():
    """The lesion for the exact PSD routine: without it, every claim in
    the violator section would be unfalsifiable."""
    from sos_certificate import _psd_exact
    assert _psd_exact([[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]])
    assert not _psd_exact([[Fraction(1), Fraction(2)],
                           [Fraction(2), Fraction(1)]])
    assert not _psd_exact([[Fraction(0), Fraction(1)],
                           [Fraction(1), Fraction(1)]])
    assert _psd_exact([[Fraction(0), Fraction(0)],
                       [Fraction(0), Fraction(3)]])


# ---------------------------------------------------------------------------
# the lift's bookkeeping
# ---------------------------------------------------------------------------


def test_lift_index_and_equalities_are_satisfied_by_real_configurations():
    """Every real configuration is a feasible point of the lift's first
    moment --- if it were not, the relaxation would not be a bound."""
    cases = [([0.0, 2.2], [(1.0, 0.4)]), ([], [(0.0, 0.2), (7.0, 0.49)]),
             ([0.0, 1.0, 5.0], [(2.0, 0.3), (9.0, 0.1)])]
    for on, pr in cases:
        n, k = len(on), len(pr)
        L = lift_index(n, k)
        z, sig, kinds = atoms(on, pr)
        assert list(sig) == list(L.sigma) and list(kinds) == list(L.kinds)
        Q = qmat(z)
        p = np.zeros(L.d)
        for a in range(L.N):
            for b in range(a, L.N):
                p[L.ix[a, b]] = Q[a, b].real
                if b > a:
                    p[L.iy[a, b]] = Q[a, b].imag
        M, rhs = structural_equalities(L)
        assert np.abs(M @ p - rhs).max() < 1e-12


# ---------------------------------------------------------------------------
# (b), (c), (d): the SDP families
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_relaxation_is_a_valid_lower_bound():
    """The relaxation must sit below Xi at every real configuration."""
    from sos_certificate import relaxation_is_a_lower_bound
    for rec in relaxation_is_a_lower_bound([(1, 1), (2, 1), (0, 2)],
                                           samples=25):
        assert rec["valid"], rec


@pytest.mark.slow
def test_pair_energy_special_case_n_zero():
    """(b) The ``n = 0`` control, in both directions.

    The CONE's own minimum at n = 0 is 0, i.e. ``sum Q^2 = 4k`` is sharp
    there --- that is ``PairEnergy.lean`` recovered.  The degree-2 LIFT
    does NOT reproduce it beyond k = 1: it returns ``-4k``.  Both halves
    are asserted, because the failure is the module's finding and a test
    that only checked the first half would hide it.
    """
    assert cone_local_min(0, 1, seed=0)["value"] == pytest.approx(0, abs=1e-6)
    assert cone_local_min(0, 2, seed=0)["value"] == pytest.approx(0, abs=1e-4)
    assert cone_local_min(0, 3, seed=0)["value"] == pytest.approx(0, abs=1e-4)
    assert relax(0, 1)["value"] == pytest.approx(0.0, abs=1e-6)
    for k in (2, 3):
        assert relax(0, k)["value"] == pytest.approx(-4.0 * k, abs=1e-3)


@pytest.mark.slow
def test_planted_infeasibility():
    """(c) At the one size the relaxation solves tightly, raising the
    constant above the true optimum must be rejected."""
    assert relax(0, 1, constant=4.0)["value"] == pytest.approx(0.0, abs=1e-6)
    for c in (4.25, 5.0, 8.0):
        assert relax(0, 1, constant=c)["value"] < -1e-3


@pytest.mark.slow
def test_clarabel_and_scs_agree():
    """(d) Two independent solvers on the same programme."""
    for n, k in ((0, 1), (1, 1), (2, 1), (0, 2)):
        a = relax(n, k, solver="CLARABEL")["value"]
        b = relax(n, k, solver="SCS")["value"]
        assert abs(a - b) < 2e-3, (n, k, a, b)


@pytest.mark.slow
def test_recorded_sdp_values_still_hold():
    """The recorded campaign must not drift silently."""
    for (n, k), v in list(SDP_RECORD["values"].items())[:6]:
        got = relax(n, k)["value"]
        assert got == pytest.approx(v, abs=2e-3), (n, k, got, v)


@pytest.mark.slow
def test_cone_minima_recorded_values():
    for (n, k), v in list(CONE_RECORD["bare"].items())[:4]:
        got = cone_local_min(n, k, seed=0)["value"]
        assert got == pytest.approx(v, abs=1e-3), (n, k, got, v)


@pytest.mark.slow
def test_derived_ranges_shrink_but_do_not_close_the_cone_gap():
    """The constructive half of the diagnosis: the derived window ranges
    cut the deficit by more than an order of magnitude and leave it
    negative --- a pointwise entry bound cannot close it."""
    bare = cone_local_min(4, 1, seed=0)["value"]
    ranged = cone_local_min(4, 1, seed=0, depth_cap=True, phi_range=True,
                            cross_cap=True)["value"]
    assert bare < -1.0
    assert -0.3 < ranged < -1e-4
    assert ranged > 10 * bare


@pytest.mark.slow
def test_relaxation_minimiser_at_n_zero_is_a_configuration():
    """The diagnosis of WHERE the looseness is: at n=0, k=2 the
    relaxation's first moment is a genuine Gram matrix of atoms and has
    ``Xi > 0``; the negative value lives in the moment matrix alone."""
    from sos_certificate import realizability_report
    r = relax(0, 2)
    L = r["index"]
    assert r["value"] < -1.0
    assert target_from_Q(r["Q"], L.kinds, THETA_FULL, 2) > 0
    rep = realizability_report(r["Q"], L.kinds, L.sigma, restarts=8)
    assert rep["relative"] < 1e-5, rep


def test_target_from_config_agrees_with_target_from_Q():
    on, pr = [0.0, 3.3], [(1.0, 0.25)]
    z, _, kinds = atoms(on, pr)
    assert target_from_config(on, pr) == pytest.approx(
        target_from_Q(qmat(z), kinds, THETA_FULL, 1), abs=1e-12)


def test_real_configurations_never_open_the_target():
    """A sanity sweep: the obligation itself holds everywhere sampled.
    This is evidence about the statement, not about the relaxation."""
    rng = np.random.default_rng(11)
    worst = math.inf
    for _ in range(300):
        n = int(rng.integers(0, 7))
        k = int(rng.integers(0, 4))
        xs = rng.uniform(-40, 40, n)
        ts = rng.uniform(-40, 40, k)
        ys = rng.uniform(0.0, 0.5, k)
        worst = min(worst, target_from_config(xs, list(zip(ts, ys))))
    assert worst >= -1e-9, worst
