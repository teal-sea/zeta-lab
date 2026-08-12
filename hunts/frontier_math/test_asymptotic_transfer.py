"""Controls for the unit dictionary and the asymptotic error budget.

Four questions the module has to answer under control:

(a) does their (7.1) norm `a` really equal our LAW D constant `A`, and by an
    identity rather than a coincidence of two decimal expansions;
(b) does the unit conversion round-trip - the same configuration assembled on
    our grid (step 1, constant 2 pi A) and on theirs (step 2 pi in x = tau L,
    constant a) has to give the same hat-unit R, tr(PQ), ||Q||_F^2 and D;
(c) which error term dominates the budget, and does it scale in T the way the
    source's own bound says it does;
(d) is there a finite height at which the extra census term clears the whole
    budget, and where.

Each carries its planted fault: a wrong normalisation carried across the
change of variable must show up as a factor 2 pi, and the deformed census
kernel must reduce to the Montgomery-Taylor one at lam = 1.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from asymptotic_transfer import (  # noqa: E402
    A, C_U, IMPROVEMENT, TWO_PI, HD, HD_slope, PaperParams, a_star, a_vs_A,
    budget_table, budget_total, census_floor_at_crossover,
    census_floor_lambda_sensitivity, crossover_l, dominant_term,
    drift_coefficient, error_budget, floor_at_lambda, g_lambda_is_g_at_one,
    grid_step_invariance, grid_sum_ladder, improvement_scaling,
    moment_closed_forms_vs_quadrature, poisson_constant, roundtrip,
    wrong_normalisation_lesion,
)
from lp_certificate import FLOOR_SCIPY  # noqa: E402

#: the source's headline Thm-A-line constant.
HD_ONE = 0.6725007036794117


# ---------------------------------------------------------------------------
# (a) the a-vs-A relation
# ---------------------------------------------------------------------------


def test_their_a_is_our_A_exactly():
    """a = a*(lam) = sin(th)/th, and A = Phi2(0) is that at lam = 1."""
    r = a_vs_A()
    assert r["closed_vs_A"] == 0.0                      # same real number
    assert r["quad_vs_A"] < 1e-7                        # and the quadrature
    assert abs(a_star(1.0) - 2 * math.sin(math.sqrt(2) / 2) / math.sqrt(2)) < 1e-15
    assert abs(A - 0.9187253698655684) < 1e-15


def test_the_starred_moments_reproduce_the_ratio_constant():
    """cRatio(lam; a*, b*, J*) = c*_lam is the source's own consistency law."""
    for row in moment_closed_forms_vs_quadrature((1.0, 0.99, 0.9, 0.5)):
        assert row["c_defect"] < 1e-12, row
        assert row["a_defect"] < 1e-7 and row["b_defect"] < 1e-7
        assert row["J_defect"] < 1e-7
    assert abs(HD(1.0) - HD_ONE) < 1e-12
    assert abs(HD_slope() - 0.6847) < 1e-3               # the price of lam < 1


# ---------------------------------------------------------------------------
# (b) the unit conversion, and its round-trip
# ---------------------------------------------------------------------------


def test_poisson_constant_is_the_norm_at_either_grid_step():
    """(2 pi/h) int phi^2: 2 pi A at h = 1, A at h = 2 pi (their a L^2 / L^2)."""
    assert abs(poisson_constant(1.0) - TWO_PI * A) < 1e-12
    assert abs(poisson_constant(TWO_PI) - A) < 1e-12
    rows = grid_sum_ladder(Ks=(100, 200, 400))
    for row in rows:
        assert row["unit_defect"] < 1e-5
    # the residual is truncation, so it halves with the span
    assert rows[1]["unit_defect"] < 0.6 * rows[0]["unit_defect"]
    assert rows[2]["unit_defect"] < 0.6 * rows[1]["unit_defect"]
    assert rows[2]["gram_defect"] < 0.6 * rows[1]["gram_defect"]


def test_normalised_gram_is_grid_step_independent():
    """The (2 pi/h) cancels: our grid and theirs compute the same omega."""
    rows = grid_step_invariance(spans=(600.0, 1200.0))
    for row in rows:
        assert row["worst_defect"] < 1e-3
    assert rows[1]["worst_defect"] < 0.7 * rows[0]["worst_defect"]


def test_unit_conversion_round_trips_on_the_composition_inputs():
    """R, tr(PQ), ||Q||_F^2, D: same numbers on both grids, factor 1."""
    rows = roundtrip(spans=(600.0, 1200.0))
    for row in rows:
        # tr P = N for unit vectors (the known quantity), up to truncation
        assert abs(row["trP_theirs"] - row["N"]) < 1e-3
        # D = ||Ahat||_F^2 - sum m^2 holds exactly once the truncated unit
        # norms are accounted for, and the accounting is the whole residual
        assert row["D_identity_explained"] < 1e-12
        for name in ("R", "trPQ", "fro2_Q"):
            assert abs(row[name]["ratio"] - 1.0) < 5e-2, (name, row[name])
    assert rows[1]["D_identity_defect"] < 0.7 * rows[0]["D_identity_defect"]
    assert (abs(rows[1]["trP_theirs"] - rows[1]["N"])
            < 0.7 * abs(rows[0]["trP_theirs"] - rows[0]["N"]))
    # both grids approach the kernel-only reference, and do so like 1/span
    for name in ("R", "trPQ", "fro2_Q"):
        assert rows[1][name]["rel_ours"] < 0.7 * rows[0][name]["rel_ours"]
        assert rows[1][name]["rel_theirs"] < 0.7 * rows[0][name]["rel_theirs"]
    assert abs(rows[1]["D_ratio"] - 1.0) < abs(rows[0]["D_ratio"] - 1.0)


def test_lesion_a_wrong_normalisation_is_a_clean_factor_two_pi():
    """The planted fault this seam exists to catch, measured."""
    les = wrong_normalisation_lesion()
    assert abs(les["good_unit_norm"] - 1.0) < 1e-5
    assert abs(les["measured_lesion_ratio"] - 1.0 / TWO_PI) < 1e-12
    assert les["lesioned_unit_norm"] < 0.2          # visibly not a unit vector


# ---------------------------------------------------------------------------
# (c) the error budget
# ---------------------------------------------------------------------------


def test_admissibility_is_the_sources_own():
    """0 < lam < 1, w >= 1, 8w <= L - and lam = 1 is NOT admissible."""
    assert not PaperParams(lam=1.0).is_valid(1e4)
    assert not PaperParams(lam=0.9, w=0.5).is_valid(1e4)
    assert not PaperParams(lam=0.9, w=1.0).is_valid(5.0)      # 8w > L
    assert PaperParams(lam=0.999, w=1.0).is_valid(1e4)
    P = PaperParams(lam=0.999)
    assert P.lam1(1e4) < P.lam                                # lam1 = L/ell1


def test_dominant_term_is_the_window_moment_drift():
    """At every admissible height the budget is led by |cinv(T) - 1/c*|."""
    for l in (1e4, 1e6):
        P = PaperParams(lam=1.0 - 1.5 / l)
        top = dominant_term(l, P)
        assert top.name.startswith("drift"), (l, top)
        assert top.constant.startswith("explicit")


def test_the_dominant_term_scales_like_one_over_L():
    """35.52 w/L: ten times the height, one tenth the term, at two T."""
    vals = {}
    for l in (1e4, 1e5):
        P = PaperParams(lam=1.0 - 1.5 / l)
        terms = {t.name: t.value for t in error_budget(l, P)}
        vals[l] = terms["drift |cinv(T)-1/c*|"]
        assert abs(vals[l] * P.L(l) / 35.52 - 1.0) < 0.01    # the constant
    assert abs(vals[1e4] / vals[1e5] - 10.0) < 0.05


def test_the_dominant_terms_constant_is_derived_not_fitted():
    """4/(l1 a^2) + 16 l1/a^2 + 8 cinv/a + |dcinv/dl1|(2log2-1) = 35.52."""
    dc = drift_coefficient()
    assert abs(dc["from_b"] - 4.739) < 1e-3
    assert abs(dc["from_J"] - 18.956) < 1e-3
    assert abs(dc["from_a"] - 11.559) < 1e-3
    assert abs(dc["from_lam1_offset"] - 0.264517) < 1e-5
    assert abs(dc["total"] - 35.519106) < 1e-5
    assert abs(-dc["dcinv_dlam1"] - HD_slope()) < 1e-5     # = HD'(1)
    # and the budget's own measurement converges to it
    for l in (1e5, 1e6):
        P = PaperParams(lam=1.0 - 1.5 / l)
        assert abs(P.cinv_drift(l) * P.L(l) / dc["total"] - 1.0) < 1e-3


def test_budget_is_o_of_one_and_no_term_is_left_out():
    """Every term falls, the total falls like 1/l, and calE is not the leader."""
    totals = [budget_total(l, PaperParams(lam=1.0 - 1.5 / l))
              for l in (1e4, 1e5, 1e6)]
    assert totals[0] > totals[1] > totals[2] > 0
    assert abs(totals[0] / totals[1] - 10.0) < 0.3
    l = 1e6
    P = PaperParams(lam=1.0 - 1.5 / l)
    terms = {t.name: t.value for t in error_budget(l, P)}
    assert terms["R2 = C2 calE cinv N"] < terms["drift |cinv(T)-1/c*|"]
    assert len(terms) == 7


def test_the_budget_table_reports_the_verdict_at_each_height():
    rows = budget_table(ls=(1e3, 1e6))
    for row in rows:
        assert row["valid"]
        assert row["improvement"] == IMPROVEMENT
        assert row["total"] > row["improvement"]      # neither height suffices
        assert row["lam1"] < row["lam"] < 1.0


# ---------------------------------------------------------------------------
# (d) the crossover
# ---------------------------------------------------------------------------


def test_crossover_exists_is_finite_and_is_reported():
    cr = crossover_l()
    assert cr["exists"]
    assert 1e6 < cr["l"] < 1e7                       # l = log(T/2pi)
    assert abs(cr["l"] - 3.9e6) / 3.9e6 < 0.15
    assert 1.5e6 < cr["log10_T"] < 1.9e6             # T is astronomically large
    assert cr["budget"] < cr["improvement"]
    assert 0.0 < cr["k"] < 8.0 and cr["lam"] < 1.0
    # one notch below the crossover the errors still dominate
    assert budget_total(cr["l"] / 2, PaperParams(lam=1.0 - cr["k"] * 2 / cr["l"])) \
        > IMPROVEMENT


def test_crossover_moves_linearly_with_the_existential_constant():
    """C multiplies only the calE-side terms, so the crossover creeps."""
    from asymptotic_transfer import crossover_sensitivity
    rows = crossover_sensitivity(Cs=(1.0, 10.0))
    assert all(r["exists"] for r in rows)
    assert rows[1]["l"] > rows[0]["l"]
    assert rows[1]["l"] < 3.0 * rows[0]["l"]


def test_crossover_height_is_inverse_in_the_improvement():
    """l_cross * improvement is roughly constant: T_cross ~ exp(K/improvement)."""
    rows = improvement_scaling(factors=(1.0, 10.0))
    prods = [r["l_times_improvement"] for r in rows]
    assert all(20.0 < p < 60.0 for p in prods), prods
    assert abs(prods[0] / prods[1] - 1.0) < 0.15


# ---------------------------------------------------------------------------
# the census kernel away from lam = 1
# ---------------------------------------------------------------------------


def test_the_deformed_kernel_is_the_MT_kernel_at_lambda_one():
    """g_{lam,lam1} at lam = lam1 = 1 IS cg_transplant.g_kernel."""
    assert g_lambda_is_g_at_one() < 1e-14


def test_the_deformed_kernel_reproduces_the_pinned_census_floor():
    """At lam = 1 the deformed instrument IS the reading's own LP."""
    assert abs(floor_at_lambda(1.0) / FLOOR_SCIPY - 1.0) < 1e-12
    assert abs(C_U - FLOOR_SCIPY) == 0.0


@pytest.mark.slow
def test_the_census_floor_survives_the_lambda_the_crossover_uses():
    """1 - lam1 ~ 5e-7 there; c_u must not move enough to matter."""
    rows = census_floor_lambda_sensitivity(deltas=(0.0, 1e-4))
    assert abs(rows[1]["slope"]) < 1e-2               # dc_u/dlam ~ -5e-4
    assert rows[1]["floor"] > rows[0]["floor"]        # lam < 1 raises it
    cf = census_floor_at_crossover()
    assert cf["exists"]
    assert cf["one_minus_lam1"] < 1e-5
    assert cf["instrument_vs_pinned"] < 1e-15
    assert 0.0 <= cf["shift"] < 1e-3 * C_U            # under 0.1% of the floor
