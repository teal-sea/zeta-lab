"""Controls for the co-optimizing adversary (audit follow-through).

Fast tier only: small K, few restarts.  The full hunt's numbers are in
the ledger; these tests pin that the instrument keeps its power and its
dictionary, not the full search.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import numpy as np  # noqa: E402
import pytest  # noqa: E402

import coopt_adversary as ca  # noqa: E402


def test_dictionary_closed_forms_match_matrices():
    """budget_terms against GridAssembly on the battery ADV rows: the
    defect must be truncation-grade, not convention-grade."""
    rec = ca.dictionary_control(K=600)
    assert rec["worst_defect"] < 5e-3, rec


def test_lesion_deleting_slack_violates():
    """Detector power: with the slack term deleted the battery's worst
    row must show V > 0.  A budget that passes even then has no teeth."""
    assert ca.lesion_budget_without_slack() > 0


def test_theta_one_stacking_is_unbounded():
    """Convention control: at theta = 1 the R charge vanishes and
    stacked multiplicity profit must grow linearly and end positive."""
    ok, vals = ca.theta_one_control()
    assert ok, vals


def test_self_stacking_enters_R():
    """A multiplicity-2 point must be charged m(m-1) = 2 at omega^2(0):
    the coincident-distinct-points model of the band dual."""
    g1 = ca._damage_min(0.49, 1)
    r1 = ca.budget_terms([g1], [1], [0.0], [0.49])
    r2 = ca.budget_terms([g1], [2], [0.0], [0.49])
    assert abs((r2["R"] - r1["R"]) - 2.0) < 1e-12


def test_matrix_verification_expands_multiplicities():
    """verify_on_matrices must reproduce the closed-form self-stacking:
    R_matrix for an m=2 point ~ 2 (coincident points, omega^2(0) = 1)."""
    g1 = ca._damage_min(0.49, 1)
    rec = ca.budget_terms([g1], [2], [0.0], [0.49])
    rec.update({"xs": [g1], "ms": [2], "ts": [0.0], "ys": [0.49]})
    chk = ca.verify_on_matrices(rec, K=600)
    assert abs(chk["R_matrix"] - rec["R"]) < 5e-3
    assert chk["defect"] < 5e-3


def test_no_violation_on_structured_seeds_fast():
    """The verdict on the structured seeds at reduced iteration count.
    (The full 57-restart hunt is the ledger's record; this pins that
    the committed instrument still finds no violation where it looked.)"""
    rows = [ca.polish(s, maxiter=800) for s in ca.seeds()]
    worst = max(r["V"] for r in rows)
    assert worst <= 1e-9, [r["name"] for r in rows if r["V"] > 1e-9]


@pytest.mark.slow
def test_no_violation_full_hunt():
    rows = ca.hunt(rng_count=40)
    assert all(r["V"] <= 1e-9 for r in rows)


def test_joint_minima_are_minima():
    """The joint-field minima the seeds use must actually be negative
    local minima of the summed field."""
    pairs = [(0.0, 0.49), (6.406, 0.49)]
    mins = ca.joint_damage_minima(pairs, n=3)
    assert mins
    for g in mins:
        w = sum(float(ca._chain.W(np.array([g - t]), y)[0])
                for t, y in pairs)
        assert w < 0
