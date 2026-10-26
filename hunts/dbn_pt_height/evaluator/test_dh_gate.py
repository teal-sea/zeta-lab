"""Tests for dh_gate.py, on development boxes only.

The gate's own boxes (Z1 to Z4, C1, C2) are not touched here: the gate is run
once, as preregistered in DH_GATE_PREREG.md, by ``dh_gate.main``.  These tests
use two boxes the preregistration does not name.  D0 is around Spira's zero
0.574356 + 166.479306i, z = 332.959 + 0.149i, which was left out of the gate
for this purpose. D1 is a box at t = 0.1 that hunt #61's route finds
zero-free.

    .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/evaluator/test_dh_gate.py
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import dh_gate as G  # noqa: E402

D0 = (F(0), (F("3328/10"), F("3331/10"), F("8/100"), F("22/100")))
D1 = (F(1, 10), (F(600), F("6005/10"), F("1/10"), F("3/10")))


def test_development_boxes_are_not_gate_boxes() -> None:
    for t, box in (D0, D1):
        for g in G.GATE_BOXES.values():
            assert not (g["t"] == t and g["box"] == box)


def test_truth_on_the_development_boxes() -> None:
    """Hunt #61's decided counts: one zero in D0, none in D1."""
    r = G.truth(D0[1], D0[0])
    assert r["status"] == "decided" and r["N"] == 1
    r = G.truth(D1[1], D1[0])
    assert r["status"] == "decided" and r["N"] == 0


def test_the_pipeline_counts_the_development_zero() -> None:
    r = G.dh_barrier(D0[1], D0[0])
    assert r["n_failed"] == 0 and r["winding"] == 1


def test_the_pipeline_calls_the_development_control_zero_free() -> None:
    r = G.dh_barrier(D1[1], D1[0])
    assert r["n_failed"] == 0 and r["winding"] == 0


@pytest.mark.parametrize("fault", ["one_corner", "main_terms_only"])
def test_permissive_faults_call_the_development_zero_free(fault: str) -> None:
    """The faults that the gate exists to catch do, on D0, what they would do on
    a gate box: they call a box with a zero in it zero-free."""
    r = G.dh_barrier(D0[1], D0[0], faults=frozenset([fault]))
    assert r["winding"] == 0


@pytest.mark.parametrize("fault", ["no_M2", "no_margin"])
def test_margin_faults_are_invisible_on_a_clean_box(fault: str) -> None:
    """Measured on D0: weakening the margin does not change the count here,
    because |H| on the boundary is far above any margin.  The gate records
    these two as possibly not caught, which is what this shows."""
    r = G.dh_barrier(D0[1], D0[0], faults=frozenset([fault]))
    assert r["winding"] == 1


def test_the_evaluation_budget_leaves_a_box_undecided() -> None:
    r = G.dh_barrier(D0[1], D0[0], max_evaluations=5)
    assert r["winding"] is None and r["n_failed"] > 0


def test_unknown_faults_are_refused() -> None:
    with pytest.raises(ValueError):
        G.dh_barrier(D0[1], D0[0], faults=frozenset(["typo"]))


def test_the_decision_table() -> None:
    c = G.classify
    assert c("zero", 1, 1) == "REFUSE"
    assert c("zero", 1, None) == "REFUSE_WEAK"
    assert c("zero", 1, 0) == "ACCEPT"
    assert c("zero", 1, 2) == "INCONSISTENT"
    assert c("zero", 0, 0) == "TRUTH_EMPTY"
    assert c("zero", None, 0) == "TRUTH_UNAVAILABLE"
    assert c("control", 0, 0) == "DISCRIMINATES"
    assert c("control", 0, None) == "NON_DISCRIMINATING"
    assert c("control", 0, 1) == "INCONSISTENT"
    assert c("control", 1, 1) == "CONTROL_NOT_EMPTY"


def test_the_verdict_rule() -> None:
    v = G.verdict
    assert v({"Z1": "REFUSE", "Z2": "REFUSE_WEAK", "C1": "DISCRIMINATES"}) == "PASS"
    assert v({"Z1": "REFUSE", "Z2": "ACCEPT", "C1": "DISCRIMINATES"}) == "FAIL"
    assert v({"Z1": "REFUSE", "C1": "INCONSISTENT"}) == "FAIL"
    assert v({"Z1": "REFUSE_WEAK", "C1": "DISCRIMINATES"}) == "INCONCLUSIVE"
    assert v({"Z1": "REFUSE", "C1": "NON_DISCRIMINATING"}) == "INCONCLUSIVE"
    assert v({"Z1": "REFUSE", "Z2": "TRUTH_EMPTY", "C1": "DISCRIMINATES"}) == "PASS"


def test_the_recorded_gate_run_is_the_preregistered_one() -> None:
    """dh_gate_results.json holds the run of RUNS.md E7: the preregistered boxes,
    every fault, and the verdicts recorded there."""
    import json

    d = json.loads((HERE / "dh_gate_results.json").read_text())
    assert d["preregistration"] == "DH_GATE_PREREG.md"
    assert set(d["truth"]) == set(G.GATE_BOXES)
    assert all(v["status"] == "decided" for v in d["truth"].values())
    assert {k: v["N"] for k, v in d["truth"].items()} == {"Z1": 1, "Z2": 1, "Z3": 1, "Z4": 1, "C1": 0, "C2": 0}
    assert set(d["runs"]) == {"clean", *G.FAULTS}
    want = {"clean": "PASS", "one_corner": "FAIL", "main_terms_only": "FAIL",
            "no_margin": "PASS", "no_M2": "PASS", "narrow_frame": "FAIL"}
    assert {k: v["verdict"] for k, v in d["runs"].items()} == want
    for k, run in d["runs"].items():  # the verdicts follow from the rows by the preregistered rule
        assert G.verdict(run["rows"]) == run["verdict"]
        for box, row in run["rows"].items():
            g = G.GATE_BOXES[box]
            assert G.classify(g["kind"], d["truth"][box]["N"], run["outputs"][box]["winding"]) == row
    assert all(o["winding"] == 1 for b, o in d["runs"]["clean"]["outputs"].items() if b.startswith("Z"))
