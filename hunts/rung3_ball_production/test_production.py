"""Hunt #145: the production workflow and the steps it runs (production.py).

Nothing here launches Lean or GitHub.  These tests pin the workflow's trigger and limits,
the request validation, the site assignment, and the predicates that decide whether a
job (and the run) counts: the axiom audit, the planted fault's refusal, the verdict.
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest
import yaml

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WF = ROOT / ".github" / "workflows" / "rung3-production.yml"


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


prod = _load("rung3_production", HERE / "production.py")
BASE = {"tower": "whole", "plan": "lean/cert/rung3_plan2.json",
        "toolchain": prod.TOOLCHAIN, "mathlib": prod.MATHLIB}
CALIBRATE = {"mode": "calibrate", **BASE, "sites": ["centre", "B_right_06"],
             "jobs": 1, "lean_jobs": 1}
FULL = {"mode": "full", **BASE, "jobs": 20, "lean_jobs": 2, "fault_site": "B_right_06"}


# --------------------------------------------------------------------------- the workflow

def _wf() -> dict:
    return yaml.safe_load(WF.read_text())


def test_workflow_triggers_only_on_the_request_file_on_this_branch():
    wf = _wf()
    on = wf[True] if True in wf else wf["on"]       # YAML 1.1 reads `on` as True
    assert set(on) == {"push"}
    assert on["push"]["branches"] == ["hunt/rung3-ball-production"]
    assert on["push"]["paths"] == ["hunts/rung3_ball_production/RUN_REQUEST.json"]


def test_workflow_limits():
    wf = _wf()
    assert wf["permissions"] == {"contents": "read"}
    assert wf["concurrency"]["group"] == "rung3-production"
    assert wf["concurrency"]["cancel-in-progress"] is False
    for name, job in wf["jobs"].items():
        assert job["timeout-minutes"] <= 350, name
    sites = wf["jobs"]["sites"]
    assert sites["strategy"]["max-parallel"] <= 6
    assert sites["strategy"]["fail-fast"] is False
    assert wf["env"]["MATHLIB_REV"] == prod.MATHLIB


def test_workflow_never_restores_a_copied_lake():
    text = WF.read_text()
    for step in _wf()["jobs"]["sites"]["steps"]:
        if step.get("uses", "").startswith("actions/cache"):
            assert "lean/.lake" not in step["with"]["path"]
    assert "lake exe cache get" in text and "production.py\" toplevels" in text
    assert "timeout 300m" in text


def test_artifacts_are_attempt_unique_and_resume_reads_them():
    text = WF.read_text()
    assert "rung3-production-job${{ matrix.job }}-attempt${{ github.run_attempt }}" in text
    assert "rung3-production-record-job${{ matrix.job }}-attempt${{ github.run_attempt }}" in text
    assert "pattern: rung3-production-job${{ matrix.job }}-attempt*" in text


# --------------------------------------------------------------------------- the request

def test_requests_validate():
    prod.validate(CALIBRATE)
    prod.validate(FULL)
    for bad in ({**CALIBRATE, "tower": "staged"}, {**CALIBRATE, "sites": ["B_right_06"]},
                {**CALIBRATE, "mathlib": "0" * 40}, {**FULL, "jobs": 40},
                {**FULL, "lean_jobs": 4}, {**FULL, "fault_site": "nope"},
                {**FULL, "mode": "other"}):
        with pytest.raises(AssertionError):
            prod.validate(bad)


def test_full_assignment_covers_every_site_once_under_the_cap():
    bins = prod.assign(FULL["jobs"])
    flat = [s for b in bins for s in b]
    assert sorted(flat) == sorted(prod.plan_sites()) and len(flat) == 215
    loads = [prod.projected_cpu(b) for b in bins]
    assert max(loads) <= prod.PER_JOB_CPU_S_MAX
    assert max(loads) - min(loads) < 0.1 * max(loads)
    assert prod.assign(FULL["jobs"]) == bins                  # deterministic
    assert prod.job_sites(CALIBRATE, 0) == ["centre", "B_right_06"]


def test_theorem_names_follow_the_generator():
    assert prod.theorem("B_right_06", "big") == "upper_B_right_06"
    assert prod.theorem("g_left_03", "grid") == "beta_g_left_03"
    assert prod.theorem("centre", "centre") == "centre_lt_centre"


# --------------------------------------------------------------------------- the predicates

def test_axiom_audit_accepts_exactly_the_standard_three():
    out = prod.parse_axioms(
        "'ZetaLean.DH.Cert.upper_X' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
        "'ZetaLean.DH.Cert.beta_Y' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]\n"
        "'ZetaLean.DH.Cert.beta_Z' does not depend on any axioms\n")
    assert prod.axioms_ok(out["ZetaLean.DH.Cert.upper_X"])
    assert not prod.axioms_ok(out["ZetaLean.DH.Cert.beta_Y"])
    assert not prod.axioms_ok(out["ZetaLean.DH.Cert.beta_Z"])
    assert not prod.axioms_ok(None)
    assert not prod.axioms_ok(["propext", "Classical.choice", "Quot.sound",
                               "ZetaLean.DH.Cert.upper_B_left_00"])


def test_fault_refusal_is_read_off_the_failing_declaration():
    src = ("namespace Prime_2\n\ndef S : ComplexBall := x\n"
           "private lemma ev_whole : a = b := by\n  decide +kernel\n\nend Prime_2\n"
           "lemma hp_2 : c := by\n  simpa\n")
    log = "/x/CB/Primes.lean:5:2: error: Tactic `decide` failed\n/x/CB/Primes.lean:9:2: error: mismatch\n"
    assert prod.error_decls(log, src, "Primes.lean") == ["Prime_2.ev_whole", "hp_2"]


def test_verdict_counts_only_a_complete_clean_run(tmp_path):
    req = tmp_path / "req.json"
    req.write_text(json.dumps(CALIBRATE))
    rec = tmp_path / "records" / "a"
    rec.mkdir(parents=True)
    (rec / "sites.json").write_text(json.dumps({s: {"status": "ok", "cpu_s": 1, "olean_bytes": 1}
                                                for s in CALIBRATE["sites"]}))
    (rec / "axioms.json").write_text(json.dumps({s: {"ok": True} for s in CALIBRATE["sites"]}))
    prod.cmd_verdict(CALIBRATE, tmp_path / "records")
    (rec / "axioms.json").write_text(json.dumps({"centre": {"ok": True},
                                                 "B_right_06": {"ok": False}}))
    with pytest.raises(SystemExit):
        prod.cmd_verdict(CALIBRATE, tmp_path / "records")
    with pytest.raises(SystemExit):           # full mode with no fault record never counts
        prod.cmd_verdict(FULL, tmp_path / "records")
