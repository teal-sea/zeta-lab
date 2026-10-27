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
FULL = {"mode": "full", **BASE, "jobs": 20, "lean_jobs": 1, "fault_site": "B_right_06",
        "calibration": prod.calibration()}


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
                {**FULL, "mode": "other"}, {k: v for k, v in FULL.items() if k != "calibration"},
                {**FULL, "calibration": {**FULL["calibration"], "cpu_scale": 0.3}},
                {**FULL, "lean_jobs": 2}, {**FULL, "jobs": 3}):
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


def test_full_plan_is_sized_from_the_runner_calibration():
    c = PILOT_JSON["calibration_runner"]
    assert c["conclusion"] == "success" and c["run"] == 40350287309      # attempt 2
    assert set(c["sites"]) == {"centre", "B_right_06"}
    assert all(v["status"] == "ok" for v in c["sites"].values()) and all(c["axioms_ok"].values())
    for sid, v in c["sites"].items():
        assert c["cpu_scale"][sid] == round(v["cpu_s"] / v["projected_cpu_s"], 3)
    assert c["setup_s"] == c["job_s"] - c["steps_s"]["generate"] - c["steps_s"]["compile"] \
        - c["steps_s"]["axioms"]
    cal = prod.calibration()
    assert cal["cpu_scale"] == max(c["cpu_scale"].values())
    walls = [prod.job_wall_bound_s(FULL, ids) for ids in prod.assign(FULL["jobs"])]
    assert max(walls) <= prod.JOB_WALL_S_MAX
    assert 2 * cal["peak_rss_gb"] > prod.RUNNER_RSS_GB          # why lean_jobs is 1


PILOT_JSON = json.loads((HERE / "pilot.json").read_text())


@pytest.mark.parametrize("key,run", [("calibration_runner_v1", 40340279740),
                                     ("calibration_runner", 40350287309)])
def test_pilot_md_quotes_the_runner_calibration(key, run):
    text = " ".join((HERE / "PILOT.md").read_text().split())
    c = PILOT_JSON[key]
    assert c["run"] == run and c["conclusion"] == "success" and all(c["axioms_ok"].values())
    for sid, v in c["sites"].items():
        row = (f"| {v['cpu_s']:,.1f} | {v['wall_s']:,.1f} | {v['peak_rss_bytes'] / 1e9:.2f} | "
               f"{v['olean_bytes']:,} | {v['projected_cpu_s']:,.1f} | {c['cpu_scale'][sid]:.3f} |")
        assert row in text, sid
    assert f"took {c['job_s']} s in all, of which {c['setup_s']} s was setup" in text
    assert f"run {run}" in text


def test_no_public_name_repeats_across_the_215_whole_mode_sites():
    c = PILOT_JSON["namespace_census"]
    assert c["sites"] == 215 and c["whole_repeated_names"] == 0
    assert c["prime_towers"] == PILOT_JSON["whole_projection"]["towers"] == 15608
    assert c["staged_repeated_names"] == c["staged_public_names_per_tower"] * (
        c["prime_towers"] - c["distinct_primes"])
    assert c["staged_sites_sharing_prime_2"] == 215
    text = " ".join((HERE / "PILOT.md").read_text().split())
    assert f"declare {c['whole_public_names']:,} public names, and **none repeats**" in text
    assert f"{c['staged_repeated_names']:,} repeated" in text
    assert f"({c['staged_distinct_colliding_names']:,} distinct names)" in text


# --------------------------------------------------------------------------- the fault step under bash -e

def _fault_step_script() -> str:
    steps = _wf()["jobs"]["sites"]["steps"]
    return next(s for s in steps if s.get("name") == "compile the faulted site (must be refused)")["run"]


def _run_under_bash_e(script: str, tmp_path: Path) -> tuple[int, Path]:
    """GitHub's `bash -e {0}`, with `python` stubbed: the compile exits 1 (a refused
    fault), `refused` records its arguments."""
    import os
    import subprocess
    bindir = tmp_path / "bin"
    bindir.mkdir()
    marker = tmp_path / "refused.args"
    (bindir / "python").write_text(
        "#!/usr/bin/env bash\n"
        'case "$*" in\n'
        '  *72_rung3_ball_compile.py*) echo "Primes.lean failed"; exit 1 ;;\n'
        f'  *" refused "*) echo "$*" > "{marker}"; exit 0 ;;\n'
        "esac\nexit 3\n")
    (bindir / "python").chmod(0o755)
    (tmp_path / "gen").mkdir()
    (tmp_path / "gen" / "CB_right_06.manifest.json").write_text("{}")
    env = dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}", HUNT="h", REQ="r.json")
    p = subprocess.run(["bash", "-e", "-c", script], cwd=tmp_path, env=env,
                       capture_output=True, text=True)
    return p.returncode, marker


def test_fault_step_reaches_refused_under_bash_e(tmp_path):
    rc, marker = _run_under_bash_e(_fault_step_script(), tmp_path)
    assert rc == 0 and marker.is_file()
    assert "--rc 1" in marker.read_text() and " refused " in f" {marker.read_text()} "


def test_the_old_fault_step_lost_its_verdict_under_bash_e(tmp_path):
    """The control: the step as run in 40353536947 aborts before `refused`."""
    old = ("set -uo pipefail\nmkdir -p out\n"
           "python scripts/72_rung3_ball_compile.py --lean-project lean --output-root out \\\n"
           "  --jobs 1 --module-jobs 1 gen/*.manifest.json 2>&1 | tee out/compile.log\n"
           "rc=${PIPESTATUS[0]}\n"
           'python "$HUNT/production.py" refused --request "$REQ" --gen gen --out out --rc "$rc"\n')
    rc, marker = _run_under_bash_e(old, tmp_path)
    assert rc != 0 and not marker.exists()


def test_fault_mode_plans_the_fault_job_alone():
    req = {"mode": "fault", **BASE, "fault_site": "B_right_06", "lean_jobs": 1,
           "completes_run": 40353536947, "attempt": 2}
    prod.validate(req)
    with pytest.raises(AssertionError):
        prod.validate({k: v for k, v in req.items() if k != "completes_run"})


@pytest.mark.parametrize("req,jobs", [
    (CALIBRATE, ["0"]),
    (FULL, [str(j) for j in range(20)] + ["fault"]),
    ({"mode": "fault", **BASE, "fault_site": "B_right_06", "lean_jobs": 1,
      "completes_run": 40353536947, "attempt": 2}, ["fault"])])
def test_plan_prints_the_matrix_for_every_mode(req, jobs, capsys):
    prod.cmd_plan(req)
    out = dict(line.split("=", 1) for line in capsys.readouterr().out.splitlines())
    assert out["mode"] == req["mode"] and json.loads(out["jobs"]) == jobs
    assert out["lean_jobs"] == str(req["lean_jobs"])


def test_verdict_pairs_a_full_run_with_a_fault_run(tmp_path):
    full = tmp_path / "records" / "000040353536947" / "rung3-production-record-job0-attempt1"
    fault = tmp_path / "records" / "000040999999999" / "rung3-production-record-jobfault-attempt1"
    full.mkdir(parents=True)
    fault.mkdir(parents=True)
    sites = sorted(prod.plan_sites())
    (full / "sites.json").write_text(json.dumps({s: {"status": "ok"} for s in sites}))
    (full / "axioms.json").write_text(json.dumps({s: {"ok": True} for s in sites}))
    with pytest.raises(SystemExit):                 # sites alone: no fault, no count
        prod.cmd_verdict(FULL, tmp_path / "records")
    (fault / "fault.json").write_text(json.dumps({"refused_at_ev_whole": True}))
    prod.cmd_verdict(FULL, tmp_path / "records")


def test_axiom_parser_reads_names_ending_in_a_prime():
    out = prod.parse_axioms(
        "'ZetaLean.DH.Rung3Assembly.Plan2.dh_zero_located' depends on axioms: [propext]\n"
        "'ZetaLean.DH.Rung3Assembly.Plan2.dh_zero_located'' depends on axioms: "
        "[propext, Classical.choice, Quot.sound]\n")
    assert out["ZetaLean.DH.Rung3Assembly.Plan2.dh_zero_located'"] == sorted(prod.STANDARD_AXIOMS)
    assert out["ZetaLean.DH.Rung3Assembly.Plan2.dh_zero_located"] == ["propext"]


# --------------------------------------------------------------------------- the production record

PROD = PILOT_JSON.get("production", {})


def test_production_verdict_follows_from_its_site_records():
    v, sites = PROD["verdict"], PROD["sites"]
    assert set(sites) == set(prod.plan_sites()) and v["sites"] == 215
    assert v["sites_ok"] == sum(1 for r in sites.values() if r["status"] == "ok") == 215
    assert v["axioms_clean"] == 215 and v["axiom_sets"] == [["Classical.choice", "Quot.sound", "propext"]]
    assert v["olean_bytes"] == sum(r["olean_bytes"] for r in sites.values())
    assert v["cpu_core_hours"] == pytest.approx(sum(r["cpu_s"] for r in sites.values()) / 3600, abs=0.01)
    assert PROD["fault_run"]["fault"]["refused_at_ev_whole"] is True
    assert PROD["fault_run"]["fault"]["error_decls"][0] == "Prime_B_right_06_2.ev_whole"


def test_every_final_declaration_rests_on_the_standard_axioms():
    ax = PROD["assembly_box"]["axioms"]
    assert set(ax) == set(prod.FINAL) and len(ax) == 17
    assert all(prod.axioms_ok(a) for a in ax.values())
    printed = PROD["assembly_box"]["printed"]
    results = (HERE / "RESULTS.md").read_text()
    for line in printed.strip().splitlines():
        assert line in results, line                       # quoted verbatim
    assert all(r["returncode"] == 0 and not r["killed_by_guard"]
               for r in PROD["assembly_box"]["runs"])


def test_the_strip_reassembly_rests_on_the_standard_axioms_and_moved_nothing():
    """Door 2: the re-assembly of the same 215 site oleans with `Strip.lean`. The new
    theorem and the 17 old declarations print exactly the three axioms, quoted verbatim in
    RESULTS.md; the downloads and the oleans of the first assembly came back byte for byte;
    each planted fault in the strip condition was refused at the new theorem."""
    s = PROD["strip_assembly"]
    ax = s["axioms"]
    assert list(ax) == prod.FINAL + prod.STRIP and len(ax) == 18
    assert all(prod.axioms_ok(a) for a in ax.values())
    results = (HERE / "RESULTS.md").read_text()
    for line in s["printed"].strip().splitlines():
        assert line in results, line
    assert [r["tag"] for r in s["runs"]] == ["support", "assembly", "separation", "strip", "axioms"]
    assert all(r["returncode"] == 0 and not r["killed_by_guard"] and r["mem_available_gib_low"] > 20
               for r in s["runs"])
    assert s["collect"]["artifacts"] == PROD["collect"]["artifacts"]   # the same 20 digests
    assert s["collect"]["same_artifacts_as_first"] is True
    assert s["site_root_oleans"] == {"count": 215, "sha256_equal_first_receipts": True}
    assert s["zetalean_build_unchanged"] is True
    olean = s["assembly_oleans"]
    assert all(v["equal_first"] for k, v in olean.items() if "Strip" not in k)
    assert {k for k in olean if "Strip" in k} == {"Rung3Assembly/Strip.olean"}
    f = s["strip_faults"]
    want = ["ZetaLean.DH.Rung3Assembly.Plan2.davenport_heilbronn_strip"]
    assert f["control"]["returncode"] == 0 and f["control"]["refused_at"] == []
    for tag in ("re-below-square", "line-through-square"):
        assert f[tag]["returncode"] == 1 and f[tag]["refused_at"] == want, tag
        assert not f[tag]["killed_by_guard"], tag
    assert "oleans on disk under <cache>/" in s["where"]


def test_door_one_records_a_same_kernel_replay_and_a_priced_second_kernel():
    """Door 1: `leanchecker --fresh` over the closure of all 18 declarations accepted, inside
    the estimate written before it; it can fail (a missing module, a one-byte olean fault);
    `con-ron` checked samples only, read the same fault, and the full run is priced, not
    run. RESULTS.md quotes the figures and never calls the replay independent."""
    r = PROD["replay"]
    a = r["stage_a"]
    assert a["command"][-2:] == ["--fresh", "Rung3Assembly.Final"]
    assert a["exit_code"] == 0 and a["stop_reason"] is None and a["stdout"] == a["stderr"] == ""
    lo_h, hi_h = r["replay_sample"]["estimate_written_h"]
    assert lo_h * 3600 <= a["wall_s"] <= hi_h * 3600
    lo_gb, hi_gb = r["replay_sample"]["estimate_written_peak_rss_gb"]
    assert lo_gb <= a["peak_sampled_tree_rss_kib"] * 1024 / 1e9 <= hi_gb
    assert a["min_memavailable_kib"] > 20 * 2**20
    assert r["replay_sample"]["all_accepted"] and r["replay_sample"]["modules"] == 175
    c = r["census"]
    assert c["constants"] == sum(g["constants"] for g in c["groups"].values()) + c["site_constants"]
    assert (c["modules"], c["constants"], c["site_constants"]) == (11955, 1569505, 761387)
    assert r["collect"] == {"same_artifacts_as_first": True, "site_root_oleans_equal_first": True}
    assert r["assembly_oleans_equal_strip_run"] is True
    assert list(r["axioms"]) == prod.FINAL + prod.STRIP and all(map(prod.axioms_ok, r["axioms"].values()))
    assert r["nonexistent_module"]["exit_code"] == 1
    f = r["olean_fault"]
    assert f["control_exit"] == 0 and f["fault_exit"] == 1
    assert f["refused_at"].endswith("Prime_B_right_06_2.ev_whole._proof_1_1")
    assert f["kernel_error"] == "application type mismatch"
    b = r["stage_b"]
    assert b["conron_sample"]["exit_code"] == 0 and b["conron_centre_towers"]["exit_code"] == 0
    assert "accepted 61782 declarations (--verified)" in b["conron_sample"]["lines"][-1]
    pair = b["conron_fault_pair"]
    assert pair["clean"]["exit_code"] == 0 and pair["fault"]["exit_code"] == 1
    assert "Prime_B_right_06_2.ev_whole._proof_1_1" in pair["fault"]["lines"][-1]
    assert b["decision"].startswith("stopped at the estimate") and b["nanoda"] == "not run"
    assert b["projection"]["wall_h_16_workers"] > 24
    text = " ".join((HERE / "RESULTS.md").read_text().split())
    for q in ("7 h 17 min 46 s", "22.76 GB peak RSS", "1,569,505 constants", "761,387",
              "receipts-replay-20261027", "not an external verifier", "about 1,300 core-hours"):
        assert q in text, q
    for bad in ("independent replay accepted", "independently replayed", "independent kernel accepted"):
        assert bad not in text, bad


def test_the_box_faults_were_each_refused_where_planted():
    bf = PROD["box_faults"]
    assert bf["fault-tower-whole-outcome"]["refused_at"][0] == "Prime_B_right_06_2.ev_whole"
    assert bf["fault-tail-rad-outcome"]["refused_at"] == ["ZetaLean.DH.Cert.enc_B_right_06"]
    assert bf["fault-M-outcome"]["refused_at"] == ["ZetaLean.DH.Cert.upper_B_right_06"]
    assert bf["centre-eps-eps-at-bound"]["returncode"] == 1
    assert bf["centre-eps-eps-half"]["returncode"] == 1
    assert bf["centre-eps-eps-at-bound"]["refused_at"] == ["centre_lt_centre"]
    assert bf["centre-eps-control"]["returncode"] == 0 and bf["centre-eps-control"]["eps"] == "1/2000"
    assert bf["centre-eps-eps-above-bound"]["returncode"] == 0
    for tag in ("fault-tail-rad-outcome", "fault-M-outcome"):
        assert bf[tag]["recompiled"] == ["CB_right_06.lean"]   # only the touched module


def test_results_md_quotes_the_production_numbers():
    text = " ".join((HERE / "RESULTS.md").read_text().split())
    v, asm = PROD["verdict"], {r["tag"]: r for r in PROD["assembly_box"]["runs"]}
    zipped = sum(a["bytes"] for a in PROD["collect"]["artifacts"])
    for q in (f"{v['cpu_core_hours']} runner core-hours", f"{v['olean_bytes']:,} bytes",
              f"{zipped:,} bytes zipped", f"{asm['assembly']['cpu_s']} CPU-s",
              f"{asm['assembly']['peak_rss_bytes'] / 1e9:.2f} GB peak RSS",
              "run 40353536947", "run 40372531479", "verdict --runs 40353536947 40372531479"):
        assert q in text, q
    assert len(PROD["collect"]["artifacts"]) == 20
