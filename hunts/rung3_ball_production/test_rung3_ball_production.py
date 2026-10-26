"""Hunt #145: what pilot.json records, and that the documents quote it.

Nothing here launches Lean.  These tests pin (1) the Lean environment and that no
production shard was launched, (2) the kernel outcomes the pilot recorded, (3) that every
derived rate in pilot.json follows from its own raw samples, (4) the structural counts
against scripts/67 and the plan numbers the prose quotes, and (5) that the tables in
PILOT.md and OWNER_MEMO.md are the ones report.py renders from pilot.json, so a number in
a document cannot drift from the measurement behind it.
"""
from __future__ import annotations

import importlib.util
import json
import statistics as st
from fractions import Fraction as F
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PILOT = json.loads((HERE / "pilot.json").read_text())


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


report = _load("rung3_ball_production_report", HERE / "report.py")


# --------------------------------------------------------------------------- environment

def test_the_lean_environment_is_the_pinned_one_fetched_fresh():
    s = PILOT["setup"]
    assert s["lean_toolchain"] == "leanprover/lean4:v4.35.0-rc2"
    assert "version 4.35.0-rc2" in s["lean_version"]
    assert s["all_packages_own_toplevel"] and s["all_heads_match_manifest"]
    mathlib = next(p for p in s["packages"] if p["name"] == "mathlib")
    assert mathlib["manifest_rev"].startswith("065356127b1d")
    assert {"Ball", "BallTerm", "BallCertSupport", "DHCertSupport", "DHAssembly",
            "DHTailBound2"} <= set(s["zetalean_built"])
    assert len(s["zetalean_built"]) == 15 and len(s["packages"]) == 9
    assert s["box"]["vcpus"] == 32


def test_no_production_shard_was_launched():
    """Across both attempts scripts/72 compiled the pilot site and nothing else, and no
    checkpoint exists for any other root; the centre was generated, never compiled."""
    a = PILOT["launch_audit"]
    assert a["scripts72_manifests"] == ["CB_right_06.manifest.json"]
    assert a["checkpoint_roots"] == ["CB_right_06"]
    assert not any(f.startswith("Ccentre") or f.startswith("CB_") or f.startswith("Cg_")
                   for f in a["direct_lean_files"])


# --------------------------------------------------------------------------- kernel outcomes

def test_the_generator_replayed_byte_for_byte():
    g = PILOT["generator_replay"]
    assert g["identical"] and len(g["this_run"]) == 10
    assert all(g["this_run"][m["path"]] == m["sha256"] for m in PILOT["site"]["modules"])


def test_the_pilot_site_compiled_every_module():
    site = PILOT["site"]
    assert site["site"] == "B_right_06" and site["K"] == 17
    assert site["status"] == "ok"
    assert site["compile"]["returncode"] == 0
    assert [m["status"] for m in site["modules"]] == ["ok"] * 10
    assert site["modules"][-1]["path"] == "CB_right_06.lean"


def test_the_site_theorems_use_only_the_standard_axioms():
    ax = PILOT["axioms"]
    assert ax["returncode"] == 0
    assert "upper_B_right_06" in ax["probe"] and "enc_B_right_06" in ax["probe"]
    assert ax["axioms"] == ["Classical.choice", "Quot.sound", "propext"]
    assert "sorryAx" not in ax["output"]
    assert ax["output"].count("depends on axioms") == 2


def test_every_planted_fault_in_the_site_was_refused():
    faults = {f["fault"]["expected_failure"]: f for f in PILOT["faults"]}
    assert len(faults) == 3
    for expected, f in faults.items():
        assert f["driver_returncode"] != 0, expected
        assert f["site_status"] == "failed", expected
        assert len(f["failed_modules"]) == 1, expected
        assert f["recompiled"] == f["failed_modules"], expected
        assert f["errors"], expected
        assert any(d.endswith(expected) for d in f["error_declarations"]), expected


def test_the_radius_faults_sit_just_inside_the_line():
    by = {f["fault"]["expected_failure"].split(".")[-1]: f["fault"] for f in PILOT["faults"]}
    tower = by["ev_mul_29"]
    assert F(tower["old_rad"]) - F(tower["new_rad"]) == F(1, F(tower["old_rad"]).denominator)
    tail = by["enc_B_right_06"]
    assert F(tail["new_r"]) < F(tail["tail_bound"]) <= F(tail["old_r"])
    assert F(tail["tail_bound"]) - F(tail["new_r"]) < F(1, 2**39)
    assert tail["occurrences_replaced"] == 3
    big = by["upper_B_right_06"]
    assert F(big["new_M"]) < F(big["u_plus_rad"]) < F(big["old_M"])


def test_the_centre_eps_probe_accepts_eps_and_refuses_below_the_bound():
    runs = {r["tag"]: r for r in PILOT["centre_eps"]}
    assert len(runs) == 4
    assert runs["centre-eps-control"]["returncode"] == 0
    assert F(runs["centre-eps-control"]["eps"]) == F(1, 2000)
    above = runs["centre-eps-eps-above-bound"]
    assert above["returncode"] == 0
    assert F(above["u_plus_rad"]) < F(above["eps"]) <= F(above["u_plus_rad"]) + F(1, 2**64)
    for tag in ("centre-eps-eps-at-bound", "centre-eps-eps-half"):
        assert runs[tag]["returncode"] != 0, tag
    at = runs["centre-eps-eps-at-bound"]
    assert F(at["eps"]) == F(at["u_plus_rad"]) < F(1, 2000)
    assert F(runs["centre-eps-eps-half"]["eps"]) == F(1, 4000) < F(at["u_plus_rad"])
    # each refusal is an error inside the probe's theorem, not an import or parse problem
    for tag in ("centre-eps-eps-at-bound", "centre-eps-eps-half"):
        errs = runs[tag]["log_errors"]
        assert errs and all("CentreEps_" in e for e in errs), tag
        assert not any("unknown" in e.lower() for e in errs), tag
    for tag in ("centre-eps-control", "centre-eps-eps-above-bound"):
        assert runs[tag]["log_errors"] == [], tag


def test_mirror_and_kernel_literals_agree_once_one_is_exact():
    m = PILOT["mirror"]
    assert m["centre_agrees"] and m["seeded_one_agrees_bit_for_bit"]
    assert m["copy_of_scripts65_reproduces_it"]
    extra = F(m["scripts65_extra_radius"])
    assert extra == F(m["scripts63_cpowBox_1"][2]) > 0
    assert F(m["scripts65_normBound"]) - F(m["manifest_normBound"]) == extra
    assert F(m["manifest_normBound"]) < F(m["M"])
    stored = json.loads((ROOT / "lean" / "cert" / "rung3_ball_validation.json").read_text())
    row = next(r for r in stored["sites"] if r["id"] == "B_right_06")
    assert row["normBound"] == m["scripts65_normBound_float"]


# --------------------------------------------------------------------------- arithmetic

def test_tower_rates_follow_from_their_samples():
    for key, u in PILOT["tower"].items():
        if not u.get("net_cpu_s"):
            continue
        assert u["net_cpu_s"] == [round(c - u["baseline_cpu_s"], 3) for c in u["cpu_s"]], key
        assert u["cpu_s_per_atom"] == round(st.mean(u["net_cpu_s"]) / 30, 4), key
    assert PILOT["v433_record"]["tower_cpu_s_per_atom"] == 1.2504


def test_composite_rate_follows_from_its_samples():
    by = PILOT["composite_by_atoms"]
    assert set(by) == {"10", "100"}
    c = PILOT["composite"]
    assert c is not None and c["atoms_per_run"] == 100 and c == by["100"]
    for n, u in by.items():
        assert u["runs"] == 3, n
        assert u["cpu_s_per_atom"] == round(st.mean(u["net_cpu_s"]) / int(n), 4), n


def test_in_situ_rates_follow_from_the_module_records():
    site = PILOT["site"]
    ins = site["in_situ"]
    shards = [m for m in site["modules"] if m["kind"] == "primes-shard"]
    assert sum(m["towers"] for m in shards) == ins["towers"] == 23
    net = sum(m["cpu_s"] - m["import_probe_cpu_s"] for m in shards)
    assert abs(net - ins["tower_net_cpu_s"]) < 0.01
    assert ins["cpu_s_per_tower_atom"] == round(ins["tower_net_cpu_s"] / (23 * 30), 4)
    assert ins["composites"] == 48 and ins["nonzero_terms"] == 68 and ins["N"] == 85


def test_the_p1801_tower_costs_about_what_the_p2_tower_costs():
    """PILOT.md section 4: close to the same CPU per atom with about three times the text."""
    t2, t1801 = PILOT["tower"]["2"], PILOT["tower"]["1801"]
    assert t1801["runs"] == 2 and t2["runs"] == 3
    assert 2.9 <= t1801["file_bytes"] / t2["file_bytes"] <= 3.3
    assert 0.8 <= t1801["cpu_s_per_atom"] / t2["cpu_s_per_atom"] <= 1.3


def test_threads_change_wall_time_not_cpu():
    """PILOT.md section 3: -j1 lands slightly below the default-thread shard CPU, and the
    -j1 tower inside the default-thread tower's spread."""
    j = PILOT["shard_j1"]
    assert j["module"] == "CB_right_06/Primes02.lean" and j["runs"] == 1
    assert 0.9 < j["net_cpu_s"] / j["default_threads_net_cpu_s"] < 1.0
    lo, hi = PILOT["tower"]["2"]["cpu_s_per_atom_range"]
    assert lo <= PILOT["tower"]["tower-j1"]["cpu_s_per_atom"] <= hi
    assert j["wall_s"][0] > j["cpu_s"][0]          # one thread, stretched by the load


def test_neither_lever_moves_the_tower_outside_its_spread():
    """OWNER_MEMO.md item 3: -j1 and linters off both land inside the default spread."""
    lo, hi = PILOT["tower"]["2"]["cpu_s_per_atom_range"]
    for tag in ("tower-j1", "tower-Dlinter.all=false"):
        u = PILOT["tower"][tag]
        assert u["runs"] == 3, tag
        assert lo <= u["cpu_s_per_atom"] <= hi, (tag, u["cpu_s_per_atom"], lo, hi)


def test_almost_all_warnings_are_the_seq_focus_linter():
    site = PILOT["site"]
    assert site["log_warnings_total"] > 0
    assert site["log_warnings_seq_focus_total"] >= 0.9 * site["log_warnings_total"]


def test_the_numbers_runs_md_quotes():
    site = PILOT["site"]
    box = site["compile"]["box"]
    assert (round(box["load1_min"]), round(box["load1_max"]), round(box["load1_mean"])) == \
        (62, 121, 90)
    assert round(site["compile"]["load_at_start"][0]) == 63
    shards = [m for m in site["modules"] if m["kind"] == "primes-shard"]
    assert [m["towers"] for m in shards] == [7, 5, 5, 5, 1]
    per_tower = [m["net_cpu_s"] / m["towers"] for m in shards]
    assert all(69 <= x < 76 for x in per_tower), per_tower
    per_byte = [m["net_cpu_s"] / m["bytes"] for m in shards]
    assert per_byte[0] / per_byte[3] > 1.4      # the per-byte rate falls as p grows
    big = PILOT["tower_bytes_by_prime"]["big"]
    assert 2.0 <= big["89"] / big["2"] <= 2.5    # "their text roughly doubled" (PILOT.md)


def test_the_site_counts_match_scripts67():
    budget = _load("rung3_ball_atom_budget_for_test",
                   ROOT / "scripts" / "67_rung3_ball_atom_budget.py")
    prime = budget._sieve(200)
    assert budget.site_atoms(17, prime) == (774, 23, 48)
    counts = budget.plan_atom_counts()
    assert counts["atoms"] == 549_149 and counts["sites"] == 215
    assert counts["primes"] == 15_608
    assert counts["by_kind"]["grid"]["atoms"] == 341_718
    assert counts["by_kind"]["centre"] == {"sites": 1, "atoms": 10_233, "primes": 278,
                                           "composites": 1_169}
    a = PILOT["atom_only"]
    assert (a["tower_atoms"], a["other_atoms"]) == (468_240, 80_909)


def test_the_plan_numbers_the_documents_quote():
    plan = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())
    assert len(plan["big"]["boxes"]) == 110 and len(plan["grid"]) == 104
    assert plan["centre"]["K"] == 361 == max(
        [b["K"] for b in plan["big"]["boxes"]] + [g["K"] for g in plan["grid"]]
        + [plan["centre"]["K"]])
    assert F(plan["small"]["eps"]) == F(1, 2000) and F(plan["M"]) == F(25499, 10000)
    assert F(plan["small"]["w"]) == F(3, 64) and F(plan["big"]["w2"]) == F(7, 32)
    assert F(plan["L"]) == 16
    ks = sorted((b["K"], b["id"]) for b in plan["big"]["boxes"])
    assert [i for k, i in ks if k == ks[0][0]] == ["B_bottom_23", "B_right_06", "B_top_22"]
    assert ks[0][0] == 17 and ks[-1][0] == 61
    assert (min(g["K"] for g in plan["grid"]), max(g["K"] for g in plan["grid"])) == (85, 114)


def test_the_projection_adds_up():
    p = PILOT["projection"]
    assert abs(sum(p["core_hours"].values()) - p["total_core_hours"]) < 0.2
    assert len(p["sites"]) == 215
    assert abs(sum(s["cpu_s"] for s in p["sites"]) / 3600 - p["total_core_hours"]) < 0.2
    for n, w in p["wall_clock"].items():
        assert abs(w["wall_h_one_core_each"] - p["total_core_hours"] / min(32, int(n))) < 0.01
    models = PILOT["projection_models"]
    assert p["model"] in ("in_situ_per_byte", "in_situ_per_tower")
    assert p["total_core_hours"] == max(models["in_situ_per_byte"]["total_core_hours"],
                                        models["in_situ_per_tower"]["total_core_hours"])
    assert {k: v for k, v in p.items() if k not in ("sites", "model")} == models[p["model"]]


# --------------------------------------------------------------------------- documents

@pytest.mark.parametrize("doc", ["PILOT.md", "OWNER_MEMO.md"])
def test_documents_carry_the_tables_report_renders(doc):
    text = (HERE / doc).read_text()
    blocks = report.markdown_tables(PILOT)
    used = [name for name in blocks if f"<!-- table:{name} -->" in text]
    assert used, f"{doc} quotes no rendered table"
    for name in used:
        start = text.index(f"<!-- table:{name} -->") + len(f"<!-- table:{name} -->")
        stop = text.index(f"<!-- /table:{name} -->")
        assert text[start:stop].strip() == blocks[name].strip(), (doc, name)


def _case_log_entry() -> str:
    text = (ROOT / "hunts" / "README.md").read_text()
    start = text.index("### Hunt #145:")
    return text[start:text.index("\n### Hunt #", start + 1)]


def test_the_case_log_entry_quotes_pilot_json():
    entry = " ".join(_case_log_entry().split())
    p = PILOT
    ins = p["site"]["in_situ"]
    models = p["projection_models"]
    lo, hi = sorted(models[k]["total_core_hours"]
                    for k in ("in_situ_per_byte", "in_situ_per_tower"))
    pr = p["projection"]
    box = p["setup"]["box"]
    ratio = p["import_model"]["rss_bytes_per_imported_olean_byte"]
    w = pr["wall_clock"]
    quoted = [
        f"{p['tower']['2']['cpu_s_per_atom']:.2f} CPU-s per tower atom",
        f"{ins['cpu_s_per_tower_atom']:.2f} in the site's five prime shards",
        f"{ins['cpu_s_per_composite']:.3f} per composite",
        f"{lo:,.0f} to {hi:,.0f} core-hours",
        f"{w['24']['wall_h_measured_cores_per_process']:,.0f} hours of wall clock at 24",
        f"{w['16']['wall_h_one_core_each']:,.0f} hours at 16 processes",
        f"{pr['olean_gb_est_per_tower']:,.0f} to {pr['olean_gb_est']:,.0f} GB of oleans",
        f"{box['disk_free_gb']:,.0f} GB free",
        f"{ratio:.2f} bytes of RSS per olean byte",
        f"{ratio * pr['olean_gb_est_per_tower']:,.0f} to {ratio * pr['olean_gb_est']:,.0f} GB",
        f"peak RSS {p['site']['max_peak_rss_gib']:.1f} GiB",
        f"at most {p['site']['max_rss_anon_gib']:.1f} GiB",
        f"{p['import_model']['base_cpu_s']:.0f} CPU-s to import",
    ]
    missing = [q for q in quoted if q not in entry]
    assert not missing, missing
    assert "#145" in entry and "rung3_ball_production/" in entry


@pytest.mark.parametrize("doc", ["PILOT.md", "OWNER_MEMO.md", "RUNS.md", "MISSION.md"])
def test_documents_carry_no_em_dash(doc):
    # The reserved-word scan for every file under hunts/ is
    # tests/test_hunt_probe_discipline.py; it is not repeated here.
    assert "\u2014" not in (HERE / doc).read_text(), f"{doc} has an em dash"
