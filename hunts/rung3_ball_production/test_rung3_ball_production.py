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


@pytest.mark.parametrize("doc", ["PILOT.md", "OWNER_MEMO.md", "RUNS.md", "MISSION.md",
                                 "PRODUCTION.md"])
def test_documents_carry_no_em_dash(doc):
    # The reserved-word scan for every file under hunts/ is
    # tests/test_hunt_probe_discipline.py; it is not repeated here.
    assert "\u2014" not in (HERE / doc).read_text(), f"{doc} has an em dash"


# --------------------------------------------------------------------------- 2026-10-26: decide +kernel

DK = PILOT["decide_kernel"]


def test_decide_net_cpu_follows_from_its_samples():
    base = st.median(DK["baseline_cpu_s"])
    assert DK["baseline_cpu_s_median"] == pytest.approx(base)
    for name in ("TowerNormNum", "TowerNormNumEq", "TowerDecide", "TowerDecideEq",
                 "WholeDecide", "TowerWhole_p2", "TowerWhole_p1801_box",
                 "Composite_decide", "Kappa_decide"):
        r = DK[name]
        assert set(r["returncodes"]) == {0}, name
        assert r["net_cpu_s_median"] == pytest.approx(st.median(r["cpu_s"]) - base, abs=0.01)


def test_decide_planted_faults_were_refused_where_planted():
    assert DK["fault"]["returncode"] == 1 and DK["fault"]["refused_decls"] == ["ev_mul_29"]
    assert DK["whole_fault"]["returncode"] == 1 and DK["whole_fault"]["refused_decls"] == ["ev_p2"]
    assert DK["whole"]["returncode"] == 0 and not DK["whole"]["timed_out"]
    assert DK["whole"]["eval_stdout"] == "true"
    for line in DK["axioms_printed"]:
        assert line.endswith("depends on axioms: [propext, Classical.choice, Quot.sound]")


def test_decide_verdict_against_the_threshold_recorded_in_advance():
    v = DK["verdict"]
    assert DK["threshold_full_tower_cpu_s"] == 10.0
    assert "**at most 10 CPU-s** confirms the repricing" in (HERE / "RUNS.md").read_text()
    assert v["staged_decide_full_tower_net_cpu_s"] == DK["TowerDecide"]["net_cpu_s_median"]
    assert not v["staged_meets_threshold"] and v["whole_meets_threshold"]
    assert v["whole_decision_full_tower_net_cpu_s"] == [
        DK["TowerWhole_p2"]["net_cpu_s_median"], DK["TowerWhole_p1801_box"]["net_cpu_s_median"]]


def test_decide_reprice_adds_up():
    r = DK["reprice"]
    assert r["towers"] == PILOT["atom_only"]["tower_atoms"] // 30 == 15608
    lo, hi = sorted(DK["verdict"]["whole_decision_full_tower_net_cpu_s"])
    assert r["tower_core_hours"] == [round(r["towers"] * lo / 3600, 1),
                                     round(r["towers"] * hi / 3600, 1)]
    rest = sum(v for k, v in PILOT["projection"]["core_hours"].items() if k != "tower")
    assert r["other_core_hours_unchanged"] == pytest.approx(rest, abs=0.01)
    assert 20 <= r["total_core_hours"][0] <= r["total_core_hours"][1] <= 90


def test_pilot_md_quotes_the_decide_numbers():
    text = " ".join((HERE / "PILOT.md").read_text().split())
    for name in ("TowerNormNum", "TowerNormNumEq", "TowerDecide", "TowerDecideEq",
                 "WholeDecide", "TowerWhole_p2", "TowerWhole_p1801_box"):
        assert f"| {DK[name]['net_cpu_s_median']:.1f} |" in text, name
    lo, hi = DK["reprice"]["total_core_hours"]
    assert f"**{lo:.0f} to {hi:.0f} core-hours**" in text
    assert f"{DK['reprice']['towers']:,} prime towers" in text


def test_no_file_in_this_hunt_carries_the_reserved_word():
    """The lexical rule covers every file type here, `.lean` included (the discipline
    test scans only `.py`, `.md` and `.json`)."""
    word = "certi" + "fied"
    hits = [str(p.relative_to(HERE)) for p in HERE.rglob("*")
            if p.is_file() and "__pycache__" not in p.parts and ".lake" not in p.parts
            and word in p.read_text(errors="ignore").lower()]
    assert not hits, hits


# --------------------------------------------------------------------------- the assembly emitter

assembly = _load("rung3_ball_production_assembly", HERE / "assembly.py")
PLAN2 = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())
SUPPORT = HERE / "lean" / "Rung3Assembly" / "Support.lean"
EMITTED = assembly.emitted(PLAN2)


def test_assembly_is_byte_stable_and_pinned():
    """The emitted modules are not committed (they cannot be `module` files: see
    assembly.py); pilot.json pins their SHA-256, the text the harness elaborated."""
    assert assembly.emitted(PLAN2) == EMITTED
    assert PILOT["assembly_emitted"] == assembly.pins(PLAN2)
    assert not (HERE / "lean" / "Rung3Assembly" / "Assembly.lean").exists()


def test_the_committed_lean_is_a_module():
    assert SUPPORT.read_text().startswith("module\n")


def test_assembly_imports_every_site_root_exactly_once():
    text = EMITTED["Assembly.lean"]
    imports = [l.split()[1] for l in text.splitlines() if l.startswith("import ")]
    roots = [m for m in imports if m != "Rung3Assembly.Support"]
    ids = [sid for sid, _ in assembly.sites(PLAN2)]
    assert len(ids) == len(set(ids)) == 215
    assert sorted(roots) == sorted(f"C{sid}" for sid in ids) and len(roots) == len(set(roots))


def test_assembly_uses_each_site_theorem_where_the_plan_puts_it():
    """Each big box bounds exactly one boundary piece; each grid point closes the cells on
    either side of it (one at a corner of its edge, two inside); the centre is used once."""
    import re
    text = EMITTED["Assembly.lean"]
    for b in PLAN2["big"]["boxes"]:
        assert len(re.findall(rf"\bupper_{b['id']}\b", text)) == 1, b["id"]
    for seg in ("bottom", "top", "left", "right"):
        pts = [g for g in PLAN2["grid"] if g["segment"] == seg]
        for i, g in enumerate(pts):
            want = 1 if i in (0, len(pts) - 1) else 2
            assert len(re.findall(rf"\bbeta_{g['id']}\b", text)) == want, g["id"]
    assert len(re.findall(r"\bcentre_lt_centre\b", text)) == 1
    assert "theorem davenport_heilbronn : davenport_heilbronn_statement :=" in text
    assert "sorry" not in text and "axiom" not in text
    assert "sorry" not in SUPPORT.read_text()


def test_the_stub_harness_rests_on_the_stubs_and_two_real_sites():
    """The emitted body elaborated against 213 stub interfaces and the oleans of two real
    whole-mode sites, imported together: only the three standard axioms and the 213 stubs
    appear, never the real sites' theorems."""
    h = PILOT["assembly_harness"]
    real = ["B_right_06", "B_bottom_23"]
    assert h["returncode"] == 0 and h["errors"] == 0 and h["real_sites"] == real
    std = ["Classical.choice", "Quot.sound", "propext"]
    stubs = sorted([f"beta_{g['id']}" for g in PLAN2["grid"]] + ["centre_lt_centre"]
                   + [f"upper_{b['id']}" for b in PLAN2["big"]["boxes"] if b["id"] not in real])
    for name in ("davenport_heilbronn", "dh_zero_located'", "dh_separation_of"):
        assert h["axioms"][name] == sorted(std + stubs), name
    assert len(stubs) == 213


def test_production_runbook_quotes_both_prices():
    text = " ".join((HERE / "PRODUCTION.md").read_text().split())
    wp = PILOT["whole_projection"]
    assert f"**{PILOT['projection']['total_core_hours']:.0f} core-hours**" in text
    assert f"**{wp['total_core_hours']:.0f} core-hours** ({wp['total_core_hours']})" in text
    lo, hi = wp["olean_gb"]
    assert f"{lo:.1f} to {hi:.1f} GB of oleans" in text
    assert "nothing here has been launched" in text


# --------------------------------------------------------------------------- the whole-tower mode

WS = PILOT["whole_site"]          # with site-qualified tower namespaces (the current generator)
WS1 = PILOT["whole_site_v1"]      # the first whole-mode run, Prime_<p>; PILOT.md section 9
gen60 = _load("rung3_generate_for_hunt", ROOT / "scripts" / "60_rung3_generate.py")


def _pilot_site():
    site = dict(next(b for b in PLAN2["big"]["boxes"] if b["id"] == "B_right_06"))
    site["M"] = PLAN2["M"]
    return site


def test_default_emission_is_byte_identical_to_the_2026_10_21_sources():
    """The generator change leaves the default (staged) output alone: the pilot site's
    sources hash as they did when the 2026-10-21 pilot compiled them."""
    import hashlib
    files, _ = gen60.emit_site_modules(_pilot_site(), "big")
    got = {rel: hashlib.sha256(text.encode()).hexdigest() for rel, text in files}
    assert got == PILOT["generator_replay"]["this_run"]


def test_whole_site_sources_are_the_generator_output():
    import hashlib
    files, _ = gen60.emit_site_modules(_pilot_site(), "big", tower="whole")
    got = {rel: hashlib.sha256(text.encode()).hexdigest() for rel, text in files}
    assert got == WS["sources"] and WS["module_count"] == len(files) == 5


def test_whole_site_compiled_and_its_totals_add_up():
    assert WS["status"] == "ok" and all(m["status"] == "ok" for m in WS["modules"])
    assert WS["cpu_s_total"] == pytest.approx(sum(m["cpu_s"] for m in WS["modules"]), abs=0.1)
    assert WS["olean_bytes_total"] == sum(m["olean_bytes"] for m in WS["modules"])
    assert WS["max_peak_rss_bytes"] == max(m["peak_rss_bytes"] for m in WS["modules"])
    old = WS["staged_2026_10_21"]
    assert old["cpu_s_total"] == PILOT["site"]["modules_cpu_s"]
    assert WS["cpu_s_total"] < old["cpu_s_total"] / 10
    assert WS["olean_bytes_total"] < old["olean_bytes_total"] / 10


def test_whole_mode_faults_are_refused_at_the_faulted_tower():
    f = WS["faults"]
    assert f["p2-rad-low"]["returncode"] == 1
    assert "Prime_B_right_06_2.ev_whole" in f["p2-rad-low"]["refused"]
    assert f["p89-cre-high"]["returncode"] == 1
    assert "Prime_B_right_06_89.ev_whole" in f["p89-cre-high"]["refused"]
    for tag, v in WS1["faults"].items():          # the first run, before the rename
        assert v["returncode"] == 1 and any(r.endswith(".ev_whole") for r in v["refused"])
    for tag in f:
        assert all(r.startswith(("Prime_", "ZetaLean.DH.Cert.hp_")) for r in f[tag]["refused"])


def test_whole_site_import_ratio_follows_from_its_probes():
    ip = WS["import_probe"]
    ratio = (ip["root_peak_rss_bytes"] - ip["base_peak_rss_bytes"]) / WS["olean_bytes_total"]
    assert ip["rss_bytes_per_imported_olean_byte"] == pytest.approx(ratio, abs=0.001)


WP = PILOT["whole_projection"]


def test_whole_projection_covers_the_plan_and_adds_up():
    ids = [sid for sid, _ in assembly.sites(PLAN2)]
    assert sorted(r["id"] for r in WP["rows"]) == sorted(ids) and WP["sites"] == 215
    assert WP["towers"] == PILOT["decide_kernel"]["reprice"]["towers"] == 15608
    assert WP["modules"] == sum(r["modules"] for r in WP["rows"])
    assert WP["total_core_hours"] == pytest.approx(
        sum(r["cpu_s"] for r in WP["rows"]) / 3600, abs=0.05)
    lo, hi = WP["olean_gb"]
    assert lo == pytest.approx(min(sum(r["olean_bytes"] for r in WP["rows"]),
                                   sum(r["olean_bytes_by_source"] for r in WP["rows"])) / 1e9,
                               abs=0.01)
    ratio = WS1["import_probe"]["rss_bytes_per_imported_olean_byte"]
    assert WP["assembly_import_rss_gb"] == [round(ratio * lo, 2), round(ratio * hi, 2)]


def test_whole_projection_model_reproduces_the_pilot_site():
    row = next(r for r in WP["rows"] if r["id"] == "B_right_06")
    assert row["cpu_s"] == pytest.approx(WS1["cpu_s_total"], rel=0.02)
    assert row["olean_bytes"] == pytest.approx(WS1["olean_bytes_total"], rel=0.001)


def test_pilot_md_quotes_the_whole_mode_numbers():
    text = " ".join((HERE / "PILOT.md").read_text().split())
    lo, hi = WP["olean_gb"]
    a, b = WP["assembly_import_rss_gb"]
    for quoted in (f"**{WS1['cpu_s_total']:.1f}**", f"**{WS1['olean_bytes_total']:,}**",
                   f"**{WP['total_core_hours']:.1f} core-hours**",
                   f"**{lo:.1f} to {hi:.1f} GB**", f"**{a:.1f} to {b:.1f} GB**",
                   f"{WS1['import_probe']['rss_bytes_per_imported_olean_byte']:.2f} bytes of RSS",
                   f"{WP['largest_site']['cpu_s']:,.0f} CPU-s",
                   "(a) This box: not as it is run today", "(b) GitHub Actions shards"):
        assert quoted in text, quoted


def test_the_centre_import_probe_ratio():
    c = PILOT["import_probe_centre"]
    assert c["olean_bytes"] == PILOT["calibration_runner_v1"]["sites"]["centre"]["olean_bytes"]
    ratio = (c["root_peak_rss_bytes"] - c["base_peak_rss_bytes"]) / c["olean_bytes"]
    assert c["rss_bytes_per_imported_olean_byte"] == pytest.approx(ratio, abs=0.001)
