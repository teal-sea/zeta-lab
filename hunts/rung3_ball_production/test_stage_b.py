"""Hunt #145, door 1, Stage B: the site-wise `con-ron` fleet's instruments.

Nothing here launches Lean, a checker or a VM. These tests pin the manifest hash (the
join of the coverage step), the census groups, the tower-time model the cost estimate
used, the planted fault's one-byte arithmetic, and the shape of the exporter.
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


man = _load("rung3_shard_manifest", HERE / "shard_manifest.py")
fleet = _load("rung3_conron_fleet", HERE / "conron_fleet.py")

HDR = {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"}}}


def _write(tmp_path: Path, name: str, records: list[dict]) -> Path:
    p = tmp_path / name
    p.write_text("\n".join(json.dumps(r) for r in [HDR, *records]) + "\n")
    return p


def _export(order: str, lit: str = "2") -> list[dict]:
    """`axiom ax : P` and `theorem t : Q := lit`-shaped records, names in either order."""
    names = [("P", 1), ("Q", 2), ("ax", 3), ("t", 4)] if order == "a" else \
            [("t", 1), ("ax", 2), ("Q", 3), ("P", 4)]
    idx = dict(names)
    recs = [{"in": i, "str": {"pre": 0, "str": s}} for s, i in names]
    recs += [{"ie": 0, "const": {"name": idx["P"], "us": []}},
             {"ie": 1, "const": {"name": idx["Q"], "us": []}},
             {"ie": 2, "natVal": lit},
             {"axiom": {"name": idx["ax"], "levelParams": [], "type": 0, "isUnsafe": False}},
             {"thm": {"name": idx["t"], "levelParams": [], "type": 1, "value": 2, "all": [idx["t"]]}}]
    return recs


def _rows(path: Path) -> dict[str, list[str]]:
    return {l.split("\t")[0]: l.split("\t")[1:] for l in path.read_text().splitlines()}


def test_manifest_hash_ignores_export_indices_and_sees_one_literal(tmp_path):
    a = man.manifest(str(_write(tmp_path, "a.ndjson", _export("a"))), str(tmp_path / "a.tsv"))
    b = man.manifest(str(_write(tmp_path, "b.ndjson", _export("b"))), str(tmp_path / "b.tsv"))
    c = man.manifest(str(_write(tmp_path, "c.ndjson", _export("a", "3"))), str(tmp_path / "c.tsv"))
    ra, rb, rc = (_rows(tmp_path / f"{x}.tsv") for x in "abc")
    assert ra == rb                                     # same declarations, other numbering
    assert ra["ax"] == rc["ax"] and ra["t"][1] != rc["t"][1]   # one literal moves one hash
    assert ra["t"][2] == rc["t"][2]                     # the type hash stays: types are matched alone
    assert a["axioms"] == ["ax"] and a["by_kind"] == {"axiom": 1, "thm": 1}
    assert a["declarations"] == b["declarations"] == c["declarations"] == 2


def test_census_groups_follow_stage_a_and_keep_cli_out_of_the_sites():
    o = fleet.origin
    assert o("CB_right_06.Primes") == o("Cg_left_16") == o("Ccentre.Terms") == "sites"
    assert o("Cli.Basic") == "deps" and o("Mathlib.Analysis.Complex.Basic") == "Mathlib"
    assert o("RHHeight100.Main100") == o("HardyZ.Core") == "hunt137"
    assert o("Rung3Assembly.Final") == "assembly" and o("Lean.Elab") == o("Init.Prelude") == "core"


def test_tower_model_passes_through_the_measured_towers():
    for p, t in ((2, 16.0), (89, 265.0), (401, 400.0), (1801, 648.0)):
        assert abs(fleet.tower_cpu_s(p) - t) < 1e-9
    ps = fleet.primes_excluding_5(23)
    assert ps[0] == 2 and 5 not in ps and ps[-1] == 89 and len(ps) == 23


def test_the_planted_fault_is_one_byte_of_one_word():
    old = (2 * 36391283805789411 + 1).to_bytes(8, "little")
    new = (2 * 36391283805789410 + 1).to_bytes(8, "little")
    assert sum(x != y for x, y in zip(old, new)) == 1


def test_the_exporter_is_a_module_and_only_picks_names():
    src = (HERE / "lean" / "ExportShard.lean").read_text()
    assert src.startswith("module\n") and "public import LeanExport.Basic" in src
    assert src.count("LeanExport.dumpEnv env") == 3       # names, site, top: the toolchain's writer
    assert "addDeclCore 0 0 d none (doCheck := true)" in src  # every glue declaration through Lean's kernel
    assert "Cli" in src and "CB_" in src                  # a site module is CB_*, Cg_* or Ccentre


def test_no_key_is_written_or_passed_on_argv():
    src = (HERE / "conron_fleet.py").read_text()
    assert "--plain" in src and "capture_output=True" in src
    assert "os.environ[\"NOVITA_API_KEY\"]" not in src and "envs=" not in src


# --------------------------------------------------------------------------- the recorded run

PILOT = json.loads((HERE / "pilot.json").read_text())
FLEET = PILOT["production"]["replay"].get("stage_b_fleet")


def test_every_site_and_the_top_shard_was_accepted_and_both_faults_refused():
    """The record of 2026-10-27: 215 site shards and the top shard accepted by
    `con-ron --verified`, each with the count its stream implies, and the planted one-byte
    fault refused on both providers at the declaration Stage A's fault named."""
    assert FLEET is not None
    shards = FLEET["shards"]
    sites = [k for k in shards if k.startswith("site:") and "#" not in k]
    assert len(sites) == 215
    for k in sites + ["top"]:
        s = shards[k]
        assert s["state"] == "done" and s["exit_code"] == 0, k
        assert s["lines"] == [f"con-ron: accepted {s['accepted']} declarations (--verified)"], k
    for k in ("fault:B_right_06", "fault:B_right_06#novita"):
        (line,) = shards[k]["lines"]
        assert shards[k]["exit_code"] == 1 and line.startswith("con-ron: rejected: application type mismatch")
        assert "Prime_B_right_06_2.ev_whole._proof_1_1" in line
    assert {v["provider"] for s in shards.values() for v in s["vms"]} == {"instabox", "novita"}


def test_the_shards_cover_the_closure_of_the_18_final_declarations():
    c = FLEET["coverage"]
    assert c["shards_accepted"] == c["shards_expected"] == 216 and not c["missing"]
    assert c["clash_count"] == 0 and not c["manifests_without_kernel_hashes"]
    g = c["glue"]
    assert g["site_theorems"] == g["matched"] == 435 and not g["mismatched"] and not g["absent"]
    assert c["abstracted"] == c["abstracted_with_glue_in_top"] == 18
    assert c["closure_size"] == 675388 and c["closure_unchecked_count"] == 0
    assert c["census_constants"] == 1569505
    rows = c["by_origin"]
    assert sum(r["constants"] for r in rows.values()) == 1569505
    assert rows["sites"]["constants"] == rows["sites"]["checked"] == 761387
    assert sum(r["in_closure"] for r in rows.values()) == 675388
    assert sum(r["closure_via_glue"] for r in rows.values()) == 18


def test_the_run_stayed_under_its_cap_and_left_no_vm():
    assert FLEET["cost_usd"]["instabox"] + FLEET["cost_usd"]["novita_list"] < 40
    assert FLEET["registry_alive"] == 0


class _Clock:
    """A fake `time` for the dead-man: sleep advances the clock, nothing waits."""

    def __init__(self, t0: float):
        self.t = t0
        self.gmtime, self.strftime = __import__("time").gmtime, __import__("time").strftime

    def time(self) -> float:
        return self.t

    def sleep(self, s: float) -> None:
        self.t += s


def _fake_providers(run: Path, clock: _Clock, late_at: float):
    """InstaBox and Novita fakes. One machine is registered when the dead-man fires; a second,
    whose create was in flight, appears in InstaBox's own listing only at `late_at`, after the
    first clean sweep. Every delete records whether RUN/STOP already existed."""
    deletes: list[tuple[str, bool]] = []
    alive = {"m-early"}

    class IB:
        def delete(self, mid):
            deletes.append((mid, (run / "STOP").exists()))
            alive.discard(mid)

        def machine(self, mid):
            return None if mid not in alive else {"id": mid}

        def list_mine(self):
            if clock.t >= late_at and "m-late" not in {d for d, _ in deletes}:
                alive.add("m-late")
            return [{"id": m, "name": m, "state": "running"} for m in sorted(alive)]

    class NV:
        def kill(self, sid):
            return True

        def list_mine(self):
            return []

    return IB, NV, deletes


def test_deadman_writes_stop_before_deleting_and_outlasts_an_in_flight_create(tmp_path, monkeypatch):
    """Review of #366 (P1): at the deadline the dead-man deleted VMs without persisting
    RUN/STOP, and Fleet.step gates launches on STOP, so the fleet could provision replacements
    after the sweep. Now STOP is written before the first delete, and the dead-man stays until
    the providers have been empty for DEADMAN_QUIET_S, so a machine whose create was in flight
    (here one appearing 10 minutes after the first clean sweep) is still deleted."""
    clock = _Clock(1_000_000.0)
    IB, NV, deletes = _fake_providers(tmp_path, clock, late_at=clock.t + 600)
    monkeypatch.setattr(fleet, "RUN", tmp_path)
    monkeypatch.setattr(fleet, "REG", tmp_path / "vms.jsonl")
    monkeypatch.setattr(fleet, "time", clock)
    monkeypatch.setattr(fleet, "InstaBox", IB)
    monkeypatch.setattr(fleet, "Novita", NV)
    monkeypatch.setattr(fleet, "log", lambda *a: None)
    fleet.registry_add({"provider": "instabox", "id": "m-early", "event": "created"})

    class A:
        deadline = clock.t - 1                  # the deadline has passed and STOP is absent

    assert not (tmp_path / "STOP").exists()
    fleet.cmd_deadman(A)
    assert (tmp_path / "STOP").exists() and "deadman deadline" in (tmp_path / "STOP").read_text()
    assert deletes and all(stop_was_there for _, stop_was_there in deletes)
    assert {"m-early", "m-late"} <= {d for d, _ in deletes}
    assert fleet.DEADMAN_QUIET_S > fleet.PROVISION_TIMEOUT_S
