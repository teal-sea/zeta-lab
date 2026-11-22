"""The export route: what is read off an export file, and a self-test that can fail.

The two programs it drives, lean4export and nanoda, are built on runners only.
Here they are stubs: a `lean4export` that writes a small file in the export
format for each toy declaration, and a `nanoda` that rejects a marked proof
and an axiom its configuration does not permit. What is tested is this
repository's side: the reading of the format, the configuration, and that the
self-test passes a checker only if it tells the three toy theorems apart.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import export_check as ec  # noqa: E402


def _lines(*objs) -> str:
    return "".join(json.dumps(o) + "\n" for o in objs)


META = {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                 "lean": {"githash": "abc", "version": "4.33.1"}, "format": {"version": "3.1.0"}}}


def test_an_export_is_read_by_kind_and_its_axioms_named(tmp_path: Path) -> None:
    f = tmp_path / "e.ndjson"
    f.write_text(_lines(
        META,
        {"str": {"pre": 0, "str": "Classical"}, "in": 1},
        {"str": {"pre": 1, "str": "choice"}, "in": 2},
        {"str": {"pre": 0, "str": "sorryAx"}, "in": 3},
        {"str": {"pre": 0, "str": "M"}, "in": 4},
        {"str": {"pre": 4, "str": "thm"}, "in": 5},
        {"num": {"pre": 5, "i": 1}, "in": 6},
        {"str": {"pre": 4, "str": "T"}, "in": 7},
        {"str": {"pre": 7, "str": "mk"}, "in": 8},
        {"str": {"pre": 7, "str": "rec"}, "in": 9},
        {"str": {"pre": 4, "str": "f"}, "in": 10},
        {"sort": 0, "ie": 0},
        {"axiom": {"name": 2, "levelParams": [], "type": 0, "isUnsafe": False}},
        {"axiom": {"name": 3, "levelParams": [], "type": 0, "isUnsafe": False}},
        {"inductive": {"types": [{"name": 7, "isUnsafe": False}], "ctors": [{"name": 8, "isUnsafe": False}],
                       "recs": [{"name": 9, "isUnsafe": False}]}},
        {"def": {"name": 10, "levelParams": [], "type": 0, "value": 0, "hints": "abbrev", "safety": "partial", "all": [10]}},
        {"thm": {"name": 5, "levelParams": [], "type": 0, "value": 0, "all": [5]}},
        {"thm": {"name": 6, "levelParams": [], "type": 0, "value": 0, "all": [6]}},
    ), encoding="utf-8")
    consts = tmp_path / "consts.jsonl"
    consts.write_text(_lines(
        {"name": ["M", "thm"], "kind": "theorem", "unsafe": False, "partial": False},
        {"name": ["M", "thm", 1], "kind": "theorem", "unsafe": False, "partial": False},
        {"name": ["M", "thm", "1"], "kind": "theorem", "unsafe": False, "partial": False},   # a string, not the number
        {"name": ["M", "impl"], "kind": "def", "unsafe": True, "partial": False},
        {"name": ["M", "other"], "kind": "theorem", "unsafe": False, "partial": False},
    ), encoding="utf-8")
    s = ec.summarise(str(f), str(consts))
    assert s["meta"]["format"] == {"version": "3.1.0"} and s["lines"] == 18
    assert s["kinds"] == {"axiom": 2, "constructor": 1, "def": 1, "inductive": 1, "recursor": 1, "thm": 2}
    assert s["n_declared"] == 8
    assert s["axioms"] == ["Classical.choice", "sorryAx"] and s["axioms_not_permitted"] == ["sorryAx"]
    assert s["unsafe_or_partial"] == ["M.f"]
    # the module: two of its constants are in the export, one is unsafe and
    # so not for a checker of proofs, and two are not there at all
    assert s["module"] == {"constants": 5, "unsafe_or_partial": ["M.impl"],
                           "missing_from_export": ["M.thm.1", "M.other"]}
    assert "declared" not in s and "module" not in ec.summarise(str(f))


def test_the_configuration_permits_the_three_axioms_and_no_other(tmp_path: Path) -> None:
    cfg = ec.nanoda_config(str(tmp_path / "e.ndjson"), threads=3)
    assert cfg["permitted_axioms"] == ["propext", "Classical.choice", "Quot.sound"]
    assert cfg["unpermitted_axiom_hard_error"] is True and cfg["num_threads"] == 3
    assert cfg["export_file_path"] == str(tmp_path / "e.ndjson") and cfg["use_stdin"] is False


STUB_LAKE = '#!/bin/sh\nif [ "$1" = build ]; then exit 0; fi\nshift\nexec "$@"\n'

#: writes an export for `<module> -- <decl>`: `worse` carries a marked proof, `lazy` the axiom sorryAx
STUB_EXPORT = r'''#!/usr/bin/env python3
import json, sys
decl = sys.argv[sys.argv.index("--") + 1]
out = [{"meta": {"format": {"version": "3.1.0"}}},
       {"str": {"pre": 0, "str": "propext"}, "in": 1},
       {"str": {"pre": 0, "str": "sorryAx"}, "in": 2},
       {"str": {"pre": 0, "str": decl}, "in": 3},
       {"axiom": {"name": 1, "levelParams": [], "type": 0, "isUnsafe": False}}]
if decl == "lazy":
    out.append({"axiom": {"name": 2, "levelParams": [], "type": 0, "isUnsafe": False}})
thm = {"name": 3, "levelParams": [], "type": 0, "value": 0, "all": [3]}
if decl == "worse":
    thm["stub_wrong_proof"] = True
out.append({"thm": thm})
sys.stdout.write("".join(json.dumps(o) + "\n" for o in out))
'''

#: a checker: exit 1 on the marked proof or on an axiom the configuration does not permit
STUB_NANODA = r'''#!/usr/bin/env python3
import json, sys
cfg = json.load(open(sys.argv[1]))
names = {0: ""}
for line in open(cfg["export_file_path"]):
    o = json.loads(line)
    if "str" in o:
        names[o["in"]] = o["str"]["str"]
    if "thm" in o and o["thm"].get("stub_wrong_proof") and MODE != "accepts":
        print("declaration type mismatch"); sys.exit(1)
    if "axiom" in o and names[o["axiom"]["name"]] not in cfg["permitted_axioms"] and MODE != "accepts":
        print("axiom not permitted"); sys.exit(1)
if MODE == "rejects":
    print("no"); sys.exit(1)
print("checked"); sys.exit(0)
'''


def _stubs(tmp_path: Path, monkeypatch, mode: str) -> tuple[str, str]:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir(parents=True)
    for name, text in (("lake", STUB_LAKE), ("lean4export", STUB_EXPORT),
                       ("nanoda", STUB_NANODA.replace("MODE", repr(mode)))):
        (bin_dir / name).write_text(text)
        (bin_dir / name).chmod(0o755)
    monkeypatch.setenv("PATH", f"{bin_dir}{os.pathsep}{os.environ['PATH']}")
    return str(bin_dir / "lean4export"), str(bin_dir / "nanoda")


def test_the_selftest_passes_a_checker_that_tells_the_three_apart(tmp_path: Path, monkeypatch) -> None:
    l4e, nanoda = _stubs(tmp_path, monkeypatch, "checks")
    got = ec.selftest(l4e, nanoda, "leanprover/lean4:v4.33.1", str(tmp_path / "w"))
    assert got["passed"] is True and got["build_rc"] == 0
    assert {d: c["accepted"] for d, c in got["cases"].items()} == {"honest": True, "worse": False, "lazy": False}
    assert got["cases"]["lazy"]["axioms"] == ["propext", "sorryAx"]
    # the toy on disk has the theorem that rests on sorry beside the three of the replay's self-test
    assert (tmp_path / "w" / "toy" / "src" / "Lib" / "Lazy.lean").read_text() == ec.LAZY


@pytest.mark.parametrize("mode", ["accepts", "rejects"])
def test_the_selftest_fails_a_checker_that_accepts_everything_or_nothing(tmp_path: Path, monkeypatch, mode: str) -> None:
    l4e, nanoda = _stubs(tmp_path, monkeypatch, mode)
    got = ec.selftest(l4e, nanoda, "leanprover/lean4:v4.33.1", str(tmp_path / "w"))
    assert got["passed"] is False
    want = {"accepts": {"honest": True, "worse": True, "lazy": True},
            "rejects": {"honest": False, "worse": False, "lazy": False}}[mode]
    assert {d: c["accepted"] for d, c in got["cases"].items()} == want


def test_a_run_passes_only_with_the_checker_and_the_axioms_and_says_what_it_covered(tmp_path: Path, monkeypatch) -> None:
    import subprocess
    l4e, nanoda = _stubs(tmp_path, monkeypatch, "checks")
    consts = tmp_path / "consts.jsonl"
    consts.write_text(_lines({"name": ["honest"], "kind": "theorem", "unsafe": False, "partial": False},
                             {"name": ["aux"], "kind": "theorem", "unsafe": False, "partial": False}))

    def run(decl: str):
        p = subprocess.run([sys.executable, str(HERE / "export_check.py"), "run", "--lean4export", l4e, "--nanoda", nanoda,
                            "--lean-dir", str(tmp_path), "--module", "Lib.X", "--decl", decl, "--consts", str(consts),
                            "--work", str(tmp_path / f"w-{decl}")], capture_output=True, text=True)
        return p.returncode, json.loads(p.stdout.strip().splitlines()[-1])

    code, out = run("honest")
    assert code == 0 and out["passed"] is True and out["nanoda"]["accepted"] is True
    # accepted, and still not the whole module: one of its constants is not in the export
    assert out["covers_the_module"] is False and out["export"]["module"]["missing_from_export"] == ["aux"]
    code, out = run("worse")
    assert code == 1 and out["passed"] is False and out["nanoda"]["exit_code"] == 1
    code, out = run("lazy")
    assert code == 1 and out["export"]["axioms_not_permitted"] == ["sorryAx"]
