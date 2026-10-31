"""Planted-fault runner for the chain lane's prose checks (RUNS.md, entry C3).

Each fault edits one note once, runs test_chain.py, records whether the edit
was refused (the test turned red), then restores the file's text.  The C2
runner of 2026-10-21 was a scratchpad script that was not kept; this is its
reconstruction from the fault kinds C2 lists.  Run from the repository root:

    .venv/bin/python hunts/dbn_pt_height/planted_faults.py
"""
import json, os, subprocess, sys, time
from pathlib import Path

os.chdir(Path(__file__).resolve().parents[2])
PY = sys.executable
H = "hunts/dbn_pt_height"
FAULTS = [
    # the adversary's kinds
    ("commit count", f"{H}/CHAIN.md", "778 commits", "779 commits"),
    ("date (ISO)", f"{H}/CHAIN.md", "On 2019-04-15 Terence Tao", "On 2019-04-16 Terence Tao"),
    ("date (prose)", f"{H}/CHAIN.md", "5 July 2024", "7 July 2024"),
    ("float digits", f"{H}/CHAIN.md", "0.03028099814", "0.03028099815"),
    ("19/200", f"{H}/REDUCTION.md", "19/200", "19/100"),
    ("attribution", f"{H}/CHAIN.md", "by Fabrice Imparato", "by Terence Tao"),
    ("negated headline", f"{H}/CHAIN.md", "only at N = N0 = 630783", "over all N >= N0 = 630783"),
    ("DH zero", f"{H}/REDUCTION.md", "0.8085", "0.8058"),
    ("locator", f"{H}/CHAIN.md", "[Q:B1]", "[Q:B2]"),
    ("four-digit number", f"{H}/CHAIN.md", "N = 1650000", "N = 1600000"),
    # the others
    ("parent comment", f"{H}/CHAIN.md", "(comment 483072037)", "(comment 483072038)"),
    ("'the same day'", f"{H}/CHAIN.md", "replied the same day", "replied the next day"),
    ("case-log date", "hunts/README.md", "(`dbn_pt_height/`, opened 2026-10-21)", "(`dbn_pt_height/`, opened 2026-10-20)"),
    ("large number", f"{H}/REDUCTION.md", "66476100549959", "66476100549958"),
    ("2018 table", f"{H}/CHAIN.md", "N from 282094 to 13000000", "N from 282094 to 14000000"),
    ("part C cell (0.16 uses)", f"{H}/REDUCTION.md", "| **yes** | no |\n| **0.1595**", "| no | no |\n| **0.1595**"),
    ("part C cell (0.2 inherits)", f"{H}/REDUCTION.md", "[Q:C1] | no | yes |", "[Q:C1] | no | no |"),
]
ARGS = [PY, "-m", "pytest", "-q", "-x", "-p", "no:cacheprovider", f"{H}/test_chain.py"]
ARGS.insert(5, "-" + "n0")


def run() -> bool:
    return subprocess.run(ARGS, capture_output=True, text=True).returncode == 0


out = []
assert run(), "baseline must be green"
for kind, path, old, new in FAULTS:
    p = Path(path)
    text = p.read_text(encoding="utf-8")
    if old not in text:
        out.append({"kind": kind, "file": path, "result": "target string absent"})
        print(json.dumps(out[-1]), flush=True)
        continue
    p.write_text(text.replace(old, new, 1), encoding="utf-8")
    try:
        t = time.perf_counter()
        green = run()
    finally:
        p.write_text(text, encoding="utf-8")
    out.append({"kind": kind, "file": path, "old": old, "new": new,
                "result": "NOT refused" if green else "refused", "seconds": round(time.perf_counter() - t, 1)})
    print(json.dumps(out[-1]), flush=True)
assert run(), "restored tree must be green"
print(json.dumps({"refused": sum(r["result"] == "refused" for r in out), "of": len(out)}))
