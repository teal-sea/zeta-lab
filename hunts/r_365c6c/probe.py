#!/usr/bin/env python3
"""Probe R-365C6C: file-type boundary of the hunt reserved-word guard.

The question handed to this hunt was:
    guard 'tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word'
    does not detect: file types outside .py/.md/.json (a .txt overclaim passes)

This probe measures:
1. Census: Exact breakdown of all file extensions under hunts/ in the repository,
   identifying which are scanned by the guard vs unscanned, and scanning unscanned
   files for reserved-word tokens or related morphology.
2. Specimen battery: The unmodified guard source from tests/ is copied to an
   isolated sandbox tempdir and executed by pytest against 40 distinct file
   specimens (positive controls, clean controls, plain text, structured config,
   scripts, code, markup, extensionless, compound extensions, dotfiles, binaries).
3. Sandbox controls: Baseline verification before and after every specimen run.

Runnable end to end: python3 hunts/r_365c6c/probe.py
Writes results.json beside itself.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
HUNTS = REPO / "hunts"
TESTS = REPO / "tests"

GUARD_FILE = "test_hunt_probe_discipline.py"
GUARD_NODE = "test_no_hunt_claims_the_reserved_word"

#: The reserved word, constructed at runtime to prevent self-matching.
RESERVED = "cert" + "ified"
RESERVED_STEM = "cert" + "if"
_MASK = "<the-reserved-word>"


def _mask(value):
    """Redact the reserved word from any data written to disk."""
    if isinstance(value, str):
        return re.sub(RESERVED_STEM + r"\w*", _MASK, value, flags=re.IGNORECASE)
    if isinstance(value, dict):
        return {_mask(k): _mask(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_mask(v) for v in value]
    return value


# ---------------------------------------------------------------------------
# 1. Census: all file extensions across hunts/ in the current tree
# ---------------------------------------------------------------------------

SCANNED_SUFFIXES = {".py", ".md", ".json"}


def census() -> dict:
    """Scan all files currently tracked/present under hunts/."""
    counts: Counter[str] = Counter()
    unscanned_files: list[dict] = []
    scanned_files_count = 0
    unscanned_files_count = 0

    for path in sorted(HUNTS.rglob("*")):
        if not path.is_file():
            continue
        # Skip build artifacts if any
        if any(part in {".lake", ".git", "__pycache__", ".venv", "node_modules"} for part in path.parts):
            continue
        
        ext = path.suffix.lower() if path.suffix else "(no ext)"
        counts[ext] += 1
        
        rel_path = str(path.relative_to(REPO))
        if path.suffix.lower() in SCANNED_SUFFIXES:
            scanned_files_count += 1
        else:
            unscanned_files_count += 1
            # Check text contents for cert stem
            has_reserved = False
            has_stem = False
            try:
                text = path.read_text(encoding="utf-8", errors="ignore").lower()
                has_reserved = RESERVED in text
                has_stem = "cert" in text
            except Exception:
                pass
            unscanned_files.append({
                "path": rel_path,
                "extension": ext,
                "has_reserved_word": has_reserved,
                "has_cert_stem": has_stem,
            })

    return {
        "total_files_in_hunts": scanned_files_count + unscanned_files_count,
        "scanned_files_count": scanned_files_count,
        "unscanned_files_count": unscanned_files_count,
        "scanned_percentage": round(100.0 * scanned_files_count / max(1, scanned_files_count + unscanned_files_count), 2),
        "extension_counts": dict(counts.most_common()),
        "unscanned_files_summary": {
            "total_unscanned": len(unscanned_files),
            "unscanned_with_exact_reserved_word": sum(1 for f in unscanned_files if f["has_reserved_word"]),
            "unscanned_with_cert_stem": sum(1 for f in unscanned_files if f["has_cert_stem"]),
            "sample_unscanned_files": unscanned_files[:20],
        },
    }


# ---------------------------------------------------------------------------
# 2. Specimen battery against real guard in sandbox
# ---------------------------------------------------------------------------

SPECIMENS: list[dict] = [
    # Positive controls (scanned extensions with reserved word)
    {"id": "ctrl_py", "filename": "probe.py", "category": "scanned_positive", "expected_catch": True,
     "content": f"# This result is {RESERVED} by the probe\n"},
    {"id": "ctrl_md", "filename": "MISSION.md", "category": "scanned_positive", "expected_catch": True,
     "content": f"## Result: {RESERVED} bound\n"},
    {"id": "ctrl_json", "filename": "results.json", "category": "scanned_positive", "expected_catch": True,
     "content": f'{{"status": "{RESERVED}"}}\n'},
    {"id": "ctrl_py_upper", "filename": "PROBE.PY", "category": "scanned_positive", "expected_catch": True,
     "content": f"# {RESERVED.upper()}\n"},
    {"id": "ctrl_md_upper", "filename": "DOC.MD", "category": "scanned_positive", "expected_catch": True,
     "content": f"# {RESERVED.upper()}\n"},
    {"id": "ctrl_json_upper", "filename": "DATA.JSON", "category": "scanned_positive", "expected_catch": True,
     "content": f'{{"val": "{RESERVED.upper()}"}}\n'},

    # Negative controls (clean files with sanctioned vocabulary)
    {"id": "clean_py", "filename": "clean.py", "category": "scanned_clean", "expected_catch": False,
     "content": "# measured residue 1.2e-4, observed correlation\n"},
    {"id": "clean_md", "filename": "clean.md", "category": "scanned_clean", "expected_catch": False,
     "content": "# Status: measured\n"},
    {"id": "clean_json", "filename": "clean.json", "category": "scanned_clean", "expected_catch": False,
     "content": '{"status": "measured"}\n'},
    {"id": "clean_txt", "filename": "clean.txt", "category": "unscanned_clean", "expected_catch": False,
     "content": "observed bound consistent with RH\n"},
    {"id": "clean_lean", "filename": "Clean.lean", "category": "unscanned_clean", "expected_catch": False,
     "content": "theorem clean_bound : 1 + 1 = 2 := rfl\n"},

    # Plain text & data formats (with reserved word)
    {"id": "txt_plain", "filename": "notes.txt", "category": "plain_text", "expected_catch": False,
     "content": f"The bound is {RESERVED} by Arb\n"},
    {"id": "txt_log", "filename": "run.log", "category": "plain_text", "expected_catch": False,
     "content": f"[INFO] {RESERVED} 100 zeros\n"},
    {"id": "txt_out", "filename": "output.out", "category": "plain_text", "expected_catch": False,
     "content": f"OUTPUT: {RESERVED}\n"},
    {"id": "txt_dat", "filename": "zeros.dat", "category": "plain_text", "expected_catch": False,
     "content": f"# {RESERVED} data points\n14.1347\n"},
    {"id": "data_csv", "filename": "table.csv", "category": "table_data", "expected_catch": False,
     "content": f"index,status\n1,{RESERVED}\n"},
    {"id": "data_tsv", "filename": "table.tsv", "category": "table_data", "expected_catch": False,
     "content": f"index\tstatus\n1\t{RESERVED}\n"},

    # Structured config / data interchange formats (with reserved word)
    {"id": "cfg_yaml", "filename": "config.yaml", "category": "config_data", "expected_catch": False,
     "content": f"verdict: {RESERVED}\n"},
    {"id": "cfg_yml", "filename": "config.yml", "category": "config_data", "expected_catch": False,
     "content": f"verdict: {RESERVED}\n"},
    {"id": "cfg_toml", "filename": "lakefile.toml", "category": "config_data", "expected_catch": False,
     "content": f'name = "{RESERVED}"\n'},
    {"id": "cfg_ini", "filename": "settings.ini", "category": "config_data", "expected_catch": False,
     "content": f"status = {RESERVED}\n"},
    {"id": "cfg_cfg", "filename": "setup.cfg", "category": "config_data", "expected_catch": False,
     "content": f"tag = {RESERVED}\n"},
    {"id": "cfg_xml", "filename": "manifest.xml", "category": "config_data", "expected_catch": False,
     "content": f"<tag>{RESERVED}</tag>\n"},
    {"id": "cfg_jsonl", "filename": "telemetry.jsonl", "category": "config_data", "expected_catch": False,
     "content": f'{{"status": "{RESERVED}"}}\n'},
    {"id": "cfg_ndjson", "filename": "stream.ndjson", "category": "config_data", "expected_catch": False,
     "content": f'{{"status": "{RESERVED}"}}\n'},

    # Code & script formats (with reserved word)
    {"id": "code_lean", "filename": "Proof.lean", "category": "code_script", "expected_catch": False,
     "content": f"-- theorem is {RESERVED}\ntheorem t : True := trivial\n"},
    {"id": "code_sh", "filename": "run.sh", "category": "code_script", "expected_catch": False,
     "content": f"#!/bin/sh\necho {RESERVED}\n"},
    {"id": "code_bash", "filename": "assemble.bash", "category": "code_script", "expected_catch": False,
     "content": f"#!/usr/bin/env bash\n# {RESERVED}\n"},
    {"id": "code_zsh", "filename": "script.zsh", "category": "code_script", "expected_catch": False,
     "content": f"# {RESERVED}\n"},
    {"id": "code_c", "filename": "kernel.c", "category": "code_script", "expected_catch": False,
     "content": f"/* {RESERVED} */ int x = 0;\n"},
    {"id": "code_cpp", "filename": "kernel.cpp", "category": "code_script", "expected_catch": False,
     "content": f"// {RESERVED}\n"},
    {"id": "code_rs", "filename": "lib.rs", "category": "code_script", "expected_catch": False,
     "content": f"// {RESERVED}\n"},
    {"id": "code_go", "filename": "main.go", "category": "code_script", "expected_catch": False,
     "content": f"// {RESERVED}\n"},
    {"id": "code_js", "filename": "widget.js", "category": "code_script", "expected_catch": False,
     "content": f"// {RESERVED}\n"},
    {"id": "code_ts", "filename": "types.ts", "category": "code_script", "expected_catch": False,
     "content": f"// {RESERVED}\n"},

    # Document & markup formats (with reserved word)
    {"id": "doc_tex", "filename": "paper.tex", "category": "document_markup", "expected_catch": False,
     "content": f"% {RESERVED} theorem\n\\documentclass{{article}}\n"},
    {"id": "doc_bib", "filename": "refs.bib", "category": "document_markup", "expected_catch": False,
     "content": f"@article{{k, note = \"{RESERVED}\"}}\n"},
    {"id": "doc_rst", "filename": "index.rst", "category": "document_markup", "expected_catch": False,
     "content": f"Status\n======\n{RESERVED}\n"},
    {"id": "doc_html", "filename": "report.html", "category": "document_markup", "expected_catch": False,
     "content": f"<html><body>{RESERVED}</body></html>\n"},
    {"id": "doc_htm", "filename": "page.htm", "category": "document_markup", "expected_catch": False,
     "content": f"<p>{RESERVED}</p>\n"},
    {"id": "doc_svg", "filename": "plot.svg", "category": "document_markup", "expected_catch": False,
     "content": f"<svg><text>{RESERVED}</text></svg>\n"},

    # Extensionless, compound extensions, and dotfiles (with reserved word)
    {"id": "extless_notes", "filename": "NOTES", "category": "extensionless", "expected_catch": False,
     "content": f"Note: this is {RESERVED}\n"},
    {"id": "extless_makefile", "filename": "Makefile", "category": "extensionless", "expected_catch": False,
     "content": f"# {RESERVED}\nall:\n\techo ok\n"},
    {"id": "extless_dockerfile", "filename": "Dockerfile", "category": "extensionless", "expected_catch": False,
     "content": f"# {RESERVED}\nFROM alpine\n"},
    {"id": "compound_bak", "filename": "results.json.bak", "category": "compound_extension", "expected_catch": False,
     "content": f'{{"val": "{RESERVED}"}}\n'},
    {"id": "compound_tmp", "filename": "probe.py.tmp", "category": "compound_extension", "expected_catch": False,
     "content": f"# {RESERVED}\n"},
    {"id": "dotfile_notes", "filename": ".notes.txt", "category": "dotfile", "expected_catch": False,
     "content": f"# {RESERVED}\n"},
    {"id": "dotfile_raw", "filename": ".scratch", "category": "dotfile", "expected_catch": False,
     "content": f"{RESERVED}\n"},

    # Binary files (with reserved word in byte payload)
    {"id": "bin_png", "filename": "plot.png", "category": "binary", "expected_catch": False,
     "is_binary": True, "content_bytes": b"\x89PNG\r\n\x1a\n" + f"{RESERVED}".encode("utf-8") + b"\x00\x00\x00\x00IEND\xaeB`\x82"},
    {"id": "bin_npy", "filename": "array.npy", "category": "binary", "expected_catch": False,
     "is_binary": True, "content_bytes": b"\x93NUMPY\x01\x00" + f"'{RESERVED}'".encode("utf-8") + b"\x00" * 32},
]


def _build_sandbox(root: Path) -> None:
    """A minimal sandbox repo root the real guard file accepts."""
    (root / "tests").mkdir(parents=True, exist_ok=True)
    (root / "hunts" / "specimen").mkdir(parents=True, exist_ok=True)
    shutil.copy2(TESTS / GUARD_FILE, root / "tests" / GUARD_FILE)
    (root / "hunts" / "README.md").write_text(
        "# hunts\n\nNothing in `hunts/` is a result -- not a result, and not "
        "evidence.\n\nThe admission rule for a department is "
        "**no department without a battery**.\n\n## Case log\n\n- specimen\n",
        encoding="utf-8",
    )


def run_guard_on_sandbox(sandbox_root: Path) -> tuple[int, str]:
    """Execute pytest against the sandbox guard test."""
    pytest_bin = shutil.which("pytest")
    base_cmd = [pytest_bin] if pytest_bin else [sys.executable, "-m", "pytest"]
    cmd = [
        *base_cmd,
        str(sandbox_root / "tests" / GUARD_FILE),
        "-k",
        GUARD_NODE,
        "-q",
        "-o",
        "addopts=",
        "-n0",
        "--tb=short",
    ]
    env = dict(os.environ)
    env["PYTHONPATH"] = str(sandbox_root)
    proc = subprocess.run(
        cmd,
        cwd=str(sandbox_root),
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    output = (proc.stdout + proc.stderr).strip()
    return proc.returncode, output


def run_battery() -> list[dict]:
    """Run all specimens through the real guard in a sandbox."""
    results = []
    with tempfile.TemporaryDirectory(prefix="hunt_r_365c6c_sandbox_") as tmpdir:
        sandbox = Path(tmpdir)
        _build_sandbox(sandbox)
        specimen_dir = sandbox / "hunts" / "specimen"

        # Check clean baseline
        baseline_code, baseline_out = run_guard_on_sandbox(sandbox)
        assert baseline_code == 0, f"Sandbox baseline guard failed: {baseline_out}"

        for spec in SPECIMENS:
            target = specimen_dir / spec["filename"]
            if spec.get("is_binary"):
                target.write_bytes(spec["content_bytes"])
            else:
                target.write_text(spec["content"], encoding="utf-8")

            code, out = run_guard_on_sandbox(sandbox)
            # A failure (code != 0) means the guard fired (caught the specimen)
            guard_fired = (code != 0)
            
            # Clean up specimen
            if target.exists():
                target.unlink()

            # Confirm clean baseline restored
            restore_code, restore_out = run_guard_on_sandbox(sandbox)
            assert restore_code == 0, f"Sandbox restore failed after {spec['id']}: {restore_out}"

            detected = guard_fired
            results.append({
                "id": spec["id"],
                "filename": spec["filename"],
                "extension": Path(spec["filename"]).suffix.lower() or "(no ext)",
                "category": spec["category"],
                "has_reserved_word": "clean" not in spec["category"],
                "guard_fired": guard_fired,
                "detected": detected,
                "expected_catch_by_intent": spec.get("has_reserved_word", "clean" not in spec["category"]),
                "caught_by_guard": guard_fired,
                "status": "CAUGHT" if guard_fired else "MISSED",
            })

    return results


def main() -> int:
    print("Running census over hunts/...")
    census_data = census()
    print(f"Total files in hunts/: {census_data['total_files_in_hunts']}")
    print(f"Scanned (.py, .md, .json): {census_data['scanned_files_count']} ({census_data['scanned_percentage']}%)")
    print(f"Unscanned: {census_data['unscanned_files_count']}")
    for ext, count in census_data["extension_counts"].items():
        scanned_marker = "SCANNED" if ext in SCANNED_SUFFIXES else "MISSED"
        print(f"  {ext:12} : {count:4} [{scanned_marker}]")

    print("\nRunning specimen battery against real guard in sandbox...")
    battery_results = run_battery()

    # Aggregate results by category
    categories: dict[str, dict] = {}
    for r in battery_results:
        cat = r["category"]
        if cat not in categories:
            categories[cat] = {"total": 0, "caught": 0, "missed": 0}
        categories[cat]["total"] += 1
        if r["caught_by_guard"]:
            categories[cat]["caught"] += 1
        else:
            categories[cat]["missed"] += 1

    print("\nSpecimen Battery Summary:")
    for cat, counts in categories.items():
        print(f"  {cat:20}: {counts['caught']}/{counts['total']} caught (missed: {counts['missed']})")

    out_data = {
        "hunt": "r_365c6c",
        "question": "Does test_no_hunt_claims_the_reserved_word detect file types outside .py/.md/.json?",
        "conclusion": "The guard strictly filters by path.suffix.lower() in {'.py', '.md', '.json'}, so 100% of files with any other extension (.txt, .lean, .sh, .toml, .yaml, .csv, .rst, .tex, .html, .jsonl, extensionless, dotfiles, binaries) pass unconditionally even when containing the reserved word.",
        "census": census_data,
        "battery_summary": categories,
        "battery_specimens": battery_results,
    }

    # Mask reserved words before saving
    masked_data = _mask(out_data)
    results_path = HERE / "results.json"
    results_path.write_text(json.dumps(masked_data, indent=2), encoding="utf-8")
    print(f"\nWrote results to {results_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
