#!/usr/bin/env python3
"""Probe for Hunt R-2946DE: empirical measurement of make_context.py --check on meta/

Measures the sensitivity of `scripts/make_context.py --check` to public functions,
classes, constants, new modules, and documentation files added or modified under `meta/`.

Runs against an isolated temporary copy of the repository in /tmp with strict
unmutated baseline and per-mutant undo controls.
"""

from __future__ import annotations

import ast
import difflib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def run_cmd(args: list[str], cwd: Path) -> tuple[int, str, str]:
    proc = subprocess.run(
        args,
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=False,
    )
    return proc.returncode, proc.stdout, proc.stderr


def diff_lines(a: str, b: str) -> tuple[int, list[str]]:
    alines = a.splitlines(keepends=True)
    blines = b.splitlines(keepends=True)
    diff = list(difflib.unified_diff(alines, blines, fromfile="before", tofile="after"))
    return len(diff), diff


def setup_sandbox(tmpdir: Path) -> Path:
    sandbox = tmpdir / "repo"
    sandbox.mkdir()

    dirs_to_copy = [
        "zeta",
        "ontology",
        "harness",
        "dossier",
        "docs",
        "scripts",
        "tests",
        "meta",
        "compiler",
    ]
    for d in dirs_to_copy:
        src = REPO_ROOT / d
        if src.exists():
            shutil.copytree(src, sandbox / d)

    files_to_copy = [
        "CONTEXT.md",
        "AGENTS.md",
        "README.md",
        "pyproject.toml",
    ]
    for f in files_to_copy:
        src = REPO_ROOT / f
        if src.exists():
            shutil.copy2(src, sandbox / f)

    return sandbox


def run_guard(sandbox: Path) -> tuple[int, str, str]:
    script = sandbox / "scripts" / "make_context.py"
    return run_cmd([sys.executable, str(script), "--check"], cwd=sandbox)


def regenerate_context(sandbox: Path) -> str:
    script = sandbox / "scripts" / "make_context.py"
    run_cmd([sys.executable, str(script)], cwd=sandbox)
    return (sandbox / "CONTEXT.md").read_text(encoding="utf-8")


def census_meta_symbols(sandbox: Path) -> list[dict]:
    meta_dir = sandbox / "meta"
    symbols = []
    for py_file in sorted(meta_dir.rglob("*.py")):
        rel = py_file.relative_to(sandbox)
        try:
            tree = ast.parse(py_file.read_text(encoding="utf-8"))
        except SyntaxError:
            continue
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if not node.name.startswith("_"):
                    symbols.append({
                        "file": str(rel),
                        "type": "function",
                        "name": node.name,
                        "lineno": node.lineno,
                    })
            elif isinstance(node, ast.ClassDef):
                if not node.name.startswith("_"):
                    symbols.append({
                        "file": str(rel),
                        "type": "class",
                        "name": node.name,
                        "lineno": node.lineno,
                    })
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for t in targets:
                    if isinstance(t, ast.Name) and t.id.isupper() and not t.id.startswith("_"):
                        symbols.append({
                            "file": str(rel),
                            "type": "constant",
                            "name": t.id,
                            "lineno": node.lineno,
                        })
    return symbols


def evaluate_mutant(
    sandbox: Path,
    baseline_context: str,
    mutant_id: str,
    name: str,
    category: str,
    apply_fn,
) -> dict:
    cleanup_fn = apply_fn(sandbox)

    # 1. Run guard
    code, stdout, stderr = run_guard(sandbox)
    fired = (code != 0)

    # 2. Check diff of regenerated CONTEXT.md
    regen = regenerate_context(sandbox)
    diff_count, dlines = diff_lines(baseline_context, regen)

    token_in_diff = any(mutant_id.lower() in line.lower() or name.lower() in line.lower() for line in dlines)

    # 3. Clean up and verify undo control
    cleanup_fn()
    (sandbox / "CONTEXT.md").write_text(baseline_context, encoding="utf-8")
    undo_code, undo_out, _ = run_guard(sandbox)
    if undo_code != 0:
        raise RuntimeError(f"Undo control failed for mutant {mutant_id}: {undo_out}")

    return {
        "id": mutant_id,
        "name": name,
        "category": category,
        "fired": fired,
        "exit_code": code,
        "diff_lines": diff_count,
        "token_in_diff": token_in_diff,
        "guard_output": stdout.strip(),
    }


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="hunt_r2946de_") as tmp:
        sandbox = setup_sandbox(Path(tmp))
        baseline_context = (sandbox / "CONTEXT.md").read_text(encoding="utf-8")

        # Control 1: unmutated baseline
        code, out, _ = run_guard(sandbox)
        if code != 0:
            print(f"FATAL: Unmutated baseline failed: {out}")
            return 1
        print("Control 1 (unmutated baseline): PASSED (exit 0)")

        # Curated Battery
        results = []

        # --- Category 1: Public function additions in meta/ ---
        def m01_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\ndef meta_probe_public_helper(x: int) -> int:\n    \"\"\"Docstring.\"\"\"\n    return x + 1\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M01",
            "public function appended to meta/ledger.py",
            "meta_public_function", m01_apply
        ))

        def m02_apply(s: Path):
            p = s / "meta" / "evals" / "asymmetry.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\ndef evaluate_asymmetry_metric() -> bool:\n    \"\"\"Run eval.\"\"\"\n    return True\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M02",
            "public function appended to meta/evals/asymmetry.py",
            "meta_public_function", m02_apply
        ))

        def m03_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\nasync def run_meta_async_scan() -> None:\n    \"\"\"Async helper.\"\"\"\n    pass\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M03",
            "public async function appended to meta/ledger.py",
            "meta_public_function", m03_apply
        ))

        # --- Category 2: In-place symbol renames in meta/ ---
        def m04_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            mut = orig.replace("class Category(str, Enum):", "class MetaCat(str, Enum):   ")
            p.write_text(mut, encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M04",
            "public class renamed in place in meta/ledger.py",
            "meta_inplace_rename", m04_apply
        ))

        def m05_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            mut = orig.replace("def load_ledger(", "def read_ledger(")
            p.write_text(mut, encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M05",
            "public function load_ledger renamed in place in meta/ledger.py",
            "meta_inplace_rename", m05_apply
        ))

        def m06_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            mut = orig.replace("LEDGER_PATH = ", "META_LPATH  = ")
            p.write_text(mut, encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M06",
            "public uppercase constant LEDGER_PATH renamed in place in meta/ledger.py",
            "meta_inplace_rename", m06_apply
        ))

        # --- Category 3: Public classes and constants added to meta/ ---
        def m07_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\nclass MetaExperimentRegistry:\n    \"\"\"Registry.\"\"\"\n    pass\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M07",
            "public class appended to meta/ledger.py",
            "meta_class_addition", m07_apply
        ))

        def m08_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\nMETA_DEFAULT_TIMEOUT: int = 30\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M08",
            "public uppercase constant appended to meta/ledger.py",
            "meta_constant_addition", m08_apply
        ))

        def m09_apply(s: Path):
            p = s / "meta" / "evals" / "asymmetry.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\nASYMMETRY_EVAL_VERSION = \"2.0\"\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M09",
            "public uppercase constant appended to meta/evals/asymmetry.py",
            "meta_constant_addition", m09_apply
        ))

        # --- Category 4: New modules and files in meta/ ---
        def m10_apply(s: Path):
            p = s / "meta" / "new_framework.py"
            p.write_text("\"\"\"New framework.\"\"\"\n\ndef execute_framework():\n    pass\n\nclass FrameworkRunner:\n    pass\n", encoding="utf-8")
            return lambda: p.unlink()

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M10",
            "new module meta/new_framework.py added",
            "meta_new_module", m10_apply
        ))

        def m11_apply(s: Path):
            p = s / "meta" / "evals" / "new_eval_metric.py"
            p.write_text("\"\"\"New eval.\"\"\"\n\ndef score_metric():\n    return 1.0\n", encoding="utf-8")
            return lambda: p.unlink()

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M11",
            "new module meta/evals/new_eval_metric.py added",
            "meta_new_module", m11_apply
        ))

        def m12_apply(s: Path):
            p = s / "meta" / "meta_methodology.md"
            p.write_text("# Meta Methodology\n\nGuidelines for research.\n", encoding="utf-8")
            return lambda: p.unlink()

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M12",
            "new markdown document meta/meta_methodology.md added",
            "meta_doc", m12_apply
        ))

        def m13_apply(s: Path):
            p = s / "meta" / "README.md"
            orig = p.read_text(encoding="utf-8")
            mut = orig.replace("the second laboratory", "the modified laboratory")
            p.write_text(mut, encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M13",
            "meta/README.md title changed in place",
            "meta_doc", m13_apply
        ))

        # --- Category 5: Line counts, docstrings and formatting in meta/ ---
        def m14_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\n\n\n\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M14",
            "5 blank lines appended to meta/ledger.py",
            "meta_formatting", m14_apply
        ))

        def m15_apply(s: Path):
            p = s / "meta" / "ledger.py"
            orig = p.read_text(encoding="utf-8")
            mut = orig.replace("The intervention ledger", "The modified intervention ledger")
            p.write_text(mut, encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M15",
            "meta/ledger.py module docstring first line modified",
            "meta_docstring", m15_apply
        ))

        def m16_apply(s: Path):
            p = s / "meta" / "evals" / "__init__.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text("\"\"\"Evals package docstring.\"\"\"\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M16",
            "docstring added to empty meta/evals/__init__.py",
            "meta_docstring", m16_apply
        ))

        # --- Category 6: In-scope positive controls in scanned directories ---
        def m17_apply(s: Path):
            p = s / "zeta" / "core.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\ndef positive_control_func(): pass\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M17",
            "public function appended to zeta/core.py (positive control)",
            "positive_control", m17_apply
        ))

        def m18_apply(s: Path):
            p = s / "ontology" / "schema.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\ndef positive_control_schema(): pass\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M18",
            "public function appended to ontology/schema.py (positive control)",
            "positive_control", m18_apply
        ))

        def m19_apply(s: Path):
            p = s / "harness" / "protocol.py"
            orig = p.read_text(encoding="utf-8")
            p.write_text(orig + "\n\ndef positive_control_protocol(): pass\n", encoding="utf-8")
            return lambda: p.write_text(orig, encoding="utf-8")

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M19",
            "public function appended to harness/protocol.py (positive control)",
            "positive_control", m19_apply
        ))

        def m20_apply(s: Path):
            p = s / "docs" / "99-positive-control-doc.md"
            p.write_text("# Positive Control Doc\n\nContent.\n", encoding="utf-8")
            return lambda: p.unlink()

        results.append(evaluate_mutant(
            sandbox, baseline_context, "M20",
            "new doc docs/99-positive-control-doc.md added (positive control)",
            "positive_control", m20_apply
        ))

        # --- Exhaustive symbol census and mutation across meta/ ---
        meta_symbols = census_meta_symbols(sandbox)
        exhaustive_results = []
        for i, sym in enumerate(meta_symbols, 1):
            sym_id = f"EX_{i:02d}"

            def make_apply(s_info: dict):
                def _apply(s: Path):
                    sf = s / s_info["file"]
                    orig = sf.read_text(encoding="utf-8")
                    if s_info["type"] == "function":
                        mut = orig.replace(f"def {s_info['name']}(", f"def mut_{s_info['name']}(")
                    elif s_info["type"] == "class":
                        mut = orig.replace(f"class {s_info['name']}", f"class Mut_{s_info['name']}")
                    else:
                        mut = orig.replace(f"{s_info['name']} =", f"MUT_{s_info['name']} =")
                    sf.write_text(mut, encoding="utf-8")
                    return lambda: sf.write_text(orig, encoding="utf-8")
                return _apply

            res = evaluate_mutant(
                sandbox, baseline_context, sym_id,
                f"{sym['type']} {sym['name']} in {sym['file']}",
                "meta_exhaustive_symbol",
                make_apply(sym),
            )
            exhaustive_results.append(res)

        # Structure final data
        meta_mutants = [r for r in results if r["category"].startswith("meta_")]
        pos_controls = [r for r in results if r["category"] == "positive_control"]

        meta_fired_count = sum(1 for r in meta_mutants if r["fired"])
        pos_fired_count = sum(1 for r in pos_controls if r["fired"])
        exhaustive_fired_count = sum(1 for r in exhaustive_results if r["fired"])

        data = {
            "meta_mutants_total": len(meta_mutants),
            "meta_mutants_fired": meta_fired_count,
            "meta_detection_rate": f"{meta_fired_count / len(meta_mutants):.1%}",
            "positive_controls_total": len(pos_controls),
            "positive_controls_fired": pos_fired_count,
            "positive_detection_rate": f"{pos_fired_count / len(pos_controls):.1%}",
            "meta_symbols_total": len(meta_symbols),
            "exhaustive_mutants_total": len(exhaustive_results),
            "exhaustive_mutants_fired": exhaustive_fired_count,
            "exhaustive_detection_rate": f"{exhaustive_fired_count / len(exhaustive_results):.1%}",
            "curated_battery": results,
            "exhaustive_battery": exhaustive_results,
            "meta_symbols_census": meta_symbols,
        }

        out_path = Path(__file__).resolve().parent / "results.json"
        out_path.write_text(json.dumps(data, indent=2), encoding="utf-8")
        print(f"Wrote {out_path}")

        print("\n--- Summary ---")
        print(f"Meta curated mutants: {meta_fired_count}/{len(meta_mutants)} fired ({data['meta_detection_rate']})")
        print(f"Meta exhaustive symbols: {exhaustive_fired_count}/{len(exhaustive_results)} fired ({data['exhaustive_detection_rate']})")
        print(f"Positive controls: {pos_fired_count}/{len(pos_controls)} fired ({data['positive_detection_rate']})")

    return 0


if __name__ == "__main__":
    sys.exit(main())
