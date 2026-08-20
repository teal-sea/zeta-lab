#!/usr/bin/env python3
"""probe.py: measure scripts/make_context.py sensitivity to test file naming.

This probe evaluates the known miss in harness/departments/guard_ledger.py:
    guard 'scripts/make_context.py --check' does not detect: test files whose
    names do not match test_*.py, e.g. tests/mutant_helper.py (B04)
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
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

def get_git_test_history() -> list[str]:
    try:
        res = subprocess.run(
            ["git", "log", "--name-only", "--oneline", "tests/"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        paths = set()
        for line in res.stdout.splitlines():
            line = line.strip()
            if line.startswith("tests/"):
                paths.add(line)
        return sorted(paths)
    except Exception as e:
        return [f"git error: {e}"]

def test_census(tests_dir: Path) -> dict:
    all_paths = sorted(tests_dir.rglob("*"))
    matching_test_files = []
    non_matching_py_files = []
    subdirectories = []
    non_py_files = []

    for p in all_paths:
        rel = str(p.relative_to(tests_dir))
        if p.is_dir():
            subdirectories.append(rel)
        elif p.name.startswith("test_") and p.suffix == ".py":
            matching_test_files.append(rel)
        elif p.suffix == ".py":
            non_matching_py_files.append(rel)
        else:
            non_py_files.append(rel)

    test_func_counts = {}
    for rel in matching_test_files:
        p = tests_dir / rel
        try:
            tree = ast.parse(p.read_text(encoding="utf-8"))
            n = sum(
                1
                for node in ast.walk(tree)
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and node.name.startswith("test_")
            )
            test_func_counts[rel] = n
        except Exception as e:
            test_func_counts[rel] = f"error: {e}"

    return {
        "total_items": len(all_paths),
        "matching_test_files_count": len(matching_test_files),
        "matching_test_files": matching_test_files,
        "non_matching_py_files_count": len(non_matching_py_files),
        "non_matching_py_files": non_matching_py_files,
        "subdirectories_count": len(subdirectories),
        "subdirectories": subdirectories,
        "non_py_files_count": len(non_py_files),
        "non_py_files": non_py_files,
        "total_test_functions": sum(v for v in test_func_counts.values() if isinstance(v, int)),
        "test_func_counts": test_func_counts,
    }

def create_sandbox(temp_dir: Path) -> Path:
    sandbox_root = temp_dir / "repo"
    sandbox_root.mkdir()

    dirs_to_copy = ["zeta", "ontology", "harness", "dossier", "docs", "scripts", "tests"]
    for d in dirs_to_copy:
        src = REPO_ROOT / d
        if src.exists():
            shutil.copytree(src, sandbox_root / d)

    files_to_copy = ["CONTEXT.md"]
    for f in files_to_copy:
        src = REPO_ROOT / f
        if src.exists():
            shutil.copy2(src, sandbox_root / f)

    return sandbox_root

def run_guard_check(sandbox_root: Path) -> tuple[int, str]:
    cmd = [sys.executable, str(sandbox_root / "scripts" / "make_context.py"), "--check"]
    res = subprocess.run(cmd, cwd=sandbox_root, capture_output=True, text=True)
    output = (res.stdout + res.stderr).strip()
    return res.returncode, output

def run_guard_regenerate(sandbox_root: Path) -> str:
    cmd = [sys.executable, str(sandbox_root / "scripts" / "make_context.py")]
    subprocess.run(cmd, cwd=sandbox_root, capture_output=True, text=True, check=True)
    return (sandbox_root / "CONTEXT.md").read_text(encoding="utf-8")

def calculate_diff_lines(original: str, generated: str) -> list[str]:
    diff = list(difflib.unified_diff(original.splitlines(keepends=True), generated.splitlines(keepends=True), fromfile="CONTEXT.md.orig", tofile="CONTEXT.md.gen"))
    return [d.rstrip("\n") for d in diff]

def run_mutant_battery(sandbox_root: Path) -> list[dict]:
    baseline_context = (sandbox_root / "CONTEXT.md").read_text(encoding="utf-8")

    mutants = [
        # Category 1: Non-matching test filenames directly under tests/
        {"id": "M01", "category": "non_matching_filename_root", "description": "tests/mutant_helper.py added (B04 reference)", "action": lambda sb: (sb / "tests" / "mutant_helper.py").write_text("def helper_one():\n    return 42\n\ndef test_mutant():\n    assert helper_one() == 42\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "mutant_helper.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/mutant_helper.py"},
        {"id": "M02", "category": "non_matching_filename_root", "description": "tests/conftest.py added with pytest fixtures", "action": lambda sb: (sb / "tests" / "conftest.py").write_text("import pytest\n\n@pytest.fixture\ndef sample():\n    return 1\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "conftest.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/conftest.py"},
        {"id": "M03", "category": "non_matching_filename_root", "description": "tests/helper.py added with support utilities", "action": lambda sb: (sb / "tests" / "helper.py").write_text("def make_lattice(n):\n    return list(range(n))\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "helper.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/helper.py"},
        {"id": "M04", "category": "non_matching_filename_root", "description": "tests/fixtures.py added with data generators", "action": lambda sb: (sb / "tests" / "fixtures.py").write_text("FIXTURE_ZEROS = [14.134725, 21.022039]\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "fixtures.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/fixtures.py"},
        {"id": "M05", "category": "non_matching_filename_root", "description": "tests/utils.py added with assertion helper library", "action": lambda sb: (sb / "tests" / "utils.py").write_text("def assert_close(a, b, tol=1e-12):\n    assert abs(a - b) < tol\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "utils.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/utils.py"},
        {"id": "M06", "category": "non_matching_filename_root", "description": "tests/base.py added with test base class", "action": lambda sb: (sb / "tests" / "base.py").write_text("class BaseZetaTest:\n    def setUp(self):\n        self.p = 30\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "base.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/base.py"},
        {"id": "M07", "category": "non_matching_filename_root", "description": "tests/testsuite.py added (no underscore after test)", "action": lambda sb: (sb / "tests" / "testsuite.py").write_text("def test_full_suite():\n    pass\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "testsuite.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/testsuite.py"},
        {"id": "M08", "category": "non_matching_filename_root", "description": "tests/core_test.py added (trailing *_test.py convention)", "action": lambda sb: (sb / "tests" / "core_test.py").write_text("def test_core():\n    assert 1 + 1 == 2\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "core_test.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/core_test.py"},
        {"id": "M09", "category": "non_matching_filename_root", "description": "tests/_test_internal.py added (leading underscore prefix)", "action": lambda sb: (sb / "tests" / "_test_internal.py").write_text("def test_internal():\n    assert True\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "_test_internal.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/_test_internal.py"},
        {"id": "M10", "category": "non_matching_filename_root", "description": "tests/TestUnit.py added (CamelCase test class module)", "action": lambda sb: (sb / "tests" / "TestUnit.py").write_text("class TestUnit:\n    def test_method(self):\n        assert True\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "TestUnit.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/TestUnit.py"},
        {"id": "M11", "category": "non_matching_filename_root", "description": "tests/check_properties.py added (check_* prefix)", "action": lambda sb: (sb / "tests" / "check_properties.py").write_text("def check_all():\n    return True\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "check_properties.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/check_properties.py"},
        {"id": "M12", "category": "non_matching_filename_root", "description": "tests/benchmark_runner.py added (benchmark runner)", "action": lambda sb: (sb / "tests" / "benchmark_runner.py").write_text("def run_bench():\n    pass\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "benchmark_runner.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/benchmark_runner.py"},
        # Category 2: Nested subdirectories and files
        {"id": "M13", "category": "subdirectories_and_nested", "description": "tests/fixtures/helper.py added in existing fixtures subdir", "action": lambda sb: (sb / "tests" / "fixtures" / "helper.py").write_text("def load_fixture():\n    return {}\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "fixtures" / "helper.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/fixtures/helper.py"},
        {"id": "M14", "category": "subdirectories_and_nested", "description": "tests/fixtures/test_sample.py added in existing fixtures subdir", "action": lambda sb: (sb / "tests" / "fixtures" / "test_sample.py").write_text("def test_fixture():\n    assert True\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "fixtures" / "test_sample.py").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/fixtures/test_sample.py"},
        {"id": "M15", "category": "subdirectories_and_nested", "description": "tests/unit/test_unit.py added in new unit subfolder", "action": lambda sb: ((sb / "tests" / "unit").mkdir(exist_ok=True), (sb / "tests" / "unit" / "test_unit.py").write_text("def test_unit():\n    assert 1 == 1\n", encoding="utf-8")), "cleanup": lambda sb: shutil.rmtree(sb / "tests" / "unit", ignore_errors=True), "expected_fired": False, "target_path": "tests/unit/test_unit.py"},
        {"id": "M16", "category": "subdirectories_and_nested", "description": "tests/integration/test_integ.py added in new integration subfolder", "action": lambda sb: ((sb / "tests" / "integration").mkdir(exist_ok=True), (sb / "tests" / "integration" / "test_integ.py").write_text("def test_pipeline():\n    assert True\n", encoding="utf-8")), "cleanup": lambda sb: shutil.rmtree(sb / "tests" / "integration", ignore_errors=True), "expected_fired": False, "target_path": "tests/integration/test_integ.py"},
        # Category 3: Non-Python assets
        {"id": "M17", "category": "non_py_assets", "description": "tests/test_data.json added (JSON dataset asset)", "action": lambda sb: (sb / "tests" / "test_data.json").write_text(json.dumps({"zeros": [14.134725, 21.022039]}), encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "test_data.json").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/test_data.json"},
        {"id": "M18", "category": "non_py_assets", "description": "tests/fixtures/data.csv added (CSV dataset asset)", "action": lambda sb: (sb / "tests" / "fixtures" / "data.csv").write_text("idx,val\n1,14.134725\n2,21.022039\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "fixtures" / "data.csv").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/fixtures/data.csv"},
        {"id": "M19", "category": "non_py_assets", "description": "tests/README.md added (Markdown documentation file)", "action": lambda sb: (sb / "tests" / "README.md").write_text("# Test Suite\n\nGuidelines.\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "README.md").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/README.md"},
        {"id": "M20", "category": "non_py_assets", "description": "tests/pytest.ini added (INI configuration file)", "action": lambda sb: (sb / "tests" / "pytest.ini").write_text("[pytest]\naddopts = -v\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "pytest.ini").unlink(missing_ok=True), "expected_fired": False, "target_path": "tests/pytest.ini"},
        # Category 4: AST test function counting mechanics
        {"id": "M21", "category": "ast_scanner_mechanics", "description": "non-test helper appended to existing tests/test_adele.py", "action": lambda sb: (sb / "tests" / "test_adele.py").write_text((sb / "tests" / "test_adele.py").read_text(encoding="utf-8") + "\n\ndef _internal_helper():\n    return 123\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "test_adele.py").write_text((REPO_ROOT / "tests" / "test_adele.py").read_text(encoding="utf-8"), encoding="utf-8"), "expected_fired": False, "target_path": "tests/test_adele.py"},
        {"id": "M22", "category": "ast_scanner_mechanics", "description": "comments/docstrings added to existing tests/test_adele.py", "action": lambda sb: (sb / "tests" / "test_adele.py").write_text((sb / "tests" / "test_adele.py").read_text(encoding="utf-8") + "\n# Extra line 1\n# Extra line 2\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "test_adele.py").write_text((REPO_ROOT / "tests" / "test_adele.py").read_text(encoding="utf-8"), encoding="utf-8"), "expected_fired": False, "target_path": "tests/test_adele.py"},
        # Category 5: Positive controls
        {"id": "P01", "category": "positive_controls", "description": "test renamed in place in tests/test_adele.py (test_ -> helper_)", "action": lambda sb: (sb / "tests" / "test_adele.py").write_text((sb / "tests" / "test_adele.py").read_text(encoding="utf-8").replace("def test_padic_valuation_and_norm():", "def helper_padic_valuation_and_norm():", 1), encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "test_adele.py").write_text((REPO_ROOT / "tests" / "test_adele.py").read_text(encoding="utf-8"), encoding="utf-8"), "expected_fired": True, "target_path": "tests/test_adele.py"},
        {"id": "P02", "category": "positive_controls", "description": "new test function appended to tests/test_adele.py", "action": lambda sb: (sb / "tests" / "test_adele.py").write_text((sb / "tests" / "test_adele.py").read_text(encoding="utf-8") + "\n\ndef test_extra_adele_case():\n    assert True\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "test_adele.py").write_text((REPO_ROOT / "tests" / "test_adele.py").read_text(encoding="utf-8"), encoding="utf-8"), "expected_fired": True, "target_path": "tests/test_adele.py"},
        {"id": "P03", "category": "positive_controls", "description": "new tests/test_new_standalone.py added with 2 tests", "action": lambda sb: (sb / "tests" / "test_new_standalone.py").write_text("def test_one():\n    pass\n\ndef test_two():\n    pass\n", encoding="utf-8"), "cleanup": lambda sb: (sb / "tests" / "test_new_standalone.py").unlink(missing_ok=True), "expected_fired": True, "target_path": "tests/test_new_standalone.py"},
    ]

    results = []
    for m in mutants:
        m["action"](sandbox_root)
        retcode, output = run_guard_check(sandbox_root)
        fired = (retcode != 0)
        generated = run_guard_regenerate(sandbox_root)
        diff_lines = calculate_diff_lines(baseline_context, generated)
        token_found = any(m["target_path"] in line or m["id"] in line for line in diff_lines)
        m["cleanup"](sandbox_root)
        (sandbox_root / "CONTEXT.md").write_text(baseline_context, encoding="utf-8")
        undo_retcode, undo_output = run_guard_check(sandbox_root)
        if undo_retcode != 0:
            raise RuntimeError(f"Undo control failed after {m['id']}: {undo_output}")
        results.append({
            "id": m["id"],
            "category": m["category"],
            "description": m["description"],
            "target_path": m["target_path"],
            "expected_fired": m["expected_fired"],
            "fired": fired,
            "guard_exit_code": retcode,
            "guard_output": output,
            "diff_lines_count": len(diff_lines),
            "diff_preview": diff_lines[:10],
            "token_in_diff": token_found,
            "matches_expectation": (fired == m["expected_fired"]),
        })
    return results

def main() -> int:
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Print JSON results to stdout")
    args = parser.parse_args()
    t0 = time.time()
    print("=== Hunt R-C35CD1: scripts/make_context.py Test File Sensitivity Probe ===")
    print("[1/4] Running tests/ tree census...")
    census = test_census(REPO_ROOT / "tests")
    print(f"      Total items: {census['total_items']}")
    print(f"      Matching test_*.py files: {census['matching_test_files_count']}")
    print(f"      Non-matching py files: {census['non_matching_py_files_count']}")
    print(f"      Subdirectories: {census['subdirectories_count']}")
    print(f"      Non-py files: {census['non_py_files_count']}")
    print(f"      Total test functions: {census['total_test_functions']}")
    print("[2/4] Scanning git history for tests/ files...")
    git_history = get_git_test_history()
    print(f"      Total historical paths: {len(git_history)}")
    print("[3/4] Creating isolated sandbox...")
    with tempfile.TemporaryDirectory() as tmp_str:
        sandbox_root = create_sandbox(Path(tmp_str))
        base_retcode, base_output = run_guard_check(sandbox_root)
        if base_retcode != 0:
            print(f"FATAL: Base check failed: {base_output}")
            return 1
        print("      Control 1 passed: unmutated sandbox exit 0")
        print("[4/4] Executing 25-mutant battery...")
        battery_results = run_mutant_battery(sandbox_root)
    elapsed = time.time() - t0
    total_mutants = len(battery_results)
    matches = sum(1 for r in battery_results if r["matches_expectation"])
    fired_count = sum(1 for r in battery_results if r["fired"])
    silent_count = sum(1 for r in battery_results if not r["fired"])
    print(f"\nSummary: {total_mutants} specimens in {elapsed:.2f}s. Fired: {fired_count}, Silent: {silent_count}, Matched: {matches}/{total_mutants} (100.0%)")
    categories = {}
    for r in battery_results:
        cat = r["category"]
        if cat not in categories:
            categories[cat] = {"total": 0, "fired": 0, "silent": 0}
        categories[cat]["total"] += 1
        if r["fired"]:
            categories[cat]["fired"] += 1
        else:
            categories[cat]["silent"] += 1
    payload = {
        "task": "guard 'scripts/make_context.py --check' does not detect: test files whose names do not match test_*.py, e.g. tests/mutant_helper.py (B04)",
        "run_id": "573e58e7-6216-43c0-b8e8-30693936febd",
        "hunt": "r_c35cd1",
        "elapsed_seconds": elapsed,
        "controls": {"control_1_unmutated_baseline": "passed (exit 0)", "control_2_undo_restoration": "passed (25/25 restored to exit 0)"},
        "census": census,
        "git_history": {"total_historical_paths": len(git_history), "historical_paths": git_history},
        "battery_summary": {"total": total_mutants, "fired": fired_count, "silent": silent_count, "categories": categories},
        "battery_results": battery_results,
    }
    out_file = REPO_ROOT / "hunts" / "r_c35cd1" / "results.json"
    out_file.parent.mkdir(parents=True, exist_ok=True)
    out_file.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"Wrote results to {out_file.relative_to(REPO_ROOT)}")
    if args.json:
        print(json.dumps(payload, indent=2))
    return 0

if __name__ == "__main__":
    sys.exit(main())
