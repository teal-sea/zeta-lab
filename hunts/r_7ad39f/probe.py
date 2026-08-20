#!/usr/bin/env python3
"""Hunt R-7AD39F: probe measuring make_context.py --check sensitivity to in-place private-to-public helper renames.

This probe measures whether and under what conditions scripts/make_context.py --check
detects private helpers renamed to public names in place across all repository modules,
isolating the __all__ filter mechanism from the line-count tell.
"""

from __future__ import annotations

import argparse
import ast
import difflib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))
import scripts.make_context as mc

SCANNED_DIRS = ["zeta", "ontology", "harness", "dossier", "docs", "scripts", "tests"]
EXTRA_FILES = ["CONTEXT.md"]


@dataclass
class Mutant:
    mid: str
    category: str
    description: str
    expected_fired: bool
    rationale: str
    apply_fn: Callable[[Path], None]
    token: str = ""
    line_count_changes: bool = False
    has_all: bool = True


def _replace_exact(root: Path, rel_path: str, old: str, new: str) -> None:
    target = root / rel_path
    text = target.read_text(encoding="utf-8")
    if old not in text:
        raise ValueError(f"Pattern {old!r} not found in {rel_path}")
    target.write_text(text.replace(old, new, 1), encoding="utf-8")


def _append_text(root: Path, rel_path: str, text_to_append: str) -> None:
    target = root / rel_path
    text = target.read_text(encoding="utf-8")
    target.write_text(text + text_to_append, encoding="utf-8")


# ---------------------------------------------------------------------------
# Battery of 25 curated mutants
# ---------------------------------------------------------------------------

CURATED_MUTANTS: list[Mutant] = [
    # Category 1: In-place length-neutral private helper rename in __all__ modules, WITHOUT __all__ edit
    Mutant(
        mid="M01",
        category="in-place private rename in __all__ module (no __all__ edit)",
        description="zeta/core.py: _num(s) -> pubnum(s) in place (same line count, not in __all__)",
        expected_fired=False,
        rationale="module_api filters top-level defs by __all__; in-place edit preserves line count, so CONTEXT.md is byte-identical",
        apply_fn=lambda r: _replace_exact(r, "zeta/core.py", "def _num(s):", "def pubnum(s):"),
        token="pubnum",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M02",
        category="in-place private rename in __all__ module (no __all__ edit)",
        description="zeta/epstein.py: _dh_mean_spacing -> pdh_mean_spacing in place (not in __all__)",
        expected_fired=False,
        rationale="epstein.py declares __all__; private helper renamed public in place is omitted from CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "zeta/epstein.py", "def _dh_mean_spacing(", "def pdh_mean_spacing("),
        token="pdh_mean_spacing",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M03",
        category="in-place private rename in __all__ module (no __all__ edit)",
        description="zeta/heatflow.py: _xi_local -> pxi_local in place (not in __all__)",
        expected_fired=False,
        rationale="heatflow.py declares __all__; length-neutral rename does not alter CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "zeta/heatflow.py", "def _xi_local(", "def pxi_local("),
        token="pxi_local",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M04",
        category="in-place private rename in __all__ module (no __all__ edit)",
        description="zeta/zeros.py: _rs_theta_local -> prs_theta_local in place (not in __all__)",
        expected_fired=False,
        rationale="zeros.py declares __all__; length-neutral rename does not alter CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "zeta/zeros.py", "def _rs_theta_local(", "def prs_theta_local("),
        token="prs_theta_local",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M05",
        category="in-place private rename in __all__ module (no __all__ edit)",
        description="zeta/rigor.py: _exact(value) -> pexact(value) in place (not in __all__)",
        expected_fired=False,
        rationale="rigor.py declares __all__; length-neutral rename does not alter CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "zeta/rigor.py", "def _exact(value)", "def pexact(value)"),
        token="pexact",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M06",
        category="in-place private rename in __all__ module (no __all__ edit)",
        description="ontology/registry.py: _role_reasons -> prole_reasons in place (not in __all__)",
        expected_fired=False,
        rationale="registry.py declares __all__; length-neutral rename does not alter CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "ontology/registry.py", "def _role_reasons(", "def prole_reasons("),
        token="prole_reasons",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M07",
        category="in-place private rename in __all__ module (no __all__ edit)",
        description="harness/integrity.py: _guard -> pguard in place (not in __all__)",
        expected_fired=False,
        rationale="integrity.py declares __all__; length-neutral rename does not alter CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "harness/integrity.py", "def _guard(", "def pguard("),
        token="pguard",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M08",
        category="in-place private rename in __all__ module (no __all__ edit)",
        description="dossier/report.py: _section -> psection in place (not in __all__)",
        expected_fired=False,
        rationale="dossier/report.py declares __all__; length-neutral rename does not alter CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "dossier/report.py", "def _section(", "def psection("),
        token="psection",
        line_count_changes=False,
        has_all=True,
    ),

    # Category 2: In-place length-neutral private helper rename in non-__all__ modules
    Mutant(
        mid="M09",
        category="in-place private rename in non-__all__ module",
        description="harness/demo.py: _section -> psection in place (no __all__ declared)",
        expected_fired=True,
        rationale="demo.py has no __all__; module_api indexes all public defs, so psection appears in CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "harness/demo.py", "def _section(", "def psection("),
        token="psection",
        line_count_changes=False,
        has_all=False,
    ),
    Mutant(
        mid="M10",
        category="in-place private rename in non-__all__ module",
        description="harness/demo.py: _department_block -> pdepartment_block in place (no __all__ declared)",
        expected_fired=True,
        rationale="demo.py has no __all__; new public function is indexed into CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "harness/demo.py", "def _department_block(", "def pdepartment_block("),
        token="pdepartment_block",
        line_count_changes=False,
        has_all=False,
    ),
    Mutant(
        mid="M11",
        category="in-place private rename in non-__all__ module",
        description="harness/demo.py: _the_turn -> pthe_turn in place (no __all__ declared)",
        expected_fired=True,
        rationale="demo.py has no __all__; new public function is indexed into CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "harness/demo.py", "def _the_turn(", "def pthe_turn("),
        token="pthe_turn",
        line_count_changes=False,
        has_all=False,
    ),
    Mutant(
        mid="M12",
        category="in-place private rename in non-__all__ module",
        description="harness/new_department.py: _valid_name -> pvalid_name in place (no __all__ declared)",
        expected_fired=True,
        rationale="new_department.py has no __all__; new public function is indexed into CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "harness/new_department.py", "def _valid_name(", "def pvalid_name("),
        token="pvalid_name",
        line_count_changes=False,
        has_all=False,
    ),

    # Category 3: In-place length-neutral private helper rename in __all__ module WITH __all__ edit
    Mutant(
        mid="M13",
        category="in-place private rename in __all__ module (WITH __all__ edit)",
        description="zeta/core.py: _num -> pubnum in place, and 'pubnum' replaces 'xi' in __all__ (same length)",
        expected_fired=True,
        rationale="__all__ now includes pubnum, so pubnum appears in CONTEXT.md and xi disappears",
        apply_fn=lambda r: (
            _replace_exact(r, "zeta/core.py", "def _num(s):", "def pubnum(s):"),
            _replace_exact(r, "zeta/core.py", '"xi",', '"pubnum",')
        ),
        token="pubnum",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M14",
        category="in-place private rename in __all__ module (WITH __all__ edit)",
        description="zeta/epstein.py: _dh_mean_spacing -> pdh_mean_spacing in place, and added to __all__ in-line",
        expected_fired=True,
        rationale="__all__ includes pdh_mean_spacing, so it reaches CONTEXT.md",
        apply_fn=lambda r: (
            _replace_exact(r, "zeta/epstein.py", "def _dh_mean_spacing(", "def pdh_mean_spacing("),
            _replace_exact(r, "zeta/epstein.py", '"epstein_zeta",', '"epstein_zeta", "pdh_mean_spacing",')
        ),
        token="pdh_mean_spacing",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M15",
        category="in-place private rename in __all__ module (WITH __all__ edit)",
        description="ontology/registry.py: _role_reasons -> prole_reasons in place, and replaces validate_domain in __all__",
        expected_fired=True,
        rationale="__all__ includes prole_reasons, so it reaches CONTEXT.md",
        apply_fn=lambda r: (
            _replace_exact(r, "ontology/registry.py", "def _role_reasons(", "def prole_reasons("),
            _replace_exact(r, "ontology/registry.py", '"validate_domain",', '"prole_reasons",')
        ),
        token="prole_reasons",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M16",
        category="in-place private rename in __all__ module (WITH __all__ edit)",
        description="harness/integrity.py: _guard -> pguard in place, and added to __all__ in-line",
        expected_fired=True,
        rationale="__all__ includes pguard, so it reaches CONTEXT.md",
        apply_fn=lambda r: (
            _replace_exact(r, "harness/integrity.py", "def _guard(", "def pguard("),
            _replace_exact(r, "harness/integrity.py", '"report_claim",', '"report_claim", "pguard",')
        ),
        token="pguard",
        line_count_changes=False,
        has_all=True,
    ),

    # Category 4: Non-length-neutral private helper rename in __all__ module (line-count tell)
    Mutant(
        mid="M17",
        category="non-length-neutral rename in __all__ module (line count changes)",
        description="zeta/core.py: _num -> pubnum with trailing blank line appended to file",
        expected_fired=True,
        rationale="File length increases by 1, so CONTEXT.md line count changes (*232 lines* -> *233 lines*) and guard fires",
        apply_fn=lambda r: (
            _replace_exact(r, "zeta/core.py", "def _num(s):", "def pubnum(s):"),
            _append_text(r, "zeta/core.py", "\n")
        ),
        token="pubnum",
        line_count_changes=True,
        has_all=True,
    ),
    Mutant(
        mid="M18",
        category="non-length-neutral rename in __all__ module (line count changes)",
        description="zeta/epstein.py: _dh_mean_spacing -> pdh_mean_spacing with trailing blank line appended",
        expected_fired=True,
        rationale="File length increases by 1, tripping line-count tell",
        apply_fn=lambda r: (
            _replace_exact(r, "zeta/epstein.py", "def _dh_mean_spacing(", "def pdh_mean_spacing("),
            _append_text(r, "zeta/epstein.py", "\n")
        ),
        token="pdh_mean_spacing",
        line_count_changes=True,
        has_all=True,
    ),
    Mutant(
        mid="M19",
        category="non-length-neutral rename in __all__ module (line count changes)",
        description="ontology/registry.py: _role_reasons -> prole_reasons with signature split across two lines",
        expected_fired=True,
        rationale="Signature split increases line count by 1, tripping line count tell",
        apply_fn=lambda r: _replace_exact(
            r,
            "ontology/registry.py",
            "def _role_reasons(obj: Any, role: str, methods: Sequence[str], attrs: Sequence[str]) -> list[str]:",
            "def prole_reasons(\n    obj: Any, role: str, methods: Sequence[str], attrs: Sequence[str]\n) -> list[str]:"
        ),
        token="prole_reasons",
        line_count_changes=True,
        has_all=True,
    ),
    Mutant(
        mid="M20",
        category="non-length-neutral rename in __all__ module (line count changes)",
        description="harness/integrity.py: _guard -> pguard with signature split across two lines",
        expected_fired=True,
        rationale="Line count increase trips CONTEXT.md line count check",
        apply_fn=lambda r: _replace_exact(
            r,
            "harness/integrity.py",
            "def _guard(name: str, thunk: Any) -> CheckResult:",
            "def pguard(\n    name: str, thunk: Any\n) -> CheckResult:"
        ),
        token="pguard",
        line_count_changes=True,
        has_all=True,
    ),

    # Category 5: Private classes and constants
    Mutant(
        mid="M21",
        category="private class in __all__ module (no __all__ edit)",
        description="zeta/rigor.py: class _PrecGuard -> class PPrecGuard in place (not in __all__)",
        expected_fired=False,
        rationale="Private class renamed to public class in place in __all__ module is ignored by module_api",
        apply_fn=lambda r: _replace_exact(r, "zeta/rigor.py", "class _PrecGuard:", "class PPrecGuard:"),
        token="PPrecGuard",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M22",
        category="private class in __all__ module (WITH __all__ edit)",
        description="zeta/rigor.py: class _PrecGuard -> class PPrecGuard and added to __all__ in-line",
        expected_fired=True,
        rationale="Class is in __all__, so it reaches CONTEXT.md classes list",
        apply_fn=lambda r: (
            _replace_exact(r, "zeta/rigor.py", "class _PrecGuard:", "class PPrecGuard:"),
            _replace_exact(r, "zeta/rigor.py", '"DATA_DIR",', '"DATA_DIR", "PPrecGuard",')
        ),
        token="PPrecGuard",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M23",
        category="private class in __all__ module (no __all__ edit)",
        description="harness/shams.py: class _AliasSubject -> class PAliasSubject in place (not in __all__)",
        expected_fired=False,
        rationale="shams.py declares __all__; length-neutral class rename without __all__ edit is silent",
        apply_fn=lambda r: _replace_exact(r, "harness/shams.py", "class _AliasSubject:", "class PAliasSubject:"),
        token="PAliasSubject",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M24",
        category="public constant added to __all__ module (length-neutral)",
        description="zeta/rigor.py: replace private constant with uppercase public constant in-line",
        expected_fired=True,
        rationale="module_api extracts all uppercase constants regardless of __all__; uppercase constant reaches CONTEXT.md",
        apply_fn=lambda r: _replace_exact(r, "zeta/rigor.py", "_LOG2_10 = 3.321928094887362", "PLOG2_10 = 3.321928094887362"),
        token="PLOG2_10",
        line_count_changes=False,
        has_all=True,
    ),
    Mutant(
        mid="M25",
        category="append blank line only (no symbol change)",
        description="zeta/core.py: append one blank line (control: line count tell alone)",
        expected_fired=True,
        rationale="Line count moves from 232 to 233, tripping guard with 0 symbol changes",
        apply_fn=lambda r: _append_text(r, "zeta/core.py", "\n"),
        token="",
        line_count_changes=True,
        has_all=True,
    ),
]


# ---------------------------------------------------------------------------
# Sandbox runner and oracles
# ---------------------------------------------------------------------------


def build_sandbox(dest: Path) -> None:
    ignore = shutil.ignore_patterns("__pycache__", "*.pyc", ".pytest_cache", ".venv")
    for name in SCANNED_DIRS:
        src = REPO / name
        if src.is_dir():
            shutil.copytree(src, dest / name, ignore=ignore)
    for name in EXTRA_FILES:
        src = REPO / name
        if src.is_file():
            shutil.copy2(src, dest / name)


def run_guard(root: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [sys.executable, str(root / "scripts" / "make_context.py"), "--check"],
        capture_output=True,
        text=True,
        timeout=300,
    )
    return proc.returncode, (proc.stdout + proc.stderr).strip()


def regenerate_context(root: Path) -> str:
    subprocess.run(
        [sys.executable, str(root / "scripts" / "make_context.py")],
        capture_output=True,
        text=True,
        timeout=300,
        check=True,
    )
    return (root / "CONTEXT.md").read_text(encoding="utf-8")


def snapshot(root: Path) -> dict[str, bytes]:
    return {
        str(p.relative_to(root)): p.read_bytes()
        for p in root.rglob("*")
        if p.is_file() and not p.name.startswith(".")
    }


def restore_full(root: Path, snap: dict[str, bytes]) -> None:
    for path in list(root.rglob("*")):
        if path.is_file() and not path.name.startswith("."):
            rel = str(path.relative_to(root))
            if rel not in snap:
                path.unlink()
    for rel, data in snap.items():
        path = root / rel
        if not path.exists() or path.read_bytes() != data:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)


def diff_stats(before: str, after: str, token: str) -> dict:
    changed = [
        line
        for line in difflib.unified_diff(
            before.splitlines(), after.splitlines(), lineterm="", n=0
        )
        if line.startswith(("+", "-")) and not line.startswith(("+++", "---"))
    ]
    return {
        "context_diff_lines": len(changed),
        "token": token,
        "token_in_diff": bool(token) and any(token in line for line in changed),
    }


# ---------------------------------------------------------------------------
# Full Repository Census
# ---------------------------------------------------------------------------


def perform_census() -> dict:
    modules = []
    scanned_categories = [
        ("zeta", REPO / "zeta"),
        ("ontology", REPO / "ontology"),
        ("harness", REPO / "harness"),
        ("dossier", REPO / "dossier"),
    ]

    total_modules = 0
    modules_with_all = 0
    modules_without_all = 0
    total_private_funcs_in_all = 0
    total_private_classes_in_all = 0
    total_private_funcs_without_all = 0
    total_private_classes_without_all = 0

    for cat, dir_path in scanned_categories:
        for py_path in sorted(dir_path.glob("*.py")):
            if py_path.name.startswith("."):
                continue
            total_modules += 1
            text = py_path.read_text(encoding="utf-8")
            tree = ast.parse(text)

            has_all = False
            declared_exports = []
            for node in tree.body:
                if isinstance(node, ast.Assign) and any(
                    isinstance(t, ast.Name) and t.id == "__all__" for t in node.targets
                ):
                    has_all = True
                    try:
                        declared_exports = [str(v) for v in ast.literal_eval(node.value)]
                    except Exception:
                        declared_exports = []

            priv_funcs = []
            priv_classes = []
            pub_funcs = []
            pub_classes = []

            for node in tree.body:
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if node.name.startswith("_"):
                        priv_funcs.append(node.name)
                    else:
                        pub_funcs.append(node.name)
                elif isinstance(node, ast.ClassDef):
                    if node.name.startswith("_"):
                        priv_classes.append(node.name)
                    else:
                        pub_classes.append(node.name)

            if has_all:
                modules_with_all += 1
                total_private_funcs_in_all += len(priv_funcs)
                total_private_classes_in_all += len(priv_classes)
            else:
                modules_without_all += 1
                total_private_funcs_without_all += len(priv_funcs)
                total_private_classes_without_all += len(priv_classes)

            modules.append({
                "rel_path": f"{cat}/{py_path.name}",
                "category": cat,
                "has_all": has_all,
                "declared_exports_count": len(declared_exports),
                "private_functions": priv_funcs,
                "private_classes": priv_classes,
                "public_functions_count": len(pub_funcs),
                "public_classes_count": len(pub_classes),
                "line_count": len(text.splitlines()),
            })

    return {
        "total_modules": total_modules,
        "modules_with_all": modules_with_all,
        "modules_with_all_pct": round(modules_with_all / total_modules * 100, 2),
        "modules_without_all": modules_without_all,
        "modules_without_all_pct": round(modules_without_all / total_modules * 100, 2),
        "total_private_symbols_in_all_modules": total_private_funcs_in_all + total_private_classes_in_all,
        "private_funcs_in_all_modules": total_private_funcs_in_all,
        "private_classes_in_all_modules": total_private_classes_in_all,
        "total_private_symbols_in_no_all_modules": total_private_funcs_without_all + total_private_classes_without_all,
        "private_funcs_in_no_all_modules": total_private_funcs_without_all,
        "private_classes_in_no_all_modules": total_private_classes_without_all,
        "modules": modules,
    }


# ---------------------------------------------------------------------------
# Automated Exhaustive Evaluation of All Private Symbols via module_api
# ---------------------------------------------------------------------------


def run_exhaustive_mutation(census: dict) -> dict:
    tested_in_all_modules = 0
    missed_in_all_modules = 0
    fired_in_all_modules = 0

    tested_in_no_all_modules = 0
    missed_in_no_all_modules = 0
    fired_in_no_all_modules = 0

    records = []

    for mod in census["modules"]:
        rel_path = mod["rel_path"]
        file_path = REPO / rel_path
        has_all = mod["has_all"]
        all_privates = mod["private_functions"] + mod["private_classes"]
        orig_text = file_path.read_text(encoding="utf-8")
        orig_api = mc.module_api(file_path)

        with tempfile.NamedTemporaryFile(mode="w+", suffix=".py", delete=False) as tmp_file:
            tmp_path = Path(tmp_file.name)
            try:
                for priv_name in all_privates:
                    pub_name = "p" + priv_name.lstrip("_")

                    # Replace definition in-place
                    replaced = False
                    old_def = f"def {priv_name}("
                    new_def = f"def {pub_name}("
                    if old_def in orig_text:
                        text_mut = orig_text.replace(old_def, new_def, 1)
                        replaced = True
                    else:
                        old_cls = f"class {priv_name}"
                        new_cls = f"class {pub_name}"
                        if old_cls in orig_text:
                            text_mut = orig_text.replace(old_cls, new_cls, 1)
                            replaced = True

                    if not replaced:
                        continue

                    tmp_path.write_text(text_mut, encoding="utf-8")
                    mut_api = mc.module_api(tmp_path)

                    # Does the API change? (functions, classes, constants, lines)
                    api_changed = (
                        mut_api["functions"] != orig_api["functions"] or
                        mut_api["classes"] != orig_api["classes"] or
                        mut_api["constants"] != orig_api["constants"] or
                        mut_api["lines"] != orig_api["lines"]
                    )
                    # If api_changed is True, CONTEXT.md changes, so make_context.py --check fires
                    fired = api_changed

                    if has_all:
                        tested_in_all_modules += 1
                        if fired:
                            fired_in_all_modules += 1
                        else:
                            missed_in_all_modules += 1
                    else:
                        tested_in_no_all_modules += 1
                        if fired:
                            fired_in_no_all_modules += 1
                        else:
                            missed_in_no_all_modules += 1

                    records.append({
                        "module": rel_path,
                        "has_all": has_all,
                        "symbol": priv_name,
                        "mutated_to": pub_name,
                        "fired": fired,
                        "api_changed": api_changed,
                    })
            finally:
                if tmp_path.exists():
                    tmp_path.unlink()

    return {
        "in_all_modules": {
            "tested": tested_in_all_modules,
            "fired": fired_in_all_modules,
            "missed": missed_in_all_modules,
            "detection_rate_pct": round(fired_in_all_modules / (tested_in_all_modules or 1) * 100, 2),
        },
        "in_no_all_modules": {
            "tested": tested_in_no_all_modules,
            "fired": fired_in_no_all_modules,
            "missed": missed_in_no_all_modules,
            "detection_rate_pct": round(fired_in_no_all_modules / (tested_in_no_all_modules or 1) * 100, 2),
        },
        "records_sample": records[:10],
    }


# ---------------------------------------------------------------------------
# Main Entry Point
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(description="Probe make_context.py --check private rename sensitivity")
    parser.add_argument("--json", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()

    print("Running Hunt R-7AD39F Probe...", flush=True)
    census = perform_census()
    print(f"Census: {census['total_modules']} modules ({census['modules_with_all']} with __all__, {census['modules_without_all']} without __all__)", flush=True)
    print(f"Private symbols in __all__ modules: {census['total_private_symbols_in_all_modules']}", flush=True)
    print(f"Private symbols in non-__all__ modules: {census['total_private_symbols_in_no_all_modules']}", flush=True)

    with tempfile.TemporaryDirectory(prefix="r7ad39f-") as tmp:
        root = Path(tmp) / "tree"
        root.mkdir()
        build_sandbox(root)

        # Control 1: Unmutated sandbox reproduces CONTEXT.md
        rc0, msg0 = run_guard(root)
        print(f"[Control 1] Unmutated sandbox: exit={rc0} ({msg0})", flush=True)
        if rc0 != 0:
            print("ERROR: Unmutated sandbox failed make_context.py --check!", file=sys.stderr, flush=True)
            return 2
        baseline_context = (root / "CONTEXT.md").read_text(encoding="utf-8")
        snap = snapshot(root)

        # Run curated battery
        print("\n--- Running Curated Battery (25 Mutants) ---", flush=True)
        curated_results = []
        for m in CURATED_MUTANTS:
            m.apply_fn(root)
            rc, msg = run_guard(root)
            fired = (rc != 0)
            new_context = regenerate_context(root)
            stats = diff_stats(baseline_context, new_context, m.token)

            # Control 2: Undo check
            restore_full(root, snap)
            rc_undo, msg_undo = run_guard(root)
            if rc_undo != 0:
                print(f"ERROR: Undo failed for mutant {m.mid}!", file=sys.stderr, flush=True)
                return 3

            match_expected = (fired == m.expected_fired)
            curated_results.append({
                "id": m.mid,
                "category": m.category,
                "description": m.description,
                "has_all": m.has_all,
                "line_count_changes": m.line_count_changes,
                "expected_fired": m.expected_fired,
                "fired": fired,
                "matches_expected": match_expected,
                "diff_lines": stats["context_diff_lines"],
                "token": stats["token"],
                "token_in_diff": stats["token_in_diff"],
                "exit_code": rc,
                "output_message": msg,
                "rationale": m.rationale,
            })
            status_str = "PASS" if match_expected else "FAIL"
            print(f"[{status_str}] {m.mid} | Fired: {str(fired):5} (Expected: {str(m.expected_fired):5}) | Diff: {stats['context_diff_lines']:2} lines | {m.description}", flush=True)

        # Run exhaustive mutation over all private symbols
        print("\n--- Running Exhaustive Mutation Over All Repository Private Symbols ---", flush=True)
        exhaustive_results = run_exhaustive_mutation(census)
        print(f"In __all__ modules: {exhaustive_results['in_all_modules']['fired']}/{exhaustive_results['in_all_modules']['tested']} fired ({exhaustive_results['in_all_modules']['detection_rate_pct']}%)", flush=True)
        print(f"In non-__all__ modules: {exhaustive_results['in_no_all_modules']['fired']}/{exhaustive_results['in_no_all_modules']['tested']} fired ({exhaustive_results['in_no_all_modules']['detection_rate_pct']}%)", flush=True)

        output_data = {
            "hunt_id": "r_7ad39f",
            "task": "guard 'scripts/make_context.py --check' does not detect: a private helper renamed public *in place*, in a module that declares __all__, by a length-neutral edit",
            "controls": {
                "control_1_unmutated_baseline_exit_code": rc0,
                "control_1_message": msg0,
                "control_2_all_undos_clean": True,
            },
            "census": census,
            "curated_battery": curated_results,
            "exhaustive_mutation": exhaustive_results,
            "summary": {
                "curated_total": len(curated_results),
                "curated_matched_expected": sum(1 for r in curated_results if r["matches_expected"]),
                "in_all_module_length_neutral_private_rename_detection_rate": exhaustive_results["in_all_modules"]["detection_rate_pct"],
                "no_all_module_length_neutral_private_rename_detection_rate": exhaustive_results["in_no_all_modules"]["detection_rate_pct"],
            },
        }

        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(output_data, indent=2), encoding="utf-8")
        print(f"\nWrote results to {args.json}", flush=True)

    return 0


if __name__ == "__main__":
    sys.exit(main())
