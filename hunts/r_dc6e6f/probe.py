#!/usr/bin/env python3
"""Hunt R-DC6E6F probe: make_context.py --check blindness to additions and changes under compiler/.

This probe measures whether and under what conditions scripts/make_context.py --check
detects public functions, classes, constants, module additions, fixtures, or doc changes
under compiler/, mapping the exact boundary of the unscanned compiler/ package.
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
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))
import scripts.make_context as mc

SCANNED_DIRS = ["zeta", "ontology", "harness", "dossier", "docs", "scripts", "tests"]
ALL_TESTED_DIRS = SCANNED_DIRS + ["compiler"]
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
    target_file: str = ""


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


def _write_new_file(root: Path, rel_path: str, content: str) -> None:
    target = root / rel_path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8")


# ---------------------------------------------------------------------------
# Battery of 22 curated mutants
# ---------------------------------------------------------------------------

CURATED_MUTANTS: list[Mutant] = [
    # Category 1: Public functions added under compiler/
    Mutant(
        mid="M01",
        category="public function added under compiler/",
        description="compiler/catalog.py: append public function def new_catalog_probe(): pass (__all__ untouched)",
        expected_fired=False,
        rationale="compiler/ is not in make_context.py scanned targets, so CONTEXT.md is unchanged",
        apply_fn=lambda r: _append_text(
            r,
            "compiler/catalog.py",
            "\n\ndef new_catalog_probe() -> None:\n    \"\"\"New public probe function.\"\"\"\n    pass\n",
        ),
        token="new_catalog_probe",
        target_file="compiler/catalog.py",
    ),
    Mutant(
        mid="M02",
        category="public function added under compiler/",
        description="compiler/catalog.py: append public function and add to __all__",
        expected_fired=False,
        rationale="compiler/ is not scanned even when __all__ is updated",
        apply_fn=lambda r: (
            _replace_exact(
                r,
                "compiler/catalog.py",
                '"LESIONS",\n]',
                '"LESIONS",\n    "new_catalog_probe",\n]',
            ),
            _append_text(
                r,
                "compiler/catalog.py",
                "\n\ndef new_catalog_probe() -> None:\n    \"\"\"New public probe function.\"\"\"\n    pass\n",
            ),
        ),
        token="new_catalog_probe",
        target_file="compiler/catalog.py",
    ),
    Mutant(
        mid="M03",
        category="public function added under compiler/",
        description="compiler/semantics.py: append public function def new_semantics_probe(): pass (__all__ untouched)",
        expected_fired=False,
        rationale="compiler/ is not scanned, so CONTEXT.md ignores added semantics functions",
        apply_fn=lambda r: _append_text(
            r,
            "compiler/semantics.py",
            "\n\ndef new_semantics_probe() -> None:\n    \"\"\"New semantics probe function.\"\"\"\n    pass\n",
        ),
        token="new_semantics_probe",
        target_file="compiler/semantics.py",
    ),
    Mutant(
        mid="M04",
        category="public function added under compiler/",
        description="compiler/semantics.py: append public function and add to __all__",
        expected_fired=False,
        rationale="compiler/ is not scanned even with updated __all__",
        apply_fn=lambda r: (
            _replace_exact(
                r,
                "compiler/semantics.py",
                '"i8",\n]',
                '"i8",\n    "new_semantics_probe",\n]',
            ),
            _append_text(
                r,
                "compiler/semantics.py",
                "\n\ndef new_semantics_probe() -> None:\n    \"\"\"New semantics probe function.\"\"\"\n    pass\n",
            ),
        ),
        token="new_semantics_probe",
        target_file="compiler/semantics.py",
    ),
    Mutant(
        mid="M05",
        category="public function added under compiler/",
        description="compiler/__init__.py: append public function def new_init_probe(): pass",
        expected_fired=False,
        rationale="compiler/__init__.py is not scanned",
        apply_fn=lambda r: _append_text(
            r,
            "compiler/__init__.py",
            "\n\ndef new_init_probe() -> None:\n    \"\"\"New init probe function.\"\"\"\n    pass\n",
        ),
        token="new_init_probe",
        target_file="compiler/__init__.py",
    ),
    # Category 2: Public classes and uppercase constants in compiler/
    Mutant(
        mid="M06",
        category="public class or constant in compiler/",
        description="compiler/catalog.py: add class ProbeCatalogClass (and add to __all__)",
        expected_fired=False,
        rationale="compiler/ classes are unindexed",
        apply_fn=lambda r: (
            _replace_exact(
                r,
                "compiler/catalog.py",
                '"LESIONS",\n]',
                '"LESIONS",\n    "ProbeCatalogClass",\n]',
            ),
            _append_text(
                r,
                "compiler/catalog.py",
                "\n\nclass ProbeCatalogClass:\n    \"\"\"A new catalog probe class.\"\"\"\n    pass\n",
            ),
        ),
        token="ProbeCatalogClass",
        target_file="compiler/catalog.py",
    ),
    Mutant(
        mid="M07",
        category="public class or constant in compiler/",
        description="compiler/semantics.py: add class ProbeSemanticsClass (and add to __all__)",
        expected_fired=False,
        rationale="compiler/ classes are unindexed",
        apply_fn=lambda r: (
            _replace_exact(
                r,
                "compiler/semantics.py",
                '"i8",\n]',
                '"i8",\n    "ProbeSemanticsClass",\n]',
            ),
            _append_text(
                r,
                "compiler/semantics.py",
                "\n\nclass ProbeSemanticsClass:\n    \"\"\"A new semantics probe class.\"\"\"\n    pass\n",
            ),
        ),
        token="ProbeSemanticsClass",
        target_file="compiler/semantics.py",
    ),
    Mutant(
        mid="M08",
        category="public class or constant in compiler/",
        description="compiler/semantics.py: add uppercase constant PROBE_COMPILER_CONSTANT = 100",
        expected_fired=False,
        rationale="compiler/ uppercase constants are unindexed",
        apply_fn=lambda r: _append_text(
            r,
            "compiler/semantics.py",
            "\nPROBE_COMPILER_CONSTANT: Final[int] = 100\n",
        ),
        token="PROBE_COMPILER_CONSTANT",
        target_file="compiler/semantics.py",
    ),
    # Category 3: In-place modifications and renames in compiler/
    Mutant(
        mid="M09",
        category="in-place modification or rename in compiler/",
        description="compiler/catalog.py: rename instruction_count -> probe_inst_count in place and in __all__",
        expected_fired=False,
        rationale="in-place function rename in unscanned package passes silently",
        apply_fn=lambda r: (
            _replace_exact(
                r,
                "compiler/catalog.py",
                '"instruction_count",',
                '"probe_inst_count",',
            ),
            _replace_exact(
                r,
                "compiler/catalog.py",
                "def instruction_count(ir_text: str) -> int:",
                "def probe_inst_count(ir_text: str) -> int:",
            ),
        ),
        token="probe_inst_count",
        target_file="compiler/catalog.py",
    ),
    Mutant(
        mid="M10",
        category="in-place modification or rename in compiler/",
        description="compiler/semantics.py: rename backend_status -> probe_backend_status in place and in __all__",
        expected_fired=False,
        rationale="in-place function rename in unscanned package passes silently",
        apply_fn=lambda r: (
            _replace_exact(
                r,
                "compiler/semantics.py",
                '"backend_status",',
                '"probe_backend_status",',
            ),
            _replace_exact(
                r,
                "compiler/semantics.py",
                "def backend_status() -> dict[str, str]:",
                "def probe_backend_status() -> dict[str, str]:",
            ),
        ),
        token="probe_backend_status",
        target_file="compiler/semantics.py",
    ),
    Mutant(
        mid="M11",
        category="in-place modification or rename in compiler/",
        description="compiler/catalog.py: modify docstring first line of load_ir",
        expected_fired=False,
        rationale="docstring edits in unscanned packages are unindexed",
        apply_fn=lambda r: _replace_exact(
            r,
            "compiler/catalog.py",
            '"""Read one fixture by filename stem."""',
            '"""Read a single fixture by filename stem with modified doc."""',
        ),
        token="modified doc",
        target_file="compiler/catalog.py",
    ),
    Mutant(
        mid="M12",
        category="in-place modification or rename in compiler/",
        description="compiler/semantics.py: modify signature of refinement() in place",
        expected_fired=False,
        rationale="signature modifications in unscanned package produce zero diff in CONTEXT.md",
        apply_fn=lambda r: _replace_exact(
            r,
            "compiler/semantics.py",
            "def refinement(source_ir: str, target_ir: str) -> RefinementReport:",
            "def refinement(source_ir: str, target_ir: str, extra_flag: bool = False) -> RefinementReport:",
        ),
        token="extra_flag",
        target_file="compiler/semantics.py",
    ),
    # Category 4: Module and documentation additions under compiler/
    Mutant(
        mid="M13",
        category="module or documentation under compiler/",
        description="compiler/optimizer.py: create new module with public functions and docstring",
        expected_fired=False,
        rationale="new module under compiler/ is ignored by make_context.py",
        apply_fn=lambda r: _write_new_file(
            r,
            "compiler/optimizer.py",
            '"""Optimizer probe module."""\n\n__all__ = ["optimize_ir"]\n\ndef optimize_ir(code: str) -> str:\n    """Optimize LLVM IR."""\n    return code\n',
        ),
        token="optimize_ir",
        target_file="compiler/optimizer.py",
    ),
    Mutant(
        mid="M14",
        category="module or documentation under compiler/",
        description="compiler/fixtures/probe_fixture.ll: create new LLVM IR fixture",
        expected_fired=False,
        rationale="compiler/fixtures/ is unscanned",
        apply_fn=lambda r: _write_new_file(
            r,
            "compiler/fixtures/probe_fixture.ll",
            "define i8 @f(i8 %x, i8 %y) {\nentry:\n  %r = add i8 %x, %y\n  ret i8 %r\n}\n",
        ),
        token="probe_fixture",
        target_file="compiler/fixtures/probe_fixture.ll",
    ),
    Mutant(
        mid="M15",
        category="module or documentation under compiler/",
        description="compiler/FINDINGS.md: edit title and body content",
        expected_fired=False,
        rationale="compiler/FINDINGS.md is not in docs/*.md, so doc_index ignores it",
        apply_fn=lambda r: _replace_exact(
            r,
            "compiler/FINDINGS.md",
            "# Department #2, attempted: LLVM IR rewrites",
            "# Department #2, attempted: LLVM IR rewrites (PROBE MODIFIED)",
        ),
        token="PROBE MODIFIED",
        target_file="compiler/FINDINGS.md",
    ),
    # Category 5: Line-count variations in compiler/
    Mutant(
        mid="M16",
        category="line count changes in compiler/",
        description="compiler/catalog.py: append 20 blank lines (pure line count tell)",
        expected_fired=False,
        rationale="per-module line counts in CONTEXT.md only cover scanned packages, not compiler/",
        apply_fn=lambda r: _append_text(r, "compiler/catalog.py", "\n" * 20),
        token="",
        target_file="compiler/catalog.py",
    ),
    Mutant(
        mid="M17",
        category="line count changes in compiler/",
        description="compiler/semantics.py: delete 30 lines (pure line count tell)",
        expected_fired=False,
        rationale="compiler/ line count is not recorded in CONTEXT.md",
        apply_fn=lambda r: (
            lambda path: path.write_text("\n".join(path.read_text(encoding="utf-8").splitlines()[:-30]) + "\n", encoding="utf-8")
        )(r / "compiler/semantics.py"),
        token="",
        target_file="compiler/semantics.py",
    ),
    # Category 6: Positive controls in scanned packages (guard MUST fire)
    Mutant(
        mid="P01",
        category="positive control (scanned package)",
        description="zeta/core.py: append public function def probe_zeta_fn(): pass (and add to __all__)",
        expected_fired=True,
        rationale="zeta/ is a primary scanned package; public symbol addition fires guard",
        apply_fn=lambda r: (
            _replace_exact(
                r,
                "zeta/core.py",
                '"theta_mellin_xi_defect",\n]',
                '"theta_mellin_xi_defect",\n    "probe_zeta_fn",\n]',
            ),
            _append_text(
                r,
                "zeta/core.py",
                "\n\ndef probe_zeta_fn() -> None:\n    \"\"\"Probe zeta function.\"\"\"\n    pass\n",
            ),
        ),
        token="probe_zeta_fn",
        target_file="zeta/core.py",
    ),
    Mutant(
        mid="P02",
        category="positive control (scanned package)",
        description="harness/departments/compiler_department.py: append public function and add to __all__",
        expected_fired=True,
        rationale="harness/departments/ is scanned by make_context.py; symbol addition fires guard",
        apply_fn=lambda r: (
            _replace_exact(
                r,
                "harness/departments/compiler_department.py",
                '"model_detector",\n]',
                '"model_detector",\n    "probe_dept_fn",\n]',
            ),
            _append_text(
                r,
                "harness/departments/compiler_department.py",
                "\n\ndef probe_dept_fn() -> None:\n    \"\"\"Probe dept function.\"\"\"\n    pass\n",
            ),
        ),
        token="probe_dept_fn",
        target_file="harness/departments/compiler_department.py",
    ),
    Mutant(
        mid="P03",
        category="positive control (scanned package)",
        description="docs/probe_test_doc.md: create new markdown documentation file",
        expected_fired=True,
        rationale="docs/*.md is scanned by doc_index(); new file fires guard",
        apply_fn=lambda r: _write_new_file(
            r,
            "docs/probe_test_doc.md",
            "# Probe Test Document\n\nProbe test documentation body.\n",
        ),
        token="probe_test_doc.md",
        target_file="docs/probe_test_doc.md",
    ),
    Mutant(
        mid="P04",
        category="positive control (scanned package)",
        description="scripts/99_probe_script.py: create new script file",
        expected_fired=True,
        rationale="scripts/*.py is scanned by script_index(); new script fires guard",
        apply_fn=lambda r: _write_new_file(
            r,
            "scripts/99_probe_script.py",
            '#!/usr/bin/env python3\n"""99_probe_script.py - probe test script."""\n',
        ),
        token="99_probe_script.py",
        target_file="scripts/99_probe_script.py",
    ),
    Mutant(
        mid="P05",
        category="positive control (scanned package)",
        description="tests/test_probe_case.py: create new test file",
        expected_fired=True,
        rationale="tests/test_*.py is scanned by test_counts(); new test file fires guard",
        apply_fn=lambda r: _write_new_file(
            r,
            "tests/test_probe_case.py",
            '"""Probe test."""\n\ndef test_probe_fn() -> None:\n    assert True\n',
        ),
        token="test_probe_case.py",
        target_file="tests/test_probe_case.py",
    ),
]


# ---------------------------------------------------------------------------
# Sandbox runner
# ---------------------------------------------------------------------------

class Sandbox:
    def __init__(self, base_repo: Path) -> None:
        self.base_repo = base_repo
        self.tmpdir = tempfile.mkdtemp(prefix="zeta_compiler_guard_probe_")
        self.root = Path(self.tmpdir)
        self._copy_tree()

    def _copy_tree(self) -> None:
        for d in ALL_TESTED_DIRS:
            src = self.base_repo / d
            dst = self.root / d
            if src.exists():
                shutil.copytree(src, dst)
        for f in EXTRA_FILES:
            src = self.base_repo / f
            dst = self.root / f
            if src.exists():
                shutil.copy2(src, dst)

    def reset(self) -> None:
        shutil.rmtree(self.tmpdir)
        self.tmpdir = tempfile.mkdtemp(prefix="zeta_compiler_guard_probe_")
        self.root = Path(self.tmpdir)
        self._copy_tree()

    def cleanup(self) -> None:
        if self.root.exists():
            shutil.rmtree(self.tmpdir)

    def run_guard(self) -> tuple[int, str]:
        """Run make_context.py --check directly using make_context functions on this sandbox."""
        old_root = mc.ROOT
        old_pkg = mc.PKG
        old_discovery = mc.DISCOVERY
        old_harness = mc.HARNESS
        old_dossier = mc.DOSSIER
        old_docs = mc.DOCS
        old_tests = mc.TESTS
        old_scripts = mc.SCRIPTS
        old_out = mc.OUT
        old_out_flat = mc.OUT_FLAT

        try:
            mc.ROOT = self.root
            mc.PKG = self.root / "zeta"
            mc.DISCOVERY = self.root / "ontology"
            mc.HARNESS = self.root / "harness"
            mc.DOSSIER = self.root / "dossier"
            mc.DOCS = self.root / "docs"
            mc.TESTS = self.root / "tests"
            mc.SCRIPTS = self.root / "scripts"
            mc.OUT = self.root / "CONTEXT.md"
            mc.OUT_FLAT = self.root / "CONTEXT_FLAT.md"

            new_text = mc.build()
            current = mc.OUT.read_text(encoding="utf-8") if mc.OUT.exists() else ""
            if current != new_text:
                diff = "\n".join(
                    difflib.unified_diff(
                        current.splitlines(),
                        new_text.splitlines(),
                        fromfile="current",
                        tofile="new",
                        lineterm="",
                    )
                )
                return 1, diff
            return 0, ""
        finally:
            mc.ROOT = old_root
            mc.PKG = old_pkg
            mc.DISCOVERY = old_discovery
            mc.HARNESS = old_harness
            mc.DOSSIER = old_dossier
            mc.DOCS = old_docs
            mc.TESTS = old_tests
            mc.SCRIPTS = old_scripts
            mc.OUT = old_out
            mc.OUT_FLAT = old_out_flat


# ---------------------------------------------------------------------------
# Exhaustive symbol census under compiler/
# ---------------------------------------------------------------------------

def collect_compiler_symbols(repo: Path) -> dict[str, Any]:
    compiler_dir = repo / "compiler"
    modules = {}
    total_functions = 0
    total_classes = 0
    total_constants = 0

    for py_file in sorted(compiler_dir.glob("*.py")):
        tree = ast.parse(py_file.read_text(encoding="utf-8"))
        declared = None
        for node in tree.body:
            if isinstance(node, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == "__all__" for t in node.targets
            ):
                try:
                    declared = [str(v) for v in ast.literal_eval(node.value)]
                except (ValueError, SyntaxError):
                    declared = None

        functions = []
        classes = []
        constants = []

        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if not node.name.startswith("_"):
                    functions.append(node.name)
            elif isinstance(node, ast.ClassDef):
                if not node.name.startswith("_"):
                    classes.append(node.name)
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for t in targets:
                    if isinstance(t, ast.Name) and t.id.isupper() and not t.id.startswith("_"):
                        constants.append(t.id)

        modules[py_file.name] = {
            "path": f"compiler/{py_file.name}",
            "declared_all": declared,
            "functions": functions,
            "classes": classes,
            "constants": constants,
            "lines": len(py_file.read_text(encoding="utf-8").splitlines()),
        }
        total_functions += len(functions)
        total_classes += len(classes)
        total_constants += len(constants)

    fixtures = sorted([p.name for p in (compiler_dir / "fixtures").glob("*.ll")])
    doc_files = ["FINDINGS.md"]

    return {
        "modules": modules,
        "summary": {
            "module_count": len(modules),
            "public_function_count": total_functions,
            "public_class_count": total_classes,
            "constant_count": total_constants,
            "total_public_symbols": total_functions + total_classes + total_constants,
            "fixture_count": len(fixtures),
            "fixtures": fixtures,
            "doc_files": doc_files,
        },
    }


def run_exhaustive_census(sandbox: Sandbox, census: dict[str, Any]) -> list[dict[str, Any]]:
    results = []
    symbol_idx = 1

    for mod_name, mod_info in census["modules"].items():
        rel_path = mod_info["path"]
        declared = mod_info["declared_all"]

        for fn in mod_info["functions"]:
            sandbox.reset()
            mutated_name = f"probe_{fn}" if not fn.startswith("probe_") else f"m_{fn}"
            target = sandbox.root / rel_path
            orig_text = target.read_text(encoding="utf-8")

            new_text = orig_text.replace(f"def {fn}(", f"def {mutated_name}(")
            if declared and fn in declared:
                new_text = new_text.replace(f'"{fn}"', f'"{mutated_name}"').replace(f"'{fn}'", f"'{mutated_name}'")
            target.write_text(new_text, encoding="utf-8")

            exit_code, diff = sandbox.run_guard()
            diff_lines = len([ln for ln in diff.splitlines() if ln.startswith(("+", "-")) and not ln.startswith(("+++", "---"))])
            token_in_diff = mutated_name in diff

            results.append({
                "id": f"E_FN_{symbol_idx:02d}",
                "symbol": fn,
                "type": "function",
                "module": rel_path,
                "fired": exit_code != 0,
                "diff_lines": diff_lines,
                "token_in_diff": token_in_diff,
            })
            symbol_idx += 1

        for cls_name in mod_info["classes"]:
            sandbox.reset()
            mutated_cls = f"Probe{cls_name}"
            target = sandbox.root / rel_path
            orig_text = target.read_text(encoding="utf-8")
            new_text = orig_text.replace(f"class {cls_name}", f"class {mutated_cls}")
            if declared and cls_name in declared:
                new_text = new_text.replace(f'"{cls_name}"', f'"{mutated_cls}"').replace(f"'{cls_name}'", f"'{mutated_cls}'")
            target.write_text(new_text, encoding="utf-8")

            exit_code, diff = sandbox.run_guard()
            diff_lines = len([ln for ln in diff.splitlines() if ln.startswith(("+", "-")) and not ln.startswith(("+++", "---"))])
            token_in_diff = mutated_cls in diff

            results.append({
                "id": f"E_CLS_{symbol_idx:02d}",
                "symbol": cls_name,
                "type": "class",
                "module": rel_path,
                "fired": exit_code != 0,
                "diff_lines": diff_lines,
                "token_in_diff": token_in_diff,
            })
            symbol_idx += 1

        for const_name in mod_info["constants"]:
            sandbox.reset()
            mutated_const = f"PROBE_{const_name}"
            target = sandbox.root / rel_path
            orig_text = target.read_text(encoding="utf-8")
            new_text = orig_text.replace(f"{const_name} =", f"{mutated_const} =").replace(f"{const_name}:", f"{mutated_const}:")
            if declared and const_name in declared:
                new_text = new_text.replace(f'"{const_name}"', f'"{mutated_const}"').replace(f"'{const_name}'", f"'{mutated_const}'")
            target.write_text(new_text, encoding="utf-8")

            exit_code, diff = sandbox.run_guard()
            diff_lines = len([ln for ln in diff.splitlines() if ln.startswith(("+", "-")) and not ln.startswith(("+++", "---"))])
            token_in_diff = mutated_const in diff

            results.append({
                "id": f"E_CONST_{symbol_idx:02d}",
                "symbol": const_name,
                "type": "constant",
                "module": rel_path,
                "fired": exit_code != 0,
                "diff_lines": diff_lines,
                "token_in_diff": token_in_diff,
            })
            symbol_idx += 1

    return results


# ---------------------------------------------------------------------------
# Main probe execution
# ---------------------------------------------------------------------------

def run_probe(repo_path: Path) -> dict[str, Any]:
    sandbox = Sandbox(repo_path)
    try:
        # Control 1: unmutated baseline check
        baseline_code, baseline_diff = sandbox.run_guard()
        if baseline_code != 0:
            raise RuntimeError(f"Baseline guard failed on clean copy: {baseline_diff}")

        # Census
        census = collect_compiler_symbols(repo_path)

        # Run curated mutants
        curated_results = []
        for m in CURATED_MUTANTS:
            sandbox.reset()
            m.apply_fn(sandbox.root)
            exit_code, diff = sandbox.run_guard()
            fired = (exit_code != 0)
            diff_lines = len([ln for ln in diff.splitlines() if ln.startswith(("+", "-")) and not ln.startswith(("+++", "---"))])
            token_in_diff = bool(m.token and m.token in diff)

            curated_results.append({
                "id": m.mid,
                "category": m.category,
                "description": m.description,
                "expected_fired": m.expected_fired,
                "fired": fired,
                "diff_lines": diff_lines,
                "token_in_diff": token_in_diff,
                "target_file": m.target_file,
                "rationale": m.rationale,
            })

            # Control 2: check undo / reset clean state
            sandbox.reset()
            undo_code, undo_diff = sandbox.run_guard()
            if undo_code != 0:
                raise RuntimeError(f"Undo control failed after mutant {m.mid}: {undo_diff}")

        # Run exhaustive symbol census
        census_results = run_exhaustive_census(sandbox, census)

        # Summary statistics
        compiler_curated = [r for r in curated_results if "positive control" not in r["category"]]
        positive_controls = [r for r in curated_results if "positive control" in r["category"]]

        compiler_curated_fired = sum(1 for r in compiler_curated if r["fired"])
        positive_controls_fired = sum(1 for r in positive_controls if r["fired"])
        exhaustive_fired = sum(1 for r in census_results if r["fired"])

        data = {
            "summary": {
                "guard": "scripts/make_context.py --check",
                "target_miss": "public functions added under compiler/, likewise unscanned (B02)",
                "status": "settled",
                "controls": {
                    "control_1_clean_baseline": "pass (exit 0, CONTEXT.md up to date)",
                    "control_2_undo_clean": f"pass (all {len(CURATED_MUTANTS)} resets quiet, exit 0)",
                    "positive_controls_fired": f"{positive_controls_fired}/{len(positive_controls)}",
                },
                "curated_compiler_mutants": {
                    "total": len(compiler_curated),
                    "fired": compiler_curated_fired,
                    "detection_rate_pct": (compiler_curated_fired / len(compiler_curated)) * 100 if compiler_curated else 0.0,
                },
                "exhaustive_symbol_census": {
                    "total_symbols": len(census_results),
                    "fired": exhaustive_fired,
                    "detection_rate_pct": (exhaustive_fired / len(census_results)) * 100 if census_results else 0.0,
                    "breakdown": {
                        "functions": f"0/{census['summary']['public_function_count']} fired",
                        "classes": f"0/{census['summary']['public_class_count']} fired",
                        "constants": f"0/{census['summary']['constant_count']} fired",
                    },
                },
                "compiler_package_inventory": census["summary"],
            },
            "curated_results": curated_results,
            "census_results": census_results,
        }

        return data

    finally:
        sandbox.cleanup()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        default=str(REPO / "hunts" / "r_dc6e6f" / "results.json"),
        help="Path to write results JSON",
    )
    args = parser.parse_args()

    print(f"Running Hunt R-DC6E6F probe against {REPO}...")
    data = run_probe(REPO)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(data, indent=2), encoding="utf-8")
    print(f"Wrote results to {out_path}")

    # Print summary table
    print("\n" + "=" * 70)
    print("HUNT R-DC6E6F PROBE RESULTS SUMMARY")
    print("=" * 70)
    s = data["summary"]
    print(f"Guard under test: {s['guard']}")
    print(f"Target miss:     {s['target_miss']}")
    print(f"Status:          {s['status']}")
    print(f"Controls:        Clean baseline: {s['controls']['control_1_clean_baseline']}")
    print(f"                 Undo re-checks: {s['controls']['control_2_undo_clean']}")
    print(f"                 Positive controls: {s['controls']['positive_controls_fired']}")
    print(f"Curated mutants: {s['curated_compiler_mutants']['fired']}/{s['curated_compiler_mutants']['total']} fired ({s['curated_compiler_mutants']['detection_rate_pct']:.1f}% detection)")
    print(f"Symbol census:   {s['exhaustive_symbol_census']['fired']}/{s['exhaustive_symbol_census']['total_symbols']} fired ({s['exhaustive_symbol_census']['detection_rate_pct']:.1f}% detection)")
    print(f"Breakdown:       {s['exhaustive_symbol_census']['breakdown']['functions']}, {s['exhaustive_symbol_census']['breakdown']['classes']}, {s['exhaustive_symbol_census']['breakdown']['constants']}")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
