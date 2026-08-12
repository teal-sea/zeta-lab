"""The extension package's modules import from the package, not from a
proving service's scratch namespace.

This test exists because of a defect that has now occurred twice.

Artifacts produced by the Aristotle proof service arrive laid out in that
service's own project, whose module prefix is ``RequestProject``. When such an
artifact is landed into ``hunts/frontier_math/zeta23ext`` without rewriting its
import lines, the package stops building at the very first module -- Lean
reports ``unknown module prefix 'RequestProject'`` before it reaches any
mathematics -- while every proof in the file remains perfectly good. Nothing
about the failure is visible by reading the proofs, and nothing in the suite
noticed, because no local assembly build had ever been attempted.

First occurrence: all eight ``BandCert/`` modules (found 2026-08-12 by the
first local port survey). Second occurrence, *after* the first was fixed: the
five ``EForm/`` modules, landed the same day. A defect that recurs once the
fix is in is a defect whose fix was a repair, not a guard. This file is the
guard.

The rule is narrow on purpose: it says nothing about whether a module builds,
only that its imports name a module path this package could possibly provide.
It is cheap (a regex over a handful of files) so it can run in the fast tier,
where the assembly build that would otherwise catch this cannot.
"""

from __future__ import annotations

import pathlib
import re

PKG = pathlib.Path(__file__).resolve().parent.parent / "hunts" / "frontier_math" / "zeta23ext"

_IMPORT = re.compile(r"^import\s+([A-Za-z_][\w.]*)", re.MULTILINE)

# Prefixes a module in this package may legitimately import: Mathlib and its
# transitive dependencies, the upstream formalization, and the package itself.
_ALLOWED_PREFIXES = {
    "Mathlib",
    "Batteries",
    "Aesop",
    "Qq",
    "Plausible",
    "ImportGraph",
    "LeanSearchClient",
    "Cli",
    "ProofWidgets",
    "Zeta23",
    "Zeta23Ext",
    "Init",
    "Std",
    "Lean",
}


def _lean_files() -> list[pathlib.Path]:
    if not PKG.is_dir():  # pragma: no cover - package removed
        return []
    return [p for p in PKG.rglob("*.lean") if ".lake" not in p.parts]


def test_the_package_has_lean_modules() -> None:
    """A vacuous scan passes; this is what makes the scan below non-vacuous."""
    assert _lean_files(), f"no .lean files under {PKG} -- the scan would be vacuous"


def test_no_module_imports_a_proving_service_namespace() -> None:
    offenders: list[str] = []
    for path in _lean_files():
        text = path.read_text(encoding="utf-8", errors="ignore")
        for module in _IMPORT.findall(text):
            root = module.split(".", 1)[0]
            if root not in _ALLOWED_PREFIXES:
                offenders.append(f"{path.relative_to(PKG)}: import {module}")
    assert not offenders, (
        "these modules import a namespace this package cannot provide -- an "
        "artifact was landed without rewriting its import lines, and the "
        "package will fail to assemble at the first one:\n  "
        + "\n  ".join(offenders)
    )


def test_the_guard_fires_on_the_smallest_mutant(tmp_path) -> None:
    """Demonstration of detection power, per ``harness.guards``.

    The smallest mutant is one landed artifact whose import line still names
    the service's namespace. The guard's own logic is re-run against it here,
    with a passing control alongside, so the ledger entry in
    ``harness/departments/guard_ledger.py`` costs a runnable artifact rather
    than a sentence.
    """
    mutant = tmp_path / "Landed.lean"
    mutant.write_text("import RequestProject.Iv\n\ntheorem t : True := trivial\n")
    control = tmp_path / "Fixed.lean"
    control.write_text("import Zeta23Ext.BandCert.Iv\n\ntheorem t : True := trivial\n")

    def _offending(path: pathlib.Path) -> list[str]:
        text = path.read_text(encoding="utf-8")
        return [m for m in _IMPORT.findall(text) if m.split(".", 1)[0] not in _ALLOWED_PREFIXES]

    assert _offending(mutant) == ["RequestProject.Iv"], "guard missed the mutant"
    assert _offending(control) == [], "guard fires on the fixed file (false positive)"
