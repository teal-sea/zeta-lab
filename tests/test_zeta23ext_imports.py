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


def _reachable_from_root() -> set[str]:
    """Module names reachable from the package root by following imports."""
    root = PKG / "Zeta23Ext.lean"
    if not root.is_file():  # pragma: no cover - package removed
        return set()

    def _mod_to_path(mod: str) -> pathlib.Path:
        return PKG / pathlib.Path(*mod.split(".")).with_suffix(".lean")

    seen: set[str] = set()
    stack = [m for m in _IMPORT.findall(root.read_text(encoding="utf-8"))]
    while stack:
        mod = stack.pop()
        if mod in seen or not mod.startswith("Zeta23Ext"):
            continue
        seen.add(mod)
        path = _mod_to_path(mod)
        if path.is_file():
            stack.extend(_IMPORT.findall(path.read_text(encoding="utf-8", errors="ignore")))
    return seen


def test_no_module_is_orphaned_from_the_root() -> None:
    """Every module in the package is reachable from ``Zeta23Ext.lean``.

    Second incident, same day as the first: an edit to the root module
    replaced ``import Zeta23Ext.Bridge`` with another import, so a
    kernel-checked module stopped being built by the default target while its
    file sat untouched on disk. It happened twice, by one-line edits, and the
    import-root scan above is blind to it -- that miss is recorded on the
    ledger entry, and this is the guard that closes it.

    An orphan is not a build error. It is worse: the module rots silently and
    the package still reports success.
    """
    root = PKG / "Zeta23Ext.lean"
    if not root.is_file():  # pragma: no cover
        return
    reachable = _reachable_from_root()
    orphans = []
    for path in _lean_files():
        if path.name == "Zeta23Ext.lean":
            continue
        mod = ".".join(path.relative_to(PKG).with_suffix("").parts)
        if mod not in reachable:
            orphans.append(mod)
    assert not orphans, (
        "these modules exist in the package but nothing imports them from "
        "Zeta23Ext.lean, so `lake build` never touches them and they rot "
        "silently:\n  " + "\n  ".join(sorted(orphans))
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


def test_the_orphan_guard_fires_on_a_dropped_import(tmp_path) -> None:
    """Demonstration of detection power for the orphan check.

    The smallest mutant is the incident itself: a root module that no longer
    imports a module still present on disk.
    """
    pkg = tmp_path
    (pkg / "Pkg").mkdir()
    (pkg / "Pkg" / "Kept.lean").write_text("import Mathlib\n")
    (pkg / "Pkg" / "Dropped.lean").write_text("import Mathlib\n")

    def _orphans(root_text: str) -> list[str]:
        (pkg / "Pkg.lean").write_text(root_text)
        reachable: set[str] = set()
        stack = list(_IMPORT.findall(root_text))
        while stack:
            mod = stack.pop()
            if mod in reachable or not mod.startswith("Pkg"):
                continue
            reachable.add(mod)
            p = pkg / pathlib.Path(*mod.split(".")).with_suffix(".lean")
            if p.is_file():
                stack.extend(_IMPORT.findall(p.read_text()))
        found = []
        for p in pkg.rglob("*.lean"):
            if p.name == "Pkg.lean":
                continue
            mod = ".".join(p.relative_to(pkg).with_suffix("").parts)
            if mod not in reachable:
                found.append(mod)
        return sorted(found)

    assert _orphans("import Pkg.Kept\n") == ["Pkg.Dropped"], "orphan guard missed the mutant"
    assert _orphans("import Pkg.Kept\nimport Pkg.Dropped\n") == [], "false positive"
