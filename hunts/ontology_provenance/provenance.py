"""Requirement A as a check: what a proposed construction is built from.

`docs/09-new-ontologies.md` §5.1 Requirement A says every ingredient of a
candidate construction must come from prime-power data plus the archimedean
local factor, and that this is mechanically checkable. This module is the
checkable part of that sentence and nothing more.

What it decides
---------------
For one source file:

* ``clean``     no zero-derived name is reachable, directly or through the
                repository's own import graph;
* ``tainted``   something zero-derived is reachable, with the name and the path
                that reaches it;
* ``undecided`` the source defeats static reading (dynamic import, ``exec``,
                ``eval`` on a computed string, syntax error).

Two tiers, reported separately because a reader needs to know whether the
defining file itself did it or whether it inherited it from a helper:

* ``direct``    this file names a zero-derived quantity;
* ``reachable`` a file it imports does, and the path is printed.

What it does not do
-------------------
This is a name and import-graph analysis. It does not prove a construction is
prime-derived, and a clean verdict is not a certificate. Indirection through
``getattr``, a data file, or arithmetic that reconstructs ordinates evades it.
It is a floor, in the same sense as ``scripts/check_secrets.py``: it catches the
ordinary case, which is the case that occurs.

One deliberate coarse decision: ``import zeta`` is not treated as an edge into
``zeta.zeros``, because ``zeta/__init__.py`` re-exports everything and importing
the package is not importing the zeros. A module that reaches the zeros writes
``from zeta.zeros import ...``, calls a named zero function, or imports a helper
that does, and all three are caught.

Usage
-----
    python hunts/ontology_provenance/provenance.py <files-or-dirs...> [--json]
    pytest hunts/ontology_provenance/test_provenance.py -q
"""

from __future__ import annotations

import argparse
import ast
import json
import sys
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Final, Iterable, Sequence

CLEAN: Final = "clean"
TAINTED: Final = "tainted"
PROVIDER: Final = "provider"
UNDECIDED: Final = "undecided"

# --------------------------------------------------------------------------
# The rule set. Each entry is a zero-derived quantity under Requirement A:
# a zero, an ordinate, a xi-phase, or a zero-counting function.
# --------------------------------------------------------------------------

BANNED_NAMES: Final[dict[str, str]] = {
    # ordinate producers
    "zetazero": "zero ordinate (mpmath)",
    "zetazeroes": "zero ordinates",
    "nzeros": "zero-counting function",
    "grampoint": "Gram point, an ordinate structure",
    "siegelz": "Riemann-Siegel Z, an xi-phase object",
    "siegeltheta": "Riemann-Siegel theta, an xi-phase",
    "rs_theta": "Riemann-Siegel theta, an xi-phase",
    "riemann_siegel_theta": "Riemann-Siegel theta, an xi-phase",
    "hardy_Z": "Hardy Z, an xi-phase object",
    "Z_dh": "Hardy Z analogue, an xi-phase object",
    "Z_shifted": "Hardy Z analogue, an xi-phase object",
    "Z_kappa": "Hardy Z analogue, an xi-phase object",
    # zero finders and counters
    "zeros_on_line": "zero list",
    "count_zeros_box": "zero-counting function",
    "find_offline_zero": "zero location",
    "verify_rh_up_to": "zero verification",
    "track_zeros": "zero tracking",
    "bump_pair": "Weil zero-side test pair",
    "psi_from_zeros": "explicit formula, zero side",
    "explicit_formula_sides": "explicit formula, zero side",
    # zero tables
    "OFFLINE_ZERO_RE": "off-line zero ordinate table",
    "OFFLINE_ZERO_IM": "off-line zero ordinate table",
    # ordinate statistics
    "pair_correlation": "ordinate statistics",
    "compare_to_random_matrix": "ordinate statistics",
}

BANNED_MODULES: Final[dict[str, str]] = {
    "zeta.zeros": "the zero module",
    "zeta.statistics": "ordinate statistics",
    "zeta.heatflow": "a flow acting on Xi",
    "mpmath.zetazero": "zero ordinate",
}

# Names that make a file unreadable rather than clean.
DYNAMIC_CALLS: Final = {"exec", "eval", "__import__"}
DYNAMIC_MODULES: Final = {"importlib", "runpy"}


@dataclass
class Analysis:
    """What one file was seen to do."""

    path: str
    status: str = CLEAN
    tier: str = ""
    witness: str = ""
    path_to_taint: list[str] = field(default_factory=list)
    edges: set[str] = field(default_factory=set)
    reason: str = ""


def _module_name(path: Path, root: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    parts = list(rel.parts)
    if parts and parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def _chain(node: ast.AST) -> str:
    """Dotted name of an Attribute/Name chain, or '' when not static."""
    parts: list[str] = []
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if isinstance(node, ast.Name):
        parts.append(node.id)
        return ".".join(reversed(parts))
    return ""


def _definitions(tree: ast.Module) -> set[str]:
    """Top-level names this file defines: functions, classes, assigned names."""
    out: set[str] = set()
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            out.add(node.name)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    out.add(target.id)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            out.add(node.target.id)
    return out


def _first_hit(nodes: Iterable[ast.AST], skip: set[str]) -> tuple[str, str] | None:
    """First (witness, kind) of a banned or dynamic use, ignoring ``skip`` names."""
    for node in nodes:
        if isinstance(node, ast.Name):
            if node.id in skip:
                continue
            if node.id in BANNED_NAMES:
                return (f"uses {node.id}: {BANNED_NAMES[node.id]}", "banned")
            if node.id in DYNAMIC_CALLS:
                return (f"dynamic execution: {node.id}", "dynamic")
        elif isinstance(node, ast.Attribute):
            dotted = _chain(node)
            if not dotted:
                continue
            for banned, why in BANNED_MODULES.items():
                if dotted == banned or dotted.startswith(banned + "."):
                    return (f"uses {dotted}: {why}", "banned")
            tail = dotted.rsplit(".", 1)[-1]
            if tail in BANNED_NAMES and tail not in skip:
                return (f"uses {dotted}: {BANNED_NAMES[tail]}", "banned")
    return None


def analyse_source(text: str, path: str = "<string>", module: str = "") -> Analysis:
    """Analyse one file's source text. Never raises on bad Python.

    A file that *defines* a zero-derived quantity is a ``provider``: it is the
    source of the thing, not a construction built from it. That distinction is
    what keeps ``zeta.core`` (which defines the Riemann-Siegel theta) out of the
    tainted column, while a frame that imports or calls that theta is caught.
    """
    out = Analysis(path=path)
    try:
        tree = ast.parse(text)
    except SyntaxError as exc:
        out.status = UNDECIDED
        out.reason = f"syntax error: {exc.msg}"
        return out

    defined = _definitions(tree)

    # 1. imports first: importing a banned name is a direct hit regardless of defs
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                out.edges.add(alias.name)
                for banned, why in BANNED_MODULES.items():
                    if alias.name == banned or alias.name.startswith(banned + "."):
                        out.status, out.tier = TAINTED, "direct"
                        out.witness = f"imports {alias.name}: {why}"
                        return out
        elif isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            out.edges.add(mod)
            if mod in BANNED_MODULES:
                out.status, out.tier = TAINTED, "direct"
                out.witness = f"imports {mod}: {BANNED_MODULES[mod]}"
                return out
            for alias in node.names:
                if alias.name in BANNED_NAMES:
                    out.status, out.tier = TAINTED, "direct"
                    out.witness = (
                        f"imports {alias.name} from {mod}: {BANNED_NAMES[alias.name]}"
                    )
                    return out

    # 2. every body in the file, exempting only names this file manufactures
    #    (a name defined here is a provider of that thing, not a consumer of it)
    hit = _first_hit(
        [n for node in tree.body for n in ast.walk(node)], defined
    )
    if hit:
        witness, kind = hit
        if kind == "banned":
            out.status, out.tier, out.witness = TAINTED, "direct", witness
        else:
            out.status, out.reason = UNDECIDED, witness
        return out

    # 3. a file that defines a banned quantity is a provider, not a consumer
    banned_defs = sorted(defined & set(BANNED_NAMES))
    if banned_defs:
        out.status = PROVIDER
        out.witness = f"defines {', '.join(banned_defs)}"
        return out

    # 4. dynamic-execution machinery anywhere else still blocks a clean verdict
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name in DYNAMIC_MODULES:
                    out.status = UNDECIDED
                    out.reason = f"dynamic module: {alias.name}"
                    return out

    return out


def collect(root: Path) -> dict[str, Analysis]:
    """Analyse every laboratory module under ``root``."""
    out: dict[str, Analysis] = {}
    for path in sorted(root.rglob("*.py")):
        if any(part in {".venv", "__pycache__", ".git", "build"} for part in path.parts):
            continue
        rel = path.relative_to(root)
        if not rel.parts or rel.parts[0] not in {"zeta", "ontology", "hunts"}:
            continue
        module = _module_name(path, root)
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            analysis = Analysis(path=str(rel))
            analysis.status = UNDECIDED
            analysis.reason = f"unreadable: {exc}"
            out[module] = analysis
            continue
        out[module] = analyse_source(text, path=str(rel), module=module)
    return out


def resolve(module: str, universe: dict[str, Analysis]) -> Analysis:
    """Promote a clean module to reachable-tainted when its imports are tainted."""
    if module not in universe:
        return Analysis(path="", status=UNDECIDED, reason="not in universe")
    start = universe[module]
    if start.status != CLEAN:
        return start

    seen = {module}
    queue: deque[list[str]] = deque([[module]])
    while queue:
        trail = queue.popleft()
        current = trail[-1]
        for edge in sorted(universe.get(current, Analysis(path="")).edges):
            target = edge
            if target not in universe:
                continue
            if target in seen:
                continue
            seen.add(target)
            dep = universe[target]
            if dep.status == TAINTED:
                return Analysis(
                    path=start.path,
                    status=TAINTED,
                    tier="reachable",
                    witness=f"{dep.path}: {dep.witness}",
                    path_to_taint=trail + [target],
                    edges=start.edges,
                )
            if dep.status == UNDECIDED:
                return Analysis(
                    path=start.path,
                    status=UNDECIDED,
                    reason=f"reaches {dep.path} which cannot be read: {dep.reason}",
                    path_to_taint=trail + [target],
                    edges=start.edges,
                )
            queue.append(trail + [target])
    return start


def report(files: Iterable[str], root: Path, as_json: bool = False) -> int:
    universe = collect(root)
    rows = []
    for name in files:
        module = name
        if name.endswith(".py"):
            module = _module_name(Path(name).resolve(), root)
        verdict = resolve(module, universe)
        rows.append(
            {
                "module": module,
                "status": verdict.status,
                "tier": verdict.tier,
                "witness": verdict.witness or verdict.reason,
                "path": " -> ".join(verdict.path_to_taint) if verdict.path_to_taint else "",
            }
        )
    if as_json:
        print(json.dumps(rows, indent=2))
        return 0
    width = max((len(r["module"]) for r in rows), default=10)
    for r in rows:
        tier = f" ({r['tier']})" if r["tier"] else ""
        print(f"{r['module']:<{width}}  {r['status']}{tier}")
        if r["witness"]:
            where = f"  [{r['path']}]" if r["path"] else ""
            print(f"{'':<{width}}    {r['witness']}{where}")
    counts = {
        s: sum(1 for r in rows if r["status"] == s)
        for s in (CLEAN, TAINTED, PROVIDER, UNDECIDED)
    }
    print(f"\n{len(rows)} modules: " + ", ".join(f"{v} {k}" for k, v in counts.items()))
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("targets", nargs="+", help="files or directories")
    parser.add_argument("--root", default=str(Path(__file__).resolve().parents[2]))
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    files: list[str] = []
    for target in args.targets:
        path = Path(target)
        if path.is_dir():
            files.extend(
                str(p) for p in sorted(path.rglob("*.py"))
                if "__pycache__" not in p.parts
            )
        else:
            files.append(str(path))
    return report(files, root, as_json=args.json)


if __name__ == "__main__":
    sys.exit(main())
