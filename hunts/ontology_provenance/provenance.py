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
``from zeta.zeros import ...``, reads a named zero-derived quantity, or imports
a helper that does, and all three are caught. A reference counts, not only a
call. A from-import that a file only re-exports follows its source. An
attribute re-export does not: ``import helper`` and then ``f = helper.f`` is
a local definition whose right-hand side is an attribute, and that name still
reads clean. RESULTS names that residual.

A second coarse decision, made because the first rule set false-flagged a
coefficient-only import: ``from module import name`` follows that name, not the
rest of the module. ``import module`` still follows the module. A name whose
body cannot be read is undecided, not clean and not tainted.

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
    # Per defined name: clean, tainted, or undecided. A consumer that imports
    # one name follows this table, not the file's module-level verdict.
    symbols: dict[str, str] = field(default_factory=dict)
    # local name -> "module::original", for from-imports this file binds
    imported_symbols: dict[str, str] = field(default_factory=dict)
    # defined name -> names it reads. Calls and other loads both count:
    # an alias, a value, and a default argument are references, not calls.
    symbol_calls: dict[str, tuple[str, ...]] = field(default_factory=dict)


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


# ``from module import name`` is recorded as ``module::name``. A whole-module
# edge (``import module``, a star import, or a banned module) stays a bare name.
_SYMBOL_EDGE: Final = "::"


def _absolute_module(current: str, node: ast.ImportFrom) -> str:
    """Resolve ``from .x import`` against the file's module name, or leave it."""
    name = node.module or ""
    if not node.level:
        return name
    parts = current.split(".") if current else []
    if node.level > len(parts):
        return name
    base = parts[: len(parts) - node.level]
    if name:
        base.append(name)
    return ".".join(base)


def _local_imported(alias: ast.alias) -> str:
    return alias.asname or alias.name


def _tainted_bindings(tree: ast.Module) -> set[str]:
    """Local names bound to a banned module or a banned quantity."""
    out: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                local = _local_imported(alias)
                if local in BANNED_NAMES or alias.name in BANNED_NAMES:
                    out.add(local)
                for banned in BANNED_MODULES:
                    if alias.name == banned or alias.name.startswith(banned + "."):
                        out.add(local)
        elif isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            mod_banned = mod in BANNED_MODULES
            for alias in node.names:
                local = _local_imported(alias)
                if mod_banned or alias.name in BANNED_NAMES or local in BANNED_NAMES:
                    out.add(local)
    return out


def _body_kind(nodes: Iterable[ast.AST], bindings: set[str]) -> str:
    """Direct use inside one body: tainted, undecided, or clean."""
    undecided = False
    for node in nodes:
        if isinstance(node, ast.Name):
            if node.id in bindings or node.id in BANNED_NAMES:
                return TAINTED
            if node.id in DYNAMIC_CALLS:
                undecided = True
        elif isinstance(node, ast.Attribute):
            root: ast.AST = node
            while isinstance(root, ast.Attribute):
                root = root.value
            if isinstance(root, ast.Name) and root.id in bindings:
                return TAINTED
            dotted = _chain(node)
            if not dotted:
                continue
            for banned in BANNED_MODULES:
                if dotted == banned or dotted.startswith(banned + "."):
                    return TAINTED
            if dotted.rsplit(".", 1)[-1] in BANNED_NAMES:
                return TAINTED
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name in DYNAMIC_MODULES:
                    undecided = True
                for banned in BANNED_MODULES:
                    if alias.name == banned or alias.name.startswith(banned + "."):
                        return TAINTED
        elif isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            if mod in BANNED_MODULES or mod in DYNAMIC_MODULES:
                return TAINTED if mod in BANNED_MODULES else UNDECIDED
            for alias in node.names:
                local = _local_imported(alias)
                if alias.name in BANNED_NAMES or local in BANNED_NAMES:
                    return TAINTED
    return UNDECIDED if undecided else CLEAN


def _called_names(nodes: Iterable[ast.AST]) -> set[str]:
    """Every name read in these nodes, not only call targets.

    A zero table held at module level, an alias ``g = f``, a function passed
    as a value, and a default argument are all loads. Counting only calls
    reported those constructions clean.
    """
    return {
        node.id
        for node in nodes
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
    }


def _symbol_statuses(tree: ast.Module) -> dict[str, str]:
    """Taint of each top-level name this file defines.

    A name in the banned set is tainted for consumers even when this file is
    the one that manufactures it: the file-level verdict can still be
    ``provider``. A sibling that never reaches a tainted binding stays clean,
    which is what keeps a coefficient-only function out of a module-level hit.
    """
    bindings = _tainted_bindings(tree)
    direct: dict[str, str] = {}
    calls: dict[str, set[str]] = {}

    def record(name: str, node: ast.AST) -> None:
        walked = list(ast.walk(node))
        if name in BANNED_NAMES:
            direct[name] = TAINTED
        else:
            direct[name] = _body_kind(walked, bindings)
        calls[name] = _called_names(walked)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            record(node.name, node)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    record(target.id, node)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            record(node.target.id, node)

    changed = True
    while changed:
        changed = False
        for name, called in calls.items():
            if direct.get(name) == TAINTED:
                continue
            for callee in called:
                callee_status = direct.get(callee)
                if callee in bindings or callee in BANNED_NAMES or callee_status == TAINTED:
                    direct[name] = TAINTED
                    changed = True
                    break
                if callee_status == UNDECIDED and direct.get(name) != UNDECIDED:
                    direct[name] = UNDECIDED
                    changed = True
    return direct


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
    out.symbols = _symbol_statuses(tree)
    out.symbol_calls = {
        name: tuple(sorted(_called_names(list(ast.walk(node)))))
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        for name in (node.name,)
    }
    for node in ast.walk(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        mod = _absolute_module(module, node)
        if not mod:
            continue
        for alias in node.names:
            if alias.name == "*":
                continue
            out.imported_symbols[_local_imported(alias)] = (
                f"{mod}{_SYMBOL_EDGE}{alias.name}"
            )

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
            mod = _absolute_module(module, node)
            if mod in BANNED_MODULES:
                out.edges.add(mod)
                out.status, out.tier = TAINTED, "direct"
                out.witness = f"imports {mod}: {BANNED_MODULES[mod]}"
                return out
            specific: list[str] = []
            for alias in node.names:
                local = _local_imported(alias)
                if alias.name in BANNED_NAMES or local in BANNED_NAMES:
                    why = BANNED_NAMES.get(alias.name) or BANNED_NAMES[local]
                    shown = local if local in BANNED_NAMES else alias.name
                    out.edges.add(mod)
                    out.status, out.tier = TAINTED, "direct"
                    out.witness = f"imports {shown} from {mod}: {why}"
                    return out
                if alias.name == "*":
                    out.edges.add(mod)
                    specific = []
                    break
                specific.append(alias.name)
            else:
                for name in specific:
                    out.edges.add(f"{mod}{_SYMBOL_EDGE}{name}")

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
    propagate_symbol_taint(out)
    return out


def propagate_symbol_taint(universe: dict[str, Analysis]) -> None:
    """Push tainted symbols across ``from module import name`` references.

    Same-file references are already closed inside ``_symbol_statuses``. This
    pass closes the remaining hole: a function that reads an imported name
    whose body, in another file, reaches a zero-derived quantity. A read
    counts whether or not the name is called.

    A from-import this file does not itself define is also a symbol, so a
    re-export (``from helper import f`` in an intermediate module, then
    ``from intermediate import f``) follows the source instead of falling
    through. A local definition is not overwritten: it shadows the import.
    An attribute re-export (``import helper`` then ``f = helper.f``) is such
    a local definition. The right-hand side is an attribute, not a from-import,
    and this pass does not follow it. That name still reads clean.
    """
    local_defs = {id(analysis): set(analysis.symbols) for analysis in universe.values()}
    changed = True
    while changed:
        changed = False
        for analysis in universe.values():
            for name, called in analysis.symbol_calls.items():
                if analysis.symbols.get(name) == TAINTED:
                    continue
                for callee in called:
                    local = analysis.symbols.get(callee)
                    if local == TAINTED or callee in BANNED_NAMES:
                        analysis.symbols[name] = TAINTED
                        changed = True
                        break
                    edge = analysis.imported_symbols.get(callee)
                    if not edge or _SYMBOL_EDGE not in edge:
                        if local == UNDECIDED and analysis.symbols.get(name) == CLEAN:
                            analysis.symbols[name] = UNDECIDED
                            changed = True
                        continue
                    mod, sym = edge.split(_SYMBOL_EDGE, 1)
                    dep = universe.get(mod)
                    if dep is None:
                        continue
                    remote = dep.symbols.get(sym)
                    if remote == TAINTED or sym in BANNED_NAMES:
                        analysis.symbols[name] = TAINTED
                        changed = True
                        break
                    if remote == UNDECIDED and analysis.symbols.get(name) == CLEAN:
                        analysis.symbols[name] = UNDECIDED
                        changed = True
                    elif remote is None and dep.status in (TAINTED, UNDECIDED):
                        if analysis.symbols.get(name) == CLEAN:
                            analysis.symbols[name] = UNDECIDED
                            changed = True

            defined = local_defs[id(analysis)]
            for local_name, edge in analysis.imported_symbols.items():
                if local_name in defined or _SYMBOL_EDGE not in edge:
                    continue
                mod, sym = edge.split(_SYMBOL_EDGE, 1)
                if sym in BANNED_NAMES:
                    remote = TAINTED
                else:
                    dep = universe.get(mod)
                    remote = None if dep is None else dep.symbols.get(sym)
                if remote not in (TAINTED, UNDECIDED, CLEAN):
                    continue
                current = analysis.symbols.get(local_name)
                if current == remote:
                    continue
                if current == TAINTED:
                    continue
                if current == UNDECIDED and remote != TAINTED:
                    continue
                analysis.symbols[local_name] = remote
                changed = True


#: Laboratory directories that hold Python but are outside the scanned universe
#: (``collect`` reads only zeta/, ontology/ and hunts/). An import from one of
#: them cannot be read, so it is undecided, not clean. Third-party and standard
#: modules are outside the laboratory and stay skipped. (Review, 2026-10-30.)
UNSCANNED_LAB_PACKAGES: Final = frozenset(
    {"scripts", "harness", "tests", "meta", "dossier", "compiler", "environments",
     "telemetry", "lean"}
)


def _unscanned(target: str) -> bool:
    return target.split(".", 1)[0] in UNSCANNED_LAB_PACKAGES


def resolve(module: str, universe: dict[str, Analysis]) -> Analysis:
    """Promote a clean module to reachable-tainted when its imports are tainted.

    A ``module::name`` edge follows that name's symbol status. A bare module
    edge still follows the module verdict, except that a whole-module or star
    import of a provider is undecided: which of its zero-derived names the
    importer reads is not resolved. An unresolved name in a tainted module is
    undecided, not tainted: module granularity is not a verdict. An edge into a
    laboratory directory the scan does not read is undecided.
    """
    if module not in universe:
        return Analysis(path="", status=UNDECIDED, reason="not in universe")
    start = universe[module]
    if start.status != CLEAN:
        return start

    seen = {module}
    seen_symbols: set[tuple[str, str]] = set()
    queue: deque[list[str]] = deque([[module]])
    while queue:
        trail = queue.popleft()
        current = trail[-1]
        for edge in sorted(universe.get(current, Analysis(path="")).edges):
            if _SYMBOL_EDGE in edge:
                target, sym = edge.split(_SYMBOL_EDGE, 1)
                if target not in universe and _unscanned(target):
                    return Analysis(
                        path=start.path,
                        status=UNDECIDED,
                        reason=f"imports {sym} from {target}, outside the scanned tree",
                        path_to_taint=trail + [target],
                        edges=start.edges,
                    )
                if (target, sym) in seen_symbols or target not in universe:
                    continue
                seen_symbols.add((target, sym))
                dep = universe[target]
                sym_status = dep.symbols.get(sym)
                if sym_status == TAINTED or sym in BANNED_NAMES:
                    return Analysis(
                        path=start.path,
                        status=TAINTED,
                        tier="reachable",
                        witness=f"{dep.path}: {sym} is zero-derived",
                        path_to_taint=trail + [target],
                        edges=start.edges,
                    )
                if sym_status == UNDECIDED or sym_status is None and dep.status in (
                    TAINTED,
                    UNDECIDED,
                ):
                    why = (
                        dep.reason
                        if dep.status == UNDECIDED
                        else f"{sym} is not resolved at symbol granularity"
                    )
                    return Analysis(
                        path=start.path,
                        status=UNDECIDED,
                        reason=f"reaches {dep.path}: {why}",
                        path_to_taint=trail + [target],
                        edges=start.edges,
                    )
                continue
            target = edge
            if target not in universe:
                if _unscanned(target):
                    return Analysis(
                        path=start.path,
                        status=UNDECIDED,
                        reason=f"imports {target}, outside the scanned tree",
                        path_to_taint=trail + [target],
                        edges=start.edges,
                    )
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
            if dep.status == PROVIDER or TAINTED in dep.symbols.values():
                return Analysis(
                    path=start.path,
                    status=UNDECIDED,
                    reason=(f"imports all of {dep.path}, which holds zero-derived names; "
                            "which of them are read is not resolved"),
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
