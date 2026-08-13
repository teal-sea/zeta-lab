#!/usr/bin/env python3
"""Mutation-test the guard ``scripts/make_context.py --check``.

The guard ledger (``harness/departments/guard_ledger.py``) carries this guard
with ``fired=None``, ``known_misses=()`` and ``scope="undetermined until
demonstrated"``: nobody has ever run a mutant past it.  Its declared smallest
mutant is *"one added public symbol with CONTEXT.md left unregenerated"*.  This
probe builds that mutant and twenty siblings, runs the guard against each, and
records the outcome.

Method
------
The guard is a pure-``ast`` stdlib script whose ``ROOT`` comes from
``__file__``, so it can be pointed at a copy of the tree.  The probe copies the
directories ``build()`` reads (``zeta/``, ``ontology/``, ``harness/``,
``dossier/``, ``docs/``, ``scripts/``, ``tests/``) plus ``CONTEXT.md`` into a
temporary sandbox, checks that the sandbox reproduces the committed
``CONTEXT.md`` byte for byte, then applies one mutant at a time and undoes it.
The repository under test is never written to.

Two things are recorded per mutant, not one:

* **fired** — the guard's exit code, which is all CI sees;
* **why it fired** — the probe regenerates ``CONTEXT.md`` in the sandbox and
  diffs it against the baseline, reporting how many lines moved and whether the
  mutant's own token appears among them.

That second measurement matters because ``CONTEXT.md`` records a per-module
line count (``*NNN lines*``).  Any edit that changes a file's length moves that
number, so a guard can fire on a mutant whose *symbol* it never saw.  A mutant
that fires with ``token_in_diff=false`` is caught by accounting, not by
comprehension, and the distinction predicts which real-world edits slip through.

Each mutant carries an expectation, so the run reports agreement rather than
raw exit codes alone.  A mutant expected to miss is a scope boundary, not a
defect: the output is a boundary map.

Run:  python3 hunts/r_414eed/probe.py [--json PATH]
Standard library only (so does the guard).
"""

from __future__ import annotations

import argparse
import difflib
import json
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

REPO = Path(__file__).resolve().parent.parent.parent

#: Everything ``make_context.build()`` reads.  ``meta``/``compiler`` are copied
#: only so the boundary probes have something real to mutate.
SCANNED_DIRS = ("zeta", "ontology", "harness", "dossier", "docs", "scripts", "tests")
UNSCANNED_DIRS = ("meta", "compiler")
EXTRA_FILES = ("CONTEXT.md", "AGENTS.md", "README.md")


# ---------------------------------------------------------------------------
# edit primitives
# ---------------------------------------------------------------------------


def _append(root: Path, rel: str, text: str) -> None:
    path = root / rel
    path.write_text(path.read_text(encoding="utf-8") + text, encoding="utf-8")


def _create(root: Path, rel: str, text: str) -> None:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _replace(root: Path, rel: str, old: str, new: str, *, count: int = 1) -> None:
    path = root / rel
    text = path.read_text(encoding="utf-8")
    if old not in text:
        raise RuntimeError(f"mutant anchor missing in {rel}: {old!r}")
    path.write_text(text.replace(old, new, count), encoding="utf-8")


def _chain(*edits: Callable[[Path], None]) -> Callable[[Path], None]:
    def run(root: Path) -> None:
        for edit in edits:
            edit(root)

    return run


PUBLIC_FN = '''


def mutant_public_symbol(x: int) -> int:
    """A public symbol added by hunt r-414eed's mutation probe."""
    return x
'''

PRIVATE_FN = '''


def _mutant_private_symbol(x: int) -> int:
    """A private symbol added by hunt r-414eed's mutation probe."""
    return x
'''

PUBLIC_CLASS = '''


class MutantPublicClass:
    """A public class added by hunt r-414eed's mutation probe."""
'''


# ---------------------------------------------------------------------------
# mutant description
# ---------------------------------------------------------------------------


@dataclass
class Mutant:
    mid: str
    category: str
    description: str
    expect_fire: bool
    rationale: str
    apply: Callable[[Path], None]
    #: A string that should appear in the regenerated CONTEXT.md diff if the
    #: guard noticed the *symbol* rather than merely the file's line count.
    token: str = ""
    line_count_changes: bool = True


MUTANTS: list[Mutant] = [
    # ---- the ledger's declared smallest mutant, in three readings ---------
    Mutant(
        "M01",
        "declared smallest mutant",
        "add a public function to zeta/core.py, __all__ left alone "
        "(the literal reading of 'one added public symbol')",
        True,
        "AGENTS.md: regenerate whenever you add a public function",
        lambda r: _append(r, "zeta/core.py", PUBLIC_FN),
        token="mutant_public_symbol",
    ),
    Mutant(
        "M02",
        "declared smallest mutant",
        "add a public function to zeta/core.py and list it in __all__",
        True,
        "unambiguously part of the curated public API",
        _chain(
            lambda r: _append(r, "zeta/core.py", PUBLIC_FN),
            lambda r: _replace(
                r, "zeta/core.py", '__all__ = [\n', '__all__ = [\n    "mutant_public_symbol",\n'
            ),
        ),
        token="mutant_public_symbol",
    ),
    Mutant(
        "M03",
        "declared smallest mutant",
        "add a public function to zeta/adele.py, a module that declares no __all__",
        True,
        "no __all__ filter, so the symbol itself should reach CONTEXT.md",
        lambda r: _append(r, "zeta/adele.py", PUBLIC_FN),
        token="mutant_public_symbol",
    ),
    Mutant(
        "M04",
        "declared smallest mutant",
        "add a public function to ontology/domains/zeta_domain.py (+ __all__)",
        True,
        "the discovery layer is indexed too",
        _chain(
            lambda r: _append(r, "ontology/domains/zeta_domain.py", PUBLIC_FN),
            lambda r: _replace(
                r,
                "ontology/domains/zeta_domain.py",
                "__all__ = [\n",
                '__all__ = [\n    "mutant_public_symbol",\n',
            ),
        ),
        token="mutant_public_symbol",
    ),
    Mutant(
        "M05",
        "declared smallest mutant",
        "add a public class to harness/guards.py (+ __all__)",
        True,
        "classes are indexed alongside functions",
        _chain(
            lambda r: _append(r, "harness/guards.py", PUBLIC_CLASS),
            lambda r: _replace(
                r, "harness/guards.py", "__all__ = [\n", '__all__ = [\n    "MutantPublicClass",\n'
            ),
        ),
        token="MutantPublicClass",
    ),
    Mutant(
        "M06",
        "declared smallest mutant",
        "add a public function to dossier/status.py (+ __all__)",
        True,
        "dossier/ is one of the four indexed packages",
        _chain(
            lambda r: _append(r, "dossier/status.py", PUBLIC_FN),
            lambda r: _replace(
                r, "dossier/status.py", "__all__ = [\n", '__all__ = [\n    "mutant_public_symbol",\n'
            ),
        ),
        token="mutant_public_symbol",
    ),
    # ---- renames and signatures, which the ledger entry also names --------
    Mutant(
        "M07",
        "rename / signature",
        "rename a public function in place: zeta/core.py xi -> xi_renamed (+ __all__)",
        True,
        "the ledger names renames explicitly; line count unchanged",
        _chain(
            lambda r: _replace(r, "zeta/core.py", "def xi(s, dps", "def xi_renamed(s, dps"),
            lambda r: _replace(r, "zeta/core.py", '    "xi",\n', '    "xi_renamed",\n'),
        ),
        token="xi_renamed",
        line_count_changes=False,
    ),
    Mutant(
        "M08",
        "rename / signature",
        "change a public signature in place: zeta.core.zeta gains a keyword-only arg",
        True,
        "CONTEXT.md renders full signatures; line count unchanged",
        lambda r: _replace(
            r,
            "zeta/core.py",
            "def zeta(s, dps: int = DPS_DEFAULT):",
            "def zeta(s, dps: int = DPS_DEFAULT, *, mutant=None):",
        ),
        token="mutant = None",
        line_count_changes=False,
    ),
    Mutant(
        "M09",
        "rename / signature",
        "change a public function's docstring first line in place",
        True,
        "CONTEXT.md carries the first docstring line as the summary",
        lambda r: _replace(
            r, "zeta/core.py", '"""Riemann zeta', '"""MUTANT zeta', count=1
        ),
        token="MUTANT zeta",
        line_count_changes=False,
    ),
    # ---- module / doc / script / test level -------------------------------
    Mutant(
        "M10",
        "module-level",
        "add a whole new module zeta/mutant_module.py",
        True,
        "the package glob picks up modules outside MODULE_ORDER",
        lambda r: _create(
            r,
            "zeta/mutant_module.py",
            '"""A module added by hunt r-414eed\'s mutation probe."""\n' + PUBLIC_FN,
        ),
        token="mutant_module",
    ),
    Mutant(
        "M11",
        "module-level",
        "add an upper-case module constant to zeta/core.py",
        True,
        "constants are listed per module",
        lambda r: _append(r, "zeta/core.py", "\n\nMUTANT_CONSTANT = 1\n"),
        token="MUTANT_CONSTANT",
    ),
    Mutant(
        "M12",
        "docs / scripts / tests",
        "add a document docs/mutant-probe.md",
        True,
        "the document index is generated",
        lambda r: _create(r, "docs/mutant-probe.md", "# A mutant document\n"),
        token="mutant-probe.md",
    ),
    Mutant(
        "M13",
        "docs / scripts / tests",
        "change a document's H1 title in place (docs/00-orientation.md)",
        True,
        "the index carries titles, not just filenames",
        lambda r: _replace(r, "docs/00-orientation.md", "# 00 — Orientation", "# 00 — MUTANT"),
        token="00 — MUTANT",
        line_count_changes=False,
    ),
    Mutant(
        "M14",
        "docs / scripts / tests",
        "add a script scripts/99_mutant.py",
        True,
        "the script index is generated",
        lambda r: _create(r, "scripts/99_mutant.py", '"""A mutant script."""\n'),
        token="99_mutant.py",
    ),
    Mutant(
        "M15",
        "docs / scripts / tests",
        "add a test function to tests/test_repo_hygiene.py",
        True,
        "per-file test counts are pinned in CONTEXT.md",
        lambda r: _append(
            r,
            "tests/test_repo_hygiene.py",
            "\n\ndef test_mutant_probe() -> None:\n    assert True\n",
        ),
        token="test_repo_hygiene.py",
    ),
    Mutant(
        "M16",
        "artifact",
        "hand-edit CONTEXT.md itself (one phrase) with the tree untouched",
        True,
        "'do not edit by hand — regenerate' is a claim the guard should back",
        lambda r: _replace(r, "CONTEXT.md", "machine-readable index", "MUTANT index"),
        token="",
    ),
    # ---- boundary probes: a miss here maps scope, it is not automatically a bug
    Mutant(
        "B01",
        "boundary: unscanned package",
        "add a public function to meta/ledger.py",
        False,
        "meta/ is not one of the four indexed packages",
        lambda r: _append(r, "meta/ledger.py", PUBLIC_FN),
        token="mutant_public_symbol",
    ),
    Mutant(
        "B02",
        "boundary: unscanned package",
        "add a public function to compiler/semantics.py",
        False,
        "compiler/ is not indexed",
        lambda r: _append(r, "compiler/semantics.py", PUBLIC_FN),
        token="mutant_public_symbol",
    ),
    Mutant(
        "B03",
        "boundary: unscanned path shape",
        "add a document under docs/doors/ (a subdirectory)",
        False,
        "doc_index globs docs/*.md, not docs/**/*.md",
        lambda r: _create(r, "docs/doors/mutant-probe.md", "# A mutant door\n"),
        token="mutant-probe.md",
    ),
    Mutant(
        "B04",
        "boundary: unscanned path shape",
        "add a test file not named test_*.py (tests/mutant_helper.py)",
        False,
        "test_counts globs test_*.py",
        lambda r: _create(
            r, "tests/mutant_helper.py", "def test_mutant() -> None:\n    assert True\n"
        ),
        token="mutant_helper",
    ),
    Mutant(
        "B05",
        "boundary: by design",
        "add a private function to zeta/core.py",
        False,
        "private symbols are deliberately outside the public API index",
        lambda r: _append(r, "zeta/core.py", PRIVATE_FN),
        token="_mutant_private_symbol",
    ),
    Mutant(
        "B06",
        "boundary: the __all__ filter, isolated from the line count",
        "promote a private helper to public in place: zeta/core.py _num -> pubnum, "
        "not added to __all__ (same number of lines)",
        False,
        "module_api filters by __all__ when one is declared, so the new public "
        "name is invisible; the in-place edit removes the line-count tell",
        lambda r: _replace(r, "zeta/core.py", "def _num(s):", "def pubnum(s):"),
        token="pubnum",
        line_count_changes=False,
    ),
    Mutant(
        "B08",
        "boundary: the line-count tell, isolated from any symbol",
        "add one blank line to the end of zeta/core.py — no symbol of any kind",
        True,
        "CONTEXT.md records a per-module line count, so file length alone is "
        "enough to make the artifact stale",
        lambda r: _append(r, "zeta/core.py", "\n"),
        token="",
    ),
    Mutant(
        "B07",
        "boundary: by design",
        "change a public function's docstring below its first line",
        False,
        "CONTEXT.md keeps only the first docstring line",
        lambda r: _replace(
            r,
            "zeta/core.py",
            "This is the *workhorse* used throughout",
            "MUTANT is the *workhorse* used throughout",
        ),
        token="MUTANT is the",
        line_count_changes=False,
    ),
]


# ---------------------------------------------------------------------------
# harness
# ---------------------------------------------------------------------------


def build_sandbox(dest: Path) -> None:
    ignore = shutil.ignore_patterns("__pycache__", "*.pyc", ".pytest_cache")
    for name in SCANNED_DIRS + UNSCANNED_DIRS:
        src = REPO / name
        if src.is_dir():
            shutil.copytree(src, dest / name, ignore=ignore)
    for name in EXTRA_FILES:
        if (REPO / name).is_file():
            shutil.copy2(REPO / name, dest / name)


def run_guard(root: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [sys.executable, str(root / "scripts" / "make_context.py"), "--check"],
        capture_output=True,
        text=True,
        timeout=600,
    )
    return proc.returncode, (proc.stdout + proc.stderr).strip()


def regenerate(root: Path) -> str:
    """Run the generator (not --check) and return the CONTEXT.md it produces."""
    subprocess.run(
        [sys.executable, str(root / "scripts" / "make_context.py")],
        capture_output=True,
        text=True,
        timeout=600,
        check=True,
    )
    return (root / "CONTEXT.md").read_text(encoding="utf-8")


def snapshot(root: Path) -> dict[str, bytes]:
    return {
        str(p.relative_to(root)): p.read_bytes() for p in root.rglob("*") if p.is_file()
    }


def restore(root: Path, snap: dict[str, bytes]) -> None:
    for path in list(root.rglob("*")):
        if path.is_file() and str(path.relative_to(root)) not in snap:
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


def main() -> int:
    ap = argparse.ArgumentParser(description="mutation-test make_context.py --check")
    ap.add_argument("--json", type=Path, default=Path(__file__).with_name("results.json"))
    args = ap.parse_args()

    with tempfile.TemporaryDirectory(prefix="r414eed-") as tmp:
        root = Path(tmp) / "tree"
        root.mkdir()
        build_sandbox(root)

        # Control 1 — the unmutated sandbox must reproduce the committed
        # artifact, or every "fired" below is an artefact of the copy.
        rc0, msg0 = run_guard(root)
        print(f"[control 1] unmutated sandbox: exit={rc0}  {msg0}")
        if rc0 != 0:
            print("ABORT: sandbox does not reproduce CONTEXT.md", file=sys.stderr)
            return 2
        baseline_context = (root / "CONTEXT.md").read_text(encoding="utf-8")

        snap = snapshot(root)
        rows = []
        for m in MUTANTS:
            m.apply(root)
            rc, msg = run_guard(root)
            fired = rc != 0
            stats = diff_stats(baseline_context, regenerate(root), m.token)
            rows.append(
                {
                    "id": m.mid,
                    "category": m.category,
                    "mutant": m.description,
                    "expected_fire": m.expect_fire,
                    "fired": fired,
                    "exit_code": rc,
                    "guard_message": msg,
                    "agrees_with_expectation": fired == m.expect_fire,
                    "edit_changes_file_line_count": m.line_count_changes,
                    "rationale": m.rationale,
                    **stats,
                }
            )
            flag = "" if fired == m.expect_fire else "   <-- DISAGREES"
            print(
                f"  {m.mid}  {'FIRED    ' if fired else 'not fired'} "
                f"(expected {'fire' if m.expect_fire else 'miss'}) "
                f"diff={stats['context_diff_lines']:>3} "
                f"token={'yes' if stats['token_in_diff'] else 'no ':>3}"
                f"{flag}  {m.description}"
            )
            restore(root, snap)

            # Control 2 - the undo must leave the guard quiet, or the next
            # row inherits this row's mutation.
            rc_after, _ = run_guard(root)
            if rc_after != 0:
                print(f"ABORT: undo of {m.mid} left the sandbox dirty", file=sys.stderr)
                return 2

    in_scope = [r for r in rows if r["expected_fire"]]
    boundary = [r for r in rows if not r["expected_fire"]]
    accounting_only = [
        r["id"]
        for r in rows
        if r["fired"] and r["token"] and not r["token_in_diff"]
    ]
    summary = {
        "guard": "scripts/make_context.py --check",
        "python": sys.version.split()[0],
        "mutants_total": len(rows),
        "in_scope_total": len(in_scope),
        "in_scope_caught": sum(1 for r in in_scope if r["fired"]),
        "boundary_total": len(boundary),
        "boundary_caught": sum(1 for r in boundary if r["fired"]),
        "disagreements": [r["id"] for r in rows if not r["agrees_with_expectation"]],
        "fired_without_the_symbol_reaching_context": accounting_only,
        "controls": {
            "unmutated_sandbox_exit": rc0,
            "undo_rechecked_after_every_mutant": True,
        },
    }
    args.json.write_text(
        json.dumps({"summary": summary, "mutants": rows}, indent=2) + "\n", encoding="utf-8"
    )
    print()
    print(json.dumps(summary, indent=2))
    print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
