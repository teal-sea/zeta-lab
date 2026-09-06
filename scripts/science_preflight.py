"""Preflight for a session running this lab from an outside environment.

Written for notebook-style agent environments (Claude Science and anything like
it) that mount this repository read-only and bring their *own* Python. Those
two facts break assumptions the rest of the tree is entitled to make, and the
breakages are silent:

* ``AGENTS.md`` says "ALWAYS ``.venv/bin/python``". An outside environment has
  no such venv, so nothing enforces which mpmath, numpy or **python-flint** is
  in play.
* ``zeta/rigor.py`` falls back from Arb to mpmath's ``iv`` context when
  python-flint is missing. The fallback is *correct* and roughly **1600x
  slower**, and it removes the two-backend cross-check that is the only reason
  ``rigor.py`` may use the word this repository reserves. A run that quietly
  fell back looks exactly like a run that did not.
* Doc numbers and hunt vocabulary are enforced by tests the outside session may
  never run. On 2026-08-10 a session added a second document numbered 21 and
  used a reserved word inside ``hunts/``; both are now caught by
  ``tests/test_docs_numbering.py`` and ``tests/test_hunt_probe_discipline.py``,
  but only if you run them.

Run this first, read the verdict, then work::

    python scripts/science_preflight.py
    python scripts/science_preflight.py --allow-fallback   # accept non-Arb numerics

Exit status is 0 when the environment can support every claim this repository
knows how to make, and 1 when it cannot. ``--allow-fallback`` downgrades the
ball-arithmetic backend finding to a warning, for exploratory work that will
not use the word.
"""

from __future__ import annotations

import argparse
import importlib
import os
import re
import shutil
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# ontology/, harness/ and dossier/ are not part of the editable install.
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

DOCS = os.path.join(REPO_ROOT, "docs")
HUNTS = os.path.join(REPO_ROOT, "hunts")

_RULE = "-" * 72


def _head(title: str) -> None:
    print(f"\n{title}\n{_RULE}")


def _check_interpreter() -> list[str]:
    """Report the interpreter and whether it is the one AGENTS.md mandates."""
    problems: list[str] = []
    _head("1. interpreter")
    print(f"  executable      {sys.executable}")
    print(f"  version         {sys.version.split()[0]}")
    expected = os.path.join(REPO_ROOT, ".venv", "bin", "python")
    if os.path.realpath(sys.executable) == os.path.realpath(expected):
        print("  venv            yes, the repo's own .venv, as AGENTS.md requires")
    elif os.path.exists(expected):
        print(f"  venv            NO. This repo has one at {expected}")
        print("                  Prefer it; results here are not comparable otherwise.")
    else:
        print("  venv            absent (expected in an outside environment)")
        print("                  Pin versions yourself: see requirements.txt.")

    _head("2. dependencies")
    for mod in ("mpmath", "numpy", "scipy", "sympy", "matplotlib", "flint"):
        try:
            m = importlib.import_module(mod)
            print(f"  {mod:<12} {getattr(m, '__version__', 'present')}")
        except ImportError:
            note = "  <-- python-flint: the Arb backend" if mod == "flint" else ""
            print(f"  {mod:<12} MISSING{note}")
    try:
        import zeta

        print(f"  zeta           importable from {os.path.dirname(zeta.__file__)}")
    except ImportError as exc:  # pragma: no cover - environment dependent
        print(f"  zeta           NOT IMPORTABLE: {exc}")
        print("                 Run `pip install -e .` from the repo root.")
        problems.append("zeta is not importable; nothing else here can run")
    return problems


def _check_backend(allow_fallback: bool) -> list[str]:
    """The finding that decides whether certified language is available."""
    problems: list[str] = []
    _head("3. ball-arithmetic backend (decides what you may claim)")
    try:
        from zeta import rigor
    except ImportError as exc:  # pragma: no cover - environment dependent
        print(f"  could not import zeta.rigor: {exc}")
        return ["zeta.rigor is not importable"]

    backend = rigor.BACKEND
    available = list(rigor.available_backends())
    print(f"  BACKEND         {backend}")
    print(f"  available       {available}")
    both = {"mpmath.iv", "python-flint"} <= set(available)
    if backend == "python-flint" and both:
        print("  verdict         OK. Arb is active and both backends are present,")
        print("                  so the cross-check that entitles rigor.py to the")
        print("                  reserved word can actually run.")
    else:
        print("  verdict         DEGRADED.")
        print("                  * ~1600x slower on certified paths (one case goes")
        print("                    from 0.76 s to over twenty minutes, which reads")
        print("                    as a hung suite rather than a slow one)")
        print("                  * the five skipif(not HAVE_FLINT) tests vanish,")
        print("                    three of which ARE the Arb-vs-mpmath cross-check")
        print("                  * a green suite here is not evidence the")
        print("                    cross-check ran")
        print("                  Fix: pip install python-flint (pinned in")
        print("                  requirements.txt).")
        if allow_fallback:
            print("                  --allow-fallback given: continuing as a warning.")
        else:
            problems.append(
                "ball-arithmetic backend is degraded; pass --allow-fallback to "
                "proceed with non-certified numerics only"
            )
    return problems


def _check_plotting() -> None:
    _head("4. plotting")
    if "matplotlib.pyplot" in sys.modules:
        import matplotlib

        print(f"  pyplot already imported, backend {matplotlib.get_backend()}")
        print("  If that is interactive, figures will not render headless.")
    else:
        print("  pyplot not yet imported, good.")
    print('  Always: import matplotlib; matplotlib.use("Agg") BEFORE pyplot.')
    print("  zeta/plots.py does this already; your own cells must too.")


def _check_lean() -> None:
    _head("5. the certified arm (lean/)")
    lake = shutil.which("lake")
    if lake:
        print(f"  lake            {lake}")
        print("  A Lean build may be possible here. It needs the pinned toolchain")
        print(f"  ({_lean_toolchain()}) and a Mathlib cache (multi-GB).")
    else:
        print("  lake            not on PATH.")
        print("  No Lean work from this environment: rung 3 and anything else in")
        print("  lean/ has to run where elan and the Mathlib cache live.")
        print("  Nothing in lean/ counts until it compiles with zero sorrys, so do")
        print("  not record a Lean claim you could not build.")


def _lean_toolchain() -> str:
    path = os.path.join(REPO_ROOT, "lean", "lean-toolchain")
    try:
        with open(path, encoding="utf-8") as fh:
            return fh.read().strip()
    except OSError:  # pragma: no cover
        return "unknown"


def _doc_numbers() -> list[int]:
    pat = re.compile(r"^(\d{2})-[\w.-]+\.md$")
    return sorted(int(m.group(1)) for m in map(pat.match, os.listdir(DOCS)) if m)


def _where_to_write() -> None:
    _head("6. where your output goes")
    numbers = _doc_numbers()
    nxt = (max(numbers) + 1) if numbers else 0
    print(f"  doc numbers in use   {numbers[0]:02d}..{numbers[-1]:02d}")
    print(f"  NEXT FREE DOC NUMBER {nxt:02d}  <-- use this, never guess")
    print("     A duplicate number makes every bare `docs/NN` citation to it")
    print("     ambiguous. This has happened twice; tests/test_docs_numbering.py")
    print("     now catches it.")
    existing = sorted(
        d for d in os.listdir(HUNTS) if os.path.isdir(os.path.join(HUNTS, d))
    )
    print(f"\n  existing hunts       {existing}")
    print("  New exploratory work goes in hunts/<your-name>/ with a MISSION.md")
    print("  stating what it may and may not touch. Write MISSION.md first.")
    print("\n  May write:      hunts/<yours>/, one new docs/NN-*.md, figures/")
    print("  May NOT write:  zeta/, ontology/, harness/ without explicit")
    print("                  permission, a hunt borrowing the zeta battery is")
    print("                  the correct relationship, not a deficiency.")
    print("  Not a department: a hunt whose rivals are the zeta department's")
    print("                  rivals cannot become one by growing.")


def _rules() -> None:
    _head("7. the rules that bite hardest, and the tests that enforce them")
    print("  honest scope    Nothing here is evidence for RH (docs/08). Never")
    print("                  write language implying a computation settles or")
    print("                  supports it. If a computation appears to settle")
    print("                  something open, the correct inference is a bug.")
    print("  reserved word   'certified' belongs to zeta/rigor.py alone, and is")
    print("                  banned anywhere under hunts/ *including in a")
    print("                  sentence disclaiming it*, the check is lexical.")
    print("                  -> tests/test_hunt_probe_discipline.py")
    print("  hunt vocabulary banned: verified, confirmed, definitively, proves.")
    print("                  allowed: measured, observed, consistent with.")
    print("  every claim     numerically checked by a test, or explicitly hedged")
    print("                  at the point of use. No exceptions.")
    print("  the battery     any structural property that 'explains' RH must be")
    print("                  run through zeta.epstein.battery, the")
    print("                  Davenport-Heilbronn function satisfies the")
    print("                  functional equation, has real coefficients and a")
    print("                  real Z, and violates RH. A claim it also passes")
    print("                  distinguishes nothing.")
    print("  conventions     derive them numerically, never recall them (weil.py")
    print("                  calibrated its convention; epstein.py re-solves for")
    print("                  kappa on every call).")
    print("\n  Before handing anything back, run at least:")
    print("    python -m pytest -q tests/test_docs_numbering.py \\")
    print("        tests/test_hunt_probe_discipline.py tests/test_doors.py")
    print("    python scripts/make_context.py --check")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--allow-fallback",
        action="store_true",
        help="treat a degraded ball-arithmetic backend as a warning, not a failure",
    )
    args = parser.parse_args()

    print("zeta-lab preflight for an outside environment")
    print(f"repo root: {REPO_ROOT}")
    writable = os.access(REPO_ROOT, os.W_OK)
    print(f"repo writable from here: {'yes' if writable else 'NO (read-only mount)'}")
    if not writable:
        print("  Deliverables have to leave as artifacts, not commits. Say so")
        print("  plainly rather than implying the tree was changed.")

    problems = _check_interpreter()
    problems += _check_backend(args.allow_fallback)
    _check_plotting()
    _check_lean()
    _where_to_write()
    _rules()

    _head("verdict")
    if problems:
        for p in problems:
            print(f"  BLOCKED: {p}")
        print("\n  Exit 1. Fix the above, or re-run with --allow-fallback if you")
        print("  are doing exploratory work that will make no certified claim.")
        return 1
    print("  Ready. Every claim this repository knows how to make is available.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
