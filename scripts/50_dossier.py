#!/usr/bin/env python3
"""Validate research dossiers and print their status.

    .venv/bin/python scripts/50_dossier.py                # list every dossier
    .venv/bin/python scripts/50_dossier.py hardy_Z        # the full report
    .venv/bin/python scripts/50_dossier.py --validate     # exit non-zero if any is invalid

An experiment; see ``docs/19-research-dossiers.md``. The report prints all four
support axes and offers no aggregate, deliberately, a dossier is never
"verified", it has four independent kinds of support that fail differently.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

# ``dossier`` is not part of the editable install (same as ``ontology`` and
# ``harness``), so a script that imports it puts the repo root on sys.path.
_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from dossier import dossier_reasons, render_short, render_text  # noqa: E402
from dossier.subjects import KNOWN_DOSSIERS, load  # noqa: E402


def _build(name: str):
    return load(name).build()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "name",
        nargs="?",
        help="dossier to report on; omit to list all",
    )
    parser.add_argument(
        "--validate",
        action="store_true",
        help="validate every dossier and exit non-zero if any is malformed",
    )
    args = parser.parse_args(argv)

    if args.validate:
        failures = 0
        for name in sorted(KNOWN_DOSSIERS):
            reasons = dossier_reasons(_build(name))
            if reasons:
                failures += 1
                print(f"INVALID  {name}")
                for reason in reasons:
                    print(f"         - {reason}")
            else:
                print(f"ok       {name}")
        if failures:
            print(f"\n{failures} dossier(s) invalid")
        return 1 if failures else 0

    if args.name is None:
        print("Known dossiers (all four support axes, no aggregate):\n")
        for name in sorted(KNOWN_DOSSIERS):
            print("  " + render_short(_build(name)))
        print(f"\nFull report: {Path(__file__).name} <name>")
        return 0

    if args.name not in KNOWN_DOSSIERS:
        known = ", ".join(sorted(KNOWN_DOSSIERS))
        print(f"no dossier named {args.name!r}; known: {known}", file=sys.stderr)
        return 2

    print(render_text(_build(args.name)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
