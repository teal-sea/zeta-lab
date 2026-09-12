#!/usr/bin/env python3
"""Mutation-power measurement for the guard ``tests/test_doors.py``.

``harness/departments/guard_ledger.py`` carries the guard with ``fired=None``
and ``scope="undetermined until demonstrated"``, existence recorded, power
never measured.  ``harness/guards.py`` states the question the guard
offensive asks of every guard: *what exact incorrect computation is this
guard supposed to detect, and has that detection power actually been
demonstrated?*  The ledger names the smallest mutant that exhibits the
lesion, "a door page quoting a command that exits non-zero (e.g. a renamed
script)", and this file builds it, plus nine neighbours, and records which
of them the guard notices.

Method
------
Each mutant is applied to a throwaway ``git worktree`` checked out at HEAD,
never to the working tree.  Two tiers are then run against the mutated tree:

* **fast**: ``pytest tests/test_doors.py -m "not slow"``
* **slow**: the full node set, which shells out to the two door scripts

A mutant is CAUGHT by a tier when that tier exits non-zero, ESCAPED when it
still exits zero.  The null control (an unmutated worktree) must pass both
tiers, otherwise every "caught" below is measuring something else.

Cost discipline
---------------
The slow tier costs ~145 s a run (``06_tour.py`` ~118 s, ``23_gate_3_battery.py``
~25 s on this container), so it is not run per-mutant.  It is run three
times: on the null control, on the one mutant whose door script is expected
to be executed by it (M5), and once on a *combined* tree carrying every
mutant predicted to escape (M3, M4, M6, M7, M8) at the same time.  If the
slow tier passes a tree carrying five simultaneous broken doors, the escape
of each is measured rather than argued.

Run: ``python hunts/r_cb5ffe/probe.py``  (add ``--fast-only`` to skip the
three slow-tier runs; the escape/catch verdicts for the fast tier are
unaffected).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HUNT_DIR = Path(__file__).resolve().parent
REPO_ROOT = HUNT_DIR.parents[1]

DOORS_README = Path("docs/doors/README.md")
LEARN_PAGE = Path("docs/doors/learn.md")
TOUR = Path("scripts/06_tour.py")
BATTERY = Path("scripts/23_gate_3_battery.py")
PRIMES = Path("scripts/03_primes_from_zeros.py")

#: injected at the top of a script's body to make it exit non-zero at once.
_EXIT_STUB = "import sys as _sys; _sys.exit({code})  # mutant\n"

SLOW_TIER_TIMEOUT = 900
FAST_TIER_TIMEOUT = 300


# ---------------------------------------------------------------------------
# mutation operators, each takes the worktree root and edits it in place
# ---------------------------------------------------------------------------


def _sub_in_file(root: Path, rel: Path, old: str, new: str) -> None:
    path = root / rel
    text = path.read_text(encoding="utf-8")
    if old not in text:
        raise SystemExit(f"mutation target vanished: {old!r} not in {rel}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


def _break_script(root: Path, rel: Path, code: int) -> None:
    """Make a script exit ``code`` immediately, keeping it importable text."""
    path = root / rel
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    # insert after the module docstring if there is one, else at the top
    insert_at = 0
    if lines and lines[0].lstrip().startswith(('"""', "'''")):
        quote = lines[0].lstrip()[:3]
        if lines[0].count(quote) >= 2:
            insert_at = 1
        else:
            for i, line in enumerate(lines[1:], start=1):
                if quote in line:
                    insert_at = i + 1
                    break
    lines.insert(insert_at, _EXIT_STUB.format(code=code))
    path.write_text("".join(lines), encoding="utf-8")


def m1_readme_names_a_missing_script(root: Path) -> None:
    _sub_in_file(root, DOORS_README, "scripts/06_tour.py", "scripts/06_tour_renamed.py")


def m2_script_renamed_on_disk(root: Path) -> None:
    (root / BATTERY).rename(root / "scripts" / "23_gate_3_battery_v2.py")


def m3_door_page_names_a_missing_script(root: Path) -> None:
    _sub_in_file(
        root,
        LEARN_PAGE,
        "scripts/03_primes_from_zeros.py",
        "scripts/03_primes_from_zeros_renamed.py",
    )


def m4_door_page_command_exits_non_zero(root: Path) -> None:
    _break_script(root, PRIMES, 1)


def m5_readme_command_exits_non_zero(root: Path) -> None:
    _break_script(root, BATTERY, 3)


def m6_readme_row_loses_its_script(root: Path) -> None:
    _sub_in_file(
        root,
        DOORS_README,
        "`.venv/bin/python scripts/23_gate_3_battery.py`",
        "`less docs/doors/refute.md`",
    )


def m7_certify_door_command_broken(root: Path) -> None:
    _sub_in_file(root, DOORS_README, "lake build`", "lake buildd`")


def m8_adopt_door_command_broken(root: Path) -> None:
    _sub_in_file(
        root,
        DOORS_README,
        "tests/test_harness_protocol.py",
        "tests/test_harness_protocol_renamed.py",
    )


def _lab_page(root: Path) -> Path:
    pages = sorted((root / "interactive_lab").glob("*.html"))
    if not pages:
        raise SystemExit("interactive_lab/ has no page to mutate")
    return pages[0]


def m9_lab_page_loads_external_code(root: Path) -> None:
    page = _lab_page(root)
    text = page.read_text(encoding="utf-8")
    page.write_text(
        text.replace(
            "</head>",
            '<script src="https://cdn.example.invalid/plot.js"></script></head>',
            1,
        ),
        encoding="utf-8",
    )


def m10_lab_page_loses_its_title(root: Path) -> None:
    page = _lab_page(root)
    text = page.read_text(encoding="utf-8")
    stripped = re.sub(r"<title>.*?</title>", "", text, count=1, flags=re.S)
    if stripped == text:
        raise SystemExit(f"no <title> to remove in {page.name}")
    page.write_text(stripped, encoding="utf-8")


MUTANTS = [
    {
        "id": "M1",
        "what": "the doors README table names a script that does not exist",
        "family": "README command unrunnable",
        "apply": m1_readme_names_a_missing_script,
        "predicted": "fast",
    },
    {
        "id": "M2",
        "what": "a door's script is renamed on disk, README left pointing at the old name",
        "family": "README command unrunnable",
        "apply": m2_script_renamed_on_disk,
        "predicted": "fast",
    },
    {
        "id": "M3",
        "what": "a door *page* (learn.md) names a script that does not exist; README untouched",
        "family": "door-page command unrunnable",
        "apply": m3_door_page_names_a_missing_script,
        "predicted": "none",
    },
    {
        "id": "M4",
        "what": "a command quoted only by a door page exits non-zero",
        "family": "door-page command unrunnable",
        "apply": m4_door_page_command_exits_non_zero,
        "predicted": "none",
    },
    {
        "id": "M5",
        "what": "the command quoted by the README refute row exits non-zero",
        "family": "README command unrunnable",
        "apply": m5_readme_command_exits_non_zero,
        "predicted": "slow",
    },
    {
        "id": "M6",
        "what": "a README row's command is replaced by one naming no script at all",
        "family": "README command unrunnable",
        "apply": m6_readme_row_loses_its_script,
        "predicted": "none",
    },
    {
        "id": "M7",
        "what": "the certify door's Lean command is misspelled",
        "family": "README command unrunnable",
        "apply": m7_certify_door_command_broken,
        "predicted": "none",
    },
    {
        "id": "M8",
        "what": "the adopt door's pytest command names a test file that does not exist",
        "family": "README command unrunnable",
        "apply": m8_adopt_door_command_broken,
        "predicted": "none",
    },
    {
        "id": "M9",
        "what": "an interactive_lab page loads code from another host",
        "family": "interactive_lab contract",
        "apply": m9_lab_page_loads_external_code,
        "predicted": "fast",
    },
    {
        "id": "M10",
        "what": "an interactive_lab page loses its <title>",
        "family": "interactive_lab contract",
        "apply": m10_lab_page_loses_its_title,
        "predicted": "fast",
    },
]

#: the escape candidates, applied simultaneously so one slow-tier run
#: measures all of their slow-tier verdicts at once.
COMBINED = ["M3", "M4", "M6", "M7", "M8"]


# ---------------------------------------------------------------------------
# harness
# ---------------------------------------------------------------------------


def _pytest(root: Path, args: list[str], timeout: int) -> dict:
    cmd = [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        "-o",
        "addopts=",
        "tests/test_doors.py",
        *args,
    ]
    started = time.time()
    proc = subprocess.run(
        cmd, cwd=root, capture_output=True, text=True, timeout=timeout
    )
    tail = (proc.stdout + proc.stderr).strip().splitlines()
    return {
        "returncode": proc.returncode,
        "seconds": round(time.time() - started, 1),
        "last_line": tail[-1] if tail else "",
        "failed_nodes": sorted(
            set(re.findall(r"tests/test_doors\.py::(\w+)", proc.stdout))
        ),
    }


def _fast(root: Path) -> dict:
    return _pytest(root, ["-m", "not slow"], FAST_TIER_TIMEOUT)


def _slow(root: Path, node: str | None = None) -> dict:
    args = ["-m", "slow"] if node is None else ["-m", "slow", "-k", node]
    return _pytest(root, args, SLOW_TIER_TIMEOUT)


def _verdict(run: dict | None) -> str:
    if run is None:
        return "not-run"
    return "caught" if run["returncode"] != 0 else "escaped"


class Worktree:
    """A throwaway checkout of HEAD, reset between mutants."""

    def __init__(self, path: Path) -> None:
        self.path = path

    def __enter__(self) -> "Worktree":
        if self.path.exists():
            shutil.rmtree(self.path, ignore_errors=True)
        subprocess.run(
            ["git", "worktree", "add", "--detach", str(self.path), "HEAD"],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        return self

    def reset(self) -> None:
        subprocess.run(
            ["git", "checkout", "--", "."], cwd=self.path, check=True, capture_output=True
        )
        subprocess.run(
            ["git", "clean", "-fdq"], cwd=self.path, check=True, capture_output=True
        )

    def __exit__(self, *exc) -> None:
        subprocess.run(
            ["git", "worktree", "remove", "--force", str(self.path)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fast-only",
        action="store_true",
        help="skip the three slow-tier runs (~7 minutes of door scripts)",
    )
    parser.add_argument(
        "--workdir",
        default=os.environ.get("TMPDIR", "/tmp") + "/r_cb5ffe_worktree",
        help="where the throwaway worktree is created",
    )
    opts = parser.parse_args()

    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()

    out: dict = {
        "guard": "tests/test_doors.py",
        "head": head,
        "python": sys.version.split()[0],
        "tiers": {
            "fast": 'pytest tests/test_doors.py -m "not slow"',
            "slow": 'pytest tests/test_doors.py -m slow',
        },
        "mutants": [],
    }

    with Worktree(Path(opts.workdir)) as wt:
        # ---- null control -------------------------------------------------
        print("[null] unmutated worktree", flush=True)
        null = {"fast": _fast(wt.path)}
        if not opts.fast_only:
            null["slow"] = _slow(wt.path)
        out["null_control"] = null
        healthy = null["fast"]["returncode"] == 0 and (
            opts.fast_only or null["slow"]["returncode"] == 0
        )
        out["null_control"]["passes"] = healthy
        if not healthy:
            print("null control does not pass, every verdict below is void")

        # ---- one mutant at a time, fast tier ------------------------------
        for mutant in MUTANTS:
            wt.reset()
            mutant["apply"](wt.path)
            fast = _fast(wt.path)
            record = {
                "id": mutant["id"],
                "what": mutant["what"],
                "family": mutant["family"],
                "predicted_tier": mutant["predicted"],
                "fast": fast,
                "slow": None,
            }
            # the one mutant the slow tier is expected to execute
            if mutant["id"] == "M5" and not opts.fast_only:
                record["slow"] = _slow(wt.path, node="refute")
            out["mutants"].append(record)
            print(
                f"[{mutant['id']}] fast={_verdict(fast)} ({fast['seconds']}s) "
                f"{mutant['what']}",
                flush=True,
            )

        # ---- combined escape tree, slow tier ------------------------------
        if not opts.fast_only:
            wt.reset()
            for mutant in MUTANTS:
                if mutant["id"] in COMBINED:
                    mutant["apply"](wt.path)
            print(f"[combined {'+'.join(COMBINED)}] slow tier", flush=True)
            out["combined_escape_tree"] = {
                "mutants": COMBINED,
                "fast": _fast(wt.path),
                "slow": _slow(wt.path),
            }

    # ---- fold the combined slow verdict back into each member -------------
    combined = out.get("combined_escape_tree")
    for record in out["mutants"]:
        if combined and record["id"] in COMBINED:
            record["slow"] = dict(combined["slow"], via="combined_escape_tree")
        record["fast_verdict"] = _verdict(record["fast"])
        record["slow_verdict"] = _verdict(record["slow"])
        record["caught"] = "caught" in (record["fast_verdict"], record["slow_verdict"])

    caught = [r["id"] for r in out["mutants"] if r["caught"]]
    out["summary"] = {
        "mutants_built": len(out["mutants"]),
        "caught": caught,
        "escaped": [r["id"] for r in out["mutants"] if not r["caught"]],
        "caught_by_fast_tier": [
            r["id"] for r in out["mutants"] if r["fast_verdict"] == "caught"
        ],
        "caught_only_by_slow_tier": [
            r["id"]
            for r in out["mutants"]
            if r["slow_verdict"] == "caught" and r["fast_verdict"] != "caught"
        ],
        "power": f"{len(caught)}/{len(out['mutants'])}",
    }

    (HUNT_DIR / "results.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(out["summary"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
