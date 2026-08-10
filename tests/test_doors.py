"""The doors policy, enforced.

``docs/doors/README.md`` states the cost of a purpose: a guide page plus a
test that the page's command still works.  Until now only the discover door
paid the second half (``test_script_13_discovery_run.py``); the learn and
refute doors were promises.  This file collects the debt:

* **fast** — every ``scripts/…`` command named in the doors README table
  points at a file that exists (a renamed script would otherwise break a
  door silently), and the ``interactive_lab`` page honours its stated
  contract (single file, parses as HTML, no external scripts);
* **slow** — the learn and refute door commands actually run to exit 0.
  The certify door's command is a Lean build (its own toolchain, checked by
  CI on ``lean/``), and the adopt door's command *is* the pytest suite —
  neither can be usefully re-run from inside a test here.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from html.parser import HTMLParser

import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOORS_README = os.path.join(REPO_ROOT, "docs", "doors", "README.md")


def _door_script_commands() -> list[str]:
    """Every ``scripts/<name>.py`` mentioned in a doors README command."""
    with open(DOORS_README, encoding="utf-8") as fh:
        text = fh.read()
    return sorted(set(re.findall(r"scripts/[\w.]+\.py", text)))


def test_the_doors_readme_names_only_scripts_that_exist():
    commands = _door_script_commands()
    assert commands, "the doors README stopped naming any script — table moved?"
    for rel in commands:
        assert os.path.isfile(os.path.join(REPO_ROOT, rel)), rel


class _PageAudit(HTMLParser):
    """Collects the two facts the interactive_lab contract pins."""

    def __init__(self) -> None:
        super().__init__()
        self.external_scripts: list[str] = []
        self.saw_title = False

    def handle_starttag(self, tag, attrs):
        if tag == "script" and dict(attrs).get("src"):
            self.external_scripts.append(dict(attrs)["src"])
        if tag == "title":
            self.saw_title = True


def test_interactive_lab_pages_are_single_file_and_script_free():
    """interactive_lab/README.md: 'open the file' must stay the whole
    instruction, so a page may not load code from anywhere else."""
    lab = os.path.join(REPO_ROOT, "interactive_lab")
    pages = [f for f in os.listdir(lab) if f.endswith(".html")]
    assert pages, "interactive_lab/ lost its pages but kept its README"
    for page in pages:
        audit = _PageAudit()
        with open(os.path.join(lab, page), encoding="utf-8") as fh:
            audit.feed(fh.read())
        assert audit.saw_title, page
        assert audit.external_scripts == [], (page, audit.external_scripts)


def _run_door(script: str, timeout: int) -> None:
    proc = subprocess.run(
        [sys.executable, os.path.join(REPO_ROOT, "scripts", script)],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        timeout=timeout,
    )
    assert proc.returncode == 0, proc.stdout[-2000:] + proc.stderr[-2000:]


@pytest.mark.slow
def test_the_learn_door_command_runs():
    """docs/doors/learn.md: the ~90 s tour exits 0."""
    _run_door("06_tour.py", timeout=600)


@pytest.mark.slow
def test_the_refute_door_command_runs():
    """docs/doors/refute.md: the gate-3 battery exits 0."""
    _run_door("23_gate_3_battery.py", timeout=600)
