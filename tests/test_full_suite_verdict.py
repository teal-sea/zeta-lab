"""The nightly's numerical suite cannot be skipped quietly (issue #251).

``full.yml`` lets a hand dispatch with ``lean_only`` skip the ``full-suite``
job, and a skipped job does not fail a run.  ``full-suite-verdict`` mirrors
``lean-verdict``: it needs ``full-suite``, always runs, and fails on every
result but success, except a skip that a ``lean_only`` dispatch ordered.

The verdict step's shell is executed here under each result and event, so the
guard is tested by behaviour rather than by reading it.  The schedule-skip
case is the one the issue is about: it must be red.
"""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest
import yaml

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "full.yml"


def _jobs():
    return yaml.safe_load(WORKFLOW.read_text())["jobs"]


def _verdict_script():
    steps = _jobs()["full-suite-verdict"]["steps"]
    (step,) = [s for s in steps if "run" in s]
    return step["run"], step["env"]


def test_the_guard_is_wired_like_lean_verdict():
    jobs = _jobs()
    guard = jobs["full-suite-verdict"]
    assert guard["needs"] == "full-suite"
    assert guard["if"] == "always()"
    # the sibling it mirrors is still there
    assert jobs["lean-verdict"]["needs"] == "lean"
    assert jobs["lean-verdict"]["if"] == "always()"
    # the env feeds the script the three facts it decides on
    _, env = _verdict_script()
    assert env["RESULT"] == "${{ needs.full-suite.result }}"
    assert env["EVENT"] == "${{ github.event_name }}"
    assert env["LEAN_ONLY"] == "${{ inputs.lean_only }}"


@pytest.mark.skipif(shutil.which("bash") is None, reason="needs bash")
@pytest.mark.parametrize(
    "result, event, lean_only, passes",
    [
        ("success", "schedule", "", True),
        ("success", "workflow_dispatch", "false", True),
        # the defect: on the schedule `inputs` is empty, so a skip there is a
        # silent zero and must fail
        ("skipped", "schedule", "", False),
        ("skipped", "workflow_dispatch", "false", False),
        ("skipped", "workflow_dispatch", "", False),
        # the one ordered skip
        ("skipped", "workflow_dispatch", "true", True),
        # lean_only does not excuse anything but a skip
        ("failure", "workflow_dispatch", "true", False),
        ("cancelled", "workflow_dispatch", "true", False),
        ("failure", "schedule", "", False),
        ("cancelled", "schedule", "", False),
        ("", "schedule", "", False),
        ("neutral", "schedule", "", False),
    ],
)
def test_the_verdict_step_fails_on_anything_but_success_or_an_ordered_skip(
    result, event, lean_only, passes
):
    script, _ = _verdict_script()
    env = dict(os.environ, RESULT=result, EVENT=event, LEAN_ONLY=lean_only)
    proc = subprocess.run(
        ["bash", "-c", script], env=env, capture_output=True, text=True, timeout=30
    )
    assert (proc.returncode == 0) is passes, proc.stdout + proc.stderr
