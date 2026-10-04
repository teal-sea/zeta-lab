"""Fail-closed verdict tests; no local Lean compilation."""

import importlib.util
import os
from pathlib import Path

import pytest


SPEC = importlib.util.spec_from_file_location(
    "palomar_port_compare", Path(__file__).resolve().parents[1] / "scripts/palomar_port_compare.py"
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)
ACCEPT = "\n".join([*(f"{kernel} kernel accepts the solution" for kernel in MOD.KERNELS),
                    "Your solution is okay!"])


def test_exporter_children_use_pinned_binaries_before_elan(monkeypatch):
    monkeypatch.setenv("PATH", "/home/runner/.elan/bin:/usr/bin")
    env = MOD.compiler_environment(Path("/pinned/lean"), "/proof/lib")
    assert env["PATH"].split(os.pathsep)[0] == "/pinned/lean/bin"
    assert env["LEAN_PATH"] == "/proof/lib"
    assert env["LEAN_ABORT_ON_PANIC"] == "1"
    assert os.environ["PATH"] == "/home/runner/.elan/bin:/usr/bin"


def test_accepts_all_three_kernels():
    MOD.require_verdict(0, ACCEPT)


@pytest.mark.parametrize("kernel", MOD.KERNELS)
def test_missing_kernel_is_not_success(kernel):
    with pytest.raises(RuntimeError, match="Missing acceptance"):
        MOD.require_verdict(0, ACCEPT.replace(f"{kernel} kernel accepts the solution", ""))


@pytest.mark.parametrize("code,log", [(1, ACCEPT), (0, ""), (2, "bwrap: unavailable")])
def test_infrastructure_failure_and_empty_output_are_not_success(code, log):
    with pytest.raises(RuntimeError):
        MOD.require_verdict(code, log)


def test_negative_control_requires_the_actual_mismatch():
    MOD.require_verdict(1, "error: Challenge and solution theorem statement do not match: port_control",
                        mismatch=True)
    for code, log in ((0, ACCEPT), (1, "bwrap: permission denied"),
                      (2, "error: Challenge and solution theorem statement do not match")):
        with pytest.raises(RuntimeError):
            MOD.require_verdict(code, log, mismatch=True)
