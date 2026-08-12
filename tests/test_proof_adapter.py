"""The proof-agent adapter's contract: the kernel decides, locally, always.

The fast tier pins the contract with an injected runner (no toolchain
needed): the static scan's refusals, the compilation-alone-is-insufficient
rule from the Grasshopper case study, the not-decided path, and the
never-leave-a-broken-module-landed rule. One slow test runs the real
``lake build`` and is skipped wherever the Mathlib cache is absent.
"""

from __future__ import annotations

import shutil
import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from lean.proof_adapter import (  # noqa: E402
    LEAN_DIR,
    PACKAGE,
    check_lean_artifact,
    scan_source,
)

_CLEAN = "theorem adapter_smoke : 2 + 2 = 4 := rfl\n"


def _ok_runner(module_name: str, timeout: float):
    return True, "stub build succeeded"


def _fail_runner(module_name: str, timeout: float):
    return False, "stub build failed"


def _absent_runner(module_name: str, timeout: float):
    return None, "stub toolchain unavailable"


# ---------------------------------------------------------------------------
# 1. the static scan refuses what must never land
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "token,fragment",
    [
        ("sorry", "theorem t : 1 = 1 := by sorry\n"),
        ("admit", "theorem t : 1 = 1 := by admit\n"),
        ("axiom", "axiom convenient : 1 = 1\n"),
        ("native_decide", "theorem t : 1 = 1 := by native_decide\n"),
    ],
)
def test_the_scan_refuses(token: str, fragment: str) -> None:
    reasons = scan_source(fragment)
    assert reasons, f"the scan passed a source containing {token!r}"
    assert any(token in r for r in reasons)


def test_the_scan_is_conservative_even_in_comments() -> None:
    # Over-refusal is the safe failure mode for a gate; a comment containing
    # the token refuses, and that is the documented behaviour.
    assert scan_source("-- no sorry here\ntheorem t : 1 = 1 := rfl\n")


def test_a_clean_source_passes_the_scan() -> None:
    assert scan_source(_CLEAN) == ()


# ---------------------------------------------------------------------------
# 2. the contract: both legs, or not accepted
# ---------------------------------------------------------------------------


def test_a_clean_build_is_accepted_and_cleaned_up_only_on_rejection() -> None:
    verdict = check_lean_artifact(_CLEAN, "AdapterContractProbe", runner=_ok_runner)
    target = LEAN_DIR / PACKAGE / "AdapterContractProbe.lean"
    try:
        assert verdict["accepted"] is True
        assert verdict["sorry_free"] is True
        assert verdict["build_ok"] is True
        assert verdict["reasons"] == ()
        assert target.exists(), "an accepted artifact stays landed"
    finally:
        target.unlink(missing_ok=True)


def test_compilation_alone_is_insufficient() -> None:
    """The Grasshopper lesson: a building artifact with a sorry is refused,
    and the build is not even attempted."""
    calls: list[str] = []

    def counting_runner(module_name: str, timeout: float):
        calls.append(module_name)
        return True, "should never run"

    verdict = check_lean_artifact(
        "theorem t : 1 = 1 := by sorry\n", "AdapterSorryProbe", runner=counting_runner
    )
    assert verdict["accepted"] is False
    assert verdict["sorry_free"] is False
    assert verdict["build_ok"] is None
    assert calls == [], "the build ran on a source the scan had already refused"
    assert not (LEAN_DIR / PACKAGE / "AdapterSorryProbe.lean").exists()


def test_a_failed_build_is_refused_and_not_left_landed() -> None:
    verdict = check_lean_artifact(_CLEAN, "AdapterFailProbe", runner=_fail_runner)
    assert verdict["accepted"] is False
    assert verdict["build_ok"] is False
    assert any("kernel check failed" in r for r in verdict["reasons"])
    assert not (LEAN_DIR / PACKAGE / "AdapterFailProbe.lean").exists()


def test_an_unavailable_toolchain_is_not_decided_never_a_pass() -> None:
    verdict = check_lean_artifact(_CLEAN, "AdapterAbsentProbe", runner=_absent_runner)
    assert verdict["accepted"] is False
    assert verdict["build_ok"] is None
    assert any("not decided" in r for r in verdict["reasons"])
    assert not (LEAN_DIR / PACKAGE / "AdapterAbsentProbe.lean").exists()


def test_an_existing_module_is_never_overwritten() -> None:
    existing = LEAN_DIR / PACKAGE / "GroundTruth.lean"
    original = existing.read_text(encoding="utf-8")
    verdict = check_lean_artifact(_CLEAN, "GroundTruth", runner=_ok_runner)
    assert verdict["accepted"] is False
    assert any("refusing to overwrite" in r for r in verdict["reasons"])
    assert existing.read_text(encoding="utf-8") == original


def test_a_module_name_that_is_not_a_lean_identifier_is_refused() -> None:
    with pytest.raises(ValueError, match="module identifier"):
        check_lean_artifact(_CLEAN, "../escape", runner=_ok_runner)


# ---------------------------------------------------------------------------
# 3. the real kernel, where the cache exists
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_the_real_kernel_accepts_a_trivial_theorem() -> None:
    if shutil.which("lake") is None:
        pytest.skip("no lake on PATH")
    if not (LEAN_DIR / ".lake").is_dir():
        pytest.skip("no .lake build cache here; the real build would fetch Mathlib")
    verdict = check_lean_artifact(_CLEAN, "AdapterKernelProbe", timeout=600.0)
    target = LEAN_DIR / PACKAGE / "AdapterKernelProbe.lean"
    try:
        assert verdict["accepted"] is True, verdict
    finally:
        target.unlink(missing_ok=True)
