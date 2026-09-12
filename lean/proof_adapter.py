"""proof_adapter, external provers plug in as generators; the kernel decides.

The contract (ROADMAP.md, "The AI-implementation half", adopted build 4):

    generated Lean -> this repo's `lake build` -> zero `sorry` -> artifact

An external proof service's own "verified" claim is *input, not evidence*,
the Grasshopper case study (arXiv 2605.20120) found artifacts that compile
while a `sorry` closes the main theorem, which is this repository's oldest
Lean rule rediscovered outside it. So acceptance here has exactly two legs,
and both are local:

1. a **static refusal scan** of the source: any `sorry`, `admit`, `axiom`
   declaration or `native_decide` is a named reason to refuse. The scan is
   deliberately conservative, a match inside a comment or string still
   refuses, because the safe failure mode for a proof gate is over-refusal,
   never under;
2. a **kernel check**: `lake build` of the dropped-in module against the
   pinned ZetaLean toolchain, run by this machine, not by the service.

``accepted`` is True only when both legs pass. Anything else returns
``accepted: False`` with every reason named, in the same
safe-failure style as ``zeta.rigor`` (``build_ok: None`` means the build was
not run or could not run, "not decided", never "fine").

Submission to a generator (Harmonic's Aristotle is the first backend) is the
optional half: :func:`submit_to_aristotle` needs ``aristotlelib`` (installed
in ``.venv-tools``, not the pinned lab venv) and ``ARISTOTLE_API_KEY``. The
adapter works without either, you can hand-check any .lean artifact:

    .venv/bin/python lean/proof_adapter.py check path/to/artifact.lean

Nothing this module returns uses the reserved word: an accepted artifact is
*kernel-checked here*, and the module it landed in is what carries the claim.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent
PACKAGE = "ZetaLean"

#: Constructs that make a compiling artifact untrusted anyway. ``sorry`` and
#: ``admit`` are unfinished proofs; an ``axiom`` smuggles the theorem in as
#: an assumption; ``native_decide`` replaces the kernel with the compiler.
_REFUSALS = (
    (re.compile(r"\bsorry\b"), "contains `sorry`: an uncertified step"),
    (re.compile(r"\badmit\b"), "contains `admit`: an uncertified step"),
    (re.compile(r"^\s*axiom\b", re.MULTILINE), "declares an `axiom`: assumes what it should prove"),
    (
        re.compile(r"\bnative_decide\b"),
        "uses `native_decide`: trusts the compiler instead of the kernel",
    ),
)


def scan_source(source: str) -> tuple[str, ...]:
    """Every named reason the source is refused before any build runs.

    Conservative on purpose: a match inside a comment or a string literal
    still refuses. A generated proof has no business containing these tokens
    anywhere, and over-refusal is the safe failure mode for a gate.
    """

    return tuple(reason for pattern, reason in _REFUSALS if pattern.search(source))


def _default_runner(module_name: str, timeout: float) -> tuple[bool | None, str]:
    """Run ``lake build`` for one module. Returns (build_ok, detail).

    ``None`` means the build could not run at all (no toolchain, timeout),
    "not decided", which the caller must not upgrade to a pass.
    """

    env = dict(os.environ)
    elan_bin = str(Path.home() / ".elan" / "bin")
    env["PATH"] = os.pathsep.join([elan_bin, env.get("PATH", "")])
    if shutil.which("lake", path=env["PATH"]) is None:
        return None, "lake not found on PATH (Lean toolchain unavailable here)"
    try:
        result = subprocess.run(
            ["lake", "build", f"{PACKAGE}.{module_name}"],
            cwd=LEAN_DIR,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None, f"lake build exceeded {timeout:.0f}s: not decided"
    if result.returncode == 0:
        return True, "lake build succeeded"
    tail = (result.stdout + result.stderr).strip().splitlines()[-8:]
    return False, "lake build failed: " + " | ".join(tail)


def check_lean_artifact(
    source: str,
    module_name: str,
    *,
    build: bool = True,
    timeout: float = 1800.0,
    runner=_default_runner,
) -> dict:
    """The whole contract for one artifact, as a dict in rigor's honest style.

    ``accepted`` is True only when the static scan refuses nothing AND the
    local build succeeded. ``build_ok: None`` (not run, or could not run)
    keeps ``accepted`` False with the reason named. The artifact is written
    into ``lean/ZetaLean/<module_name>.lean`` only when the scan passes and
    ``build`` is requested; a refused artifact never lands in the package.
    """

    if not re.fullmatch(r"[A-Z][A-Za-z0-9]*", module_name):
        raise ValueError(
            f"module_name {module_name!r} must be a Lean module identifier "
            "(UpperCamelCase, letters and digits)"
        )
    scan_reasons = scan_source(source)
    reasons = list(scan_reasons)
    build_ok: bool | None = None
    detail = "build not attempted"
    if reasons:
        detail = "build skipped: the static scan already refused the artifact"
    elif build:
        target = LEAN_DIR / PACKAGE / f"{module_name}.lean"
        if target.exists() and target.read_text(encoding="utf-8") != source:
            reasons.append(
                f"module {module_name!r} already exists with different "
                "content: refusing to overwrite a landed artifact"
            )
            detail = "build skipped: target collision"
        else:
            preexisting = target.exists()
            target.write_text(source, encoding="utf-8")
            build_ok, detail = runner(module_name, timeout)
            if build_ok is None:
                reasons.append(f"kernel check not decided: {detail}")
            elif build_ok is False:
                reasons.append(f"kernel check failed: {detail}")
            if reasons and not preexisting:
                # A rejected artifact never stays landed: a broken module in
                # the package would fail everyone's next full build.
                target.unlink(missing_ok=True)
    return {
        "module": f"{PACKAGE}.{module_name}",
        "sorry_free": not scan_reasons,
        "build_ok": build_ok,
        "build_detail": detail,
        "accepted": build_ok is True and not reasons,
        "reasons": tuple(reasons),
    }


def submit_to_aristotle(statement: str) -> str:
    """Send one precise, standalone statement to the Aristotle API.

    Creates a Project (``aristotlelib.project.Project.create``, verified
    against aristotlelib 2.1.0's real async surface) and returns its
    ``project_id`` immediately: Aristotle runs for hours, so the submit
    and the collect are separate steps. Collect later with
    :func:`collect_from_aristotle`. The eventual Lean is INPUT, feed it to
    :func:`check_lean_artifact`; nothing about the service's own
    verification status is read, recorded, or trusted. Local lemmas, never
    "the theorem", are the right grain (the Grasshopper case study's
    lesson).

    Requires ``ARISTOTLE_API_KEY`` in the environment and ``aristotlelib``
    on this interpreter (it lives in ``.venv-tools``, not the lab venv).
    """

    project = _aristotle_project_class()
    import asyncio

    created = asyncio.run(project.create(prompt=statement))
    return str(created.project_id)


def collect_from_aristotle(project_id: str, destination: str | os.PathLike | None = None) -> dict:
    """Fetch a submitted project's status and, when finished, its files.

    Returns ``{"status": ..., "files": path-or-None}``. The files are raw
    generated input for :func:`check_lean_artifact`; a status other than
    finished returns ``files: None`` and the caller waits, polling every
    few hours is the right cadence, not every few seconds.
    """

    project_class = _aristotle_project_class()
    import asyncio

    async def _collect():
        project = await project_class.from_id(project_id)
        status = getattr(project, "status", None)
        files = None
        # aristotlelib 2.1.0's ProjectStatus is UNKNOWN / RUNNING / IDLE:
        # IDLE is "done working", and the files are whatever the run left.
        if status is not None and getattr(status, "name", "") == "IDLE":
            files = str(await project.get_files(destination))
        return {"status": getattr(status, "name", str(status)), "files": files}

    return asyncio.run(_collect())


def _aristotle_project_class():
    if not os.environ.get("ARISTOTLE_API_KEY"):
        raise RuntimeError(
            "ARISTOTLE_API_KEY is not set: create a key at "
            "aristotle.harmonic.fun (Dashboard -> API Keys), or source "
            "~/.zshrc where it is stored"
        )
    try:
        from aristotlelib.project import Project
    except ImportError as exc:  # pragma: no cover - environment-dependent
        raise RuntimeError(
            "aristotlelib is not importable from this interpreter; it is "
            "installed in .venv-tools, run this command with "
            ".venv-tools/bin/python, or install it where you stand"
        ) from exc
    return Project


def _main(argv: list[str]) -> int:
    if len(argv) >= 2 and argv[0] == "check":
        path = Path(argv[1])
        module_name = argv[2] if len(argv) > 2 else "AdapterCandidate"
        verdict = check_lean_artifact(
            path.read_text(encoding="utf-8"), module_name
        )
        for key, value in verdict.items():
            print(f"{key}: {value}")
        return 0 if verdict["accepted"] else 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))
