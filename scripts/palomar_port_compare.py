#!/usr/bin/env python3
"""Compare the already-built port, not a fresh Palomar registration.

Use the pinned Palomar verifier's pure export-target helpers. Builds and
exports here are trusted local research artifacts; lake comparator sandboxes
the kernel checks. This does not replace Palomar's protected-source pipeline.
"""

from __future__ import annotations

import argparse
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time


PIPELINE_REVISION = "65f0154ed776cd26c224254aa57b379137f28b0d"
KERNELS = ("Lean default", "nanoda", "con-ron")


def compiler_environment(prefix: Path, lean_path: str) -> dict[str, str]:
    """Exporter subprocesses must find the pinned binaries, not elan shims."""
    return dict(os.environ, PATH=str(prefix / "bin") + os.pathsep + os.environ["PATH"],
                LEAN_PATH=lean_path, LEAN_ABORT_ON_PANIC="1")


def require_verdict(returncode: int, log: str, *, mismatch: bool = False) -> None:
    """Reject infrastructure errors and partial kernel acceptance."""
    if mismatch:
        if returncode != 1 or not any(
            line.startswith("error: Challenge and solution theorem statement do not match")
            for line in log.splitlines()
        ):
            raise RuntimeError("Negative control did not report a statement mismatch")
        return
    if returncode != 0 or "Your solution is okay!" not in log.splitlines():
        raise RuntimeError("Comparator did not accept the pair")
    for kernel in KERNELS:
        if f"{kernel} kernel accepts the solution" not in log.splitlines():
            raise RuntimeError(f"Missing acceptance from {kernel}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pipeline", required=True, type=Path)
    parser.add_argument("--package", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    args = parser.parse_args()
    pipeline, package, evidence = (p.resolve() for p in (args.pipeline, args.package, args.evidence))
    evidence.mkdir(parents=True, exist_ok=False)
    report = {"status": "running", "comparisons_passed": 0, "negative_controls_passed": 0}
    started = time.monotonic()

    def record() -> None:
        report["elapsed_seconds"] = round(time.monotonic() - started, 2)
        (evidence / "outcome.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report), flush=True)

    def run(command: list[str], label: str, *, cwd: Path = package,
            env: dict[str, str] | None = None, check: bool = True,
            output: Path | None = None) -> subprocess.CompletedProcess:
        report["stage"] = label
        record()
        with (evidence / f"{label}.log").open("wb") as log:
            if output is None:
                proc = subprocess.run(command, cwd=cwd, env=env, stdout=log,
                                      stderr=subprocess.STDOUT, timeout=1800)
            else:
                with output.open("xb") as exported:
                    proc = subprocess.run(command, cwd=cwd, env=env, stdout=exported,
                                          stderr=log, timeout=1800)
        if check and proc.returncode:
            raise RuntimeError(f"{label} exited {proc.returncode}; see its log")
        return proc

    record()
    try:
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=pipeline, text=True
        ).strip()
        if revision != PIPELINE_REVISION:
            raise RuntimeError("Palomar helper revision differs from the audited pin")
        sys.path.insert(0, str(pipeline))
        verifier = importlib.import_module("scripts.verify_submission")
        prefix = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=package, text=True).strip())
        tools = verifier.toolchain_tools(prefix)
        primitives = verifier.primitive_targets(prefix)
        kernels = verifier.protected_kernels(tools)
        lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                           cwd=package, text=True).strip()
        if not lean_path:
            raise RuntimeError("Lake returned an empty module search path")
        env = compiler_environment(prefix, lean_path)
        config = json.loads((package / "comparator.json").read_text())
        config.pop("enable_nanoda", None)
        config["external_kernels"] = kernels
        report["tool_digests"] = {name: verifier.sha256(path) for name, path in tools.items()}
        report["pipeline_revision"] = revision

        repository = Path(subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], cwd=package, text=True
        ).strip())
        tracked = subprocess.check_output(
            ["git", "ls-files", "-z", "--", "*.lean"], cwd=repository
        ).decode().split("\0")
        sources = [repository / path for path in tracked if path and Path(path).name != "lakefile.lean"]
        if not sources:
            raise RuntimeError("Zero tracked Lean source headers found")
        report["source_headers_expected"] = len(sources)
        report["source_headers_checked"] = 0
        for start in range(0, len(sources), 64):
            batch = sources[start:start + 64]
            label = f"headers-{start}"
            run([str(tools["lean"]), "--deps-json", *(str(path) for path in batch)], label)
            entries = json.loads((evidence / f"{label}.log").read_text())["imports"]
            if len(entries) != len(batch):
                raise RuntimeError("Lean header count differs from requested source count")
            for path, entry in zip(batch, entries, strict=True):
                if not verifier.parse_lean_header(json.dumps({"imports": [entry]})).is_module:
                    raise RuntimeError(f"Lean rejected module format for {path}")
                report["source_headers_checked"] += 1
            record()

        def compare(cfg: dict, challenge: Path, solution: Path, label: str,
                    *, mismatch: bool = False) -> None:
            config_path = evidence / f"{label}.json"
            config_path.write_text(json.dumps(cfg, indent=2) + "\n")
            proc = run([str(tools["lake"]), "comparator", "--config", str(config_path),
                        "--challenge-from-export", str(challenge),
                        "--solution-from-export", str(solution)], label, cwd=evidence, env=env, check=False)
            require_verdict(proc.returncode, (evidence / f"{label}.log").read_text(), mismatch=mismatch)
            counter = "negative_controls_passed" if mismatch else "comparisons_passed"
            report[counter] += 1
            record()

        control = dict(config, challenge_module="PortChallenge", solution_module="PortSolution",
                       theorem_names=["port_control"], definition_names=[])
        targets = verifier.comparator_export_targets(control, primitives)
        control_env = dict(env, LEAN_PATH=str(evidence) + os.pathsep + str(prefix / "lib" / "lean"))
        for module, statement, proof in (("PortChallenge", "True", "trivial"),
                                         ("PortSolution", "True", "trivial"),
                                         ("PortWrong", "And True True", "And.intro trivial trivial")):
            source = evidence / f"{module}.lean"
            source.write_text(f"module\n@[expose] public section\ntheorem port_control : {statement} := {proof}\n")
            run([str(tools["lean"]), "-o", str(evidence / f"{module}.olean"), str(source)],
                f"build-{module}", cwd=evidence, env=control_env)
            run([str(tools["leanexport"]), module, "--", *targets], f"export-{module}",
                cwd=evidence, env=control_env, output=evidence / f"{module}.export")
        compare(control, evidence / "PortChallenge.export", evidence / "PortSolution.export", "positive-control")
        compare(dict(control, solution_module="PortWrong"), evidence / "PortChallenge.export",
                evidence / "PortWrong.export", "negative-control", mismatch=True)

        targets = verifier.comparator_export_targets(config, primitives)
        for key in ("challenge_module", "solution_module"):
            module = config[key]
            run([str(tools["leanexport"]), module, "--", *targets], f"export-{module}",
                env=env, output=evidence / f"{module}.export")
        compare(config, evidence / f"{config['challenge_module']}.export",
                evidence / f"{config['solution_module']}.export", "stronger-four-point")
        report["status"] = "success"
    except BaseException as error:
        report["status"] = "failure"
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        record()


if __name__ == "__main__":
    main()
