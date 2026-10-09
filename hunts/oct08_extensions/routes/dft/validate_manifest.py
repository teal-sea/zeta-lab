#!/usr/bin/env python3
"""Validate computation evidence, or explicitly check an unfilled template."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import sys

REQUIRED_TOP = {
    "schema_version",
    "claim_id",
    "repository",
    "command",
    "environment",
    "mathematics",
    "randomness",
    "run",
    "outputs",
    "checks",
    "result",
    "residual_risks",
}
REQUIRED_MATH = {
    "assertion_tested",
    "coefficient_domain",
    "conventions",
    "inputs",
    "bounds",
    "non_claims",
}

RUN_STATUSES_V2 = {
    "completed",
    "failed",
    "timeout",
    "output-limit",
    "launch-failed",
    "inputs-changed",
    "resource-limit",
    "result-missing",
    "result-invalid",
}


def file_hash(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def safe_project_path(root, name):
    """Resolve a relative artifact path without allowing it to escape root."""
    source = Path(name)
    resolved_root = root.resolve()
    if source.is_absolute() or ".." in source.parts:
        return None
    candidate = (resolved_root / source).resolve()
    return candidate if candidate.is_relative_to(resolved_root) else None


def safe_relative_name(name):
    if not isinstance(name, str) or not name.strip():
        return False
    path = Path(name)
    return not path.is_absolute() and ".." not in path.parts


def resolve_output_path(schema_version, root, manifest_path, name):
    """Resolve an output, with an ambiguity-safe v1 manifest-relative fallback."""
    project_candidate = safe_project_path(root, name)
    if project_candidate is None:
        return None, "escape"
    if schema_version != 1 or manifest_path is None:
        return project_candidate, "project"
    manifest_directory = Path(manifest_path).resolve().parent
    resolved_root = root.resolve()
    if not manifest_directory.is_relative_to(resolved_root):
        return project_candidate, "project"
    local_candidate = safe_project_path(manifest_directory, name)
    if local_candidate is None or not local_candidate.is_relative_to(resolved_root):
        return project_candidate, "project"
    if local_candidate == project_candidate:
        return project_candidate, "project"
    project_exists = project_candidate.is_file()
    local_exists = local_candidate.is_file()
    if project_exists and local_exists:
        return None, "ambiguous"
    if not project_exists and local_exists:
        return local_candidate, "manifest"
    return project_candidate, "project"


def legacy_limits(obj, root=None, manifest_path=None):
    """Return limitations inherent in a valid version 1 evidence record."""
    if isinstance(obj, dict) and obj.get("schema_version") == 1:
        limits = [
            "schema version 1 does not require hashes of execution inputs",
            "schema version 1 does not record machine-checkable resource limits or declared result files",
            "schema version 1 output paths may be project-root- or manifest-relative; ambiguous paths are rejected",
        ]
        repository = obj.get("repository")
        commit = repository.get("commit") if isinstance(repository, dict) else None
        if not isinstance(commit, str) or not commit.strip() or commit.strip().lower() == "unavailable":
            limits.append("the legacy record does not identify a repository revision")
        if root is not None and manifest_path is not None:
            for output in obj.get("outputs", []) if isinstance(obj.get("outputs"), list) else []:
                if not isinstance(output, dict) or not isinstance(output.get("path"), str):
                    continue
                _, mode = resolve_output_path(1, Path(root), Path(manifest_path), output["path"])
                if mode == "manifest":
                    limits.append("at least one output was resolved relative to the manifest directory")
                    break
        return limits
    return []


def validate(obj, template=False, root=None, manifest_path=None):
    errors = []

    def check(condition, message):
        if not condition:
            errors.append(message)

    if not isinstance(obj, dict):
        return ["top level must be an object"]
    missing = REQUIRED_TOP - obj.keys()
    check(not missing, "missing required top-level fields: " + ", ".join(sorted(missing)))
    schema_version = obj.get("schema_version")
    check(type(schema_version) is int and schema_version in {1, 2}, "unsupported schema_version")
    maths = obj.get("mathematics")
    if not isinstance(maths, dict):
        return errors + ["mathematics must be an object"]
    missing = REQUIRED_MATH - maths.keys()
    check(not missing, "missing mathematics fields: " + ", ".join(sorted(missing)))
    for key in ("repository", "environment", "randomness", "run"):
        check(isinstance(obj.get(key), dict), f"{key} must be an object")
    for key in ("outputs", "checks", "residual_risks"):
        check(isinstance(obj.get(key), list), f"{key} must be an array")
    if errors or template:
        return errors

    def nonempty(value):
        return isinstance(value, str) and bool(value.strip())

    for key in ("claim_id", "result"):
        check(nonempty(obj.get(key)), f"{key} must be nonempty")
    command = obj.get("command")
    check(nonempty(command) or (isinstance(command, list) and bool(command) and all(nonempty(x) for x in command)),
          "command must be nonempty text or an argv array")
    for key in ("assertion_tested", "coefficient_domain", "conventions"):
        check(nonempty(maths.get(key)), f"mathematics.{key} must be nonempty")
    check(isinstance(maths.get("inputs"), list), "mathematics.inputs must be an array")
    check(isinstance(maths.get("bounds"), dict) and bool(maths["bounds"]), "mathematics.bounds must state the tested range")
    check(isinstance(maths.get("non_claims"), list) and bool(maths["non_claims"]) and all(nonempty(x) for x in maths["non_claims"]),
          "mathematics.non_claims must state the limits")
    check(type(obj["repository"].get("dirty")) is bool, "repository.dirty must be boolean")
    commit = obj["repository"].get("commit")
    if schema_version == 1:
        check(commit is None or isinstance(commit, str), "legacy repository.commit must be text, null, or absent")
    else:
        check(nonempty(commit), "repository.commit must be recorded (or explicitly unavailable)")
    software = obj["environment"].get("software")
    check(isinstance(software, list) and bool(software), "environment.software must record versions")
    for i, entry in enumerate(software if isinstance(software, list) else []):
        if schema_version == 1:
            # Historical v1 records allowed one nonempty, human-readable version
            # string per program. Structured records were also valid and remain so.
            valid = nonempty(entry) or (
                isinstance(entry, dict)
                and nonempty(entry.get("name"))
                and nonempty(entry.get("version"))
            )
            check(valid, f"environment.software[{i}] needs a nonempty version string or a name/version object")
        else:
            check(isinstance(entry, dict) and nonempty(entry.get("name")) and nonempty(entry.get("version")),
                  f"environment.software[{i}] needs a name and a version")
    randomness = obj["randomness"]
    check(type(randomness.get("used")) is bool, "randomness.used must be boolean")
    if randomness.get("used"):
        check(nonempty(randomness.get("generator")) and randomness.get("seed") is not None, "random runs need generator and seed")
    run = obj["run"]
    check(nonempty(run.get("started_at")), "run.started_at must be recorded")
    runtime = run.get("runtime_seconds")
    check(type(runtime) in {float, int} and math.isfinite(runtime) and runtime >= 0, "runtime must be finite and nonnegative")
    check(type(run.get("exit_status")) is int, "run.exit_status must be an integer")
    check(bool(obj["outputs"]), "outputs must include hashed artifacts")
    for i, output in enumerate(obj["outputs"]):
        if not isinstance(output, dict):
            errors.append(f"outputs[{i}] must be an object")
            continue
        path, checksum = output.get("path"), output.get("sha256")
        check(nonempty(path), f"outputs[{i}].path must be nonempty")
        if schema_version == 2:
            check(safe_relative_name(path), f"outputs[{i}].path must be project-relative")
        if schema_version == 2 and "kind" in output:
            check(output.get("kind") in {"log", "result"}, f"outputs[{i}].kind must be log or result")
        valid_hash = isinstance(checksum, str) and bool(re.fullmatch(r"[0-9a-f]{64}", checksum))
        check(valid_hash, f"outputs[{i}].sha256 must be SHA-256")
        if root is not None and nonempty(path) and valid_hash:
            source, mode = resolve_output_path(schema_version, Path(root), manifest_path, path)
            if mode == "escape":
                errors.append(f"output escapes project: {path}")
            elif mode == "ambiguous":
                errors.append(f"ambiguous legacy output path exists relative to both project and manifest: {path}")
            elif source is None or not source.is_file():
                errors.append(f"output missing: {path}")
            elif file_hash(source) != checksum:
                errors.append(f"output changed: {path}")
    if schema_version == 2:
        v2_output_paths = [
            output.get("path") for output in obj.get("outputs", [])
            if isinstance(output, dict) and isinstance(output.get("path"), str)
        ]
        check(len(v2_output_paths) == len(set(v2_output_paths)), "v2 output paths must be unique")
        check(run.get("status") in RUN_STATUSES_V2, "invalid run.status")
        if run.get("status") == "completed":
            check(run.get("exit_status") == 0, "completed run must have zero exit status")
        if run.get("status") in {"inputs-changed", "result-missing", "result-invalid"}:
            check(run.get("exit_status") == 0, f"{run.get('status')} run must have zero process exit status")
        check(isinstance(obj.get("input_artifacts"), list) and bool(obj["input_artifacts"]), "v2 needs input_artifacts")
        v2_input_paths = [
            artifact.get("path")
            for artifact in obj.get("input_artifacts", [])
            if isinstance(artifact, dict) and isinstance(artifact.get("path"), str)
        ]
        check(len(v2_input_paths) == len(set(v2_input_paths)), "v2 input artifact paths must be unique")
        for artifact in obj.get("input_artifacts", []) if isinstance(obj.get("input_artifacts"), list) else []:
            if not isinstance(artifact, dict):
                errors.append("input artifact must be an object")
                continue
            path, before, after = artifact.get("path"), artifact.get("sha256"), artifact.get("sha256_after")
            check(nonempty(path), "input artifact needs a path")
            check(safe_relative_name(path), "input artifact path must be project-relative")
            valid_before = isinstance(before, str) and bool(re.fullmatch(r"[0-9a-f]{64}", before))
            valid_after = after is None or (isinstance(after, str) and bool(re.fullmatch(r"[0-9a-f]{64}", after)))
            check(valid_before and valid_after and "sha256_after" in artifact, "input artifact needs before/after hashes")
            if run.get("status") == "completed":
                check(before == after and after is not None, "completed run cannot have changed input hashes")
            if root is not None and nonempty(path):
                source = Path(path)
                if source.is_absolute() or ".." in source.parts or not (root / source).resolve().is_relative_to(root.resolve()):
                    errors.append(f"input escapes project: {path}")
                elif not (root / source).is_file():
                    # An absent input cannot corroborate the record, whatever was hashed.
                    errors.append(f"pinned input is missing: {path}")
                else:
                    check(file_hash(root / source) == after, f"input changed since the run: {path}")
        execution_artifacts = obj.get("execution_artifacts")
        if execution_artifacts is not None:
            check(
                isinstance(execution_artifacts, list)
                and all(safe_relative_name(path) for path in execution_artifacts)
                and len(execution_artifacts) == len(set(execution_artifacts)),
                "execution_artifacts must be a duplicate-free array of paths",
            )
            if isinstance(execution_artifacts, list):
                pinned = [
                    artifact.get("path")
                    for artifact in obj.get("input_artifacts", [])
                    if isinstance(artifact, dict) and isinstance(artifact.get("path"), str)
                ]
                check(set(execution_artifacts) == set(pinned),
                      "execution_artifacts must match pinned input_artifacts")
        declared_results = obj.get("declared_results")
        output_paths = {
            output.get("path")
            for output in obj.get("outputs", [])
            if isinstance(output, dict) and isinstance(output.get("path"), str)
        }
        result_output_paths = {
            output.get("path")
            for output in obj.get("outputs", [])
            if isinstance(output, dict) and output.get("kind") == "result"
            and isinstance(output.get("path"), str)
        }
        pinned_set = {
            artifact.get("path")
            for artifact in obj.get("input_artifacts", [])
            if isinstance(artifact, dict) and isinstance(artifact.get("path"), str)
        }
        has_result_outputs = any(
            isinstance(output, dict) and output.get("kind") == "result"
            for output in obj.get("outputs", [])
        )
        if declared_results is None:
            check(not has_result_outputs, "result outputs require declared_results")
        if declared_results is not None:
            check(
                isinstance(declared_results, list)
                and all(safe_relative_name(path) for path in declared_results)
                and len(declared_results) == len(set(declared_results)),
                "declared_results must be a duplicate-free array of paths",
            )
            if isinstance(declared_results, list):
                declared_set = set(declared_results)
                check(declared_set.isdisjoint(pinned_set),
                      "declared_results cannot overlap input_artifacts")
                check(result_output_paths.issubset(declared_set),
                      "result outputs must have been declared before execution")
                if run.get("status") == "completed":
                    check(declared_set.issubset(result_output_paths),
                          "completed run must hash every declared result")
                missing = run.get("missing_results")
                invalid = run.get("invalid_results")
                if missing is not None or invalid is not None:
                    check(isinstance(missing, list) and all(nonempty(path) for path in missing),
                          "run.missing_results must be an array of paths")
                    check(isinstance(invalid, list) and all(nonempty(path) for path in invalid),
                          "run.invalid_results must be an array of paths")
                    if (isinstance(missing, list) and isinstance(invalid, list)
                            and all(isinstance(path, str) for path in missing + invalid)):
                        check(set(missing).isdisjoint(invalid),
                              "missing_results and invalid_results must be disjoint")
                        check(set(missing) | set(invalid) == declared_set - result_output_paths,
                              "missing/invalid result records must account for every unhashed declared result")
                if run.get("status") == "result-missing":
                    check(isinstance(missing, list) and bool(missing),
                          "result-missing status needs at least one missing result")
                if run.get("status") == "result-invalid":
                    check(isinstance(invalid, list) and bool(invalid),
                          "result-invalid status needs at least one invalid result")
        output_directory = obj.get("output_directory")
        if output_directory is not None:
            valid_output_directory = safe_relative_name(output_directory) and Path(output_directory) != Path(".")
            check(valid_output_directory, "output_directory must be a nonempty project-relative directory")
            if valid_output_directory:
                directory = Path(output_directory)
                for path in output_paths:
                    if isinstance(path, str):
                        check(Path(path) != directory and Path(path).is_relative_to(directory),
                              f"output must be below output_directory: {path}")
                for path in declared_results if isinstance(declared_results, list) else []:
                    check(Path(path) != directory and Path(path).is_relative_to(directory),
                          f"declared result must be below output_directory: {path}")
                for path in pinned_set:
                    if isinstance(path, str):
                        check(not Path(path).is_relative_to(directory),
                              f"input artifact cannot be inside output_directory: {path}")
        limits = run.get("resource_limits")
        if limits is not None:
            check(isinstance(limits, dict), "run.resource_limits must be an object")
            if isinstance(limits, dict):
                missing_limits = {"memory_bytes", "cpu_seconds", "max_cores", "max_threads"} - limits.keys()
                check(not missing_limits, "run.resource_limits is missing: " + ", ".join(sorted(missing_limits)))
            for key in ("memory_bytes", "cpu_seconds", "max_cores", "max_threads"):
                value = limits.get(key) if isinstance(limits, dict) else None
                check(value is None or (type(value) is int and value > 0),
                      f"run.resource_limits.{key} must be null or a positive integer")
    return errors


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--template", action="store_true", help="allow deliberately unfilled scaffold fields")
    parser.add_argument(
        "--root", type=Path,
        help="verify artifacts in this project (v1 may fall back to the manifest directory)",
    )
    args = parser.parse_args(argv)
    obj = None
    try:
        obj = json.loads(args.manifest.read_text(encoding="utf-8"))
        errors = validate(obj, args.template, args.root, args.manifest)
    except (OSError, ValueError, TypeError) as exc:
        errors = [str(exc)]
    if errors:
        print("invalid manifest: " + "; ".join(errors), file=sys.stderr)
        return 1
    if args.template:
        print("valid template")
    elif legacy_limits(obj, args.root, args.manifest):
        print("valid legacy version 1 evidence record; "
              + "; ".join(legacy_limits(obj, args.root, args.manifest))
              + "; mathematical interpretation requires review")
    else:
        print("valid evidence record; mathematical interpretation requires review")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

