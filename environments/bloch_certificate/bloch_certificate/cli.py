"""Download the pinned archive or run model-free positive/negative controls."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import urllib.request

from .bloch_certificate import DEFAULT_ARCHIVE
from .oracle import ARCHIVE_SHA256, ARCHIVE_URL, Oracle, OracleError


def prepare(path: Path) -> Path:
    path = Path(path)
    if path.exists():
        if hashlib.sha256(path.read_bytes()).hexdigest() != ARCHIVE_SHA256:
            raise OracleError("archive digest mismatch; remove it explicitly before retrying")
        return path
    # The pinned archive is under 8 MiB. Bound the download and its wait time.
    with urllib.request.urlopen(ARCHIVE_URL, timeout=60) as response:
        blob = response.read(16 * 1024 * 1024 + 1)
    if hashlib.sha256(blob).hexdigest() != ARCHIVE_SHA256:
        raise OracleError("download digest mismatch")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as output:
        temporary = Path(output.name)
        output.write(blob)
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)
    return path


def main_prepare():
    import sys
    sys.argv[1:1] = ["prepare"]
    main()


def main_smoke():
    import sys
    sys.argv[1:1] = ["smoke"]
    main()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["prepare", "smoke"])
    parser.add_argument("--archive", type=Path, default=Path(os.environ.get("BLOCH_ARCHIVE", DEFAULT_ARCHIVE)))
    args = parser.parse_args()
    archive = prepare(args.archive)
    if args.command == "prepare":
        print(json.dumps({"status": "ready", "archive": str(archive), "sha256": ARCHIVE_SHA256}))
        return
    oracle = Oracle(archive)
    controls = [
        ("fine-reproduce", "0.0114402996202", 1),
        ("coarse-reproduce", "0.0113729923988", 1),
        ("near-reproduce", "0.0153", 1),
        ("near-branch-cutoff", "0.0153040536", 1),
        ("fine-reproduce", "0.0113", 0),
        ("coarse-reproduce", "0.09", 0),
        ("near-branch-cutoff", "0.0153", 0),
        ("near-branch-cutoff", "0.0154", 0),
    ]
    for task, target, expected in controls:
        result = oracle.grade(task, json.dumps({"target": target}))
        result.update(control=True, expected_reward=expected)
        print(json.dumps(result), flush=True)
        if result["reward"] != expected:
            raise SystemExit("control failed")


if __name__ == "__main__":
    main()
