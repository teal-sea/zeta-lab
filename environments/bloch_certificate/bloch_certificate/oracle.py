"""Exact inputs and archive-backed grading for the Bloch public demo."""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
import zipfile
from decimal import Decimal, localcontext
from pathlib import Path

ARCHIVE_URL = "https://zenodo.org/records/21975862/files/bloch-computations-1.0.0.zip?download=1"
ARCHIVE_SHA256 = "bdaa1ff347043a00733ca40d5db46c5418810d1f4e5c472d0bcb9de48ef408e7"


class OracleError(RuntimeError):
    """Infrastructure or verifier failure, never a wrong model answer."""


class Oracle:
    """Run only trusted archive code, outside the model's tool runtime.

    The archive location is operator configuration, not a tool argument.
    subprocess is process isolation, NOT an OS security sandbox. Never expose
    this process or cache to an untrusted shell on the same host/user.
    """

    def __init__(self, archive: Path, timeout: float = 90):
        self.archive = Path(archive)
        self.timeout = timeout
        self._cache = {}
        self._lock = threading.Lock()

    def run(self, mode: str) -> dict:
        if mode not in {"fine", "coarse", "near"}:
            raise ValueError("unknown verifier mode")
        with self._lock:
            try:
                blob = self.archive.read_bytes()
            except OSError as exc:
                raise OracleError("archive unavailable; run bloch-prepare first") from exc
            if hashlib.sha256(blob).hexdigest() != ARCHIVE_SHA256:
                raise OracleError("archive digest mismatch")
            if mode in self._cache:
                return dict(self._cache[mode], cached=True)
            start = time.monotonic()
            with tempfile.TemporaryDirectory(prefix="bloch-oracle-") as tmp:
                # Hash and extract the SAME bytes, avoiding a path swap between them.
                import io
                with zipfile.ZipFile(io.BytesIO(blob)) as archive:
                    prefix = "zenodo-bloch-computations/src/"
                    for member in archive.infolist():
                        relative = member.filename.removeprefix(prefix)
                        if (member.filename.startswith(prefix) and "/" not in relative
                                and Path(relative).suffix in {".py", ".npz"}):
                            Path(tmp, relative).write_bytes(archive.read(member))
                # No provider credentials or Python override flags reach upstream.
                env = {key: os.environ[key] for key in ("PATH", "SYSTEMROOT") if key in os.environ}
                env.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1")
                try:
                    process = subprocess.run(
                        [sys.executable, "-I", str(Path(__file__).with_name("worker.py")), tmp, mode],
                        cwd=tmp, env=env, text=True, capture_output=True, timeout=self.timeout,
                    )
                except subprocess.TimeoutExpired as exc:
                    raise OracleError(f"verifier timed out after {self.timeout}s") from exc
                if process.returncode:
                    raise OracleError(f"verifier exited {process.returncode}: {process.stderr[-2000:]}")
                try:
                    result = json.loads(process.stdout)
                    if not isinstance(result["gain"], str) or not result["log"]:
                        raise ValueError("missing verifier evidence")
                except (ValueError, KeyError, TypeError) as exc:
                    raise OracleError("malformed verifier output") from exc
            result.update(archive_sha256=ARCHIVE_SHA256, mode=mode,
                          elapsed_seconds=time.monotonic() - start, cached=False)
            self._cache[mode] = result
            return dict(result)


    def near_verdict(self, goal: str, target: Decimal) -> tuple[bool, dict]:
        if goal not in {"published", "cutoff"}:
            raise ValueError("goal must be published or cutoff")
        evidence = self.run("near")
        bound = Decimal.from_float(float(evidence["gain"]))
        with localcontext() as context:
            context.prec = 80
            floor = bound - Decimal("1e-10") if goal == "cutoff" else Decimal("0.0153")
        accepted = evidence["positivity"] > 0 and floor <= target < bound
        return accepted, evidence

    def grade(self, task: str, text: str) -> dict:
        if task not in {"fine-reproduce", "coarse-reproduce", "near-reproduce", "near-branch-cutoff"}:
            raise ValueError("unknown task")
        try:
            target = parse_target(text)
        except ValueError as exc:
            return {"reward": 0.0, "status": "invalid_submission", "reason": str(exc)}
        mode = task.split("-")[0]
        evidence = self.run(mode)
        if mode == "near":
            # The upstream gate uses strict < against a returned binary64 lower bound.
            # Comparing exact decimals to that exact float prevents rounding exploits.
            goal = "cutoff" if task == "near-branch-cutoff" else "published"
            accepted, evidence = self.near_verdict(goal, target)
        else:
            accepted = target == Decimal(evidence["gain"])
        return {"reward": float(accepted), "status": "accepted" if accepted else "rejected",
                "task": task, "target": str(target), "evidence": evidence,
                "scope": "near branch only, not away sectors or a Bloch theorem" if mode == "near"
                         else "fixed-radius certificate arithmetic, not its analytic bridge"}


def parse_target(text: str) -> Decimal:
    """Accept one bounded decimal string, never code or a binary64 JSON number."""
    if not isinstance(text, str) or len(text) > 256:
        raise ValueError("expected a short JSON object")

    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate key")
            result[key] = value
        return result

    obj = json.loads(text, object_pairs_hook=unique)
    if not isinstance(obj, dict) or set(obj) != {"target"}:
        raise ValueError("expected only target")
    value = obj["target"]
    if not isinstance(value, str) or not re.fullmatch(r"0\.[0-9]{1,30}", value):
        raise ValueError("target must be a decimal string between 0 and 0.1")
    number = Decimal(value)
    if not Decimal(0) < number < Decimal("0.1"):
        raise ValueError("target outside range")
    return number
