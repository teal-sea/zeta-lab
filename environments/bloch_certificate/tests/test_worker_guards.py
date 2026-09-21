"""Mutation tests for the two cross-certificate guards added by the wrapper."""
import os
import subprocess
import sys
import zipfile
from pathlib import Path

from test_oracle import archive_path

WORKER = Path(__file__).resolve().parents[1] / "bloch_certificate" / "worker.py"
PREFIX = "zenodo-bloch-computations/src/"


def extract_source(destination):
    with zipfile.ZipFile(archive_path()) as archive:
        for item in archive.infolist():
            relative = item.filename.removeprefix(PREFIX)
            if item.filename.startswith(PREFIX) and "/" not in relative and Path(relative).suffix in {".py", ".npz"}:
                Path(destination, relative).write_bytes(archive.read(item))


def run_near(source):
    env = {key: os.environ[key] for key in ("PATH", "SYSTEMROOT") if key in os.environ}
    env.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1")
    return subprocess.run([sys.executable, "-I", str(WORKER), str(source), "near"],
                          capture_output=True, text=True, cwd=source, env=env, timeout=90)


def test_near_refuses_source_data_constant_drift(tmp_path):
    extract_source(tmp_path)
    source = tmp_path / "variable_radius_certificate.py"
    source.write_text(source.read_text().replace("ETA = 0.70", "ETA = 0.69"))
    result = run_near(tmp_path)
    assert result.returncode != 0
    assert "source/data constants disagree" in result.stderr


def test_near_requires_the_fine_a3_prerequisite(tmp_path):
    extract_source(tmp_path)
    (tmp_path / "certificates.npz").unlink()
    result = run_near(tmp_path)
    assert result.returncode != 0
    assert "certificates.npz" in result.stderr
