"""Run the hunt 125 Lean build on Modal.

    modal run lean/qrh/scripts/modal_build.py

Needs a Modal login on the calling machine (`modal token new`, or MODAL_TOKEN_ID
and MODAL_TOKEN_SECRET in the environment). Nothing heavy runs locally: the
calling machine only uploads `lean/qrh` and waits.

The build itself is `namespace-build.sh` with QRH_RUNNER=modal. It works on the
container's local disk, because a Lean build writes tens of thousands of small
files and a network volume is the slow place to do that. Every ten minutes,
the build process group is paused while its cache and evidence are saved to
the Modal volume `zeta-qrh-4341-adc7f124`. A final checkpoint runs on exit too.
The previous complete archive survives an interrupted checkpoint. A retry
restores the last completed checkpoint; cached files alone are not a verdict.

A failed or timed-out build is a failed run. Partial outputs may be reused as
cache; they never raise a proof grade.
"""
import pathlib
import subprocess

import modal

QRH = pathlib.Path(__file__).resolve().parent.parent
VOLUME = "zeta-qrh-4341-adc7f124"
WORK = "/work"
PERSIST = "/persist"
ARCHIVE = f"{PERSIST}/cache.tar.zst"

app = modal.App("zeta-qrh125")
cache = modal.Volume.from_name(VOLUME, create_if_missing=True)
image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("ca-certificates", "git", "curl", "build-essential", "time",
                 "util-linux", "unzip", "zstd")
    .add_local_dir(str(QRH), "/src/qrh",
                   ignore=[".lake", "**/.lake", "**/__pycache__", "**/*.pyc"])
)


def run(cmd, **kw):
    print("+", " ".join(cmd), flush=True)
    return subprocess.run(cmd, **kw)


@app.function(image=image, cpu=8.0, memory=49152, timeout=4 * 3600,
              volumes={PERSIST: cache}, max_containers=1)
def build(revision: str) -> dict:
    import os
    import shutil
    import sys
    import time

    sys.path.insert(0, "/src/qrh/scripts")
    from modal_checkpoint import run_checkpointed, save_checkpoint

    os.makedirs(WORK, exist_ok=True)
    if os.path.exists(ARCHIVE):
        run(["tar", "--zstd", "-xf", ARCHIVE, "-C", WORK], check=True)
        warm = "warm cache restored"
    else:
        warm = "cold: no cache archive on the volume yet"
    print(warm, flush=True)

    source = f"{WORK}/source/{revision}/lean/qrh"
    shutil.rmtree(source, ignore_errors=True)
    shutil.copytree("/src/qrh", source)
    pathlib.Path(source, "source-revision.txt").write_text(revision + "\n")

    env = dict(os.environ, QRH_REMOTE_RUN="1", QRH_RUNNER="modal", QRH_CACHE=WORK)
    started = time.monotonic()
    checkpoint_times = []

    def checkpoint_current():
        checkpoint_times.append(save_checkpoint(WORK, PERSIST, revision, cache.commit))

    exit_code = run_checkpointed(
        ["bash", f"{source}/scripts/namespace-build.sh"], env=env,
        checkpoint=checkpoint_current,
    )

    evidence_root = f"{WORK}/evidence"
    runs = sorted(os.listdir(evidence_root)) if os.path.isdir(evidence_root) else []
    summary = [f"{warm}; build exit code {exit_code}"]
    if runs:
        latest = f"{evidence_root}/{runs[-1]}"
        # The supervisor's result takes precedence over a shell interrupted
        # before it could write its final outcome.
        pathlib.Path(latest, "supervisor.txt").write_text(
            f"exit_code={exit_code} wall_seconds={time.monotonic() - started:.2f}\n"
            f"checkpoint_seconds={checkpoint_times!r}\n"
        )
        shutil.copytree(latest, f"{PERSIST}/evidence/{revision}-{runs[-1]}",
                        dirs_exist_ok=True)
        for name in ("pins.txt", "cache.txt", "timings.txt", "outcome.txt", "supervisor.txt", "status.txt"):
            path = pathlib.Path(latest, name)
            if path.exists():
                summary.append(f"--- {name}\n{path.read_text().strip()}")
        summary.append(f"evidence saved to volume {VOLUME}: evidence/{revision}-{runs[-1]}")
    else:
        summary.append("no evidence directory was written: the script stopped before its first stage")
    cache.commit()
    return {"exit_code": exit_code, "summary": "\n".join(summary)}


@app.local_entrypoint()
def main():
    revision = subprocess.check_output(["git", "-C", str(QRH), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(QRH), "status", "--porcelain", "--", "."],
                                    text=True).strip()
    if dirty:
        raise SystemExit("Commit lean/qrh first: the run records the revision it built.")
    result = build.remote(revision)
    print(result["summary"])
    if result["exit_code"] != 0:
        raise SystemExit(1)
