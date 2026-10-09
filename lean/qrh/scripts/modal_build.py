"""Run the hunt 125 Lean build on Modal.

    modal run lean/qrh/scripts/modal_build.py

Needs a Modal login on the calling machine (`modal token new`, or MODAL_TOKEN_ID
and MODAL_TOKEN_SECRET in the environment). Nothing heavy runs locally: the
calling machine only uploads `lean/qrh` and waits.

The build itself is `namespace-build.sh` with QRH_RUNNER=modal. It works on the
container's local disk, because a Lean build writes tens of thousands of small
files and a network volume is the slow place to do that. Afterwards the warm
cache (elan, the pinned OpenAI checkout and its build, this package's .lake) is
packed into one archive on the Modal volume `zeta-qrh-4341-adc7f124`, and the
next run unpacks it before starting. The evidence directory (timings, logs,
axiom report) is copied to the volume and its summary is printed here.

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
    .add_local_dir(str(QRH), "/src/qrh", ignore=[".lake", "**/.lake"])
)


def run(cmd, **kw):
    print("+", " ".join(cmd), flush=True)
    return subprocess.run(cmd, **kw)


@app.function(image=image, cpu=8.0, memory=49152, timeout=4 * 3600,
              volumes={PERSIST: cache}, max_containers=1)
def build(revision: str) -> str:
    import os
    import shutil

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
    result = run(["timeout", "--signal=TERM", "--kill-after=60s", "230m",
                  "bash", f"{source}/scripts/namespace-build.sh"], env=env)

    # Save the warm cache whatever the outcome; source trees are not cached.
    keep = [p for p in os.listdir(WORK) if p not in ("source", "evidence")]
    if keep:
        tmp = f"{PERSIST}/cache.tar.zst.partial"
        run(["tar", "--zstd", "-cf", tmp, "-C", WORK, *keep], check=True)
        os.replace(tmp, ARCHIVE)

    evidence_root = f"{WORK}/evidence"
    runs = sorted(os.listdir(evidence_root)) if os.path.isdir(evidence_root) else []
    summary = [f"{warm}; build exit code {result.returncode}"]
    if runs:
        latest = f"{evidence_root}/{runs[-1]}"
        shutil.copytree(latest, f"{PERSIST}/evidence/{revision}-{runs[-1]}")
        for name in ("pins.txt", "cache.txt", "timings.txt", "outcome.txt", "status.txt"):
            path = pathlib.Path(latest, name)
            if path.exists():
                summary.append(f"--- {name}\n{path.read_text().strip()}")
        summary.append(f"evidence saved to volume {VOLUME}: evidence/{revision}-{runs[-1]}")
    else:
        summary.append("no evidence directory was written: the script stopped before its first stage")
    cache.commit()
    return "\n".join(summary)


@app.local_entrypoint()
def main():
    revision = subprocess.check_output(["git", "-C", str(QRH), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(QRH), "status", "--porcelain", "--", "."],
                                    text=True).strip()
    if dirty:
        raise SystemExit("Commit lean/qrh first: the run records the revision it built.")
    print(build.remote(revision))
