"""Checkpoint the remote build while its entire process group is paused."""

import os
from pathlib import Path
import shutil
import signal
import subprocess
import time


def signal_group(process, sig):
    try:
        os.killpg(process.pid, sig)
    except ProcessLookupError:
        pass


def stop_group(process):
    signal_group(process, signal.SIGCONT)
    signal_group(process, signal.SIGTERM)
    try:
        process.wait(timeout=30)
    except subprocess.TimeoutExpired:
        pass
    finally:
        # Also reap descendants if the shell exited before they did.
        signal_group(process, signal.SIGKILL)
        process.wait()


def run_checkpointed(command, *, env, checkpoint, interval=600, timeout=230 * 60):
    """Run one build, checkpoint every ten minutes, and stop all children on exit.

    The command must keep children in its process group. In particular, nested
    GNU timeout commands must use --foreground. Checkpoint time counts against
    the overall deadline. A timeout is always reported as exit code 124.
    """
    deadline = time.monotonic() + timeout
    process = subprocess.Popen(command, env=env, start_new_session=True)
    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return 124
            try:
                return process.wait(timeout=min(interval, remaining))
            except subprocess.TimeoutExpired:
                if time.monotonic() >= deadline:
                    return 124
                signal_group(process, signal.SIGSTOP)
                try:
                    checkpoint()
                finally:
                    signal_group(process, signal.SIGCONT)
    finally:
        stop_group(process)
        checkpoint()


def save_checkpoint(work, persist, revision, commit):
    """Publish only a complete archive, preserving the previous one on failure."""
    work, persist = Path(work), Path(persist)
    started = time.monotonic()
    keep = sorted(p.name for p in work.iterdir()
                  if p.name not in ("source", "evidence", "qrh-build.lock"))
    if keep:
        partial = persist / "cache.tar.zst.partial"
        subprocess.run(
            ["tar", "--zstd", "-cf", str(partial), "-C", str(work), *keep],
            env=dict(os.environ, ZSTD_CLEVEL="1", ZSTD_NBTHREADS="2"),
            check=True, timeout=300,
        )
        os.replace(partial, persist / "cache.tar.zst")
    evidence = work / "evidence"
    if evidence.exists():
        for run in sorted(evidence.iterdir()):
            shutil.copytree(run, persist / "evidence" / f"{revision}-{run.name}",
                            dirs_exist_ok=True)
    commit()
    elapsed = time.monotonic() - started
    print(f"checkpoint committed: wall_seconds={elapsed:.2f}", flush=True)
    return elapsed
