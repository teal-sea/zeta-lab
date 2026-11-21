"""fetch_artifact.sh: a stalled or broken artifact download is retried, not waited on.

The script wraps `gh api`. These tests put a stand-in `gh` first on PATH and
plant the three faults the wrapper exists for: a transfer that never returns,
a transfer that returns a truncated zip, and a transfer that fails outright.
"""
from __future__ import annotations

import os
import stat
import subprocess
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "fetch_artifact.sh"

# The stand-in reads a plan of behaviours, one per call, from $FAKE_PLAN and
# keeps its call count in $FAKE_COUNT. Behaviours: ok, hang, truncated, fail.
FAKE_GH = r"""#!/usr/bin/env bash
n=$(cat "$FAKE_COUNT" 2>/dev/null || echo 0)
n=$((n + 1))
echo "$n" > "$FAKE_COUNT"
echo "$*" >> "$FAKE_ARGS"
what=$(sed -n "${n}p" "$FAKE_PLAN")
case "$what" in
  ok) cat "$FAKE_ZIP" ;;
  truncated) head -c 40 "$FAKE_ZIP" ;;
  hang) exec sleep 600 ;;
  *) echo "HTTP 502" >&2; exit 1 ;;
esac
"""


def _setup(tmp_path: Path, plan: list[str]) -> dict[str, str]:
    bindir = tmp_path / "bin"
    bindir.mkdir()
    gh = bindir / "gh"
    gh.write_text(FAKE_GH)
    gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
    good = tmp_path / "good.zip"
    with zipfile.ZipFile(good, "w") as z:
        z.writestr("state.json", '{"where": {}}')
    (tmp_path / "plan.txt").write_text("\n".join(plan) + "\n")
    env = dict(os.environ)
    env.update(
        PATH=f"{bindir}{os.pathsep}{env['PATH']}",
        GITHUB_REPOSITORY="someone/somewhere",
        FAKE_PLAN=str(tmp_path / "plan.txt"),
        FAKE_COUNT=str(tmp_path / "count.txt"),
        FAKE_ARGS=str(tmp_path / "args.txt"),
        FAKE_ZIP=str(good),
        FETCH_TIMEOUT_S="1",
        FETCH_TRIES="4",
        FETCH_BACKOFF_S="0",
    )
    return env


def _run(tmp_path: Path, env: dict[str, str], artifact: str = "12345"):
    out = tmp_path / "out.zip"
    proc = subprocess.run(
        ["bash", str(SCRIPT), artifact, str(out)],
        env=env, capture_output=True, text=True, timeout=120,
    )
    return proc, out


def _calls(tmp_path: Path) -> int:
    count = tmp_path / "count.txt"
    return int(count.read_text()) if count.exists() else 0


def test_a_clean_download_is_one_call(tmp_path):
    env = _setup(tmp_path, ["ok"])
    proc, out = _run(tmp_path, env)
    assert proc.returncode == 0, proc.stderr
    assert _calls(tmp_path) == 1
    assert zipfile.ZipFile(out).namelist() == ["state.json"]
    assert (tmp_path / "args.txt").read_text().strip() == (
        "api repos/someone/somewhere/actions/artifacts/12345/zip"
    )


def test_a_stalled_transfer_is_killed_and_tried_again(tmp_path):
    """The planted fault of 2026-11-21: a transfer that never returns."""
    env = _setup(tmp_path, ["hang", "ok"])
    proc, out = _run(tmp_path, env)
    assert proc.returncode == 0, proc.stderr
    assert _calls(tmp_path) == 2
    assert "attempt 1 of 4 failed: exit 124" in proc.stderr
    assert zipfile.ZipFile(out).namelist() == ["state.json"]


def test_a_truncated_zip_is_not_accepted(tmp_path):
    """gh exits 0 but the file does not list: the next attempt must run."""
    env = _setup(tmp_path, ["truncated", "fail", "ok"])
    proc, out = _run(tmp_path, env)
    assert proc.returncode == 0, proc.stderr
    assert _calls(tmp_path) == 3
    assert "attempt 1 of 4 failed: exit 0" in proc.stderr
    assert "attempt 2 of 4 failed: exit 1" in proc.stderr
    assert zipfile.ZipFile(out).namelist() == ["state.json"]


def test_it_gives_up_after_the_last_attempt_and_leaves_no_file(tmp_path):
    env = _setup(tmp_path, ["fail", "truncated", "fail", "fail", "ok"])
    proc, out = _run(tmp_path, env)
    assert proc.returncode == 1
    assert _calls(tmp_path) == 4
    assert "could not be fetched in 4 attempts" in proc.stderr
    assert not out.exists()


def test_an_id_that_is_not_a_number_never_reaches_gh(tmp_path):
    env = _setup(tmp_path, ["ok"])
    for bad in ["", "latest", "12 34", "1;rm"]:
        proc, _ = _run(tmp_path, env, artifact=bad)
        assert proc.returncode == 2, (bad, proc.stderr)
    assert _calls(tmp_path) == 0
