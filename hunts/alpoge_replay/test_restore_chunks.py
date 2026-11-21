"""restore_chunks.sh: every listed chunk member lands, and a broken one fails the restore.

A stand-in `gh` serves bundle zips from a directory. Each bundle holds
chunk members made the way the build packs them: tar, then zstd.
"""
from __future__ import annotations

import json
import os
import shutil
import stat
import subprocess
import zipfile
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "restore_chunks.sh"

FAKE_GH = r"""#!/usr/bin/env bash
# gh api repos/<repo>/actions/artifacts/<id>/zip
id=$(echo "$2" | sed -n 's#.*/artifacts/\([0-9]*\)/zip#\1#p')
echo "$id" >> "$FAKE_CALLS"
cat "$FAKE_BUNDLES/$id.zip"
"""

pytestmark = pytest.mark.skipif(
    not all(shutil.which(t) for t in ("zstd", "jq", "unzip", "tar")), reason="needs zstd, jq, unzip and tar")


def _chunk(tmp: Path, name: str, files: dict[str, str]) -> Path:
    src = tmp / f"src-{name}"
    for rel, text in files.items():
        f = src / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text)
    out = tmp / f"chunk-{name}.tar.zst"
    tar = subprocess.run(["tar", "-C", str(src), "-cf", "-", *sorted(files)], check=True, capture_output=True)
    subprocess.run(["zstd", "-q", "-o", str(out)], input=tar.stdout, check=True)
    return out


def _setup(tmp: Path, bundles: dict[str, dict[str, dict[str, str]]]) -> dict[str, str]:
    bindir = tmp / "bin"
    bindir.mkdir()
    gh = bindir / "gh"
    gh.write_text(FAKE_GH)
    gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
    store = tmp / "bundles"
    store.mkdir()
    for art, chunks in bundles.items():
        with zipfile.ZipFile(store / f"{art}.zip", "w") as z:
            for name, files in chunks.items():
                z.write(_chunk(tmp, name, files), f"chunk-{name}.tar.zst")
    env = dict(os.environ)
    env.update(PATH=f"{bindir}{os.pathsep}{env['PATH']}", GITHUB_REPOSITORY="someone/somewhere",
               FAKE_BUNDLES=str(store), FAKE_CALLS=str(tmp / "calls.txt"),
               FETCH_TRIES="1", FETCH_BACKOFF_S="0", TMPDIR=str(tmp))
    return env


BUNDLES = {
    "111": {"r0-s0": {".lake/build/lib/lean/A/One.olean": "one", ".lake/build/lib/lean/A/One.trace": "t1",
                      ".lake/build/ir/A/One.c": "c1"},
            "r0-s1": {".lake/build/lib/lean/A/Two.olean": "two", ".lake/build/lib/lean/A/Two.ilean": "i2"},
            "r0-s2": {".lake/build/lib/lean/B/Unwanted.olean": "no"}},
    "222": {"r1-s0": {".lake/build/lib/lean/B/Three.olean": "three", ".lake/build/ir/B/Three.c": "c3"}},
}
FETCH = {"111": ["chunk-r0-s0.tar.zst", "chunk-r0-s1.tar.zst"], "222": ["chunk-r1-s0.tar.zst"]}


def test_every_listed_member_is_unpacked_and_no_other(tmp_path):
    env = _setup(tmp_path, BUNDLES)
    shard = tmp_path / "shard.json"
    shard.write_text(json.dumps({"fetch": FETCH}))
    dest = tmp_path / "lean"
    dest.mkdir()
    proc = subprocess.run(["bash", str(SCRIPT), str(shard), str(dest)], env=env, capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    got = sorted(str(p.relative_to(dest)) for p in dest.rglob("*") if p.is_file())
    assert got == [".lake/build/ir/A/One.c", ".lake/build/ir/B/Three.c", ".lake/build/lib/lean/A/One.olean",
                   ".lake/build/lib/lean/A/One.trace", ".lake/build/lib/lean/A/Two.ilean",
                   ".lake/build/lib/lean/A/Two.olean", ".lake/build/lib/lean/B/Three.olean"]
    assert (dest / ".lake/build/lib/lean/A/Two.olean").read_text() == "two"
    assert "restore: 2 bundles, 3 chunks" in proc.stdout
    assert sorted((tmp_path / "calls.txt").read_text().split()) == ["111", "222"]    # one download per bundle


def test_extra_arguments_reach_tar(tmp_path):
    """The replay restores .olean files only."""
    env = _setup(tmp_path, BUNDLES)
    shard = tmp_path / "shard.json"
    shard.write_text(json.dumps({"fetch": FETCH}))
    dest = tmp_path / "lean"
    dest.mkdir()
    proc = subprocess.run(["bash", str(SCRIPT), str(shard), str(dest), "--wildcards", "*.olean"],
                          env=env, capture_output=True, text=True, cwd=tmp_path)
    assert proc.returncode == 0, proc.stderr
    got = sorted(p.name for p in dest.rglob("*") if p.is_file())
    assert got == ["One.olean", "Three.olean", "Two.olean"]


def test_a_member_that_is_missing_or_corrupt_fails_the_restore(tmp_path):
    env = _setup(tmp_path, BUNDLES)
    dest = tmp_path / "lean"
    dest.mkdir()
    shard = tmp_path / "shard.json"
    shard.write_text(json.dumps({"fetch": {"111": ["chunk-r0-s0.tar.zst", "chunk-r9-s9.tar.zst"]}}))
    proc = subprocess.run(["bash", str(SCRIPT), str(shard), str(dest)], env=env, capture_output=True, text=True)
    assert proc.returncode != 0

    # a member that is not a zstd stream
    with zipfile.ZipFile(tmp_path / "bundles" / "333.zip", "w") as z:
        z.writestr("chunk-r2-s0.tar.zst", "this is not zstd")
    shard.write_text(json.dumps({"fetch": {"333": ["chunk-r2-s0.tar.zst"]}}))
    proc = subprocess.run(["bash", str(SCRIPT), str(shard), str(dest)], env=env, capture_output=True, text=True)
    assert proc.returncode != 0


def test_a_bundle_that_cannot_be_fetched_fails_the_restore(tmp_path):
    env = _setup(tmp_path, BUNDLES)
    dest = tmp_path / "lean"
    dest.mkdir()
    shard = tmp_path / "shard.json"
    shard.write_text(json.dumps({"fetch": {"999": ["chunk-r0-s0.tar.zst"]}}))
    proc = subprocess.run(["bash", str(SCRIPT), str(shard), str(dest)], env=env, capture_output=True, text=True)
    assert proc.returncode != 0
    assert not any(dest.rglob("*.olean"))
