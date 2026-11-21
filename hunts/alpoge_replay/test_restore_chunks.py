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


# --------------------------------------------------------------------------
# untar_needed.py: only what the shard needs, and exactly as tar would
# --------------------------------------------------------------------------

import sys  # noqa: E402

sys.path.insert(0, str(HERE))
import untar_needed as un  # noqa: E402

TREE = {
    ".lake/build/lib/lean/A/One.olean": "one",
    ".lake/build/lib/lean/A/One.olean.hash": "h1",
    ".lake/build/lib/lean/A/One.ilean": "i1",
    ".lake/build/lib/lean/A/One.trace": "t1",
    ".lake/build/ir/A/One.c": "c1",
    ".lake/build/ir/A/One.c.hash": "ch1",
    ".lake/build/lib/lean/A/One/Inner.olean": "inner",      # a module below a module of the same name
    ".lake/build/lib/lean/A/OneMore.olean": "prefix twin",  # shares a prefix, is not needed
    ".lake/build/lib/lean/B/Two.olean": "two",
    ".lake/build/ir/B/Two.c": "c2",
    ".lake/build/lib/lean/C₂/Unicode.olean": "three",
}


def test_a_path_names_its_module():
    assert un.module_of(".lake/build/lib/lean/A/One.olean.hash") == "A.One"
    assert un.module_of("./.lake/build/ir/A/One.c") == "A.One"
    assert un.module_of(".lake/build/lib/lean/A/One/Inner.trace") == "A.One.Inner"
    assert un.module_of(".lake/build/lib/lean/Main.olean") == "Main"
    assert un.module_of(".lake/build/bin/cone") is None
    assert un.module_of("somewhere/else.olean") is None


def _extract(tmp_path, need: list[str], *extra: str) -> tuple[Path, subprocess.CompletedProcess]:
    chunk = _chunk(tmp_path, "t", TREE)
    # give the files distinct, old modification times, as a real chunk has
    need_file = tmp_path / "need.txt"
    need_file.write_text("\n".join(need) + "\n", encoding="utf-8")
    dest = tmp_path / f"out{len(list(tmp_path.glob('out*')))}"
    dest.mkdir()
    tar = subprocess.run(["zstd", "-dc", str(chunk)], check=True, capture_output=True).stdout
    proc = subprocess.run([sys.executable, str(HERE / "untar_needed.py"), str(dest), str(need_file), *extra],
                          input=tar, capture_output=True)
    return dest, proc


def test_only_needed_modules_are_unpacked(tmp_path):
    dest, proc = _extract(tmp_path, ["A.One", "C₂.Unicode", "Not.In.The.Chunk"])
    assert proc.returncode == 0, proc.stderr
    got = sorted(str(p.relative_to(dest)) for p in dest.rglob("*") if p.is_file())
    assert got == sorted(k for k in TREE if un.module_of(k) in ("A.One", "C₂.Unicode"))
    assert b"kept 7, skipped 4" in proc.stderr


def test_the_suffix_filter_is_the_replay_s(tmp_path):
    dest, proc = _extract(tmp_path, ["A.One", "B.Two"], "--suffix", ".olean")
    assert proc.returncode == 0, proc.stderr
    got = sorted(str(p.relative_to(dest)) for p in dest.rglob("*") if p.is_file())
    assert got == [".lake/build/lib/lean/A/One.olean", ".lake/build/lib/lean/B/Two.olean"]


def test_what_it_unpacks_is_what_tar_unpacks(tmp_path):
    """Same bytes, same modes, same modification times as GNU tar gives."""
    src = tmp_path / "src-t"
    chunk = _chunk(tmp_path, "t", TREE)
    for i, rel in enumerate(sorted(TREE)):
        os.utime(src / rel, (1_700_000_000 + i, 1_700_000_000 + i))
    tar = subprocess.run(["tar", "-C", str(src), "-cf", "-", *sorted(TREE)], check=True, capture_output=True).stdout
    need_file = tmp_path / "need.txt"
    need_file.write_text("\n".join(sorted({un.module_of(k) for k in TREE})) + "\n", encoding="utf-8")
    ours, theirs = tmp_path / "ours", tmp_path / "theirs"
    ours.mkdir()
    theirs.mkdir()
    subprocess.run([sys.executable, str(HERE / "untar_needed.py"), str(ours), str(need_file)], input=tar, check=True)
    subprocess.run(["tar", "-x", "-f", "-", "-C", str(theirs)], input=tar, check=True)
    for rel in TREE:
        a, b = (ours / rel).stat(), (theirs / rel).stat()
        assert (ours / rel).read_bytes() == (theirs / rel).read_bytes()
        assert int(a.st_mtime) == int(b.st_mtime) == int((src / rel).stat().st_mtime), rel
        assert stat.S_IMODE(a.st_mode) == stat.S_IMODE(b.st_mode), rel


def test_a_truncated_stream_is_an_error(tmp_path):
    chunk = _chunk(tmp_path, "t", TREE)
    tar = subprocess.run(["zstd", "-dc", str(chunk)], check=True, capture_output=True).stdout
    need_file = tmp_path / "need.txt"
    need_file.write_text("A.One\nB.Two\n")
    dest = tmp_path / "out"
    dest.mkdir()
    proc = subprocess.run([sys.executable, str(HERE / "untar_needed.py"), str(dest), str(need_file)],
                          input=tar[: len(tar) // 3], capture_output=True)
    assert proc.returncode != 0


def test_the_restore_script_unpacks_only_what_is_needed_when_told_what_that_is(tmp_path):
    env = _setup(tmp_path, BUNDLES)
    shard = tmp_path / "shard.json"
    shard.write_text(json.dumps({"fetch": FETCH}))
    need = tmp_path / "need.txt"
    need.write_text("A.One\nB.Three\n")
    dest = tmp_path / "lean"
    dest.mkdir()
    proc = subprocess.run(["bash", str(SCRIPT), str(shard), str(dest)], env={**env, "RESTORE_NEED": str(need)},
                          capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    got = sorted(str(p.relative_to(dest)) for p in dest.rglob("*") if p.is_file())
    assert got == [".lake/build/ir/A/One.c", ".lake/build/ir/B/Three.c", ".lake/build/lib/lean/A/One.olean",
                   ".lake/build/lib/lean/A/One.trace", ".lake/build/lib/lean/B/Three.olean"]
    assert "files kept 5, skipped 2" in proc.stdout

    only = tmp_path / "olean-only"
    only.mkdir()
    proc = subprocess.run(["bash", str(SCRIPT), str(shard), str(only)],
                          env={**env, "RESTORE_NEED": str(need), "RESTORE_SUFFIX": ".olean"},
                          capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    assert sorted(p.name for p in only.rglob("*") if p.is_file()) == ["One.olean", "Three.olean"]

    # a corrupt member still fails it, and says why
    with zipfile.ZipFile(tmp_path / "bundles" / "333.zip", "w") as z:
        z.writestr("chunk-r2-s0.tar.zst", "this is not zstd")
    shard.write_text(json.dumps({"fetch": {"333": ["chunk-r2-s0.tar.zst"]}}))
    proc = subprocess.run(["bash", str(SCRIPT), str(shard), str(dest)], env={**env, "RESTORE_NEED": str(need)},
                          capture_output=True, text=True)
    assert proc.returncode != 0

