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



# --------------------------------------------------------------------------
# build_volume.sh: the plain path, which is the one every round now takes
# --------------------------------------------------------------------------

def test_a_shard_that_fits_gets_a_plain_directory_and_no_privileged_command(tmp_path):
    bindir = tmp_path / "bin"
    bindir.mkdir()
    sudo = bindir / "sudo"                       # any call to sudo would be a mistake on this path
    sudo.write_text('#!/usr/bin/env bash\necho "sudo $*" >> "$FAKE_SUDO"\nexit 1\n')
    sudo.chmod(sudo.stat().st_mode | stat.S_IEXEC)
    env = {**os.environ, "PATH": f"{bindir}{os.pathsep}{os.environ['PATH']}", "FAKE_SUDO": str(tmp_path / "sudo.txt")}
    target = tmp_path / "lean" / ".lake" / "build"
    script = str(HERE / "build_volume.sh")
    proc = subprocess.run(["bash", script, str(target), "42061"], env=env, capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    assert target.is_dir() and "plain directory, 42061 modules" in proc.stdout
    assert not (tmp_path / "sudo.txt").exists()
    # at the limit it is still plain; one over, it reaches for the volume (and our stand-in refuses)
    assert subprocess.run(["bash", script, str(target), "90000"], env=env, capture_output=True).returncode == 0
    proc = subprocess.run(["bash", script, str(target), "90001"], env=env, capture_output=True, text=True)
    assert proc.returncode != 0 and (tmp_path / "sudo.txt").exists()
    # a limit of zero means always compressed; nonsense is refused before anything is touched
    assert subprocess.run(["bash", script, str(target), "5", "0"], env=env, capture_output=True).returncode != 0
    assert subprocess.run(["bash", script, str(target), "many"], env=env, capture_output=True).returncode == 2


def test_the_limit_can_be_what_the_disk_holds(tmp_path):
    bindir = tmp_path / "bin"
    bindir.mkdir()
    sudo = bindir / "sudo"
    sudo.write_text('#!/usr/bin/env bash\necho "sudo $*" >> "$FAKE_SUDO"\nexit 1\n')
    sudo.chmod(sudo.stat().st_mode | stat.S_IEXEC)
    env = {**os.environ, "PATH": f"{bindir}{os.pathsep}{os.environ['PATH']}", "FAKE_SUDO": str(tmp_path / "sudo.txt")}
    target = tmp_path / "lean" / ".lake" / "build"
    script = str(HERE / "build_volume.sh")
    free_mb = shutil.disk_usage(tmp_path).free // 2**20
    # one module is a megabyte here and nothing is held back: about as many modules as megabytes free
    env1 = {**env, "BUILD_VOLUME_KB_PER_MODULE": "1000", "BUILD_VOLUME_RESERVE_MB": "0"}
    fits = str(max(1, free_mb // 2))
    proc = subprocess.run(["bash", script, str(target), fits, "disk"], env=env1, capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    assert f"plain directory, {fits} modules" in proc.stdout and "room for" in proc.stdout
    assert not (tmp_path / "sudo.txt").exists()
    # more modules than the disk has megabytes: the volume is reached for (and our stand-in refuses)
    proc = subprocess.run(["bash", script, str(target), str(free_mb * 2), "disk"], env=env1, capture_output=True, text=True)
    assert proc.returncode != 0 and (tmp_path / "sudo.txt").exists()
    # the reserve counts: with all of the free space held back there is room for nothing
    env2 = {**env, "BUILD_VOLUME_KB_PER_MODULE": "1000", "BUILD_VOLUME_RESERVE_MB": str(free_mb * 2)}
    (tmp_path / "sudo.txt").unlink()
    proc = subprocess.run(["bash", script, str(target), "1", "disk"], env=env2, capture_output=True, text=True)
    assert "room for 0 modules" in proc.stdout and proc.returncode != 0


def test_the_parent_directory_exists_before_tarfile_is_asked_to_unpack(tmp_path):
    """The fault of round 14, planted so that it fails on any Python.

    Python 3.12's tarfile, which the runners have, makes a missing parent
    with a check and then a plain mkdir; two extractors side by side can both
    pass the check, and the second dies with FileExistsError. Python 3.13,
    which this tree's tests may run on, tolerates it, so running extractors
    in parallel here proves nothing. What is pinned instead is the remedy:
    by the time tarfile is asked, the directory is already there. A stand-in
    for tarfile refuses otherwise.
    """
    import types

    class Refuses:
        def extract(self, member, dest, filter=None):
            assert os.path.isdir(os.path.join(dest, os.path.dirname(member.name))), "parent directory not made first"
            Path(dest, member.name).write_text("x")

    member = types.SimpleNamespace(name=".lake/build/lib/lean/New/Dir/M.olean")
    un.extract_member(Refuses(), member, str(tmp_path))
    assert (tmp_path / member.name).read_text() == "x"
    un.extract_member(Refuses(), member, str(tmp_path))        # and again, with everything in place


def test_many_extractors_into_one_tree_all_finish(tmp_path):
    """Sixteen extractors start together into directories none of them has made yet."""
    dirs = [f".lake/build/lib/lean/Deep/D{i}/E{i}/F{i}" for i in range(150)]
    chunks = []
    names = []
    for c in range(16):
        files = {f"{d}/M{c}.olean": f"{c}" for d in dirs}
        chunks.append(_chunk(tmp_path, f"race{c}", files))
        names += [un.module_of(k) for k in files]
    need = tmp_path / "need.txt"
    need.write_text("\n".join(names) + "\n")
    dest = tmp_path / "tree"
    dest.mkdir()
    procs = [subprocess.Popen(f"zstd -dc {chunk} | {sys.executable} {HERE / 'untar_needed.py'} {dest} {need}",
                              shell=True, stderr=subprocess.PIPE) for chunk in chunks]
    errors = [p.communicate()[1].decode() for p in procs]
    assert all(p.returncode == 0 for p in procs), [e for e in errors if "Error" in e][:1]
    assert sum(1 for _ in dest.rglob("*.olean")) == 16 * len(dirs)

