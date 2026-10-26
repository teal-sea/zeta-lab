"""exact_gram/: the snapshot guard and the per-block checkpoint of the rebuild (PREREG.md s3).

Fail closed, the shape checker/ settled on (checker/RESULTS.md s7.1,
4f706cd, 88f93a8): the key is a digest of the HEAD blobs of the rebuild's
import closure, and a block is neither computed nor served while any file of
that closure is changed in the working tree, or while an untracked file
could shadow one of the names it imports.

- The closure starts at REBUILD_ROOT and follows imports through the folders
  in FOLDERS (this folder, two_adic/, kernel/), with checker_glue's
  `imported_names` (read-only import; it raises on a dynamic import the scan
  cannot name). Data files read with open() are listed in DATA.
- The key also carries checker/'s T_S input digest (`checker_glue.ts_key`),
  so a rebuilt row records which stored rows it is compared against
  (b2e7787b at the time of PREREG).
- A checkpoint is one JSON file per (cell set, block index), written to a
  temporary name and renamed. `load_block` raises on a key mismatch: a stale
  block is refused, never skipped, and never silently recomputed.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKER = os.path.normpath(os.path.join(HERE, "..", "checker"))
if CHECKER not in sys.path:
    sys.path.insert(0, CHECKER)

import checker_glue as GLUE  # noqa: E402  (checker/, read-only)

C4S2 = "hunts/weil_propagation/c4_s2"
FOLDERS = (f"{C4S2}/exact_gram", f"{C4S2}/two_adic", f"{C4S2}/kernel")
#: the production module; it does not exist until the rebuild is funded, and
#: key() refuses to key on an absent root (PREREG.md s3).
REBUILD_ROOT = f"{C4S2}/exact_gram/rebuild.py"
DATA: tuple[str, ...] = ()


class GuardRefused(RuntimeError):
    """The rebuild's inputs are dirty, absent, or a checkpoint's key differs."""


def _git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=HERE, capture_output=True, text=True, check=True).stdout


def closure(blobs: dict, read, root: str = REBUILD_ROOT, data=DATA, folders=FOLDERS):
    """(digest, paths, names) of the import closure of root over folders.

    blobs: {repo path: blob id}; read(path) -> bytes. The digest is the sha256
    of the sorted "path<TAB>blob" lines, so a changed blob or a module entering
    or leaving the closure moves it, and a file outside it does not."""
    by_name: dict[str, list[str]] = {}
    for p in blobs:
        folder, _, rest = p.rpartition("/")
        if folder in folders and rest.endswith(".py"):
            by_name.setdefault(rest[:-3], []).append(p)
    missing = [p for p in (root, *data) if p not in blobs]
    if missing:
        raise GuardRefused(f"rebuild inputs absent from the tree: {missing}: refusing to key on them")
    paths, names, todo = set(data), set(), [root]
    while todo:
        p = todo.pop()
        if p in paths:
            continue
        paths.add(p)
        got = GLUE.imported_names(read(p).decode("utf-8"), p)
        names |= got
        todo.extend(q for n in got for q in by_name.get(n, ()))
    lines = sorted(f"{p}\t{blobs[p]}" for p in paths)
    return hashlib.sha256("\n".join(lines).encode()).hexdigest(), sorted(paths), names


def head_closure(root: str = REBUILD_ROOT, rev: str = "HEAD"):
    blobs = {}
    for ln in _git("ls-tree", "-r", rev, "--", *FOLDERS).splitlines():
        meta, path = ln.split("\t", 1)
        blobs[path] = meta.split()[2]
    top = _git("rev-parse", "--show-toplevel").strip()

    def read(p):
        return subprocess.run(["git", "cat-file", "blob", blobs[p]], cwd=top, capture_output=True, check=True).stdout

    return closure(blobs, read, root)


def dirty(porcelain: str, paths, names, folders=FOLDERS) -> list[str]:
    """Porcelain lines touching a closure path, or a <name>.py in a closure
    folder for an imported name (an untracked file that would shadow it)."""
    paths, bad = set(paths), []
    for line in porcelain.splitlines():
        if len(line) < 4:
            continue
        for p in line[3:].split(" -> "):
            p = p.strip().strip('"')
            folder, _, base = p.rpartition("/")
            if p in paths or (folder in folders and base.endswith(".py") and base[:-3] in names):
                bad.append(line)
                break
    return bad


def key(root: str = REBUILD_ROOT) -> dict:
    """The rebuild key, or GuardRefused. Re-read before every block."""
    digest, paths, names = head_closure(root)
    bad = dirty(_git("status", "--porcelain", "--untracked-files=all", "--", *FOLDERS), paths, names)
    ts_digest, ts_dirty = GLUE.ts_key()
    if bad or ts_dirty:
        raise GuardRefused(f"dirty rebuild or T_S inputs: {bad + list(ts_dirty)}")
    return {"rebuild_digest": digest, "ts_inputs_digest": ts_digest, "head": _git("rev-parse", "HEAD").strip()}


def block_path(outdir: str, tag: str, index: int) -> str:
    return os.path.join(outdir, f"{tag}_block{index:05d}.json")


def save_block(outdir: str, tag: str, index: int, k: dict, payload: dict) -> str:
    """Atomic write of one block: payload holds ball entries as [mid, rad] decimal strings."""
    os.makedirs(outdir, exist_ok=True)
    path = block_path(outdir, tag, index)
    body = {"key": {"rebuild_digest": k["rebuild_digest"], "ts_inputs_digest": k["ts_inputs_digest"]},
            "head": k.get("head"), "tag": tag, "index": index, "payload": payload}
    body["sha256_payload"] = hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(body, fh, sort_keys=True)
    os.replace(tmp, path)
    return path


def load_block(outdir: str, tag: str, index: int, k: dict):
    """The block's payload, None if absent; GuardRefused on a key or integrity mismatch."""
    path = block_path(outdir, tag, index)
    if not os.path.exists(path):
        return None
    with open(path) as fh:
        body = json.load(fh)
    want = {"rebuild_digest": k["rebuild_digest"], "ts_inputs_digest": k["ts_inputs_digest"]}
    if body.get("key") != want:
        raise GuardRefused(f"{path}: key {body.get('key')} != {want}: stale block refused")
    if hashlib.sha256(json.dumps(body["payload"], sort_keys=True).encode()).hexdigest() != body.get("sha256_payload"):
        raise GuardRefused(f"{path}: payload hash mismatch")
    return body["payload"]
