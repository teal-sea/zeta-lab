#!/usr/bin/env python3
"""Unpack, from a tar stream on stdin, only the build outputs of the modules a shard needs.

A chunk holds everything one shard built in one round. A later shard needs
part of it: the modules its own modules import. Round 12's shards each
unpacked 54 to 71 GB to get at the 10,000 to 40,000 modules they needed out
of 127,000, and that took six to thirty minutes before anything compiled.

  zstd -dc chunk.tar.zst | untar_needed.py <destination> <file of module names> [--suffix .olean]

A member is kept when its path names a needed module:
  .lake/build/lib/lean/A/B.olean   ->  A.B
  .lake/build/ir/A/B.c             ->  A.B
With --suffix only members ending in that suffix are kept (the replay reads
.olean files and nothing else). Modification times and modes are restored as
tar restores them. Prints one line: members kept, members skipped.
"""
from __future__ import annotations

import os
import sys
import tarfile

ROOTS = (".lake/build/lib/lean/", ".lake/build/ir/")


def module_of(name: str) -> str | None:
    """The module a build output belongs to, or None for anything else."""
    if name.startswith("./"):
        name = name[2:]
    for root in ROOTS:
        if name.startswith(root):
            parts = name[len(root):].split("/")
            if not parts or not parts[-1]:
                return None
            parts[-1] = parts[-1].split(".", 1)[0]
            return ".".join(parts)
    return None


def extract_member(tf, member, dest: str) -> None:
    """Unpack one member, making its parent directory first.

    Several of these programs run side by side into one tree. Python 3.12's
    tarfile makes a missing parent directory with a check and then a plain
    mkdir, and two processes can both pass the check: round 14 lost a shard
    to exactly that (FileExistsError, on the runners' Python 3.12; 3.13
    tolerates it). Made here first, tolerantly, tarfile finds the directory
    there and makes nothing.
    """
    os.makedirs(os.path.join(dest, os.path.dirname(member.name)), exist_ok=True)
    try:
        tf.extract(member, dest, filter="data")
    except TypeError:  # a Python without extraction filters
        tf.extract(member, dest)


def main() -> int:
    args = sys.argv[1:]
    suffix = None
    if "--suffix" in args:
        i = args.index("--suffix")
        suffix = args[i + 1]
        del args[i:i + 2]
    if len(args) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    dest, need_file = args
    with open(need_file, encoding="utf-8") as fh:
        need = {line.strip() for line in fh if line.strip()}
    kept = skipped = 0
    with tarfile.open(fileobj=sys.stdin.buffer, mode="r|") as tf:
        for member in tf:
            if not member.isfile():
                continue
            if (suffix is None or member.name.endswith(suffix)) and module_of(member.name) in need:
                extract_member(tf, member, dest)
                kept += 1
            else:
                skipped += 1
    print(f"untar_needed: kept {kept}, skipped {skipped}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
