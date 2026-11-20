"""Check every citation of ATLAS.md against an unpacked copy of the archive.

`quotes.json` lists, for every `path:line` cited in `ATLAS.md`, the file, the
first and last line, and the sha256 of exactly those lines. This script opens
each file in an unpacked archive, recomputes the hash, and exits non-zero on
the first kind of disagreement it finds: a missing file, a file too short, a
changed line, or a stored quote text that does not match its own hash.

The hash rule, so that anyone can recompute it by hand: read the file as
UTF-8, split on the newline character, take lines `first` to `last`
(1-based, inclusive), join them with a newline and no trailing newline,
encode as UTF-8, sha256.

Usage (the archive is untrusted data: isolate the interpreter with -I and
keep this script outside the archive):

    python -I verify_quotes.py SRC_DIR [--mathlib MATHLIB_DIR] [--quotes FILE]

`SRC_DIR` is the directory that holds `Main.lean` (`x/lean/src` inside the
published tarball); a parent of it is accepted. It may also be given in the
environment variable `RH_CLAIM_ARCHIVE`, and the Mathlib checkout in
`RH_CLAIM_MATHLIB`. Entries of the Mathlib tree are skipped, and counted as
skipped, when no Mathlib checkout is named.

Exit status: 0 every checked entry matches, 1 at least one mismatch,
2 usage error. Standard library only. Nothing here runs Lean, so a pass says
the cited text is what the atlas read, and nothing about whether a kernel
accepts it.
"""
from __future__ import annotations

import hashlib
import json
import os
import sys

ENV_ARCHIVE = "RH_CLAIM_ARCHIVE"
ENV_MATHLIB = "RH_CLAIM_MATHLIB"


def lines_hash(lines: list[str]) -> str:
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()


def read_lines(path: str, first: int, last: int) -> list[str]:
    """Lines first..last of a file, or raise ValueError saying why not."""
    try:
        with open(path, "rb") as fh:
            raw = fh.read()
    except OSError as exc:
        raise ValueError(f"cannot read file ({exc.strerror})") from None
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        raise ValueError("file is not UTF-8") from None
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    if first < 1 or last < first:
        raise ValueError(f"bad line range {first}-{last}")
    if last > len(lines):
        raise ValueError(f"file has {len(lines)} lines, range ends at {last}")
    return lines[first - 1 : last]


def resolve_src(path: str) -> str | None:
    """The directory holding Main.lean, looked for at and just below `path`."""
    for sub in ("", "src", os.path.join("lean", "src"), os.path.join("x", "lean", "src")):
        cand = os.path.join(path, sub) if sub else path
        if os.path.isfile(os.path.join(cand, "Main.lean")):
            return cand
    return None


def check_entry(entry: dict, roots: dict[str, str | None]) -> tuple[str, str]:
    """('ok' | 'skipped' | 'mismatch', detail) for one entry."""
    where = f"{entry['path']}:{entry['first']}-{entry['last']}"
    if "text" in entry:
        if lines_hash(entry["text"].split("\n")) != entry["sha256"]:
            return "mismatch", f"{where}: stored text does not hash to the stored sha256"
    root = roots.get(entry["tree"])
    if root is None:
        return "skipped", f"{where}: no {entry['tree']} tree given"
    try:
        lines = read_lines(os.path.join(root, *entry["path"].split("/")), entry["first"], entry["last"])
    except ValueError as exc:
        return "mismatch", f"{where}: {exc}"
    if lines_hash(lines) != entry["sha256"]:
        return "mismatch", f"{where}: lines differ from the recorded sha256"
    return "ok", where


def verify(entries: list[dict], roots: dict[str, str | None]) -> dict:
    report = {"ok": 0, "skipped": 0, "mismatch": 0, "details": []}
    for entry in entries:
        status, detail = check_entry(entry, roots)
        report[status] += 1
        if status != "ok":
            report["details"].append(f"{status}: {detail}")
    return report


def main(argv: list[str]) -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    quotes = os.path.join(here, "quotes.json")
    src = os.environ.get(ENV_ARCHIVE)
    mathlib = os.environ.get(ENV_MATHLIB)
    args = argv[1:]
    while args:
        arg = args.pop(0)
        if arg == "--mathlib" and args:
            mathlib = args.pop(0)
        elif arg == "--quotes" and args:
            quotes = args.pop(0)
        elif arg.startswith("--"):
            print(f"unknown or incomplete option {arg!r}\n\n{__doc__}")
            return 2
        else:
            src = arg
    if not src:
        print(f"no archive given: pass SRC_DIR or set {ENV_ARCHIVE}\n\n{__doc__}")
        return 2
    resolved = resolve_src(src)
    if resolved is None:
        print(f"no Main.lean at or below {src!r}: this is not the unpacked archive")
        return 2
    if mathlib is not None and not os.path.isdir(os.path.join(mathlib, "Mathlib")):
        print(f"no Mathlib directory inside {mathlib!r}")
        return 2
    with open(quotes, encoding="utf-8") as fh:
        data = json.load(fh)
    report = verify(data["entries"], {"archive": resolved, "mathlib": mathlib})
    for line in report["details"]:
        print(line)
    print(
        f"{len(data['entries'])} entries: {report['ok']} match, "
        f"{report['mismatch']} mismatch, {report['skipped']} skipped"
    )
    return 1 if report["mismatch"] else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
