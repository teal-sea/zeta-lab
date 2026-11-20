"""Build quotes.json from the citations of ATLAS.md and an unpacked archive.

ATLAS.md is the source of truth for what is cited. Two forms are read:

* a citation is a backticked `path.lean:first-last` (or `path.lean:line`);
  the first path component may be one of the abbreviations below, and a path
  that starts with `Mathlib/` belongs to the Mathlib tree;
* a verbatim quote is a fenced block tagged `lean` whose preceding non-blank
  line carries exactly one citation. Its text must equal the cited lines.

Every citation becomes an entry of quotes.json with the sha256 of the cited
lines (rule in verify_quotes.py). A displayed quote also stores its text; a
bare citation stores only a head, the first 96 characters of its first line,
so that a reader of quotes.json can see what the pointer points at.

quotes.json also records, for every archive file with a displayed quote, how
many of its content lines (not blank, not an import) are displayed in total,
so that the tests can see a file being reproduced piece by piece.

Usage:

    python -I make_quotes.py SRC_DIR --mathlib MATHLIB_DIR [--check] [--fill]

`--check` writes nothing and exits non-zero if quotes.json is stale.
`--fill` first rewrites ATLAS.md, replacing every `lean` block whose only
line is `@@` by the lines its citation names, so that no quoted text is
typed by hand. Standard library only; the archive is read as text and
nothing in it is run.
"""
from __future__ import annotations

import importlib.util
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

#: Abbreviations for the long directory names on the spine.
ABBREVIATIONS = {
    "CB": "Development/AutomorphicArithmetic/CharacterBoxes",
    "TGC": "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses",
    "DL": "Development/AutomorphicArithmetic/DedekindLFunctions",
    "LT": "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems",
    "PC": "Development/AutomorphicArithmetic/PrimitiveCosets",
    "TPS": "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries",
    "FND": "Development/AutomorphicArithmetic/Foundations",
    "AV": "Development/AutomorphicArithmetic/AutomorphicVarieties",
    "AVT": "Development/AbelianVarietyTheory",
    "SWB": "Formalism/SizeWindowBrackets",
}

#: A displayed quote is short: this many lines at most.
MAX_QUOTE_LINES = 12
HEAD_CHARS = 96
#: A `lean` block holding only this line is filled from the cited lines.
PLACEHOLDER = "@@"

CITATION = re.compile(r"`([^\s`:]+\.lean):(\d+)(?:-(\d+))?`")

#: Hashes of the published tarball, recorded by the session that unpacked it.
ARCHIVE = {
    "source": "https://alpo.ge/lean.tar.gz.part01 to part14, concatenated",
    "tarball_sha256": "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc",
    "src_dir_inside_tarball": "lean/src",
    "lean_toolchain": "leanprover/lean4:v4.33.1",
}
MATHLIB = {"tag": "v4.33.1", "rev": "0df444a360eaa60ab8c11dca51a86af692955474"}


def _verifier():
    spec = importlib.util.spec_from_file_location(
        "rh_claim_atlas_verify_quotes", os.path.join(HERE, "verify_quotes.py")
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def expand(path: str) -> tuple[str, str]:
    """(tree, full relative path) for a cited path."""
    head, _, rest = path.partition("/")
    if head == "Mathlib":
        return "mathlib", path
    if head in ABBREVIATIONS and rest:
        return "archive", ABBREVIATIONS[head] + "/" + rest
    return "archive", path


def parse_atlas(text: str) -> tuple[list[dict], list[str]]:
    """Citations of an atlas text, in order of first appearance, and problems.

    Each citation is {tree, path, first, last, cited_as, text?}; `text` is
    present when a `lean` block displays the cited lines.
    """
    problems: list[str] = []
    found: dict[tuple, dict] = {}
    lines = text.split("\n")
    in_block = False
    block_tag = ""
    block: list[str] = []
    block_owner: dict | None = None
    last_text_line = ""
    for lineno, line in enumerate(lines, 1):
        if line.startswith("```"):
            if not in_block:
                in_block = True
                block_tag = line[3:].strip()
                block = []
                block_owner = None
                if block_tag == "lean":
                    cites = CITATION.findall(last_text_line)
                    if len(cites) != 1:
                        problems.append(
                            f"line {lineno}: a lean block needs exactly one citation on the "
                            f"line before it, found {len(cites)}"
                        )
                    else:
                        tree, path = expand(cites[0][0])
                        first = int(cites[0][1])
                        last = int(cites[0][2] or cites[0][1])
                        block_owner = found[(tree, path, first, last)]
            else:
                in_block = False
                if block_tag == "lean" and block_owner is not None:
                    shown = "\n".join(block)
                    if "text" in block_owner and block_owner["text"] != shown:
                        problems.append(f"line {lineno}: two different blocks for one citation")
                    block_owner["text"] = shown
            continue
        if in_block:
            block.append(line)
            continue
        for m in CITATION.finditer(line):
            tree, path = expand(m.group(1))
            first = int(m.group(2))
            last = int(m.group(3) or m.group(2))
            key = (tree, path, first, last)
            if key not in found:
                found[key] = {
                    "tree": tree,
                    "path": path,
                    "first": first,
                    "last": last,
                    "cited_as": f"{m.group(1)}:{m.group(2)}" + (f"-{m.group(3)}" if m.group(3) else ""),
                }
        if line.strip():
            last_text_line = line
    if in_block:
        problems.append("unterminated fenced block")
    return list(found.values()), problems


def fill(text: str, roots: dict[str, str | None]) -> tuple[str, list[str]]:
    """The atlas text with every placeholder block replaced by its cited lines."""
    vq = _verifier()
    problems: list[str] = []
    lines = text.split("\n")
    out: list[str] = []
    last_text_line = ""
    in_block = False
    i = 0
    while i < len(lines):
        line = lines[i]
        if (not in_block and line.startswith("```lean") and i + 2 < len(lines)
                and lines[i + 1] == PLACEHOLDER and lines[i + 2].startswith("```")):
            cites = CITATION.findall(last_text_line)
            if len(cites) != 1:
                problems.append(f"line {i + 1}: a placeholder block needs exactly one citation above it")
                out.extend(lines[i:i + 3])
            else:
                tree, path = expand(cites[0][0])
                first, last = int(cites[0][1]), int(cites[0][2] or cites[0][1])
                root = roots.get(tree)
                try:
                    if root is None:
                        raise ValueError(f"no {tree} tree given")
                    got = vq.read_lines(os.path.join(root, *path.split("/")), first, last)
                except ValueError as exc:
                    problems.append(f"line {i + 1}: {exc}")
                    got = [PLACEHOLDER]
                out.append(line)
                out.extend(got)
                out.append(lines[i + 2])
            i += 3
            continue
        if line.startswith("```"):
            in_block = not in_block
        elif not in_block and line.strip():
            last_text_line = line
        out.append(line)
        i += 1
    return "\n".join(out), problems


def content_lines(lines: list[str]) -> int:
    """Lines of a file that are neither blank nor an import."""
    return sum(1 for x in lines if x.strip() and not x.startswith("import "))


def build(atlas_text: str, roots: dict[str, str]) -> tuple[dict, list[str]]:
    vq = _verifier()
    citations, problems = parse_atlas(atlas_text)
    entries = []
    for n, cite in enumerate(citations, 1):
        where = cite["cited_as"]
        root = roots.get(cite["tree"])
        if root is None:
            problems.append(f"{where}: no {cite['tree']} tree given")
            continue
        try:
            got = vq.read_lines(os.path.join(root, *cite["path"].split("/")), cite["first"], cite["last"])
        except ValueError as exc:
            problems.append(f"{where}: {exc}")
            continue
        entry = {
            "id": f"Q{n:03d}",
            "tree": cite["tree"],
            "path": cite["path"],
            "first": cite["first"],
            "last": cite["last"],
            "sha256": vq.lines_hash(got),
        }
        if "text" in cite:
            entry["kind"] = "quote"
            entry["text"] = "\n".join(got)
            if cite["text"] != entry["text"]:
                problems.append(f"{where}: the block shown in ATLAS.md differs from the cited lines")
            if len(got) > MAX_QUOTE_LINES:
                problems.append(f"{where}: {len(got)} lines shown, the limit is {MAX_QUOTE_LINES}")
        else:
            entry["kind"] = "pointer"
            entry["head"] = got[0].strip()[:HEAD_CHARS]
        entries.append(entry)
    shown: dict[str, set[int]] = {}
    for e in entries:
        if e["kind"] == "quote" and e["tree"] == "archive":
            shown.setdefault(e["path"], set()).update(range(e["first"], e["last"] + 1))
    quoted_files = {}
    for path in sorted(shown):
        try:
            with open(os.path.join(roots["archive"], *path.split("/")), encoding="utf-8") as fh:
                whole = fh.read().split("\n")
        except OSError as exc:
            problems.append(f"{path}: cannot read file ({exc.strerror})")
            continue
        quoted_files[path] = {
            "content_lines": content_lines(whole),
            "displayed_content_lines": content_lines([whole[n - 1] for n in sorted(shown[path]) if n <= len(whole)]),
        }
    data = {
        "schema": 1,
        "what": "every path:line cited in ATLAS.md, with the sha256 of exactly those lines",
        "hash_rule": (
            "read the file as UTF-8, split on newline, take lines first..last (1-based, "
            "inclusive), join with newline and no trailing newline, encode UTF-8, sha256"
        ),
        "archive": ARCHIVE,
        "mathlib": MATHLIB,
        "abbreviations": ABBREVIATIONS,
        "max_quote_lines": MAX_QUOTE_LINES,
        "quoted_files_rule": (
            "for each archive file with a displayed quote: its content lines (not blank, not an "
            "import) and how many of them the displayed quotes show in total"
        ),
        "quoted_files": quoted_files,
        "entries": entries,
    }
    return data, problems


def main(argv: list[str]) -> int:
    vq = _verifier()
    src = os.environ.get(vq.ENV_ARCHIVE)
    mathlib = os.environ.get(vq.ENV_MATHLIB)
    check = False
    do_fill = False
    args = argv[1:]
    while args:
        arg = args.pop(0)
        if arg == "--mathlib" and args:
            mathlib = args.pop(0)
        elif arg == "--check":
            check = True
        elif arg == "--fill":
            do_fill = True
        elif arg.startswith("--"):
            print(f"unknown or incomplete option {arg!r}\n\n{__doc__}")
            return 2
        else:
            src = arg
    resolved = vq.resolve_src(src) if src else None
    if resolved is None or mathlib is None:
        print(f"need the archive source directory and --mathlib\n\n{__doc__}")
        return 2
    with open(os.path.join(HERE, "ATLAS.md"), encoding="utf-8") as fh:
        atlas = fh.read()
    if do_fill and not check:
        filled, problems = fill(atlas, {"archive": resolved, "mathlib": mathlib})
        for p in problems:
            print("problem:", p)
        if problems:
            return 1
        if filled != atlas:
            with open(os.path.join(HERE, "ATLAS.md"), "w", encoding="utf-8") as fh:
                fh.write(filled)
            print(f"filled {atlas.count(chr(10) + PLACEHOLDER + chr(10))} placeholder blocks in ATLAS.md")
            atlas = filled
    data, problems = build(atlas, {"archive": resolved, "mathlib": mathlib})
    for p in problems:
        print("problem:", p)
    if problems:
        return 1
    blob = json.dumps(data, indent=1, ensure_ascii=False) + "\n"
    target = os.path.join(HERE, "quotes.json")
    if check:
        try:
            with open(target, encoding="utf-8") as fh:
                stale = fh.read() != blob
        except OSError:
            stale = True
        print("quotes.json is stale" if stale else "quotes.json is current")
        return 1 if stale else 0
    with open(target, "w", encoding="utf-8") as fh:
        fh.write(blob)
    quotes = sum(1 for e in data["entries"] if e["kind"] == "quote")
    print(f"wrote {len(data['entries'])} entries ({quotes} quotes, {len(data['entries']) - quotes} pointers)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
