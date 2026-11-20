"""Count how the ledger file of ATLAS.md section 2 (S4) uses its hypothesis `O`.

One file of the archive is read as text:
`.../ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`. Every theorem
in it takes `O : OpenLiteratureStatements`. This script splits the file into
theorem blocks (a block starts at a line beginning `theorem ` and ends before
the next one) and reports, for the text after the binder of `O`:

* blocks that read a field (`O.name`),
* blocks that do not read a field but pass `O` on as an argument,
* blocks that do not mention `O` at all,
* blocks that depend on a field transitively: they read one, or their text
  names (as a whole dotted name) a theorem of the file that does.

Usage (the tree is untrusted data, so isolate the interpreter):

    python -I ledger_count.py SRC_DIR [--out FILE]

Text only, standard library only. "Mention", "pass on" and "depend" are
statements about names in proof text, not about what a kernel would unfold.
"""
from __future__ import annotations

import json
import os
import re
import sys

LEDGER = (
    "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/"
    "ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean"
)
BINDER = re.compile(r"\(O : [^)]*\)")
FIELD = re.compile(r"(?<![\w.])O\.[A-Za-z_]")
BARE = re.compile(r"(?<![\w.])O(?![\w.])")
NAME = re.compile(r"[\w.'₀-₉]+")


def count(text: str) -> dict:
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    starts = [i for i, x in enumerate(lines) if x.startswith("theorem ")]
    blocks = {}
    for a, b in zip(starts, starts[1:] + [len(lines)]):
        name = lines[a].split()[1]
        block = "\n".join(lines[a:b])
        m = BINDER.search(block)
        blocks[name] = {
            "line": a + 1,
            "takes_O": m is not None,
            "body": block[m.end():] if m else block,
        }
    reads = {n for n, b in blocks.items() if FIELD.search(b["body"])}
    passes = {n for n, b in blocks.items() if n not in reads and BARE.search(b["body"])}
    short = {n.replace("_root_.", ""): n for n in blocks}
    uses = {}
    for n, b in blocks.items():
        tokens = {t.replace("_root_.", "").strip(".") for t in NAME.findall(b["body"])}
        uses[n] = {short[t] for t in tokens if t in short and short[t] != n}
    depends = set(reads)
    grew = True
    while grew:
        grew = False
        for n in blocks:
            if n not in depends and uses[n] & depends:
                depends.add(n)
                grew = True
    return {
        "tool": "hunts/rh_claim_atlas/ledger_count.py",
        "file": LEDGER,
        "lines": len(lines),
        "import_lines": sum(1 for x in lines if x.startswith("import ")),
        "theorems": len(blocks),
        "theorems_taking_O": sum(1 for b in blocks.values() if b["takes_O"]),
        "theorem_names_with_of_literature": sum(1 for n in blocks if "_of_literature" in n),
        "lines_reading_a_field_of_O": [i + 1 for i, x in enumerate(lines) if FIELD.search(x)],
        "blocks_reading_a_field_of_O": len(reads),
        "blocks_passing_O_on_without_reading_a_field": len(passes),
        "blocks_not_mentioning_O": len(blocks) - len(reads) - len(passes),
        "blocks_depending_on_a_field_transitively": len(depends),
        "names_depending_on_a_field_transitively": sorted(
            (n.rsplit(".", 1)[-1] for n in depends), key=str
        ),
    }


def main(argv: list[str]) -> int:
    args = argv[1:]
    out = None
    src = None
    while args:
        arg = args.pop(0)
        if arg == "--out" and args:
            out = args.pop(0)
        elif arg.startswith("--"):
            print(f"unknown or incomplete option {arg!r}\n\n{__doc__}")
            return 2
        else:
            src = arg
    if not src:
        print(__doc__)
        return 2
    path = os.path.join(src, *LEDGER.split("/"))
    try:
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
    except OSError as exc:
        print(f"cannot read the ledger file ({exc.strerror}): {path}")
        return 2
    blob = json.dumps(count(text), indent=1, sort_keys=True, ensure_ascii=False)
    if out:
        with open(out, "w", encoding="utf-8") as fh:
            fh.write(blob + "\n")
    else:
        print(blob)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
