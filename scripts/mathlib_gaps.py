#!/usr/bin/env python3
"""Which of Mathlib's 1000 famous theorems are still unformalized.

`docs/1000.yaml` in leanprover-community/mathlib4 tracks the Wikipedia
"list of theorems" against Mathlib. An entry carrying a `decl:` (or `decls:`)
field names the Lean declaration that proves it; an entry *without* one is
Mathlib saying, in its own repository, "this is famous, we want it, nobody has
built it". That second set is the contribution surface.

This script is the fact-generator for `references/mathlib-open-targets.md` --
same division of labour as `scripts/make_context.py`: regenerate the facts,
keep the judgment in the prose.

    .venv/bin/python scripts/mathlib_gaps.py            # rewrite the doc
    .venv/bin/python scripts/mathlib_gaps.py --print    # to stdout, no write
    .venv/bin/python scripts/mathlib_gaps.py --all      # every gap, not just ours

Network access is required (one raw.githubusercontent.com fetch, no auth).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import re
import sys
import urllib.request
from pathlib import Path

SOURCE = (
    "https://raw.githubusercontent.com/leanprover-community/mathlib4"
    "/master/docs/1000.yaml"
)
REPO_ROOT = Path(__file__).resolve().parent.parent
OUT = REPO_ROOT / "references" / "mathlib-open-targets.md"

# Titles worth surfacing for *this* laboratory: analytic number theory, complex
# analysis, and real-polynomial machinery. Substring match, lowercased.
RELEVANT = (
    "zeta", "prime", "critical line", "riemann", "polynomial", "root", "sturm",
    "dirichlet", "modular", "analytic", "entire", "fourier", "mertens",
    "chebyshev", "descartes", "real closed", "hardy", "selberg", "l-function",
    "tauberian", "sign",
)

_ENTRY = re.compile(r"^(Q\d+):\s*$")
_FIELD = re.compile(r"^  (\w+):\s*(.*)$")


def fetch(url: str = SOURCE) -> str:
    with urllib.request.urlopen(url, timeout=60) as fh:
        return fh.read().decode("utf-8")


def parse(text: str) -> list[dict[str, str]]:
    """Flat parse of 1000.yaml -- top-level Qxxxx keys with scalar children.

    Deliberately not pyyaml: the file's shape is fixed and shallow, and the
    repo does not otherwise depend on a YAML parser.
    """
    entries: list[dict[str, str]] = []
    cur: dict[str, str] | None = None
    for line in text.splitlines():
        m = _ENTRY.match(line)
        if m:
            if cur is not None:
                entries.append(cur)
            cur = {"qid": m.group(1)}
            continue
        if cur is None:
            continue
        f = _FIELD.match(line)
        if f:
            cur[f.group(1)] = f.group(2).strip()
    if cur is not None:
        entries.append(cur)
    return entries


def is_formalized(entry: dict[str, str]) -> bool:
    return "decl" in entry or "decls" in entry


def is_relevant(entry: dict[str, str]) -> bool:
    title = entry.get("title", "").lower()
    return any(k in title for k in RELEVANT)


def render(entries: list[dict[str, str]], *, everything: bool) -> str:
    total = len(entries)
    done = [e for e in entries if is_formalized(e)]
    gaps = [e for e in entries if not is_formalized(e)]
    ours = [e for e in gaps if is_relevant(e)]
    stamp = _dt.date.today().isoformat()

    out: list[str] = []
    w = out.append
    w("# Mathlib open targets")
    w("")
    w("**Generated** by `scripts/mathlib_gaps.py` from "
      f"[`docs/1000.yaml`]({SOURCE}) — snapshot {stamp}. Do not hand-edit; "
      "regenerate.")
    w("")
    w("Mathlib keeps `docs/1000.yaml`: the Wikipedia list of famous theorems, "
      "each entry tagged with the Lean declaration that proves it. An entry "
      "with **no `decl:` field** is the library stating, in its own tree, that "
      "the theorem is wanted and unbuilt. That is the contribution surface — "
      "not a guess about what would be welcome, but a written record of it.")
    w("")
    w("| | count |")
    w("| --- | ---: |")
    w(f"| entries tracked | {total} |")
    w(f"| formalized (`decl:` present) | {len(done)} |")
    w(f"| **unformalized** | **{len(gaps)}** |")
    w(f"| unformalized ∩ this lab's subject matter | {len(ours)} |")
    w("")
    w("A caveat that matters before anyone starts typing: absence from this "
      "file is not absence from Mathlib. `1000.yaml` tracks *famous* theorems "
      "only, and its `decl:` fields lag merges. Always confirm with a code "
      "search and an open-PR search before claiming a target.")
    w("")

    shown = gaps if everything else ours
    heading = ("Every unformalized entry" if everything
               else "Unformalized entries within this lab's reach")
    w(f"## {heading}")
    w("")
    w("| Wikidata | theorem |")
    w("| --- | --- |")
    for e in sorted(shown, key=lambda x: x.get("title", "")):
        qid = e["qid"]
        title = e.get("title", "?")
        w(f"| [{qid}](https://www.wikidata.org/wiki/{qid}) | {title} |")
    w("")
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--print", dest="to_stdout", action="store_true",
                    help="write to stdout instead of the doc")
    ap.add_argument("--all", dest="everything", action="store_true",
                    help="list every gap, not just the lab-relevant ones")
    args = ap.parse_args(argv)

    entries = parse(fetch())
    if not entries:
        print("no entries parsed — 1000.yaml layout may have changed",
              file=sys.stderr)
        return 1
    text = render(entries, everything=args.everything)

    if args.to_stdout:
        sys.stdout.write(text)
    else:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(text)
        print(f"wrote {OUT.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
