#!/usr/bin/env python3
"""Does the metadata describe the declarations actually selected?

`palomar_precheck.py` checks that a formalization.yaml is well formed. Every
Palomar submission this lab has had refused passed that bar. Both of the two
refusals that were ours were the *other* failure: a syntactically perfect
record describing a different object than the comparator selected.

  2026-08-21, DH v1 at e474535 -- the record asserted "the tree is sorry-free"
  where six deliberate sorry sit in the Challenge modules.
  2026-08-25, V2 at 8bd9bb04  -- the submission form defaulted the metadata to
  lean/bridge/formalization.yaml, the pinned V1 record for the conditional
  seven-point result, while the comparator selected the seven V2 declarations.
  Palomar's finding: the record "materially misdescribe[s] the selected seven
  declarations."

Neither is a mathematics defect and neither was detectable by reading one file
alone -- they are correspondence defects, visible only by holding two files
side by side. That is what this module does, and it is the same defect class
the lab's own hunts look for in other people's artifacts.

The three checks, and each one is a refusal that already happened:

  PAIRING    the (comparator, metadata) combination must be a row in
             lean/palomar-pairs.json, and named refused files are refused by
             name. This removes the hand selection entirely: resolve() derives
             the path to paste from the comparator.
  ALIGNMENT  every record names its declarations at alignment.statements[].lean.
             That set must equal the comparator's theorem_names exactly. This
             is the check that states Palomar's own finding in machine terms,
             and on the 2026-08-25 pair the two sets do not intersect at all:
             the record names Zeta23Ext.Palomar.seven_point_*, the comparator
             selects Zeta23Ext.PalomarV2.*.
  COUNT      where the prose also says "the N advertised declarations", N must
             equal that set's size. Secondary, and skipped when absent: the
             registered DH record does not use the phrase.
  SORRY      an unqualified whole-tree sorry-free claim is refused. A tree
             carrying deliberate placeholder sorry is not sorry-free, and the
             claim has to say which object it means. A record *discussing* that
             rule is not making the claim, so "a claim that this tree is
             sorry-free has to say which object it means" passes.

Not covered, and stated so nothing reads more into a green run than is there:
this cannot tell whether the prose is *true*, only whether it is consistent
with the comparator beside it. The editorial review is still a language model
reading for substance, and it can refuse a submission that passes every check
here.
"""
from __future__ import annotations

import json
import os
import re
import sys

try:
    import yaml
except ImportError:  # pragma: no cover - environment guard
    sys.exit("pip install pyyaml")

PAIRS = "lean/palomar-pairs.json"

WORDS = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
         "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12}

# "the four advertised declarations", "the seven advertised declarations"
COUNT_RE = re.compile(
    r"\bthe\s+(" + "|".join(WORDS) + r")\s+advertised\s+declarations?\b", re.I)

# An unqualified claim about the whole tree. The registered records say
# "the Solution module is sorry-free" or name the deliberate count instead,
# and those forms are not matched here.
TREE_SORRY_RE = re.compile(
    r"\b(?:the|this)\s+tree\s+is\s+sorry[- ]free", re.I)

# ... except when the record is stating the RULE rather than making the claim.
# Both V2 records carry "A claim that this tree is sorry-free has to say which
# object it means, and this field is that statement." That sentence is the
# discipline, not a violation of it, and an early version of this module
# refused both registered records over it.
SORRY_DISCUSSED_RE = re.compile(
    r"\bclaims?\s+that\s+(?:the|this)\s+tree\s+is\s+sorry[- ]free", re.I)


def _norm(p: str) -> str:
    return os.path.normpath(p).replace(os.sep, "/")


def load_pairs(repo: str = "."):
    with open(os.path.join(repo, PAIRS), encoding="utf-8") as fh:
        return json.load(fh)


def row_for(comparator: str, repo: str = ".") -> dict:
    """The registry row for this comparator.

    Raises rather than guessing. A comparator with no row is a new surface and
    wants a deliberate edit to lean/palomar-pairs.json, not an inference here.
    """
    c = _norm(comparator)
    for row in load_pairs(repo)["pairs"]:
        if _norm(row["comparator"]) == c:
            return row
    raise KeyError(
        f"{c} has no row in {PAIRS}. Add one deliberately; do not guess a "
        f"metadata path for a comparator the lab has not registered.")


def resolve(comparator: str, repo: str = ".") -> str:
    """The metadata path this comparator must be submitted with."""
    return row_for(comparator, repo)["metadata"]


def resolve_project(comparator: str, repo: str = ".") -> str:
    """The selected project directory for this comparator.

    Also derived rather than typed: passing `lean` where the bridge wants
    `lean/bridge` makes the precheck look for the Challenge module in the wrong
    place and report a missing file, which reads like a real defect.
    """
    return row_for(comparator, repo)["project"]


def check(repo: str, comparator: str, metadata: str):
    """-> (ok, warn, fail), each a list of human-readable lines."""
    ok: list[str] = []
    warn: list[str] = []
    fail: list[str] = []

    cmp_n, meta_n = _norm(comparator), _norm(metadata)
    pairs = load_pairs(repo)

    # --- PAIRING -----------------------------------------------------------
    for row in pairs.get("refused_metadata", []):
        if _norm(row["path"]) == meta_n:
            fail.append(f"metadata {meta_n} is refused by name: {row['reason']}")
            return ok, warn, fail

    # The registry is hand-maintained, so it can go stale or be edited wrong.
    # A pairing failure is recorded and the run CONTINUES, because alignment
    # below is derived from the two artifacts themselves and cannot go stale.
    # Either check alone would have caught the 2026-08-25 misfiling; requiring
    # both to be defeated is the point.
    match = [r for r in pairs["pairs"] if _norm(r["comparator"]) == cmp_n]
    if not match:
        fail.append(f"pairing: comparator {cmp_n} has no row in {PAIRS}")
    else:
        row = match[0]
        if _norm(row["metadata"]) != meta_n:
            fail.append(
                f"pairing: comparator {cmp_n} ({row['label']}) must be submitted "
                f"with {row['metadata']}, not {meta_n}")
        else:
            ok.append(f"pairing: {cmp_n} + {meta_n} is the {row['label']} row")

    # --- ALIGNMENT ---------------------------------------------------------
    with open(os.path.join(repo, comparator), encoding="utf-8") as fh:
        cj = json.load(fh)
    selected = set(cj.get("theorem_names") or []) | set(cj.get("definition_names") or [])

    raw = open(os.path.join(repo, metadata), encoding="utf-8").read()
    y = yaml.safe_load(raw) or {}
    stmts = ((y.get("alignment") or {}).get("statements")) or []
    described = {s.get("lean") for s in stmts if isinstance(s, dict) and s.get("lean")}

    if not described:
        fail.append(
            "alignment: the record names no declarations at "
            "alignment.statements[].lean, so nothing states what it describes")
    elif described != selected:
        missing = sorted(selected - described)
        extra = sorted(described - selected)
        detail = []
        if missing:
            detail.append(f"selected but not described: {', '.join(missing)}")
        if extra:
            detail.append(f"described but not selected: {', '.join(extra)}")
        fail.append(
            "alignment: the record describes different declarations than the "
            "comparator selects. " + "; ".join(detail))
    else:
        ok.append(f"alignment: record and comparator name the same "
                  f"{len(selected)} declarations")

    # --- COUNT (secondary; the DH record does not use the phrase) ----------
    found = {WORDS[m.group(1).lower()] for m in COUNT_RE.finditer(raw)}
    if not found:
        warn.append("count: the record does not say 'the N advertised "
                    "declarations'; alignment carries the check instead")
    elif len(found) > 1:
        fail.append(f"count: the record states two different counts {sorted(found)}")
    elif described and found != {len(described)}:
        fail.append(
            f"count: the prose says {found.pop()} advertised declarations, the "
            f"record names {len(described)}")
    else:
        ok.append(f"count: prose and record agree on {len(described)} declarations")

    # --- SORRY -------------------------------------------------------------
    hits = [m for m in TREE_SORRY_RE.finditer(raw)
            if not SORRY_DISCUSSED_RE.search(raw, max(0, m.start() - 40), m.end())]
    if hits:
        fail.append(
            f"sorry: unqualified whole-tree claim {hits[0].group(0)!r}. Name the "
            f"object (the Solution module, the advertised declarations) or state "
            f"the deliberate sorry count. This is the 2026-08-21 refusal")
    else:
        ok.append("sorry: no unqualified whole-tree sorry-free claim")

    return ok, warn, fail


def main(argv):
    repo = argv[1] if len(argv) > 1 else "."
    comparator = argv[2] if len(argv) > 2 else None
    metadata = argv[3] if len(argv) > 3 else None
    if not comparator:
        print(__doc__.strip().splitlines()[0])
        print(f"\nusage: {os.path.basename(argv[0])} <repo> <comparator> [metadata]\n")
        print("registered surfaces:")
        for row in load_pairs(repo)["pairs"]:
            print(f"  {row['label']:<10} {row['comparator']}\n"
                  f"  {'':<10} -> {row['metadata']}")
        return 2

    if metadata is None:
        metadata = resolve(comparator, repo)
        print(f"resolved metadata for {comparator}:\n\n    {metadata}\n")

    ok, warn, fail = check(repo, comparator, metadata)
    for m in ok:
        print("  PASS  " + m)
    for m in warn:
        print("  WARN  " + m)
    for m in fail:
        print("  FAIL  " + m)
    print(f"\n{len(ok)} pass, {len(warn)} warn, {len(fail)} FAIL")
    if not fail:
        print(f"\nPaste this path into the submission form, do not pick one:\n\n    {metadata}\n")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
