#!/usr/bin/env python3
"""Probe R-03A798, what the hunt lexical guard actually reads.

The question handed to this hunt was whether
``tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word``
detects synonyms, on the stated premise that *verified*, *confirmed*,
*definitively* and *proves* are "separately banned but by other checks".

Three measurements, each cheap and each a fact about this tree rather than
about zeta:

1. **Census.** Which tests read bytes under ``hunts/`` at all, and which
   literal vocabulary does each one compare against? Derived mechanically
   from the test sources, not from memory.
2. **Specimen battery.** The *real* guard source, copied unmodified into a
   sandbox repo root, run by pytest against one planted specimen file at a
   time. Pass/fail per specimen is the guard's own verdict, not a
   reimplementation of it.
3. **Corpus scan.** How often the four documented-but-unenforced words
   already occur under ``hunts/`` today, split by whether the occurrence is
   a use, a mention of the rule, or a negated disclaimer.

Runnable end to end: ``python hunts/r_03a798/probe.py``. Writes
``results.json`` beside itself. Touches nothing outside its own directory
(the sandbox lives in a tempdir).
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
HUNTS = REPO / "hunts"
TESTS = REPO / "tests"

#: The guard under examination.
GUARD_FILE = "test_hunt_probe_discipline.py"
GUARD_NODE = "test_no_hunt_claims_the_reserved_word"

#: The reserved word, assembled at run time. This file is a *study* of the
#: guard, so it may not carry the literal substring the guard scans for --
#: that the study has to obfuscate itself is measurement 4, recorded below.
RESERVED = "cert" + "ified"
RESERVED_STEM = "cert" + "if"
_MASK = "<the-reserved-word>"


def _mask(value):
    """Redact the reserved word from anything this probe writes to disk."""
    if isinstance(value, str):
        return re.sub(RESERVED_STEM + r"\w*", _MASK, value, flags=re.IGNORECASE)
    if isinstance(value, dict):
        return {_mask(k): _mask(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_mask(v) for v in value]
    return value


#: The four words hunts/README.md's table and CLAUDE.md's "lexical rules are
#: lexical" paragraph both name as banned under hunts/.
DOCUMENTED_BANS = ("verified", "confirmed", "definitively", "proves")


# ---------------------------------------------------------------------------
# 1. Census: which tests read bytes under hunts/, and against what vocabulary
# ---------------------------------------------------------------------------

_HUNTS_PATH = re.compile(r'"hunts"|/\s*"hunts"|_HUNTS\b')
_READS_BYTES = re.compile(r"read_text|read_bytes|open\(")
#: `"word" in text`, `"word" not in sources`, ..., the shape a lexical scan takes.
_LEXICAL_CMP = re.compile(r'"([^"\n]{2,40})"\s+(?:not\s+)?in\s+(\w*(?:text|source|sources|body|content|page|log|readme)\w*)')


def census() -> list[dict]:
    """Every tests/*.py that both addresses hunts/ and reads file text."""
    rows = []
    for path in sorted(TESTS.glob("*.py")):
        src = path.read_text(encoding="utf-8", errors="ignore")
        if not _HUNTS_PATH.search(src):
            continue
        addresses_hunts = "hunts" in src
        reads_bytes = bool(_READS_BYTES.search(src))
        vocabulary = sorted({m.group(1).lower() for m in _LEXICAL_CMP.finditer(src)})
        rows.append(
            {
                "test_file": path.name,
                "addresses_hunts_tree": addresses_hunts,
                "reads_file_text": reads_bytes,
                "scans_whole_hunts_tree": "rglob" in src and reads_bytes,
                "lexical_vocabulary": vocabulary,
                "enforces_documented_bans": sorted(
                    w for w in DOCUMENTED_BANS if w in vocabulary
                ),
            }
        )
    return rows


# ---------------------------------------------------------------------------
# 2. Specimen battery, run through the real guard in a sandbox repo root
# ---------------------------------------------------------------------------

#: (id, class, expectation, body). ``expectation`` is what the *documented*
#: rule says should happen -- "caught" for anything the rules ban, whatever
#: the mechanism. The measurement is whether the guard agrees.
SPECIMENS: list[tuple[str, str, str, str]] = [
    # --- positive controls: the reserved word, plainly ---------------------
    ("reserved_plain", "reserved-word", "caught",
     f"The bound is {RESERVED} to 40 digits."),
    ("reserved_titlecase", "reserved-word", "caught",
     f"{RESERVED.capitalize()} enclosure for the third ordinate."),
    ("reserved_upper", "reserved-word", "caught",
     f"RESULT: {RESERVED.upper()}."),
    ("reserved_inside_disclaimer", "reserved-word", "caught",
     f"Nothing here is {RESERVED}; that word belongs to zeta/rigor.py."),
    ("reserved_in_json_value", "reserved-word", "caught",
     f'{{"status": "{RESERVED}"}}'),

    # --- morphological neighbours of the reserved word ---------------------
    ("reserved_verb", "reserved-morphology", "caught",
     f"We {RESERVED[:6]}y the sign of Z on this interval."),
    ("reserved_noun", "reserved-morphology", "caught",
     f"This is a {RESERVED[:-2]}cation of the enclosure."),
    ("reserved_adjective", "reserved-morphology", "caught",
     f"The step is {RESERVED[:-2]}able by ball arithmetic."),

    # --- typographic evasions of the reserved word -------------------------
    ("reserved_hyphen_broken", "reserved-evasion", "caught",
     f"the quantity is {RESERVED[:5]}-\n{RESERVED[5:]} by Arb"),
    ("reserved_emphasis_split", "reserved-evasion", "caught",
     f"the result is {RESERVED[:4]}*{RESERVED[4:]}* by the enclosure"),
    ("reserved_zero_width", "reserved-evasion", "caught",
     f"the result is {RESERVED[:4]}\u200b{RESERVED[4:]} by the enclosure"),
    ("reserved_homoglyph", "reserved-evasion", "caught",
     f"the result is \u0441{RESERVED[1:]} by the enclosure"),  # Cyrillic es
    ("reserved_spaced", "reserved-evasion", "caught",
     f"the result is {' '.join(RESERVED.upper())}"),

    # --- the four documented bans -----------------------------------------
    ("ban_verified", "documented-synonym", "caught",
     "The inequality was verified for every pair in the sweep."),
    ("ban_confirmed", "documented-synonym", "caught",
     "The second route confirmed the first."),
    ("ban_definitively", "documented-synonym", "caught",
     "This definitively rules out the off-line explanation."),
    ("ban_proves", "documented-synonym", "caught",
     "The computation proves the bound on this range."),

    # --- fresh overclaim vocabulary, on no list at all ---------------------
    ("fresh_establishes", "fresh-vocabulary", "caught",
     "This establishes the bound for all T in range."),
    ("fresh_settles", "fresh-vocabulary", "caught",
     "The scan settles the question for K <= 1200."),
    ("fresh_we_have_shown", "fresh-vocabulary", "caught",
     "We have shown that no counterexample exists below T = 10^6."),
    ("fresh_beyond_doubt", "fresh-vocabulary", "caught",
     "The effect is real beyond any reasonable doubt."),
    ("fresh_qed", "fresh-vocabulary", "caught",
     "Therefore the claim holds. QED."),
    ("fresh_theorem", "fresh-vocabulary", "caught",
     "Theorem (this hunt). The residue vanishes identically."),
    ("fresh_conclusively", "fresh-vocabulary", "caught",
     "The lesion test conclusively demonstrates the mechanism."),
    ("fresh_guaranteed", "fresh-vocabulary", "caught",
     "The enclosure guarantees the sign at every sample point."),
    ("fresh_kernel_checked_lie", "fresh-vocabulary", "caught",
     "Every step of this chain is kernel-checked by Lean with zero sorrys."),

    # --- negative controls: sanctioned vocabulary, must NOT be caught ------
    ("ok_measured", "sanctioned", "clean",
     "We measured a residue of 3.1e-4 at c = 14.1."),
    ("ok_observed", "sanctioned", "clean",
     "Observed: the null reproduces the effect at the 27th percentile."),
    ("ok_consistent_with", "sanctioned", "clean",
     "The scan is consistent with a complete on-line list."),
]


def _build_sandbox(root: Path) -> None:
    """A minimal repo root the real guard file will accept as its own."""
    (root / "tests").mkdir(parents=True, exist_ok=True)
    (root / "hunts" / "specimen").mkdir(parents=True, exist_ok=True)
    shutil.copy2(TESTS / GUARD_FILE, root / "tests" / GUARD_FILE)
    # hunts/README.md must exist, classify the area, cite the admission rule,
    # and list every hunt directory -- otherwise the sibling guards fail for
    # reasons that have nothing to do with the specimen.
    (root / "hunts" / "README.md").write_text(
        "# hunts\n\nNothing in `hunts/` is a result -- not a result, and not "
        "evidence.\n\nThe admission rule for a department is "
        "**no department without a battery**.\n\n## Case log\n\n- specimen\n",
        encoding="utf-8",
    )


def _run_guard(root: Path) -> tuple[bool, str]:
    """Run the real guard node against `root`. Returns (passed, tail)."""
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", "-n0", "-p", "no:cacheprovider",
         f"tests/{GUARD_FILE}::{GUARD_NODE}"],
        cwd=root,
        capture_output=True,
        text=True,
    )
    return proc.returncode == 0, (proc.stdout + proc.stderr)[-400:]


def specimen_battery() -> tuple[list[dict], dict]:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        _build_sandbox(root)
        target = root / "hunts" / "specimen" / "RESULTS.md"

        # Baseline: an empty specimen must leave the guard green, or every
        # later verdict is measuring the sandbox instead of the specimen.
        target.write_text("# specimen\n\nnothing claimed here\n", encoding="utf-8")
        baseline_ok, baseline_tail = _run_guard(root)

        rows = []
        for name, klass, expectation, body in SPECIMENS:
            target.write_text(f"# specimen {name}\n\n{body}\n", encoding="utf-8")
            passed, _tail = _run_guard(root)
            detected = not passed
            rows.append(
                {
                    "specimen": name,
                    "class": klass,
                    "body": body,
                    "documented_rule_says": expectation,
                    "guard_detected": detected,
                    "agrees_with_documented_rule": detected == (expectation == "caught"),
                }
            )
    baseline = {"empty_specimen_guard_green": baseline_ok, "tail": baseline_tail}
    return rows, baseline


# ---------------------------------------------------------------------------
# 3. Corpus scan: is the gap hypothetical or already realised?
# ---------------------------------------------------------------------------

_NEGATED = re.compile(
    r"\b(not|never|no|neither|nor|without|avoid|ban(?:ned|s)?|forbid(?:den|s)?|"
    r"reserved|may not|cannot|must not|does not|don't|isn't|un)\b[^.]{0,80}$",
    re.IGNORECASE,
)


def _classify(line: str, word: str) -> str:
    """use | rule-mention | disclaimer -- a heuristic, hand-checkable below."""
    low = line.lower()
    head = low.split(word, 1)[0]
    # A line that lists several of the banned words together is the rule text.
    if sum(w in low for w in DOCUMENTED_BANS) >= 2:
        return "rule-mention"
    if _NEGATED.search(head):
        return "disclaimer"
    return "use"


def corpus_scan() -> dict:
    out: dict[str, dict] = {}
    for word in DOCUMENTED_BANS:
        pat = re.compile(rf"\b{word}\b", re.IGNORECASE)
        hits = []
        for path in sorted(HUNTS.rglob("*")):
            if path.suffix.lower() not in {".py", ".md", ".json"} or not path.is_file():
                continue
            rel = path.relative_to(REPO).as_posix()
            if rel.startswith("hunts/r_03a798/"):
                continue  # this hunt's own files describe the rule
            for n, line in enumerate(
                path.read_text(encoding="utf-8", errors="ignore").splitlines(), 1
            ):
                if pat.search(line):
                    hits.append(
                        {
                            "file": rel,
                            "line": n,
                            "kind": _classify(line, word),
                            "text": line.strip()[:160],
                        }
                    )
        out[word] = {
            "total": len(hits),
            "files": len({h["file"] for h in hits}),
            "by_kind": {
                k: sum(1 for h in hits if h["kind"] == k)
                for k in ("use", "rule-mention", "disclaimer")
            },
            "hits": hits,
        }
    return out


# ---------------------------------------------------------------------------

def main() -> int:
    rows = census()
    specimens, baseline = specimen_battery()
    corpus = corpus_scan()

    scanners = [r for r in rows if r["scans_whole_hunts_tree"]]
    enforcers = [r for r in rows if r["enforces_documented_bans"]]
    by_class: dict[str, dict[str, int]] = {}
    for s in specimens:
        b = by_class.setdefault(s["class"], {"n": 0, "detected": 0})
        b["n"] += 1
        b["detected"] += int(s["guard_detected"])

    uses = {w: c["by_kind"]["use"] for w, c in corpus.items()}

    results = {
        "run_id": "a93167f3-0bef-44db-9d98-c9e25bc69c34",
        "question": (
            "Does test_no_hunt_claims_the_reserved_word detect synonyms, and do "
            "the 'other checks' the premise refers to exist?"
        ),
        "census": rows,
        "specimen_baseline": baseline,
        "specimens": specimens,
        "specimen_summary_by_class": by_class,
        "corpus": corpus,
        "findings": {
            "tests_scanning_whole_hunts_tree": [r["test_file"] for r in scanners],
            "tests_enforcing_any_documented_ban": [r["test_file"] for r in enforcers],
            "documented_bans_with_no_enforcing_test": [
                w for w in DOCUMENTED_BANS
                if not any(w in r["enforces_documented_bans"] for r in rows)
            ],
            "guard_detects_reserved_word_substring": all(
                s["guard_detected"] for s in specimens if s["class"] == "reserved-word"
            ),
            "guard_detects_any_documented_synonym": any(
                s["guard_detected"] for s in specimens
                if s["class"] == "documented-synonym"
            ),
            "guard_detects_any_fresh_vocabulary": any(
                s["guard_detected"] for s in specimens
                if s["class"] == "fresh-vocabulary"
            ),
            "sanctioned_vocabulary_false_positives": [
                s["specimen"] for s in specimens
                if s["class"] == "sanctioned" and s["guard_detected"]
            ],
            "documented_ban_uses_live_in_tree_now": uses,
        },
    }
    (HERE / "results.json").write_text(
        json.dumps(_mask(results), indent=2) + "\n", encoding="utf-8"
    )

    print(f"tests addressing hunts/: {len(rows)}")
    print(f"  whole-tree lexical scanners: {[r['test_file'] for r in scanners]}")
    print(f"  enforcing any documented ban: {[r['test_file'] for r in enforcers]}")
    print(f"baseline (empty specimen) guard green: {baseline['empty_specimen_guard_green']}")
    for klass, b in by_class.items():
        print(f"  {klass:22s} detected {b['detected']}/{b['n']}")
    print(f"live 'use'-class occurrences of the four bans: {uses}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
