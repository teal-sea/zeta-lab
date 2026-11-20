# Hunt #160: a day-one atlas of the Alpoge Lean archive

Opened 2026-11-20. Status: built the same day, attacked by two reviewers
and revised the same day; text-level reading, nothing promoted. The number
#160 was provisional while the hunt was being built, because the case log in
`hunts/README.md` is a shared file this hunt may not edit. The entry was added
the same day when the hunt was landed.

Review met the second kill condition below for two sentences of the first
version: a reading contradicted by archive text (ATLAS S4, on the ledger,
and section 5, on the functional equation). Both sentences are withdrawn in
place, with the old wording kept beside the correction. The atlas is kept
as a revised map. Whether a met kill condition should retire more than the
sentences it hit is the owner's decision, not this hunt's.

## Question and scope

On 2026-11-20 Levent Alpoge posted a note claiming a Lean 4 proof of the
Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
L-functions, with a tarball of 175,187 Lean files and no accompanying paper.
No kernel has checked it. A separate session owns the kernel replay
(`hunts/alpoge_replay/`, on another branch); it is pending and this hunt
states no verdict on it.

This hunt answers one question: what would a working mathematician, or the
next agent, want to know about the archive before opening a single file?
The answer is a map, `ATLAS.md`, made by reading the archive as text.

What the hunt owes:

1. `ATLAS.md`: the statements at the top; the chain of named terms from
   `Main.lean` down to the last step whose statement mentions zeros; the
   analytic interface; where the Euler product and the Galois structure enter, and
   which hypotheses the standing rivals fail; how RH for zeta is obtained;
   the author's 20 timeline items against the tree; whole-tree statistics;
   directory names that mislead; by-products; where an auditor should look
   first; open questions.
2. `quotes.json` and `verify_quotes.py`: every `path:line` cited in the atlas
   with the sha256 of the cited lines, and a script that replays all of them
   against any unpacked copy of the archive.
3. `stats.json`, with `recount.py`, `ledger_count.py` and `build_stats.py`:
   the table behind every count in the atlas, the two tools that count, and
   the one script that writes the table from their output.
   `reader_values.json` is a frozen copy of the readers' figures, kept only
   to be compared against.

What it does not do: run Lean, execute anything from the archive, judge
whether the argument is correct, or repeat the numerics of the analytic
interface, which belong to hunt #161 (`hunts/rh_claim_interface/`).

## Inputs

- The archive, unpacked read-only by the session that downloaded it. Joined
  tarball sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
  It is not in this repository and must not be copied into it beyond short
  quoted statements with path and line.
- Mathlib source at the archive's pinned tag `v4.33.1`, for reading.
- The notes of nine readers who worked the archive the same morning. They
  are the starting point, not the evidence: a claim is kept only if the
  builder opened the archive and found the lines.

## Handling rules

The archive is untrusted data. It is read with `rg`, `sed` and
standard-library Python run with `-I`, by scripts kept outside it. Nothing in
it is executed. Names in it are machine-generated and several are misleading,
so a reading is meant to rest on a quoted statement; where one rests on a
name after all, the atlas says so. The wording is "the archive states",
never a stronger verb. The lexical rules of `hunts/` apply to every byte
here, quoted archive text included.

Quotes are short statements: twelve lines at most each, with path and line.
Length per block is not the whole rule, because adjacent blocks can add up
to a file. `quotes.json` therefore records, for each quoted file, how many
of its content lines are displayed in total, and a test pins the closed
list of files of which more than half is shown. There are five, each a file
that holds little besides the one declaration quoted: `Main.lean` (5 of 5
content lines: the five one-line theorems are the claim itself, and this is
the only file shown whole), `Imports.lean` under
`Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing` (4 of 5: the
tactic of ATLAS 10.2), `MainConclusion.lean` (4 of 6), `lemmaL.lean` (10 of
15) and `TopPlug.lean` (6 of 11). The first version also showed all of
`Statements.lean` in two adjacent blocks; it now shows two of its four
definitions and describes the others.

## Resource boundary

One core. The whole-tree recount is four to five minutes with every string,
directory and closure the atlas uses; the quote verifier is under a second.
No Lean, no network, no paid compute. Write only this directory.

```huntspec
id: rh_claim_atlas
question: What does the archive posted on 2026-11-20 state at the top, by what chain of named terms, through which analytic interface, and where should a reader or an auditor look first?
frontier: 175,187 Lean files and 17,374,215 lines with no comments and no paper; no kernel check yet (the replay is a separate hunt, pending); nine readers' notes of the same morning as unverified leads
proposed_attack: read the text from Main.lean downward, keep only claims re-opened in the archive, record every citation with the sha256 of the cited lines, and recount the statistics independently of the first tables
dead_routes:
  - Trusting identifier or directory names, several of which are shown misleading in ATLAS.md section 8
  - Using import reachability to decide what the top theorems use, since every module is in the import closure of Main
required_oracles:
  - The archive text itself at the recorded tarball sha256
  - The quote verifier verify_quotes.py, which recomputes the sha256 of every cited line range
  - An independent recount of the whole-tree statistics by recount.py against the first tables, rebuilt into stats.json by build_stats.py
  - Mathlib source at the pinned tag v4.33.1 for the definition of RiemannHypothesis
kill_conditions:
  - verify_quotes.py reports a mismatch against the published archive
  - A plain-mathematics reading in ATLAS.md is contradicted by the quoted text beside it
  - The recount disagrees with a number that stats.json marks as recomputed
  - The kernel replay shows that a term on the spine is not the term the five top theorems use
agents_may:
  - read the archive as text
  - quote short statements with path and line
  - count
  - derive readings and mark them as readings
agents_may_not:
  - run lean or lake or execute anything from the archive
  - state a verdict on the claim or on the pending replay
  - say the archive proves a statement
  - copy archive files beyond short quoted statements
  - claim novelty
  - promote their own claim
```
