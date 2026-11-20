# Hunt #160: a day-one atlas of the Alpoge Lean archive

Opened 2026-11-20. Status: built the same day, text-level reading, nothing
promoted.

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
   `Main.lean` down to the last step that mentions zeros; the single analytic
   interface; where the Euler product and the Galois structure enter, and
   which hypotheses the standing rivals fail; how RH for zeta is obtained;
   the author's 20 timeline items against the tree; whole-tree statistics;
   directory names that mislead; by-products; where an auditor should look
   first; open questions.
2. `quotes.json` and `verify_quotes.py`: every `path:line` cited in the atlas
   with the sha256 of the cited lines, and a script that replays all of them
   against any unpacked copy of the archive.
3. `stats.json` and `recount.py`: the tables behind the statistics, and the
   tool that recounts them.

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
so every reading rests on a quoted statement. The wording is "the archive
states", never a stronger verb. The lexical rules of `hunts/` apply to every
byte here, quoted archive text included.

## Resource boundary

One core. The whole-tree recount is about two and a half minutes; the quote
verifier is under a second. No Lean, no network, no paid compute. Write only
this directory.

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
  - An independent recount of the whole-tree statistics by recount.py against the first tables
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
