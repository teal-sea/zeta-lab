# Run record

## Baseline

Checkout at the repo root, branch `claude/sweet-planck-pf4oco`, shared with
other sessions of the same day; this hunt wrote only `hunts/rh_claim_atlas/`.
Python 3.13.18 from `.venv`. No numerics are done here, so the
ball-arithmetic backend is not involved. One core: this hunt ran one
whole-tree process at a time, and `rg` was run with `-j1`. Other sessions
were running their own jobs on the same machine during the revision, which
is why the same recount took 249 s once and 305 s the next time.

Inputs, none of them in the repository:

- `ARCH`: the unpacked archive source directory (`lean/src` inside the
  tarball), read-only. Joined tarball sha256
  `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, recorded
  by the session that downloaded and unpacked it. This hunt did not download
  or unpack anything and did not recompute that hash; a reviewer recomputed
  it from the 14 parts and found it equal.
- `MATHLIB`: a checkout of Mathlib at tag `v4.33.1`, commit
  `0df444a360eaa60ab8c11dca51a86af692955474`.
- The nine readers' notes and the statistical reader's tables, in session
  scratch storage. They are not committed. Scratch storage is swept when
  idle, so nothing below depends on it surviving: the reader's figures that
  the recount is compared against are frozen in `reader_values.json`, and
  every other number of `stats.json` comes from `recount.py` or
  `ledger_count.py` through `build_stats.py`.
- The two reviewers' reports and their scratch tools, also in session
  scratch storage and not committed.

The archive is untrusted data. Every script that reads it was run with
`-I` from outside it, and nothing in it was executed.

## Unit timing and estimate, before the whole-tree runs

First version. `recount.py` on `Formalism/SharpRestriction` alone: 3,093
files, 709,436 lines, 37.4 MB in 4.7 s on one core. The tree is 1,030.5 MB,
so the estimate was 1,030.5 / 37.4 × 4.7 s, about 130 s, well under the
twenty-minute line above which a run must checkpoint. Measured: 132.3 s for
the first run, 152.9 s for the second with string counts and closures.

Revision. The extended tool scans 9 more keywords, 8 tokens by line, 11
more strings, 21 directories, 20 whole words and 6 declaration names. From the 153 s of the
run with 25 strings the estimate was 200 to 250 s. Measured: 249.3 s and
304.7 s, the second on a machine shared with two other sessions' jobs. Still
far under the checkpoint line.

## What was done by hand and is not a manifest

- Reading. A few hundred archive files were opened with a line-range viewer
  (session scratch) to re-read the readers' claims, to choose the lines
  cited in `ATLAS.md`, and in the revision to reproduce each reviewer
  finding link by link.
- Quoted text is never typed. The first version of `ATLAS.md` was rendered
  from a template by a scratch script. In the revision the same step is
  `make_quotes.py --fill`: a `lean` block whose only line is `@@` is replaced
  by the lines its citation names. Three blocks were pasted from the viewer
  instead; `make_quotes.py` refuses a block that differs from its cited
  lines, and accepted them.
- In the first version the claim "this Prop name occurs exactly once in the
  tree outside import lines" (ATLAS section 9) was checked with
  `rg -n -w -F NAME ARCH -g '*.lean'` for each of the thirteen names. It is
  now a field of `stats.json` (`whole_words`).
- A scratch second scan (16:55 to 16:58 UTC) produced numbers that were then
  folded into `recount.py` and reproduced by it; the scratch tool is
  superseded and not kept.
- `reader_values.json` was written once by a scratch script from the
  statistical reader's JSON table, with the by-products reader's two figures
  (419 and 177) added by hand from that reader's notes. It is a copy of
  figures, not a count.
- In the revision, single `rg -j1` searches over the tree were used to find
  things before they were counted by the tool: the lines that conclude
  `ZeroFreeAll` and `EveryCharacter`, the definitions of the macros of
  ATLAS 10.2, the four definitions named `GoodFor`, the identifiers
  containing "tridiagonal" and "zeroMode". ATLAS section 12 lists what
  rests on such a listing alone.

## Corrections to this record

- The first version of this file gave the checkout as an absolute path on
  the machine. Removed.
- The first version said of the test run with the archive that it included
  "a fresh recount that reproduces the tables of stats.json". The test then
  compared nine fields. It did not compare the zero counts, the string
  counts, the import closures, the leaf counts or the file shape, and
  `stats.json` had no committed generator. A reviewer showed seven changes
  to `ATLAS.md` and `stats.json` that left every test green. The manifest
  below is corrected to say what the test compared, and the revision's
  manifests say what the new test compares.

## Run manifests, first version

```runmanifest
id: rh_claim_atlas-2026-11-20-recount-first
hunt: rh_claim_atlas
started: 2026-11-20T16:50:51+00:00
finished: 2026-11-20T16:53:03+00:00
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/recount.py ARCH --out SCRATCH/recount.json --closure (eight module names)
outcome: 175187 files, 17374215 lines, longest import chain 202, 5927 import leaves, every module reachable from Main, in 132 s; all 10 depth-1 rows and all 330 depth-2 rows equal the reader's tables
artifacts:
```

```runmanifest
id: rh_claim_atlas-2026-11-20-recount-strings
hunt: rh_claim_atlas
started: 2026-11-20T17:06:08+00:00
finished: 2026-11-20T17:08:41+00:00
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/recount.py ARCH --out SCRATCH/recount2.json --closure (eight module names) --strings (25 strings)
outcome: every count of the first run reproduced; Stepanov, Vandiver, Guinand, sixfold and relative trace occur in no file; 445 Props in the Published namespace with a one-line theorem of that type for 181; 153 s
artifacts:
```

```runmanifest
id: rh_claim_atlas-2026-11-20-quotes
hunt: rh_claim_atlas
started: 2026-11-20T17:14:56+00:00
finished: 2026-11-20T17:14:56+00:00
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/make_quotes.py ARCH --mathlib MATHLIB
  - .venv/bin/python -I hunts/rh_claim_atlas/verify_quotes.py ARCH --mathlib MATHLIB
outcome: 168 entries written (64 displayed quotes, 104 pointers) from the first version of ATLAS.md; the verifier reported 168 match, 0 mismatch, 0 skipped, in under a second; superseded by the revision's quotes run
artifacts:
```

```runmanifest
id: rh_claim_atlas-2026-11-20-tests-with-archive
hunt: rh_claim_atlas
started: 2026-11-20T17:09:39+00:00
finished: 2026-11-20T17:11:59+00:00
ran:
  - RH_CLAIM_ARCHIVE=ARCH RH_CLAIM_MATHLIB=MATHLIB RH_CLAIM_RECOUNT=1 .venv/bin/python -m pytest -q -n0 hunts/rh_claim_atlas
outcome: 22 passed in 140 s, including the replay of every citation against the archive and a fresh recount compared with stats.json on nine fields only (totals, depth-2 rows, depth, histogram, edges, declaration counts, one Published count); this record first claimed the whole table, see the corrections above
artifacts:
```

```runmanifest
id: rh_claim_atlas-2026-11-20-final-replay
hunt: rh_claim_atlas
started: 2026-11-20T17:14:56+00:00
finished: 2026-11-20T17:15:04+00:00
ran:
  - RH_CLAIM_ARCHIVE=ARCH RH_CLAIM_MATHLIB=MATHLIB .venv/bin/python -m pytest -q -n0 hunts/rh_claim_atlas
  - .venv/bin/python -m pytest -q -n0 hunts/rh_claim_atlas tests/test_hunt_probe_discipline.py tests/test_huntspec.py
outcome: first version, 21 passed and 1 skipped (the recount) with the archive at hand; without it 42 passed, 2 skipped, and 1 failed, the case-log coverage test, which fails until hunts/README.md gains entries for this hunt and three others opened the same day
artifacts:
```

## Run manifests, revision after review

```runmanifest
id: rh_claim_atlas-2026-11-20-ledger
hunt: rh_claim_atlas
started: 2026-11-20T17:53:00+00:00
finished: 2026-11-20T17:53:00+00:00
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/ledger_count.py ARCH --out SCRATCH/ledger.json
outcome: 814 lines, 208 imports, 195 theorems all taking O; 4 read a field (lines 284, 286, 460, 618), 39 pass O on, 152 do not mention it, 13 reach a field transitively; equal to both reviewers' counts
artifacts:
```

```runmanifest
id: rh_claim_atlas-2026-11-20-recount-extended
hunt: rh_claim_atlas
started: 2026-11-20T17:53:18+00:00
finished: 2026-11-20T17:57:28+00:00
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/recount.py ARCH --out SCRATCH/recount3.json --closure (8) --strings (36) --dirs (20) --words (16) --decl-names (6)
outcome: every count of the two earlier runs reproduced; new, each equal to a reviewer's figure, instance 8199 with scoped and local, 11594 files with a line over 1000 bytes, 82 Formalism sub-directories with a Statement file directly inside, 467 and 191 by the wider Published rule, kexactB reached on 469 lines in 72 files; 249 s
artifacts:
```

```runmanifest
id: rh_claim_atlas-2026-11-20-recount-final
hunt: rh_claim_atlas
started: 2026-11-20T18:01:10+00:00
finished: 2026-11-20T18:06:15+00:00
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/recount.py ARCH --out SCRATCH/recount4.json (the arguments now recorded in stats.json, recount_arguments)
  - .venv/bin/python -I hunts/rh_claim_atlas/build_stats.py SCRATCH/recount4.json SCRATCH/ledger.json
  - .venv/bin/python -I hunts/rh_claim_atlas/build_stats.py SCRATCH/recount4.json SCRATCH/ledger.json --check
outcome: one keyword, one directory and four whole words added; every other field equal to the run before; stats.json written, 27 comparisons with the reader of which 24 agree and 3 are reconciled by the following row; the check reports that stats.json is what the recount and the ledger count give; 305 s; superseded, one field of the table built from this run was not reproducible (see the first tests run of the revision)
artifacts:
```

```runmanifest
id: rh_claim_atlas-2026-11-20-quotes-revision
hunt: rh_claim_atlas
started: 2026-11-20T18:17:53+00:00
finished: 2026-11-20T18:17:53+00:00
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/make_quotes.py ARCH --mathlib MATHLIB --fill
  - .venv/bin/python -I hunts/rh_claim_atlas/verify_quotes.py ARCH --mathlib MATHLIB
outcome: 238 entries written (75 displayed quotes, 163 pointers) from the revised ATLAS.md, nine of the new quote blocks filled from their cited lines; the verifier reports 238 match, 0 mismatch, 0 skipped, in under a second; the run was repeated after each later prose edit and this is the last
artifacts:
  - hunts/rh_claim_atlas/quotes.json
  - hunts/rh_claim_atlas/ATLAS.md
```

```runmanifest
id: rh_claim_atlas-2026-11-20-tests-revision-first
hunt: rh_claim_atlas
started: 2026-11-20T18:16:45+00:00
finished: 2026-11-20T18:20:59+00:00
ran:
  - RH_CLAIM_ARCHIVE=ARCH RH_CLAIM_MATHLIB=MATHLIB RH_CLAIM_RECOUNT=1 .venv/bin/python -m pytest -q -n0 hunts/rh_claim_atlas
outcome: 31 passed and 1 failed in 255 s; the fresh recount differed from stats.json in one field, import_closures; cause, the twelve largest directories of each closure were chosen with ties broken by set order, which changes from run to run; module and line counts were equal; recount.py now breaks ties by name
artifacts:
```

```runmanifest
id: rh_claim_atlas-2026-11-20-recount-deterministic
hunt: rh_claim_atlas
started: RECOUNT5_STARTED
finished: RECOUNT5_FINISHED
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/recount.py ARCH --out SCRATCH/recount5.json (the arguments recorded in stats.json, recount_arguments)
  - .venv/bin/python -I hunts/rh_claim_atlas/build_stats.py SCRATCH/recount5.json SCRATCH/ledger.json
  - .venv/bin/python -I hunts/rh_claim_atlas/build_stats.py SCRATCH/recount5.json SCRATCH/ledger.json --check
outcome: RECOUNT5_OUTCOME
artifacts:
  - hunts/rh_claim_atlas/stats.json
```

```runmanifest
id: rh_claim_atlas-2026-11-20-tests-revision
hunt: rh_claim_atlas
started: TESTS_STARTED
finished: TESTS_FINISHED
ran:
  - RH_CLAIM_ARCHIVE=ARCH RH_CLAIM_MATHLIB=MATHLIB RH_CLAIM_RECOUNT=1 .venv/bin/python -m pytest -q -n0 hunts/rh_claim_atlas
  - .venv/bin/python -m pytest -q -n0 hunts/rh_claim_atlas
  - .venv/bin/python -m pytest -q -n0 tests/test_hunt_probe_discipline.py tests/test_huntspec.py
outcome: TESTS_OUTCOME
artifacts:
```

`SCRATCH` is this session's scratch directory. The recount and ledger
outputs live there and are not committed; `stats.json` is what
`build_stats.py` writes from them, and the test with `RH_CLAIM_RECOUNT=1`
rebuilds it from the archive and compares every field but the timing.

## Not run

- Lean, Lake, or anything from the archive.
- The full repository suite. Only this directory's tests and the two shared
  tests named in the hand-back were run.
- A literature search for the windowed Landau statement, for the mean-square
  statements of ATLAS 10.5, or for any by-product.
- The reviewers' scratch tools, with two exceptions used as cross-checks.
  The faithfulness reviewer's ledger counter was run once beside
  `ledger_count.py` and gave the same figures (195, 4, 39, 152). The same
  reviewer's independent parser was run on the revised `ATLAS.md`: 75
  displayed blocks equal to their cited lines, 238 distinct citations, none
  bad. Every other figure of the reviewers was reproduced with this hunt's
  own tools or with single searches, and where that was not done
  `RESULTS.md` says so.
