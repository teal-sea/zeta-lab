# Run record

## Baseline

Checkout `/home/user/zeta-lab`, branch `claude/sweet-planck-pf4oco`, shared
with other sessions of the same day; this hunt wrote only
`hunts/rh_claim_atlas/`. Python 3.13.18 from `.venv`. No numerics are done
here, so the ball-arithmetic backend is not involved. One core throughout:
the two whole-tree passes ran one at a time, and `rg` was run with `-j1`
once the recount had started.

Inputs, none of them in the repository:

- `ARCH`: the unpacked archive source directory (`lean/src` inside the
  tarball), read-only. Joined tarball sha256
  `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, recorded
  by the session that downloaded and unpacked it. This hunt did not download
  or unpack anything and did not recompute that hash.
- `MATHLIB`: a checkout of Mathlib at tag `v4.33.1`, commit
  `0df444a360eaa60ab8c11dca51a86af692955474`.
- The nine readers' notes and the statistical reader's tables, in session
  scratch storage. They are not committed. Scratch storage is swept when
  idle, so nothing below depends on it surviving: every number in
  `stats.json` marked as recomputed comes from `recount.py`.

The archive is untrusted data. Every script that reads it was run with
`-I` from outside it, and nothing in it was executed.

## Unit timing and estimate, before the whole-tree run

`recount.py` on `Formalism/SharpRestriction` alone: 3,093 files, 709,436
lines, 37.4 MB in 4.7 s on one core. The tree is 1,030.5 MB, so the estimate
was 1,030.5 / 37.4 × 4.7 s, about 130 s, well under the twenty-minute line
above which a run must checkpoint. Measured: 132.3 s for the first run,
152.9 s for the second with string counts and closures.

## What was done by hand and is not a manifest

- Reading. A few hundred archive files were opened with a line-range viewer
  (session scratch) to re-verify the readers' claims and to choose the lines
  cited in `ATLAS.md`.
- `ATLAS.md` was rendered from a template in which each quote block was
  filled mechanically from the cited lines, so no quoted text was typed.
- The claim "this Prop name occurs exactly once in the tree outside import
  lines" (ATLAS section 9) was checked with
  `rg -n -w -F NAME ARCH -g '*.lean'` for each of the thirteen names.
- A scratch second scan (16:55 to 16:58 UTC) produced numbers that were then
  folded into `recount.py` and reproduced by it; the scratch tool is
  superseded and not kept.

## Run manifests

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
  - .venv/bin/python -I hunts/rh_claim_atlas/recount.py ARCH --out SCRATCH/recount2.json --closure (the eight module names of stats.json) --strings (the 25 strings of stats.json)
outcome: every count of the first run reproduced; Stepanov, Vandiver, Guinand, sixfold and relative trace occur in no file; 445 Props in the Published namespace with a one-line theorem of that type for 181; 153 s
artifacts:
  - hunts/rh_claim_atlas/stats.json
```

```runmanifest
id: rh_claim_atlas-2026-11-20-quotes
hunt: rh_claim_atlas
started: 2026-11-20T17:14:56+00:00
finished: 2026-11-20T17:14:56+00:00
ran:
  - .venv/bin/python -I hunts/rh_claim_atlas/make_quotes.py ARCH --mathlib MATHLIB
  - .venv/bin/python -I hunts/rh_claim_atlas/verify_quotes.py ARCH --mathlib MATHLIB
outcome: 168 entries written (64 displayed quotes, 104 pointers) from the final ATLAS.md; the verifier reports 168 match, 0 mismatch, 0 skipped, in under a second
artifacts:
  - hunts/rh_claim_atlas/quotes.json
  - hunts/rh_claim_atlas/ATLAS.md
```

```runmanifest
id: rh_claim_atlas-2026-11-20-tests-with-archive
hunt: rh_claim_atlas
started: 2026-11-20T17:09:39+00:00
finished: 2026-11-20T17:11:59+00:00
ran:
  - RH_CLAIM_ARCHIVE=ARCH RH_CLAIM_MATHLIB=MATHLIB RH_CLAIM_RECOUNT=1 .venv/bin/python -m pytest -q -n0 hunts/rh_claim_atlas
outcome: 22 passed in 140 s, including the replay of every citation against the archive and a fresh recount that reproduces the tables of stats.json; run before the last prose edits to ATLAS.md, which changed no citation
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
outcome: 21 passed and 1 skipped (the recount) with the archive at hand, on the final files; without it 42 passed, 2 skipped, and 1 failed, the case-log coverage test, which fails until hunts/README.md gains entries for this hunt and three others opened the same day
artifacts:
```

`SCRATCH` is this session's scratch directory. The two recount outputs live
there and are not committed; `stats.json` is the trimmed table built from the
second one and from the reader's tables, with every copied field marked.

## Not run

- Lean, Lake, or anything from the archive.
- The full repository suite. Only this directory's tests and the two shared
  tests named in the hand-back were run.
- A literature search for the windowed Landau statement or for any
  by-product.
