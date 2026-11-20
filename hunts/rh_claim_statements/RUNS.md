# Run record

## Baseline

Checkout `/home/user/zeta-lab`, branch `claude/sweet-planck-pf4oco`, opened at
`c6fbf9fb` (other sessions committed checkpoints to the same branch while this
hunt ran; none of them touches the instruments here). `zeta.rigor.BACKEND` is
`python-flint` (backends `['mpmath.iv', 'python-flint']`). python-flint 0.9.0,
numpy 2.5.5, Python 3.13.18, PARI 2.17.2 through cypari2. Four cores and 15 GB
shared with other sessions: every run below was one process on one core.

`ARCH` is the read-only archive root `.../scratchpad/archive/x/lean/src`
(joined tarball sha256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`), `MATHLIB`
the Mathlib checkout at the archive's pinned revision `0df444a` (tag
`v4.33.1`), `SCRATCH` this session's scratch directory
`.../scratchpad/rh_claim_statements`. Nothing from `ARCH` was executed; no
Lean or Lake was run.

## Archive scans (ripgrep, read only)

Run from `ARCH` with `rg -j1`. Each is one pass over 175,187 files.

1. Notation, 4.8 s, 33 lines:
   `rg -n --no-heading "^\s*(@\[[^\]]*\]\s*)?(public |meta )*(notation3?|infix[lr]?|prefix|postfix|macro|syntax|macro_rules|elab|elab_rules|declare_syntax_cat|binder_predicate|unif_hint|run_cmd|open .* renaming)\b" -g '*.lean' . > SCRATCH/tools/notation_scan.txt`
2. Declarations that could capture an identifier, 1.4 s, 666 lines, with
   `NAMES` the alternation printed by `build_ledger.py --print-names`:
   `rg -n --no-heading "^\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable|local|scoped|public|unsafe|partial|nonrec)\s+)*(def|abbrev|structure|class|inductive|opaque|alias|irreducible_def|instance|theorem|lemma|axiom)\s+((_root_\.)?[^\s:({\[]*\.)?(NAMES)(\s|:|\(|\{|\[|$)" -g '*.lean' . > SCRATCH/tools/decl_index.txt`
3. Scoped declarations, 0.9 s, 233 lines (all `scoped instance` or tactic
   `scoped macro`; none is term-level notation):
   `rg -n --no-heading "^\s*(@\[[^\]]*\]\s*)*scoped\s*(\[[^\]]*\]\s*)?(notation3?|infix[lr]?|prefix|postfix|macro|syntax|instance)\b" -g '*.lean' .`
   Those whose namespace is opened by a claim's file were listed by a scratch
   script (`SCRATCH/tools/shadow.py`); they are instances on archive-local
   types, reachable from C37, C38, C39 and C52 only.

The lakefile (`ARCH/../lakefile.toml`) sets `autoImplicit = false` and
`relaxedAutoImplicit = false`. `rg -c autoImplicit` over the files of the 79
claims finds nothing.

## Unit timings and the estimate, before the scaled run

The fast tier (every claim on its reduced range, every mutant) is the unit:
29.0 s of one core for 76 claims and 98 mutants (17:45 UTC). The full ranges
scale the zeta covers by the height (C02 and C03 from 24 or 32 to 200, C05
from 8 x 16 to 16 x 100 in area) and the sieves from 2 * 10^5 to 10^7.
Estimate written before launch: 5 to 8 minutes of one core, of which more
than half in C05, C06 and C17. Measured: 3 min 22 s (C17 71 s, C05 16 s, C06
9 s, C63 7 s, C02 and C03 6 s each).

Two timings changed the design before the recorded run:

- a direct Arb cover of C02 to t = 30 took 32 s and did not reach its
  tolerance in 400,000 boxes (that version also had two defects in its box
  logic); with Taylor models the same range takes 0.5 s and 1,048 boxes;
- a cover for C06 at M = 100 did not finish in 100 s (each box sums 100
  series). It was replaced by covers for M = 2, 3, 10 and 29 sample points
  for M = 100 and 1000.

Total compute for the hunt, development runs included: about 25 CPU-minutes.

## Run manifests

```runmanifest
id: rh_claim_statements-2026-11-20-ledger
hunt: rh_claim_statements
started: 2026-11-20T17:55:59+00:00
finished: 2026-11-20T17:56:00+00:00
ran:
  - rg scans 1 and 2 above, from ARCH
  - .venv/bin/python -I hunts/rh_claim_statements/build_ledger.py --arch ARCH --mathlib MATHLIB --decl-index SCRATCH/tools/decl_index.txt --notation-scan SCRATCH/tools/notation_scan.txt
outcome: 79 statements and 98 mutants written with 75 Mathlib definition sites; every identifier resolved; no archive declaration can capture a Mathlib identifier of any statement; claims.json has sha256 512bfa1d7fc40a0f23fdf0294ac3624b4ce3f27edec64ea21e3b19f9254e2215
artifacts:
  - hunts/rh_claim_statements/claims.json
```

```runmanifest
id: rh_claim_statements-2026-11-20-aborted
hunt: rh_claim_statements
started: 2026-11-20T17:46:50+00:00
finished: 2026-11-20T17:55:18+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_statements.runner --decoys (three attempts)
outcome: the first attempt did not start (no time binary on this machine); the second was stopped after 80 s inside C05, whose initial boxes were 1 wide and gave Taylor discs of radius 3; the third completed in 3 min 23 s with 79 of 79 holding and 98 of 98 mutants rejected, and was superseded because the ledger was edited after it (C65 regraded from complete cover to measured on a range, two convention notes added)
artifacts:
```

```runmanifest
id: rh_claim_statements-2026-11-20-full
hunt: rh_claim_statements
started: 2026-11-20T17:56:06+00:00
finished: 2026-11-20T17:59:28+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_statements.runner --decoys
outcome: 79 of 79 statements hold in the sense of their grade (9 complete covers, 17 exact on a finite domain, 53 measured on a range), none fails and none is undecided; 98 of 98 mutants are rejected with a witness; 200.7 s in the checks, 3 min 22 s of wall clock on one core
artifacts:
  - hunts/rh_claim_statements/results.json
```

```runmanifest
id: rh_claim_statements-2026-11-20-precision
hunt: rh_claim_statements
started: 2026-11-20T17:59:28+00:00
finished: 2026-11-20T18:04:25+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_statements.runner --prec-scale 2 --no-mutants --only C01,C02,C03,C04,C05,C06,C07,C08,C09,C10,C11,C12,C13,C14,C15,C16,C17,C18,C19,C20,C21,C25,C26,C27,C28,C29,C30,C31,C62,C63,C65,C69,C71,C72,C73,C79 --out hunts/rh_claim_statements/results_prec2.json
outcome: with every working precision doubled all 36 Arb-based claims hold again; every supremum enclosure intersects its 64-bit counterpart, upper ends moving by at most 1.9e-4 (C06, tolerance 2e-3) and other margins by at most 3.1e-5 (C17, tolerance 5e-3); 4 min 57 s of wall clock, of which 189 s in C17
artifacts:
  - hunts/rh_claim_statements/results_prec2.json
```

```runmanifest
id: rh_claim_statements-2026-11-20-tests
hunt: rh_claim_statements
started: 2026-11-20T18:06:08+00:00
finished: 2026-11-20T18:06:30+00:00
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/rh_claim_statements tests/test_hunt_probe_discipline.py tests/test_huntspec.py
  - RH_CLAIM_ARCHIVE=ARCH .venv/bin/python -m pytest -q -n0 hunts/rh_claim_statements -k "archive or ledger or mutant_is_one"
  - .venv/bin/python scripts/make_context.py --check
outcome: 216 passed, 1 skipped and 1 failed in 22 s; the failure is test_every_hunt_directory_is_covered_by_the_case_log, which stops at the first hunt directory without a case-log entry in hunts/README.md (grh_class_number, another session's) and will keep failing for this directory until the entry handed back with this hunt is added, since this hunt may not edit that file; the hunt's own 194 tests pass (76 fast-tier claims, 98 mutants, ledger, recorded run, precision response, planted faults, decoys), and with the archive path set the statement and file hashes of all 79 claims match; the tests leave the git tree unchanged and CONTEXT.md is up to date
artifacts:
```
