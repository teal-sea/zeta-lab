# RUNS: `dbn_pt_height`

Each lane appends its own entries; neither edits the other's. Timings are wall
clock on the shared swarm box (32 vCPU), single process, under whatever load
the other workflows were putting on it; the 1-minute load average at launch is
recorded with each entry because it inflates every number here.

## Evaluator lane (`evaluator/`)

### E1. Milestone 1 oracle grid: estimate before launch (2026-10-21 16:56 UTC)

Two independent routes to H_t on the grid x in {200, 250, 300, 350, 400},
y in {0, 0.5, 1}, t in {0, 0.05, 0.2, 0.5} (60 points per route), plus four
points at x = 1000 and 2000 for the heat-kernel route only.

- Unit timings measured first, one process each, load average about 120:
  `zeta.heatflow.H_t` at x = 400 needs dps 94 and took 191.8 s for the first
  call (building the memoised Phi rule) and 22.7 s for a second point;
  at x = 200, dps 60, 10.1 s and 0.5 s.  The heat-kernel quadrature
  (`oracles.Ht_heat_kernel`, dps 30) took 13.9 s at x = 200, 18.5 s at
  x = 400, 67 s at x = 2000 and 196 s at x = 20000.
- Estimate: Phi route, one rule per x value, about 10 + 40 + 80 + 130 + 190 s
  of rule builds plus 60 points at 0.5 to 23 s, about 18 minutes; heat-kernel
  route 60 points at about 17 s plus the four larger points, about 25 minutes.
  Two single-core processes, under 1 GB each.
- Checkpointing: one JSON line per point, appended as it completes
  (`evaluator/agreement_phi.jsonl`, `evaluator/agreement_hk.jsonl`); a rerun
  skips finished points.
- Actual: the Phi route finished at 17:04 (8 minutes) and the heat-kernel
  route at 17:12 (16 minutes), load average 85 to 105. Results are in
  `evaluator/EVALUATOR.md`, milestone 1.

```runmanifest
id: dbn_pt_height-2026-10-21-evaluator-grid
hunt: dbn_pt_height
started: 2026-10-21T16:56Z
finished: 2026-10-21T17:12Z
ran:
  - .venv/bin/python hunts/dbn_pt_height/evaluator/agreement.py phi hunts/dbn_pt_height/evaluator/agreement_phi.jsonl
  - .venv/bin/python hunts/dbn_pt_height/evaluator/agreement.py hk hunts/dbn_pt_height/evaluator/agreement_hk.jsonl
artifacts:
  - hunts/dbn_pt_height/evaluator/agreement_phi.jsonl
  - hunts/dbn_pt_height/evaluator/agreement_hk.jsonl
outcome: all 124 oracle values lie inside the evaluator's A + B - C enclosures, and dropping e_C breaks containment at 7 of the 60 grid points
```

### E2. Row 2: one evaluation, one rectangle at two times, Euler 2 and Euler 5 units (2026-10-21 17:00 to 17:15 UTC)

Every run below is a single process of a few minutes; none needed an estimate
entry of its own (rule 3 applies above about 20 minutes), and none was
detached without a watcher. `row2_check.py` and both parts of
`euler5_check.py` were each run twice, the second time only to change how the
balls are written into the JSON; every computed value agreed between the runs
and the second run's files are the ones kept. The timings are measured wall
clock and are not pinned by any test.

- One direct evaluation of f_t, C_t/B_t, e_A, e_B, e_C and e_{C,0} at
  x = X, y = 0.16733, t = 0.186 (N = 630783, exact error terms): 36.6 s
  (53.3 s in the first run).
- The Euler 2 (trib2) bound at N0, one variant: 2.9 to 9.9 s.
- One barrier rectangle [X, X + 1] x [0.16733, 1], including both O(N) passes:
  at t = 0.186, 118.8 s (73.2 s derivative bounds, 45.3 s multi-evaluation
  set-up, 0.3 s for the 68 mesh evaluations); at t = 0, 115.3 s (69.1 s,
  45.3 s, 0.9 s for 580 evaluations). First run: 147.6 s and 131.0 s.
- Euler 5, F_{630783, 640783} at row 2's parameters: 19,223,489 terms in
  113.9 s (5.9 microseconds per term; 7.9 in the first run, at load 106).
  Seven variants of the paper's interval F_{69098, 8x10^4}: about six minutes.

```runmanifest
id: dbn_pt_height-2026-10-21-evaluator-row2
hunt: dbn_pt_height
started: 2026-10-21T17:00Z
finished: 2026-10-21T17:15Z
ran:
  - .venv/bin/python hunts/dbn_pt_height/evaluator/row2_check.py (twice; the second run's output is kept)
  - .venv/bin/python hunts/dbn_pt_height/evaluator/euler5_check.py paper hunts/dbn_pt_height/evaluator/euler5_paper.json (twice)
  - .venv/bin/python hunts/dbn_pt_height/evaluator/euler5_check.py row2 hunts/dbn_pt_height/evaluator/euler5_row2_unit.json (twice)
  - scratch exploration scripts in the session scratchpad for Table 1 rows 1 to 5, Euler 5 variants and N1, not kept; test_effective.py recomputes each of their numbers
artifacts:
  - hunts/dbn_pt_height/evaluator/row2_check.json
  - hunts/dbn_pt_height/evaluator/euler5_paper.json
  - hunts/dbn_pt_height/evaluator/euler5_row2_unit.json
outcome: the printed 0.0376 is reproduced as the trib2 lower bound on the Euler 2 mollified f, whose bound on f itself is 0.0292; one rectangle winds 0 at t = 0.186 and at t = 0; the printed Euler 5 value 0.0263 is not reproduced by any variant tried
```

### E3. Projections from the E2 units (estimates; nothing here was run)

These are multiplications of the measured unit costs above, under the load of
E2. Every hour figure is an estimate. A C implementation would change all of
them: the project's own C/Arb run of this barrier reports 133.169 s of wall
time for all 435 rectangles (its log's last line, read as data).

**(a) The full row-2 asymptotic sweep** (Theorem 1.2(ii) region at t = t0, to
the right of the barrier):

- Lower edge y = y0, N from N0 to N1: Euler 5 F_{N-,N+} on intervals covering
  [N0, N1]. N1, where the unmollified triangle bound reaches the 0.045 margin
  of the paper's claim (c): `unmollified_triangle_bound` gives 0.0376 at
  N = 5e6 and 0.169 at N = 1e7 (pinned by `test_row2_N1_estimate_for_the_projection`),
  so N1 is between 5e6 and 1e7; 6e6 is used below.
- One interval costs 30 N+ terms at 5.9 to 7.9 microseconds per term, plus
  tables of b_m for m <= N+ (about 2 GB per process at N+ = 6e6, extrapolated
  from about 80 bytes per stored ball as traced by Python, plus limb storage).
- The covering is not known until F is computed along it. Doubling intervals
  (four, N+ summing to about 1.5e7) cost about 4.5e8 terms, 45 to 60 minutes on
  one core; intervals of ratio 1.1 (24 of them, N+ summing to about 6.1e7)
  cost about 1.8e9 terms, 3 to 4 hours on one core. Split over n into at most
  8 processes: about 6 to 30 minutes wall.
- The upper and side edges and the region N >= N1 use closed forms and sums
  of a few thousand terms: minutes. The region N >= N1 also needs a proof
  that the triangle bound increases with N, which this lane has not done.

**(b) A (t0, y0) re-optimisation at X <= 6.0e12** (Platt and Trudgian's
verification height allows X/2 <= 3e12; N0 <= 690988 there):

- Envelope: the Euler 2 bound at N0(X) on a 20 x 20 grid of (t0, y0) is about
  400 passes of 3 to 10 s, about 70 minutes on one core, under 10 minutes on 8
  processes. Screening by Euler 5 at N0 instead costs 2 to 3 minutes per point,
  about 16 hours for 400 points on one core.
- Barrier location: the paper's Euler-product screening of shifts (line 1189)
  is cheap; checking a handful of candidates by direct evaluation costs 40 to
  55 s each.
- Barrier: the project's row-2 run needed 435 rectangles (7,368,456 mesh
  points), the t-step count being set by D_t of about 5.5e4 at t = 0 against a
  mesh minimum of |f| near 4.7, so a re-optimised (t0, X) near this height
  needs a comparable count. At 115 to 150 s per rectangle as written, about 16
  hours on one core, about 2 hours wall on 8 processes. Two changes not
  implemented here, derivative bounds computed once per t-interval with t as a
  ball and a t-independent moment set-up (the paper's double expansion), would
  remove the two O(N) passes per rectangle; the remainder is a few hundred
  mesh evaluations of about 1 to 3 ms per rectangle, plausibly under an hour on
  one core (unmeasured).
- Asymptotic sweep for the chosen parameters: as in (a), 1 to 4 hours on one
  core.
- Total per candidate (t0, y0, X): about 18 to 22 hours on one core as written
  (about 3 hours wall on 8 processes), or roughly 3 to 6 hours on one core with
  the two barrier changes. Not included: the Davenport-Heilbronn refusal
  control that gates any Lambda statement, which needs an effective
  approximation for the DH heat flow that `effective.py` does not have.

## Chain lane (`MISSION.md`, `CHAIN.md`, `REDUCTION.md`, `chain.json`, `sources.json`)

### C1. Sourcing and reading (2026-10-21 16:23 to 17:23 UTC)

- Estimate before starting: reading and downloads only, no numerics; under one
  CPU-minute in total and well under 1 GB of memory. The largest single object
  was the 196150822-byte Zenodo archive (about two minutes to fetch; extracted
  to about 208 MB). No job was detached and nothing ran longer than a few
  seconds, so no checkpointing was needed.
- Every download went into a new, empty directory under
  `<cache>/dbn/` whose name starts `chain-`; nothing there
  was executed. Archives were listed for symlinks and parent paths before
  extraction. Each file's URL, SHA-256, size and retrieval time is in
  `sources.json`.
- `test_chain.py`, as first written, re-read all 129 quotations of this pass
  from those hashed bytes and ran in about 7 s on one core.

```runmanifest
id: dbn_pt_height-2026-10-21-chain
hunt: dbn_pt_height
started: 2026-10-21T16:23Z
finished: 2026-10-21T17:23Z
ran:
  - curl downloads of the arXiv sources, the Polymath wiki snapshots, the blog threads, the GitHub API records and the Zenodo files into new directories under <cache>/dbn
  - git clone of km-git-acc/dbn_upper_bound and teorth/optimizationproblems, and a no-checkout clone of the 463464q435q43 fork exported at its two pinned commits
  - a quotation builder run with the venv python in isolated mode from the scratchpad, writing chain.json and sources.json
  - .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/test_chain.py
artifacts:
  - hunts/dbn_pt_height/MISSION.md
  - hunts/dbn_pt_height/CHAIN.md
  - hunts/dbn_pt_height/REDUCTION.md
  - hunts/dbn_pt_height/chain.json
  - hunts/dbn_pt_height/sources.json
  - hunts/dbn_pt_height/test_chain.py
outcome: row 2's asymptotic-region hypothesis was found verified only at N = N0 in the Polymath record, and the 0.16 and 0.1595 rows were found to depend on the 0.1875 reduction, whose zeta-specific inputs are the verification height and the Euler-mollified lower bound
```

### C2. Repair after the adversarial review (2026-10-21, evening UTC)

- Estimate before starting: reading and a handful of small downloads, no
  numerics beyond the lane's own tests; under one CPU-minute in total and well
  under 1 GB of memory. Nothing was detached and nothing ran longer than a
  minute, so no checkpointing was needed.
- New downloads, each into a new, empty directory under
  `<cache>/dbn/` whose name starts `chain-r2-`: the two 2019
  referee reports, the comments of issues 107, 118 and 126, the tenth-thread
  results table (an image), and the 0.172422 package's version 1.1 submission
  archive (4516835 bytes, its md5 equal to the record's), which was listed for
  symlinks and parent paths before extraction. Nothing there was executed. A
  second download of the issue 131 comments had the recorded SHA-256 and was
  deleted.
- The referee reports, the results table and the version 1.1 PDF were read in
  the session's PDF and image readers. The version 1.1 TeX in the archive
  carries the same anchor statements and is what the test re-reads.
- `test_chain.py` now re-reads every quotation, checks every fact and runs in
  about nine seconds on one core. Planted edits, one at a time and restored
  after each: the adversary's kinds (commit counts, two dates, the float digits,
  19/200, an attribution, a negated headline, the DH zero, a locator, numbers of
  four or more digits) and others (a parent comment, "the same day", "no reply",
  a case-log date, a line number, the 2018 table, the part C dependency cells).
  All were refused once two checks were added for the last two kinds; the
  first run refused all but those two.

```runmanifest
id: dbn_pt_height-2026-10-21-chain-repair
hunt: dbn_pt_height
started: 2026-10-21T21:55Z
finished: 2026-10-21T23:00Z
ran:
  - curl downloads of the referee reports, the issue 107, 118 and 126 comments, the tenth-thread results table and the 0.172422 version 1.1 archive into new chain-r2- directories under <cache>/dbn
  - a repair builder and a facts builder run with the venv python in isolated mode from the scratchpad, rewriting chain.json and sources.json from their committed versions
  - .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/test_chain.py
  - a planted-fault runner in the scratchpad that edits one note at a time, runs the lane test and restores the file
artifacts:
  - hunts/dbn_pt_height/CHAIN.md
  - hunts/dbn_pt_height/REDUCTION.md
  - hunts/dbn_pt_height/chain.json
  - hunts/dbn_pt_height/sources.json
  - hunts/dbn_pt_height/test_chain.py
  - hunts/README.md
outcome: the verdict now says N0 and y0 only, quotes the 2019-04-15 sentence in full, adds the 2018 routes and the corrected 2024 thread; the 0.172422 row was found not to inherit the row-2 gap in the version the catalogue cites; the A4 gap was restated as a shipped producer with no shipped run
```

### C3. Did the C2 final pass complete? A re-run (2026-10-26)

- The question. The C2 manifest says the repair ran to 23:00Z, but no file of
  the hunt in the stalled checkout was modified after 22:45Z (`CHAIN.md` was
  last, at 22:45:09Z; the other notes between 22:39Z and 22:44Z). The C2
  planted-fault runner was a scratchpad script that was not kept, and no log
  of its last pass survives. So the record cannot say whether the final pass
  completed: C2's "finished: 23:00Z" and "All were refused" are unconfirmed.
- The re-run. `planted_faults.py` reconstructs the runner from the kinds C2
  lists, seventeen faults in all, one edit at a time, restored after each. On
  the checkpoint commit (the notes exactly as left on 2026-10-21), sixteen were
  refused and one was not: swapping the tag after the 5 July 2024 comment for
  another existing tag. The tag checks asked only that a cited quotation
  exist. If that is the kind C2 called "a locator", C2's last claim did not
  hold for the files it left; if C2 meant something else, it was not
  re-tested.
- The repair. A new check ties each quotation-bound fact to its own tag in the
  same paragraph (three facts that point back at a block quotation are named
  exemptions, and the case-log entry carries no tags), with a planted swap as
  its control. After it, all seventeen faults are refused. The lane test
  passes, with the cache present, in about six seconds on one core.

```runmanifest
id: dbn_pt_height-2026-10-26-chain-planted-faults
hunt: dbn_pt_height
started: 2026-10-26T12:50Z
finished: 2026-10-26T12:56Z
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/test_chain.py (checkpoint commit 44daad385: 262 passed, 6.2 s)
  - .venv/bin/python hunts/dbn_pt_height/planted_faults.py (checkpoint: 16 of 17 refused, the [Q:B1] to [Q:B2] swap not)
  - .venv/bin/python hunts/dbn_pt_height/planted_faults.py (with the tag-placement check: 17 of 17 refused)
  - .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/test_chain.py (264 passed)
artifacts:
  - hunts/dbn_pt_height/planted_faults.py
  - hunts/dbn_pt_height/test_chain.py
outcome: whether the C2 final pass completed is not determinable from the record; on the checkpointed notes one of seventeen reconstructed faults (a swapped citation tag) passed, and after a tag-placement check all seventeen are refused
```
