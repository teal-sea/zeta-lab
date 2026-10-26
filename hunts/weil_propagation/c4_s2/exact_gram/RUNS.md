# RUNS: exact_gram/

Every estimate here was written before the spend it prices. Box: the shared
32 vCPU / 115 GiB Linux VM, python-flint 0.9.0 (Arb backend confirmed,
`zeta.rigor.BACKEND = python-flint`), `ctx.threads = 1`, one process,
`nice -n 10`.

## 1. The block-price run (2026-10-26)

**Estimate before the run** (from the smoke test of 2000 w-nodes: 2.4e−6 s
per phase, 6.4e−9 s per real ball multiply-add at 133 bits): one block at
the 280-mode grid is 128 × 238,764 phases (about 75 s) plus 2 × 128 ×
238,764 × 280 products (about 110 s), so about 3 min per precision and
about 10 min for the whole script at both precisions. Under one core-hour:
no ask needed.

**Measured** (`price_block.py` → `price_block.json`; load average 36 to 46,
under the 64 ceiling; RSS at most 0.76 GiB). One block = 128 s-nodes at the
top of s ≥ 0 on the stored S = 2266.1, all 238,764 w-nodes of the
(280, Kmax = 14) grid, 14 dyadic levels, synthetic mode values (timing does
not depend on them):

| piece | dps 40 (133 bits) | dps 60 (200 bits) |
|---|---|---|
| (P) phases, BLOCK × nw sin_cos | 95.8 s (3.14e−6 s each) | 116.5 s (3.81e−6 s each) |
| (H) hat products, two real ball products | 159.5 s (9.3e−9 s per multiply-add) | 219.9 s (1.29e−8 s) |
| (R) ρ for two families (280 × 280 LU per block, upper estimate) | 2.3 s | 3.4 s |
| (M) window sums, three cells at N = 32 | 0.45 s | 0.50 s |
| **one block** | **258 s** | **340 s** |

One-time pieces, timed on samples: a Bessel table j_0 .. j_650 per node,
0.67 to 0.70 ms above the turning point and 9 to 10 ms below it (arb's j);
kernel/'s eigensolve at dps 40, 1.5 s at 60 modes and 4.7 s at 120.

**The ball product is not the old wall.** bound_quad/'s 200 core-hours used
2.2e−7 s per (s, w, mode) product, measured as a 1 × 2000 row times
2000 × 80 on a loaded laptop. In block shape the same arithmetic is 9.3e−9 s
per real multiply-add here (24 times less), and the Python-level phases
(3.1e−6 s each, independent of nvec) are now a third of the block.

```runmanifest
id: c4_s2_exact_gram-2026-10-26-price
hunt: c4_s2_exact_gram
started: 2026-10-26T12:55-05:00
finished: 2026-10-26T13:12-05:00
ran:
  - nice -n 10 .venv/bin/python hunts/weil_propagation/c4_s2/exact_gram/price_block.py
  - .venv/bin/python hunts/weil_propagation/c4_s2/exact_gram/estimate.py
outcome: one block of the 280-mode grid costs 258 s at dps 40 and 340 s at dps 60 on one core; the full rebuild is estimated at about 155 core-hours
artifacts:
  - hunts/weil_propagation/c4_s2/exact_gram/price_block.json
  - hunts/weil_propagation/c4_s2/exact_gram/estimate.json
```

## 2. The estimate for the full rebuild (PREREG s1 grid)

`estimate.py` → `estimate.json`; scaling rules in its docstring (phases ∝ nw,
products ∝ nw · nvec, ρ ∝ nvec², window sums ∝ Σ(2N + 1)²). At S' = 10^4
the w-grid grows to 382,068 nodes and the s ≥ 0 grid to 160,000 nodes,
1,250 blocks:

| build | S' | Kmax | nw | blocks | block (dps 40) | dps 40 total | dps-60 replay (every 16th) | **production** |
|---|---|---|---|---|---|---|---|---|
| rebuild, 280 modes, N = 8, 16, 32 | 10,000 | 14 | 382,068 | 1,250 | 412 s | 143.5 h | 11.9 h | **155 core-hours** |

The one-time terms (mode table on every w-node and 14 v-nodes per G_b node,
the eigensolve) are 0.6 core-hours of it. This matches the brief's "about
200 core-hours" in size but not in make-up: the old figure was the hats on
the stored grid at a 24 times slower product, while this one is the wider,
finer grid PREREG needs at the measured product.

**The cheap door, not taken.** On the stored S = 2266.1 the same rebuild is
284 blocks of 258 s, about 20 core-hours, seven times less, but there
bound_quad/'s crude E1 is 1.455e−2, above the decision scale (PREREG s1).
A tail-mass lemma for E1 (bound_quad/ s2.2: the heuristic tail mass is 3.38
against the bound's nvec at 80 modes) would buy that factor. It is a
derivation, not compute.

## 3. The mode-count sweep (same scaling, same E1 target 7.0e−4)

| build | S' | Kmax | nw | blocks | production |
|---|---|---|---|---|---|
| 364 modes | 11,400 | 15 | 619,644 | 1,425 | 341 core-hours |
| 500 modes | 13,400 | 16 | 1,070,388 | 1,675 | 869 core-hours |
| 700 modes | 15,800 | 17 | 1,928,628 | 1,975 | 2,398 core-hours |
| 700 modes with N = 64 | 22,300 | 17 | 2,074,896 | 2,788 | 3,636 core-hours |

**The brief's 100 to 300 core-hours for the sweep does not hold.** Kmax =
kmax_for(nvec) doubles the w-range at each step (2^15, 2^16, 2^17), and
E1's crude bound grows with nvec and 2N + 1, which pushes S' up. Only the
364-mode build is near that range. The tail-mass lemma of s2 would cut
every row (S' falls back towards the stored S).

## 4. Placement (proposed to the coordinator, not run)

- **Memory per process**: under 1 GiB with the mode table streamed per
  w-chunk. The table itself (382,068 × 280 balls at 133 bits, about 8 GB)
  is built once per job on the runner's local disk (about 0.6 core-hours),
  never uploaded, and read by every worker process.
- **GitHub Actions** (4 vCPU, 16 GB, 6 h per job): 4 worker processes per
  job, each well under 4 GB; about 5.4 h of blocks per process after the
  table, about 47 blocks per process, about 188 per job: **7 jobs**, one
  wave inside the 20-job limit, wall time about 6 h. Each job is one shard
  of contiguous blocks with its own checkpoint (PREREG s6), uploaded as a
  small artifact (about 3 MB); assembly and the exact-inertia count run
  afterwards on this box (minutes).
- **Fits the free tier**: one block is 7 minutes and well inside 16 GB, so no
  cloud spend is needed for the 280-mode rebuild. The 364-mode build fits
  the same way (about 15 jobs). The 500 and 700-mode builds need roughly
  40 and 100+ job-slots and would compete with CI for a day or more.
- Not added: no workflow file exists on this branch. If approved, the
  workflow lands in this folder's PR for review before any run.

## 5. Before any production block

PREREG s1's prerequisites P1 to P4 (the a priori quadrature and tail
bounds) must be derived and committed, `rebuild.py` written and committed
(guard.py refuses to key on its absence today), and the gate test of
PREREG s4 item 3 must pass inside it.

## 6. The coordinator's ruling on the ask (2026-10-26)

- **(A) the 280-mode rebuild: approved on GitHub Actions, after P1 to P4
  land.** Order: commit P1 to P4 and `rebuild.py` with tests; then a
  workflow in the house pattern (`.github/workflows/bloch-higher.yml`,
  `dh-floor-rerun.yml`): triggered only by a push to `hunt/c4-exact-gram`
  that touches `exact_gram/RUN_REQUEST.json` (the run parameters), not by
  the workflow file; `permissions: contents: read`; a concurrency group;
  `timeout-minutes` at most 350; at most 7 parallel jobs; per-shard
  checkpoints as artifacts; BLAS and OpenMP threads pinned; the guard
  checked before compute. The workflow is pushed **without**
  `RUN_REQUEST.json`, the coordinator reviews it in PR #362 and replies
  "go", and only then is `RUN_REQUEST.json` committed. Estimate for that
  run: s2 (155 core-hours, 7 jobs of 6 h).
- **(B) the sweep: deferred** until a bounded attempt (at most 3 agent-days)
  at the tail-mass lemma for E1, then re-priced. s3's prices
  (341 / 869 / 2,398 / 3,636 core-hours) stand as the correction of the
  brief's 100 to 300.
- Nothing has run under either ruling yet.

## 7. P1 to P4 and the toy (2026-10-26, second unit)

Derivations in BOUNDS.md, code in `bounds.py` and `rebuild.py`, tests in
`test_bounds.py` and `test_rebuild.py`. Runs on the box, each under a
minute, single process, `nice -n 10`, none needing an ask:

- toy rebuild (2 modes, Kmax 6, S' = 12, Δ = 1/16, 193 nodes): about 15 s
  (about 22 s with the dps-60 replay); the test file runs in about 48 s;
- G_z of four prolates at K = 10: about 9 s; it contains the identity
  entrywise (BOUNDS.md s4.2);
- the production-size bound checks (280 modes; `test_bounds.py`, slow):
  about 55 s;
- `tailmass.py` (280 modes, s up to 10^4, closed form, float64): about
  2 minutes.

P4 is not closed: G_b's regions B and C are not built (BOUNDS.md s4.3, s4.4),
so a run with the exact provider stops at setup (PREREG row D0).

## 8. The workflow review and the re-pricing (2026-10-26)

**Review (coordinator, 2026-10-26): changes requested, made.** Trigger,
permissions, concurrency, thread pinning, preflight and the `if: always()`
upload are kept. Added:
(1) **resume**: a re-run attempt downloads this job's earlier-attempt
checkpoint artifacts, named with the attempt number;
(2) **headroom**: a `{"mode": "calibrate", "blocks": n}` request runs job 0
only and records per-block wall time and peak RSS per process
(`calibration.json`). The full run is 9 jobs × 4 processes = 36 shards,
max-parallel 6, and its preflight refuses unless the request's calibration
record gives at least 25 percent headroom inside the 335-minute self-stop;
(3) **memory**: the full-mode preflight requires 4 × peak RSS < 13 GB and
the on-disk mode table < 10 GB, and refuses while `rebuild.py` has no
disk-backed table (`DiskModeTable`, the next unit with P4).
`test_exact_gram.py::test_workflow_matches_the_ruling` pins the shape. The
calibration may run once P4 closes and the coordinator is asked; 'go' for
the full rebuild follows its numbers. No RUN_REQUEST.json is committed.

**Re-pricing with the a posteriori tail** (LEMMA.md s5; `estimate.py`,
`estimate.json` key `builds_aposteriori`; same block price, same E1 target
7.0e−4, tail mass from the measured model Σ(4n + 1)/(πS)):

| build | S' | nw | blocks | production (was, s2, s3) |
|---|---|---|---|---|
| rebuild, 280 modes | 2,700 | 246,768 | 338 | **28 core-hours** (155) |
| 364 modes | 3,200 | 456,924 | 400 | **72** (341) |
| 500 modes | 3,900 | 869,172 | 488 | **209** (869) |
| 700 modes | 4,900 | 1,683,216 | 613 | **658** (2,398) |
| 700 modes, N = 64 | 6,200 | 1,712,544 | 775 | **844** (3,636) |

At 36 shards the 280-mode rebuild is about 10 blocks per process (about
45 minutes at the box's block time), so the calibration will likely show
that fewer jobs suffice. The shard count follows the calibration, not this
table. Sweep B stays deferred (coordinator) until it is re-asked with these
prices.

## 9. Unit 3 (2026-10-26): P4 closed, the disk table, the calibration request

**Grades of the s8 figures** (asked by the coordinator). The re-priced
rebuild (about 28 core-hours) and sweep B (72 / 209 / 658 / 844) are
**estimates** built on three things: the measured block price (s1, measured
on this box, one block), the measured ζ-family tail mass (m_z = 21.8 at
S = 2266, measured, float64, closed-form hats checked against the ball hats
to about 1e−12), and the assumption that the b family's tail mass follows
the same model (not measured). The tail bound used in a run is
a posteriori: the run's own sums replace the model. None of the five
figures is a measurement of a run.

**P4 closed** (BOUNDS.md s4.5, s4.6). G_b's regions B and C are built by
integration by parts against the fast factor's expansion, with each region
checked against direct quadrature and a planted fault per region
(`test_p4.py`, 12 tests). PREREG row D0's precondition is lifted.

**The Gram at 280 modes, priced** (`gram_unit_cost.json`, measured on this
box at load average about 30):
- region A, one 12-node panel at m = 1: 0.58 to 0.60 s at u = 100 and
  5000, 1.30 s at u = 10. About 0.1 s of that is the panel itself; the rest
  is a per-call entry loop, now done once per G_b. About 2.3e5 panels
  (5.5e6 node evaluations at K = 14) gives **about 7 core-hours**;
- one endpoint derivative table (R = 120, 280 modes): 7.0 s;
- regions B and C: one piece with its two endpoints, 92 s; eight pieces
  sharing the same two endpoints, 115 s. So about 3.3 s per piece with
  about 90 s fixed per endpoint pair. With M = 34, m_max = 101 and
  t_max = 125 at target 1e−20 that is about 127 t-groups of about 7 to
  8 minutes, **about 16 core-hours**;
- the m = 0 tail and G_z: under 1 core-hour.

**Gram total: about 23 to 25 core-hours on this box (estimate from these
units, load average about 30)**, sharded into 24 parts (`gram_b_assign`:
region A units round-robin, the IBP units in t-groups so that each part
builds few endpoint tables). That is about 1 hour per part here, more on a
runner, and the calibration measures it. Over one core-hour in total: the
calibration ask states it.

**The disk-backed mode table** (`rebuild.DiskModeTable`): one file per
dyadic level, 40 bytes per ball (mantissa, exponent and radius from
`man_exp`), a sha256 per file verified at open (fail closed), streamed in
chunks of 2048 nodes. The dps-60 replay streams its own table and stores
nothing (`StreamTable`). Measured at 20 modes (`rss_probe.py`,
`rss_probe.json`, fresh subprocesses):

| | in memory | disk-backed |
|---|---|---|
| table | 184 bytes per ball resident | 40 bytes per ball on disk, 0 resident |
| one block of hats | +222 MB over the start | +67 MB over the start |

At 280 modes and S' = 2,700 (6.9e7 balls) that is about 12.8 GB resident per
process in memory, against about 2.6 GiB on disk, with a few hundred MB of
streaming buffers per process (extrapolated: buffers scale with the chunk
and nvec, about 0.2 to 0.4 GB). The 280-mode start-up RSS is 98 MB, with a
615 MB peak while the prolate data are built. Four processes are estimated
at 4 to 5 GB per runner, under the 13 GB the preflight requires. The
calibration measures it on a runner.

**The calibration request** (sent to the coordinator, **not committed**):
`mode: calibrate`, `blocks: 2`, 36 shards (job 0: shards 0 to 3, two blocks
each, block 0 replayed at dps 60), the 280-mode grid at S' = 2,700, G_b in
24 parts (6 jobs of 4 processes, max-parallel 6) merged by one job, cells
2.2, 2.5, 2.9 and N = 8, 16, 32. Estimated cost: the Gram (about 23 to 25
core-hours, above), plus one table build (about 0.2 core-hours), plus
8 blocks (about 0.6 core-hours at the box's block time) plus one dps-60
replay: **about 25 to 27 core-hours**, all of it GitHub Actions (0 USD).
The Gram is reused by the full run only if it is re-uploaded; as written,
the full run recomputes it (a door, not taken).

## 10. The calibration run (2026-10-26)

**Approved by the coordinator, exactly as quoted**, and committed as
`RUN_REQUEST.json` (sha256 8eeae788a323296caa186693a6be82b4e3e7635396f7931dbc87013d2b20c7e7,
commit 46491c421). Run: https://github.com/teal-sea/zeta-lab/actions/runs/40342431754
(push event; the plan job succeeded and six Gram jobs started).

**The coordinator's conditions for the full run** (to be met before it is
asked for, with the exact full request):
1. **Reuse this calibration's gram.json**, never recompute it (about
   24 core-hours). Either commit gram.json to the branch, if it is under
   about 10 MB, with its sha256 here, or download it across runs
   (`permissions: actions: read`, `actions/download-artifact@v4` with
   `run-id` and `github-token`) and have the preflight check the sha256
   recorded from this run.
2. **Record** the per-part Gram times, the table build time and size, and
   the per-block wall time and peak RSS per process, all from this run's
   artifacts (`calibration.json`, `gram_time_*.txt`).
3. **Re-size** the full plan from those numbers with at least 25 percent
   headroom, then ask with the exact full request.

The outcome of this run is not recorded yet. It belongs in a later dated
section, from its artifacts.

**Attempt 1 failed before any compute** (run 40342431754). The plan job and
every Gram job's preflight passed, but the "4 Gram parts" step wrote into
`prepared/`, which only a resume download creates. All six Gram jobs
exited within a minute, and merge and shards were skipped (no compute
spent). Fixed in a3cd044f1 (`mkdir -p` before every step that writes,
pinned by `test_workflow_matches_the_ruling`). **Attempt 2**, approved by
the coordinator: the approved request with the single added line
`"attempt": 2`, everything else byte-identical, sha256 5503a14f41fb82e1775e376eb002bcc4bba0185f837036e6d4a9c989e91253ca.

## 11. The calibration's outcome and the full run's size (2026-10-26, unit 4)

**Terminal outcome: success.** Run 40342895119 (attempt 2's request), every
job `success`, 14:47:10Z to 17:15:03Z. The eight artifacts were downloaded as
zips through the API and each zip's SHA-256 matched GitHub's recorded digest
(8 of 8). The figures below are read from them by `collect_calibration.py`
into `calibration_40342895119.json`, and from the job step times in the API.
All are **measured**, one run, GitHub-hosted `ubuntu-latest` (4 vCPU).

```runmanifest
id: c4_s2_exact_gram-2026-10-26-calibration
hunt: c4_s2_exact_gram
started: 2026-10-26T14:47Z
finished: 2026-10-26T17:15Z
ran:
  - GitHub Actions run 40342895119 (workflow c4-exact-gram, RUN_REQUEST.json sha256 5503a14f41fb82e1775e376eb002bcc4bba0185f837036e6d4a9c989e91253ca)
  - .venv/bin/python hunts/weil_propagation/c4_s2/exact_gram/collect_calibration.py <artifacts>
outcome: success; the Gram cost 13.1 core-hours in 24 parts, a block of 128 nodes costs 841 to 932 s per process with four running, the dps-60 replay block about 3,600 s
artifacts:
  - hunts/weil_propagation/c4_s2/exact_gram/calibration_40342895119.json
  - hunts/weil_propagation/c4_s2/exact_gram/gram.json
```

**Per job** (wall from the API; CPU is the sum of the four processes'
user plus system seconds; peak RSS is the largest single process):

| job | wall | CPU | peak RSS per process |
|---|---|---|---|
| plan | 8 s | | |
| gram parts 0 (parts 0 to 3) | 67.4 min | 12,414 s | 6.33 GiB |
| gram parts 1 (4 to 7) | 46.5 min | 9,002 s | 6.28 GiB |
| gram parts 2 (8 to 11) | 40.3 min | 7,095 s | 6.15 GiB |
| gram parts 3 (12 to 15) | 33.9 min | 5,438 s | 5.47 GiB |
| gram parts 4 (16 to 19) | 31.2 min | 5,637 s | 5.40 GiB |
| gram parts 5 (20 to 23) | 39.9 min | 7,703 s | 5.33 GiB |
| merge | 1.1 min | | |
| shards 0 (calibrate) | 79.1 min | 8,892 s plus the table build | 1.40 GiB (0.97 GiB table build) |

**Per Gram part** (CPU seconds): 0: 3,977 (G_z rides with part 0);
1: 3,446; 2: 3,546; 3: 1,444; 4: 2,729; 5: 2,062; 6: 1,698; 7: 2,513;
8: 1,782; 9: 1,233; 10: 1,719; 11: 2,361; 12: 1,403; 13: 1,982; 14: 1,435;
15: 619; 16: 1,277; 17: 1,807; 18: 1,075; 19: 1,478; 20: 2,327; 21: 1,576;
22: 2,126; 23: 1,674. Total **13.1 core-hours**, against s9's estimate of
23 to 25 (an overestimate by about 1.8). The partition is unbalanced (619 to
3,977 s, a factor 6.4): `gram_b_assign` deals region A round-robin and the
IBP t-groups by count, not by cost. No part is recomputed (below), so the
partition is left as it is; a recompute would first re-deal the units by
these measured costs. The four Gram processes of a job each peaked at 5.3
to 6.3 GiB, 21 to 25 GiB summed, above a 16 GB runner: the peaks did not
coincide in this run, and a recompute would have to check memory first.

**Shards** (job 0, shards 0 to 3, two blocks each, four processes at once):

| process | blocks (s each) | wall | peak RSS |
|---|---|---|---|
| shard 0 | block 0: 2,938 (with the dps-60 replay); block 1: 546 (alone, after the others ended) | 3,505 s | 1.40 GiB |
| shard 1 | 932, 859 | 1,812 s | 0.71 GiB |
| shard 2 | 932, 841 | 1,795 s | 0.70 GiB |
| shard 3 | 921, 857 | 1,800 s | 0.71 GiB |

Setup (loading the Gram, opening the table) is about 21 s per process.
A block is 841 to 932 s with four processes running and 546 s alone: the
four processes slow each other by about 1.6 (shared memory bandwidth). The
replay block ran 1,800 s alongside the others and 1,138 s alone; at the
contended rate that is about 1,800 + 1,138 × 1.6 ≈ 3,600 s (**estimate**
from the measured parts), which is the price used below. Against s8's
re-pricing (28 core-hours, built on the box's 412 s block alone) the block
is about 2.3 times dearer on a runner with four running.

**Table and disk.** The mode table built in 1,194 s (one process, 0.97 GiB
peak) to **2.58 GiB** on the runner's disk, under the preflight's 10 GB.
Each block checkpoint is about 8.5 MB (the running sums at every (c, N));
every block's file is uploaded, so the full run would upload about 338 ×
8.5 MB ≈ 2.9 GB of artifacts. Only each shard's last file is read by
`assemble`; pruning the superseded ones before upload is a door, not taken.

**The calibration record's defect.** The workflow's `calibration.json`
listed shard 0 with block 0 only: it read the checkpoints in `glob` order
and kept the last one read, not the last block. The table above reads every
checkpoint; the step now sorts (the last block's file carries all the
times), and so does `collect_calibration.py`.

**A defect found while sizing.** 338 blocks in 36 shards of 10 leave shards
34 and 35 empty, and `run_shard` read `rng[0]` of an empty range: job 8
would have failed with an IndexError after its other shards finished.
`run_shard` now returns `None` for an empty shard without reading a key or
writing a file (`assemble` already skipped them), pinned by
`test_a_shard_with_no_blocks_returns_none`.

### 11.1 The Gram is reused, by digest

`gram.json` from the merge job is **20,048,277 bytes, sha256
2b907a79a8a127e0626f9ade01ee7f8335761e7cbf564a48d386cb5854a94872**, under
the 50 MB limit, so it is **committed** beside the request
(`exact_gram/gram.json`; no cross-run download, no `actions: read`).
Checked here before committing: its request key equals `_gram_key` of the
request, `is_bound` is true, both matrices load and invert in balls at
133 bits (largest radius 1.0e−11 in G_z and 6.0e−11 in G_b; in the inverses
3.1e−11 and 4.5e−10). The radii are far above the 1e−20 target named by
`gram_target_exp`. They are carried in every ρ, so this costs nothing in
validity. It is a door on ε_q that is not taken: the binding term sits elsewhere, below.

In full mode the workflow runs no gram and no merge job. The shards job
copies `exact_gram/gram.json` into `prepared/` and refuses unless its
sha256 equals the request's `gram_sha256`. `rebuild.setup` checks the same
digest again and refuses if the file is absent, so a missing Gram can no
longer fall through to recomputing it in-process. Both refusals are
pinned (`test_a_gram_named_by_sha256_is_fail_closed`, with a one-byte
planted change; `test_workflow_matches_the_ruling`).

### 11.2 The full run, sized from the calibration

Per process, the worst shard holds 9 ordinary blocks and one replay block
(the replay set is every 16th block; no shard of 10 holds two):

- worst process: 9 × 932 + 3,600 + 60 = **12,048 s (200.8 min)**, against
  0.75 × 335 = 251 min inside the processes' self-stop;
- worst job: install and download (about 3 min) + table build (1,200 s) +
  200.8 min ≈ **224 min**, against the 350-minute cap: **36 % under** (at
  least 25 % required). The preflight checks both, per shard, from the
  request's `calibration` record;
- every one of the 9 jobs holds a replay shard, so each projects at about
  224 min;
- **max-parallel 4** (rung 3's production and the Skewes main run share the
  repo's 20-job pool; PR CI needs slots): 9 jobs in three waves,
  **about 11.2 hours wall**;
- **compute**: 104 core-hours of shard processes (316 ordinary blocks at
  932 s, 22 replay blocks at 3,600 s, setup), 3 of table builds; the runners
  are held about 2,014 runner-minutes (4 vCPU each), GitHub Actions only,
  0 USD;
- memory: 4 × 1.40 GiB = 5.6 GiB per runner, under the preflight's 13 GB.

The 932 s is the slowest ordinary block measured, the 3,600 s is the
estimate above, and the cost of a block does not depend on s: the work per
block is the same table products and sin_cos over the same logs, and s
enters only as their arguments.

**Pipefail.** The workflow now sets `defaults: run: shell: bash`, which
GitHub runs as `bash -eo pipefail`; without a shell key a step runs
`bash -e` without pipefail, and a failing command piped to `tee` passes.
The piped lines today are echo only, so this is a guard, not a fix.

### 11.3 What the full run evaluates, and when it stops

With ε_t null (LEMMA.md does not close the truncation), the run can reach
PREREG rows **D0, D1 or D2** at each c, never D3. Its output is the 34
shards' window sums. `assemble` and the C_N(ε) counts are run afterwards on
them, as PREREG s2 and s4 fix.

- **D0** if ε_q is not finite, a Gram fails to invert in balls, or a check
  of PREREG s4 fails;
- **D1** if ε_q is finite and below 1.18e−2 (c = 2.9): C_8, C_16, C_32 at
  ε_q + ε_aux on the three spaces, about R^(280) only;
- **D2** if ε_q is finite and at or above 1.18e−2.

**Radius only, for feasibility** (no centre read): after the calibration's
8 blocks the Frobenius norm of the radius of the partial ΔT sum at
(2.9, 32) is at most 1.1e−6 per shard and falls with s (6.4e−7, 4.2e−7,
2.2e−9 for shards 1 to 3). The ball radius is therefore not expected to be
the binding term of ε_q. The P3 alias and the a posteriori tail are the
binding terms (E1 target 7.0e−4, s8).

**Kill conditions** (each stops the run or its reading, never skips):
1. a dps-60 replay block whose balls do not intersect the 133-bit balls
   (PREREG s4 item 1): the process raises, that job fails, nothing is
   counted;
2. a guard refusal: the closure moved or is dirty, a checkpoint has a
   stale key, or the Gram's sha256 differs from the request's;
3. a preflight failure: backend not Arb, headroom, memory or table size;
4. a process reaching its 335-minute self-stop: its job fails with
   checkpoints uploaded, and the run is **not** resumed without a new ask
   (the projection said 201 min, so the calibration was wrong);
5. `assemble` refusing a missing or short shard.

**The full request** (sent to the coordinator, **not committed** until its
reply). It is the calibration request with `mode: full`, `blocks` and
`attempt` removed, and `gram_sha256` and `calibration` added:

```json
{
 "mode": "full",
 "shards": 36,
 "gram_parts": 24,
 "prepared": "prepared",
 "nvec": 280,
 "dps": 40,
 "prec": 133,
 "Kmax": 14,
 "S_prime": 2700,
 "delta_num": 1,
 "delta_den": 16,
 "block": 128,
 "M": 34,
 "J": 40,
 "kb": 90,
 "cells": ["2.2", "2.5", "2.9"],
 "Ns": [8, 16, 32],
 "gram": "exact",
 "gram_target_exp": 20,
 "gram_R": 120,
 "local_data": ["satake", [1]],
 "replay_every": 16,
 "replay_prec": 200,
 "gram_sha256": "2b907a79a8a127e0626f9ade01ee7f8335761e7cbf564a48d386cb5854a94872",
 "calibration": {
  "run": 40342895119,
  "block_wall_s": 932,
  "replay_block_wall_s": 3600,
  "setup_s": 60,
  "table_build_s": 1200,
  "peak_rss_gb": 1.40,
  "table_disk_gb": 2.58
 }
}
```

### 11.4 The full run

**Approved by the coordinator** ("go", 2026-10-26), exactly as quoted above.
It is committed as `RUN_REQUEST.json`, sha256
e5ad7bce8fd7762d47f75c9a5ed2b2ab8a3bc3956943deb40452c46de1c4f5be. The
coordinator's conditions:
- no second request while this run is pending or running;
- on any kill condition, report the shards and the reason, and ask before
  any re-request, which names only those shards with a new `attempt` field;
- after a clean finish, run `assemble` and the C_N(ε) counts and read
  D0, D1 and D2 per c exactly as PREREG s3 writes them, never D3 while
  ε_t is null.
