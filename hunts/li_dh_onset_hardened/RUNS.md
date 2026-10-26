# li_dh_onset_hardened: estimates and run manifests

The box: 32 vCPU, 115 GiB, shared with a campaign pinning Lean jobs. Rules in
`MISSION.md`. Every estimate below was written before the spend it prices.

## Estimate 1 (2026-10-26, before any run)

Timed one unit: `log F(s)` in Arb (four `acb.zeta` Hurwitz values, one
`acb.lgamma`), warm, single process, at four points on or near a circle of
radius about 0.9999: 0.7 to 1.5 ms at 128 bits, 1.1 to 2.4 ms at 200 bits,
1.4 to 2.8 ms at 250 bits, 0.1 to 0.2 ms where Re s is in the thousands.
`acb.dft` on 65536 points at 200 bits: 0.54 s.

First-wave jobs, each single process:

| job | units | estimate |
|---|---|---|
| admissibility (top edge, line grid, two small boxes, sigma bound) | about 2e4 ball evaluations at 128 bits | under 2 min |
| evaluator timing (1000 nodes x 2 precisions, 20 iv nodes, xi control) | 2000 Arb + 20 iv evaluations, one small DFT | under 5 min (iv Euler-Maclaurin about 1 s per node) |
| aliasing-circle cover and sizing | adaptive cover of the circle r', likely 1e4 to 1e5 balls | under 10 min |

All three are far below the one-core-hour gate.

## First wave, 2026-10-26

Box state at launch: 1-minute load 27 to 36 on 32 vCPU, MemAvailable 66 to 72 GiB.
At most two of this hunt's processes ran at once, each `nice -n 10`.

```runmanifest
id: li_dh_onset_hardened-2026-10-26-admissibility
hunt: li_dh_onset_hardened
started: 2026-10-26T13:18
finished: 2026-10-26T13:19
ran:
  - .venv/bin/python hunts/li_dh_onset_hardened/admissibility.py --T 160
  - .venv/bin/python hunts/li_dh_onset_hardened/admissibility.py --T 133 --out artifacts/admissibility_T133.json
outcome: at 128 bits the box count is 98 at T = 160 and 78 at T = 133, the line sign changes 94 and 74, two located off-line zeros right of the line in each, so N_box = N_line + 2q closes exactly at both heights, and dropping a quadruple or displacing a square breaks it; 14 s and 12 s
artifacts:
  - hunts/li_dh_onset_hardened/artifacts/admissibility.json
  - hunts/li_dh_onset_hardened/artifacts/admissibility_T133.json
```

```runmanifest
id: li_dh_onset_hardened-2026-10-26-evaluator
hunt: li_dh_onset_hardened
started: 2026-10-26T13:16
finished: 2026-10-26T13:18
ran:
  - .venv/bin/python hunts/li_dh_onset_hardened/evaluator.py
outcome: 1.03 ms per node at 200 bits and 1.83 ms at 250 bits over 1000 nodes of the c = 5000 circle; the iv route meets every Arb ball at 20 height-stratified nodes and a kappa moved by 2^-120 misses at 17 of them; the xi control contains all 48 committed values and both planted faults flip it; DH at r = 0.9 and r = 0.99 agree to 2e-30 for n <= 200 and both contain hunt 128's table
artifacts:
  - hunts/li_dh_onset_hardened/artifacts/evaluator.json
```

A defect found and fixed during this wave, recorded because it would have made
a control vacuous: the first version of `evaluator.ball_box` built the Arb box
with `arb.lower()`/`upper()` outside a precision guard, so it rounded to 53
bits and the "every Arb ball meets the iv box" check compared boxes of width
1e-17 instead of 1e-43. The planted kappa fault (2^-120) passed undetected,
which is how it was found; the box is now built from the exact midpoint and
radius. A second defect of the same family: `balls.segment_arg_change` built
its rectangle before entering the precision guard, so the location squares of
half-width 1e-20 dissolved into 53-bit rounding and the count never resolved.
Both are fixed before every run recorded above.

```runmanifest
id: li_dh_onset_hardened-2026-10-26-sizing
hunt: li_dh_onset_hardened
started: 2026-10-26T13:20
finished: 2026-10-26T13:23
ran:
  - .venv/bin/python hunts/li_dh_onset_hardened/sizing.py
outcome: M(rho) bounded by 91602 to 109567 on four aliasing circles between 1 - 5e-5 and 1 - 4.3e-5, every arg chain closing; at tol 1e-10 and n <= 500000 the aliasing bound needs 2^21 nodes at c = 5000, 2^19 at c = 2000 to 3000, and 2^24 at c = 1e4
artifacts:
  - hunts/li_dh_onset_hardened/artifacts/sizing.json
```

```runmanifest
id: li_dh_onset_hardened-2026-10-26-rehearsal
hunt: li_dh_onset_hardened
started: 2026-10-26T13:40
finished: 2026-10-26T13:42
ran:
  - .venv/bin/python hunts/li_dh_onset_hardened/rehearsal.py
outcome: at c = 5000 and N = 2^17 the ball branch tracker crosses the whole circle and closes, 71 s sampling, 18 s tracking, 2 s DFT; a first attempt was stopped after 13 CPU-minutes spent on unnecessarily wide balls, fixed by S_BALL_MAX
artifacts:
  - hunts/li_dh_onset_hardened/artifacts/rehearsal.json
```

## Estimate 2 (2026-10-26): production, not yet run

From the rehearsal (1.09 ms per node at 192 bits, contended rate up to 1.83 ms):

| run | N | bits | node evaluations | core-hours |
|---|---|---|---|---|
| c = 5000, n <= 500000 | 2^21 | 162 (run at 192) | 1,048,577 | 0.4 to 0.6 |
| c = 2500, n <= 500000 | 2^19 | 234 (run at 256) | 262,145 | 0.15 to 0.3 |

Both together, as a production-scale two-radii check: under one core-hour, one
process at a time, under 2 GB each. The lambda table (5e5 balls) stays out of git
and is recorded by SHA-256; only the sign summary, n\*, and the balls near n\*
are committed. Sent to the coordinator as an `ask` before any spend.

## Production, 2026-10-26 (approved by the coordinator: A then B, sequential)

Pre-registered in `MISSION.md` (commit 8964573b4), before run A started.
`trapezoid.S_BALL_MAX`, the refactor to `evaluate_nodes`, and the incremental
rho^{-n} in `li_balls` landed after the first-wave artifacts were written. They
change how a decision is reached, not what it is. The xi control and both DH
radii tests were rerun live against the changed code and passed. Box during the
runs: load 28 to 40 on 32 vCPU, MemAvailable 65 to 69 GiB, peak RSS about
3.7 GB (run A).

```runmanifest
id: li_dh_onset_hardened-2026-10-26-production-A
hunt: li_dh_onset_hardened
started: 2026-10-26T13:50:44
finished: 2026-10-26T14:10:55
ran:
  - .venv/bin/python hunts/li_dh_onset_hardened/production.py --tag A --c 5000 --log2N 21 --prec 192
outcome: controls passed in-run; 1048577 node evaluations in 1098 s, tracking 26 s, DFT 31 s; branch closed; the first ball-negative index is 328997 with no undecided index before it; 1211 s in all
artifacts:
  - hunts/li_dh_onset_hardened/artifacts/production_A.json
  - hunts/li_dh_onset_hardened/artifacts/big/lambda_A.txt (out of git, sha256 5ebe86082023966b65f06d1c11c020bd5718b6ff7c85b8fcf0450e041f87396b)
```

```runmanifest
id: li_dh_onset_hardened-2026-10-26-production-B
hunt: li_dh_onset_hardened
started: 2026-10-26T14:11:08
finished: 2026-10-26T14:18:35
ran:
  - .venv/bin/python hunts/li_dh_onset_hardened/production.py --tag B --c 2500 --log2N 19 --prec 256
  - .venv/bin/python hunts/li_dh_onset_hardened/compare.py
outcome: controls passed in-run; the first ball-negative index is again 328997 with none undecided; the A and B balls intersect at all 500000 indices; 447 s
artifacts:
  - hunts/li_dh_onset_hardened/artifacts/production_B.json
  - hunts/li_dh_onset_hardened/artifacts/two_radii.json
  - hunts/li_dh_onset_hardened/artifacts/big/lambda_B.txt (out of git, sha256 b46903b3e8141688d1ca52f5733f3deb5ba999e4653eaa35ae745c2590bbd2e4)
```

The chunk checkpoints (`artifacts/ckpt_A/` 92 MB, `ckpt_B/` 27 MB) were
deleted after the runs landed. They are working files: a rerun rebuilds them.
The two tables (50 MB) stay out of git in `artifacts/big/`. This workspace is
swept when idle, so the SHA-256 values above are the durable record, and a
rerun reproduces the tables in about 28 minutes.

## Follow-up, 2026-10-26: durability, and the independent evaluator

**The tables, made durable.** They are copied out of the sweepable workspace to
`${ZETA_LAB_CACHE:-~/.cache/zeta-lab}/li_dh_onset_hardened/` (out of git) and
checked:

    $ sha256sum ~/.cache/zeta-lab/li_dh_onset_hardened/lambda_*.txt
    5ebe86082023966b65f06d1c11c020bd5718b6ff7c85b8fcf0450e041f87396b  lambda_A.txt
    b46903b3e8141688d1ca52f5733f3deb5ba999e4653eaa35ae745c2590bbd2e4  lambda_B.txt

Both match the production manifests above.

**Regenerating each table.** Use the commit whose code produced them,
cd1a04cb1 (the production driver). The result commit 109593233 changed no code
the runs use. From the repository root:

    git worktree add ../regen-151 cd1a04cb1 && cd ../regen-151
    .venv/bin/python -m venv .venv && .venv/bin/pip install -r requirements.txt && .venv/bin/pip install -e .   # or reuse a venv with python-flint 0.9.0, mpmath 1.3.0
    nice -n 10 .venv/bin/python hunts/li_dh_onset_hardened/production.py --tag A --c 5000 --log2N 21 --prec 192   # about 20 min
    nice -n 10 .venv/bin/python hunts/li_dh_onset_hardened/production.py --tag B --c 2500 --log2N 19 --prec 256   # about 8 min
    sha256sum hunts/li_dh_onset_hardened/artifacts/big/lambda_A.txt hunts/li_dh_onset_hardened/artifacts/big/lambda_B.txt

The tables are deterministic given the code and the python-flint version: a
resumed run reproduced its table bit for bit (the smoke test before run A).

**Estimate 3 (before the independent run).** I timed `iv_fast` (f and log G in
mpmath.iv at 256 bits) on 1000 nodes spread over the upper half of the c = 2500,
N = 2^19 circle, 4 processes x 250: 0.057 s per node. The older `iv_route`
evaluator measured 0.14 s on the same nodes.

| part | estimate |
|---|---|
| 262,145 node evaluations | 4.2 core-hours (about 1.1 h wall on 4 processes) |
| the M(rho) arc cover in iv | 0.2 to 0.5 core-hours (the r = 0.95 cover took about 140 s against Arb's 1) |
| the branch cover in iv (B needed about 20k arc evaluations) | about 0.3 core-hours |
| DFT, extraction, comparison | under 0.05 core-hours |
| **total** | **about 5 core-hours**, inside the pre-approved 6 |
