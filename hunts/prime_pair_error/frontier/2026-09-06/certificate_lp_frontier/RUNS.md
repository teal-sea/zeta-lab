# Runs

All on the operator's laptop (16 GB M4) under a foreign load average of
60 to 140 from another session's agent fleet, so wall times are inflated
several-fold. Memory stayed under 300 MB per job except the one noted.

| script | N | y | wall | note |
|---|---:|---:|---:|---|
| lp_frontier.py (dense primal) | 10^3 | 2..1000 | < 1 s each | |
| lp_frontier.py | 10^4 | 10..2000 | 0.1 s .. 276 s | y=3162 killed by me at 2.9 GB |
| lp_frontier.py (first dual form) | 10^4, 10^5 | any | stalled > 10 min | monotone-chain dual is degenerate; abandoned |
| lp_allcells_cg.py | 10^4 | 100, 316 | 3 s, 242 s | matches dense to all digits |
| lp_allcells_cg.py | 10^5 | 100, 316 | 14 s, 709 s | |
| lp_allcells_cg.py | 10^5 | 1000 | queued | |
| lp_allcells_cg.py | 10^6 | 1000, 3162 | queued | expected ~10^4 excess at y=1000 by the N^{3/4} law |
| lp_prime_cells.py | 10^4 | 40..1000 | < 1 s each | |
| lp_prime_cells.py | 10^5 | 316..3162 | 5 s .. 17 s | |
| lp_prime_cells.py | 10^6 | 1000 | 135 s | y > 1193 reports unbounded (float artifact, value is 0) |
| lp_dictionaries.py --lift 15 | 10^4, 10^5 | 31, 100 | 0.4 s .. 15 s | |
| lp_dictionaries.py --lift 15 | 10^5 | 1000, 3000 | queued | |
| lp_dictionaries.py --selberg | 10^4 | 31 | 59 s | y = 100, 316 queued |

Estimate before the larger runs: constraint generation converges in 3 to 6
rounds; each round is a dense (cells x y) dual simplex, cells growing to about
4y plus the violated set. At N = 10^6, y = 1000 that is roughly 10^4 x 10^3 per
round, tens of seconds unloaded. Nothing here needed CI; anything at N = 10^7
or y = 10^4 should go there.

## CI batch, 2026-09-07 (`.github/workflows/certificate-lp-barrier.yml`)

Launched after the three queued local rows were OOM-killed under a foreign
load of 200+. Estimates, from the (10^5, 316) round profile (4364 cells, 3
rounds, ~150 s unloaded):

| job | cells expected | per-round LP | rounds | wall estimate | prediction |
|---|---:|---:|---:|---:|---|
| all-cells 10^6 / 316 | ~5k | 1 min | 4 | 10 min | 0.32/sqrt(y): 18k; drift: 3.8k |
| all-cells 10^6 / 1000 | ~15k | 5 min | 5 | 30 min | 0.32/sqrt(y): 10.1k; drift: 4.4k |
| all-cells 10^6 / 3162 | ~30k | 30 min | 5 | 3 h | 0.32/sqrt(y): 5.7k |
| all-cells 10^7 / 1000 | ~20k | 10 min | 6 | 1 h | 0.32/sqrt(y): 101k; drift: 44k |
| all-cells 10^7 / 3162 | ~50k | 1 h+ | 6 | may time out | 0.32/sqrt(y): 57k; drift: 41k |
| prime-cells 10^7 | 3.6k | seconds | 1 | 5 min | ~0.5 sqrt(N) at y = sqrt N, 0 at N^0.53 |
| lifted 10^5 / 1000, 3000; 10^6 / 3000 | 5k .. 30k | 1 .. 30 min | 4 | 0.3 .. 3 h | the hunt's family floor at its own seed support |
| selberg 10^4 / 316 | 2.5k (x2 rows) | minutes | 4 | 30 min | ~0.7 x 32.5 if the constant-factor pattern holds |

Every round's `value-psi` is the optimum of a relaxation and therefore a
rigorous lower bound on the final floor; a timed-out job still reports one.
Owner: this session (watches the run and folds the numbers into RESULTS.md).

**Outcome (run 34123341782):** 4 rows succeeded with artifacts (prime-cells
10^7, lifted 10^5/1000, all-cells 10^6/316, all-cells 10^6/1000); 6 rows hit
their time limit (GitHub reports "cancelled"), and their artifact steps did
not run. Two converged results were recovered from logs: (10^6, 1000) again
(10699.906, identical) and (10^7, 1000) = 111891.518 in 3210 s. Cause of
the waste: `lp_allcells_cg.py` appended y = sqrt(N) to every job through
its default `--alpha 0.5`, so the y = 1000 jobs went on to attempt y = 3162
after finishing. Fixed: no default alpha. The (10^7, 3162) row itself is
out of reach of plain constraint generation in 350 minutes (9.2 million
violated cells after round 0); it needs a warm start or a smarter initial
cell set before it is worth another runner-day.

## Local runs, 2026-09-07 (barrier work)

| script | (N, y) | wall | note |
|---|---|---:|---|
| barrier_lemmas.py | (10^3, 31), Y up to N | seconds | restricted dual at Y = N reproduces the LP floor |
| barrier_lemmas.py | (10^4, 100), Y up to 3000 | ~2 min | |
| barrier_lemmas.py | (10^5, 316), Y up to 9480 | ~5 min | |
| barrier_lemmas.py | (10^6, 1000), Y up to 10^4 | ~15 min, ~700 MB | the rigorous 7162 |
| barrier_lemmas.py | (10^5, 30), (10^6, 60) | ~1 min each | staircase vs restricted dual |
| lp_allcells_cg.py | (10^5, 30), (10^5, 60), (10^6, 60) | 0.1 s, 0.2 s, 3.7 s | floors at y = N^{0.3} |
| lp_frontier.py (dense) | (2 10^4, 141) and the elevation/variance probes | ~1 min | |
