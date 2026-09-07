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
