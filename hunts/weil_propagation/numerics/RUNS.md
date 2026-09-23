# RUNS: estimates written before launch

Machine: operator laptop (M-series, 16 GB). Every run is single-process,
under 10 minutes, under 1 GB, checkpointed per unit (resumable).

| run | unit cost (measured) | units | estimate | actual |
|---|---|---|---|---|
| `repro.py` | 0.03-0.8 s per cell | 19 cells | < 30 s | 5.5 s |
| `transport.py dh 64` | ~0.4 s per c incl. pairs + HF | 49 c | ~30 s | 22 s |
| `transport.py dh 128` | ~1.3 s per c | 49 c | ~70 s | 74 s |
| `transport.py zeta 64` | ~2 s per c | 49 c | ~2 min | 74 s |
| `transport.py zeta 128` | ~8 s per c (prec 900, HF at 1600) | 49 c | ~7 min | 241 s |

Unit costs from 2-5 cell smoke runs in the scratchpad (DH N=128 c in
[30, 30.25]: 5 s for 5 c; zeta N=128 c in [30, 30+1/16]: 4.9 s for 2 c).
| `crossing.py 64 96 128 192 256` | 13 eigen-solves + 3 ball LDL per N; ~0.5 s (N=128) to ~5 s (N=256) per solve | 5 N | ~3 min | 129 s |
| `edge.py dh` | ~0.5-4 s per cell | 24 cells | ~1 min | 30 s |
| `edge.py zeta` | ~1 s (N<=128) to ~60 s (N=256, HF at 3600 bits) per cell | 18 cells | ~6 min | 171 s |
| `harden.py dh 64`, `dh 128` | Temple + ball LDL per cell, 0.2-0.7 s | 98 cells | ~1 min | 8 s + 32 s |
| `harden.py zeta 64`, `zeta 128` | build at 1600 bits + LDL, ~1-3 s per cell | 98 cells | ~3 min | 28 s + 104 s |
| `precision_check.py` | 3 recomputations per cell at up to 2x precision, zeta N=128 HF at 3200 bits dominates | 4 cells | ~3 min | 27 s |
| `factA_check.py` (N' ladder 64..384) | one build at c' per rung, 0.1-6 s | 14 rungs | ~30 s | ~15 s |
| `factA_check.py` extra rungs N' = 512, 768, 1024 (DH) | build ~N'^2 entry calls at 400 bits; ~10-60 s per rung, < 1 GB | 3 rungs | ~2 min | |
| Task A `epstein_scan.py 64`, `128` (handoff from theory, 2026-09-23) | Epstein (1,1,6) both sectors at 400 bits: probe (c = 47, N = 128) 3.2 s for two sectors with double assembly; one assembly per cell, ~1.5 s (N=128), ~0.5 s (N=64) | 93 c in [2, 48] step 1/2 | ~1 min + ~2.5 min | 57 s + (N=128 running, ~4.5 s per cell: ~7 min) |
| Task A `epstein_crossing.py` | bisection to 2^-10 per (N, sector), ~13 solves + 2 ball LDL | <= 4 (N, sector) | ~1 min | |
| Task B `zeta_pole.py 64`, `128` | zeta at 900 bits + ball LDL at 1600: first run 1.4 s per cell (N=64); mu_1 by approximate spectrum adds ~0.3 s (N=64), ~2.3 s (N=128) | 117 c in [2, 60] step 1/2 | ~3 min + ~10 min (N=128 in two resumable runs under the 580 s guard) | 164 s (first N=64 run, mu_1 defect: rerun) |
| Task A control `epstein_scan.py 64 dedekind` | same as Epstein N=64 | 93 c | ~1 min | 59 s |
| Task A `epstein_offline.py` (box count [0.51,1.3]x[14,20] + findroot) | epstein_completed 1.1 s per evaluation at dps 20; ~100-200 boundary samples; findroot ~20 evaluations per seed | 1 box, <= 4 seeds | ~5 min | 242 s + 16 s |
| Task A `epstein_offline.py` lower boxes [0.51,1.3]x[0.5,7] and x[7,14] (two runs) | as above, perimeter ~15 each | 2 boxes | ~4 min each | |
| Task A `epstein_crossing.py` | as estimated above | 4 (N, sector) | ~5 min | |

Both handoff tasks sit under the 10-minute, few-GB local limit, so no CI
proposal is needed for them.

The first launch of the four transport runs used `timeout`, which macOS does
not ship, and zsh did not word-split the loop variable: nothing ran (exit
127, 0 s). Relaunched under bash with `perl -e 'alarm 580; exec ...'` as the
per-run guard.
