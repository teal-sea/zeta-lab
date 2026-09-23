# RUNS: estimates written before launch

Machine: operator laptop (M-series, 16 GB). Every run is single-process,
under 10 minutes, under 1 GB, checkpointed per unit (resumable).

| run | unit cost (measured) | units | estimate | actual |
|---|---|---|---|---|
| `repro.py` | 0.03-0.8 s per cell | 19 cells | < 30 s | 5.5 s |
| `transport.py dh 64` | ~0.4 s per c incl. pairs + HF | 49 c | ~30 s | 22 s |
| `transport.py dh 128` | ~1.3 s per c | 49 c | ~70 s | |
| `transport.py zeta 64` | ~2 s per c | 49 c | ~2 min | |
| `transport.py zeta 128` | ~8 s per c (prec 900, HF at 1600) | 49 c | ~7 min | |

Unit costs from 2-5 cell smoke runs in the scratchpad (DH N=128 c in
[30, 30.25]: 5 s for 5 c; zeta N=128 c in [30, 30+1/16]: 4.9 s for 2 c).
| `crossing.py 64 96 128 192 256` | 13 eigen-solves + 3 ball LDL per N; ~0.5 s (N=128) to ~5 s (N=256) per solve | 5 N | ~3 min | |
| `edge.py dh` | ~0.5-4 s per cell | 24 cells | ~1 min | |
| `edge.py zeta` | ~1 s (N<=128) to ~60 s (N=256, HF at 3600 bits) per cell | 18 cells | ~6 min | |

The first launch of the four transport runs used `timeout`, which macOS does
not ship, and zsh did not word-split the loop variable: nothing ran (exit
127, 0 s). Relaunched under bash with `perl -e 'alarm 580; exec ...'` as the
per-run guard.
