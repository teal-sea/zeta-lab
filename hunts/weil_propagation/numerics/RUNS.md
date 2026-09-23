# RUNS: estimates written before launch

Machine: operator laptop (M-series, 16 GB). Every run is single-process,
under 10 minutes, under 1 GB, checkpointed per unit (resumable).

| run | unit cost (measured) | units | estimate | actual |
|---|---|---|---|---|
| `repro.py` | 0.03-0.8 s per cell | 19 cells | < 30 s | 5.5 s |
| `transport.py dh 64` | ~0.4 s per c incl. pairs + HF | 49 c | ~30 s | |
| `transport.py dh 128` | ~1.3 s per c | 49 c | ~70 s | |
| `transport.py zeta 64` | ~2 s per c | 49 c | ~2 min | |
| `transport.py zeta 128` | ~8 s per c (prec 900, HF at 1600) | 49 c | ~7 min | |

Unit costs from 2-5 cell smoke runs in the scratchpad (DH N=128 c in
[30, 30.25]: 5 s for 5 c; zeta N=128 c in [30, 30+1/16]: 4.9 s for 2 c).
