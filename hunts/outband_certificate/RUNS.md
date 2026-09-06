# outband_certificate: runs

All on the operator's 16 GB Mac, `.venv/bin/python`, HiGHS through `scipy.optimize.linprog`.
Solve time grows like about X^2.7 in the truncation; the strip adds a few dozen rows and
roughly doubles the cost at the wide rungs.

## 2026-09-05 to 06, first session

`dual.py`:

| grid | case | seconds |
|---|---|---|
| X=40, J=200 | control / strip 1.5 / strip 3.0 | 0.2 / 0.6 / 9.9 |
| X=80, J=320 | control / strip 1.5 | 1.0 / 4.3 |
| X=80, J=320 | strip 1.05 | about 1.5 |

Fine sweep at X=80, J=320, eight strip edges from 1.02 to 1.5: 1 to 4 s each.

`ladder.py`, 18 solves, checkpointed to `artifacts/ladder-narrow-strip.json`:

| X | J | control | width 0.05 | width 0.10 | width 0.20 |
|---|---|---|---|---|---|
| 40 | 200 | 0.2 s | 0.2 | 0.2 | 0.3 |
| 80 | 320 | 0.9 | 1.5 | 1.6 | 2.4 |
| 120 | 480 | 3.6 | 6.3 | 8.3 | 7.9 |
| 160 | 640 | 8.9 | 16.5 | 16.9 | 22.0 |
| 240 | 960 | 61.0 | 118.0 | 92.6 | not run |
| 320 | 1280 | 133.4 | 255.3 | 417.8 | not run |

Every control value matches hunt #110's artifacts where the rungs coincide (X = 40, 80, 240,
320). The X = 320 strip solves are the only ones that took longer than the session's
foreground limit and finished in the background.
