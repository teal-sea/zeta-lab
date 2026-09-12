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

## 2026-09-06, second pass

Lattice ladder at X = 80, J = 320, strip 1.5: h = 1/16 (1 s / 3 s), 1/32 (2 s / 9 s),
1/64 (5 s / 15 s), and h = 1/32 at X = 160, J = 640 (33 s / 87 s): in-band 0.6749570,
strip 0.6830328, gain +0.00808.

`signed_window.py`: L-BFGS-B over an even profile on `[-S, S]`, ten starts, penalty on the
strip sign condition. Control on `[-1/2, 1/2]` at step 0.005 lands at J = 1.32845 (Theorem D
1.32750): the Riemann-sum convolution misreads the window's edge discontinuity by about
`1e-3`, and the optimiser compensates with a spurious negative edge. Every strip start was
rejected on the sign condition; the edge lemma in `RESULTS.md` section 5 says why. Kept as
the record of the attempt, not as an instrument.

Counterexample check: `K = sinc^2(x)(1 - c cos 4 pi x)` on `[-2000, 2000]` at step `1e-3`,
FFT: `min K = 0` (c = 1) and `5e-33` (c = 0.5); `max Khat` on `1 < |alpha| < 3.05` is `1.5e-6`
and `7.4e-7`; `min Khat` there `-0.5` and `-0.25`; nothing beyond `3.05` above `6e-11`.

Large-X lattice ladder, strip 1.5, planned as (1/16, X = 160), (1/64, 160), (1/16, 320),
(1/32, 320), each in-band and strip. Landed: (1/16, 160): in-band 0.6764627 (14 s), strip
0.6833922 (123 s), gain +0.00693; with the earlier (1/32, 160) row, gain +0.00808. **The run
was killed by the operating system for memory on the (1/64, 160) rung** (10,240 variables,
dense constraint matrix, beside the rest of a 16 GB machine's load). The (1/16, 320) and
(1/32, 320) rows are not run. They are plain scipy and belong on Modal, which is wired; not
launched here because it spends the operator's Modal budget.
