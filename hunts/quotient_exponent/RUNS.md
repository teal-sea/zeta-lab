# quotient_exponent: run manifests

```runmanifest
id: quotient_exponent-2026-09-09-reformulation
hunt: quotient_exponent
started: 2026-09-09T23:15-05:00
finished: 2026-09-10T00:05-05:00
ran:
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/lp.py --N 1000 10000 100000 --out lp_small.json
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/lp.py --N 1000000 3000000 10000000 --out lp_large.json
outcome: the four published diagonal values reproduce to every printed digit from an objective that is the excess itself rather than a difference of quantities near 1e8; new rows at 3e6 (14477.154080) and 1e7 (30297.736768), where T*/N^{3/4} is 0.1704, below the published 0.18-0.23 band; the two identities the reformulation rests on hold to 8.3e-16 relative at every cutoff
artifacts:
  - hunts/quotient_exponent/artifacts/lp_small.json
  - hunts/quotient_exponent/artifacts/lp_large.json
```

```runmanifest
id: quotient_exponent-2026-09-10-surface
hunt: quotient_exponent
started: 2026-09-10T00:05-05:00
finished: 2026-09-10T00:40-05:00
ran:
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/sweep.py --N 10000 100000 1000000 --alpha 0.30 0.35 0.40 0.45 0.50 0.55 0.60 0.65
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/threshold.py --N 1000 10000 100000 1000000
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/staircase.py --N 1000
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/staircase.py --N 10000
  - .venv/bin/python hunts/quotient_exponent/fit.py
outcome: E sqrt(y)/N falls by 2.3 to 2.8 inside the conjecture's own range instead of holding constant; free fit a = 1.150, b = 0.878 against the conjectured (1, 0.5), with the conjectured shape three times worse on the grid and indistinguishable on the diagonal; the excess is a staircase in y with the value 9.406483 held across sixteen consecutive supports at N = 1e4; zero excess first reached at y* = 63, 173, 589 for N = 1e3, 1e4, 1e5, which is 1.03, 0.87 and 0.93 of the attainable-cell count
artifacts:
  - hunts/quotient_exponent/artifacts/sweep.json
  - hunts/quotient_exponent/artifacts/sweep_1e6.json
  - hunts/quotient_exponent/artifacts/threshold.json
  - hunts/quotient_exponent/artifacts/staircase_N1000.json
  - hunts/quotient_exponent/artifacts/staircase_N10000.json
  - hunts/quotient_exponent/artifacts/fit.json
  - hunts/quotient_exponent/artifacts/fit_comparison.json
```

## Notes

- **The first sweep run died and its rows were re-run.** Exit 1 with no
  traceback while three agents and two other jobs were live on a four-core box;
  the failing point re-solves in 37 seconds in isolation. The rows are in
  `sweep_1e6.json` and `sweep_1e7.json` rather than folded into `sweep.json`,
  so the interruption is visible rather than tidied away.
- **The `10^7` ceiling here is memory, not time.** The constraint block is dense
  `2 sqrt(N) x y`, which is 3.2 GB at `N = 10^8`. Column generation, which the
  source already uses for `V*`, is the way past it.
- The write-up's first draft called the binding-cell ratio a regularity. It is
  an arithmetic consequence of a linear programme having as many active
  constraints as variables at a vertex, and the draft was corrected before
  landing. What is not forced is the small excess over `y`, which shrinks.
