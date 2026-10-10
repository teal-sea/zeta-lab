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

```runmanifest
id: quotient_exponent-2026-09-10-closed-form
hunt: quotient_exponent
started: 2026-09-10T04:20-05:00
finished: 2026-09-10T04:32-05:00
ran:
  - .venv/bin/python hunts/quotient_exponent/closed_form.py
outcome: the plateau values are exact rational multiples of a single log p, (7/2)log 2 at N=1e3, 3 log 23 at 1e4, 6 log 113 at 1e5, agreeing to 1e-14..1e-18; the mechanism is that exactly one cell carrying excess has nonzero weight, out of 14 to 181 that carry excess; at N=1e6 y=1995 the excess is 0.0 with 497 cells still carrying excess, all weightless, so the LP zeroes the weighted violation rather than the violation; grade measured, one float route
artifacts:
  - hunts/quotient_exponent/closed_form.py
  - hunts/quotient_exponent/artifacts/closed_form.json
```

*(Moved on landing, 2026-10-10: the block above carried one more line, which
`tests/test_huntspec.py` rejects as an unknown manifest key. It read, verbatim:
`estimate: 62 LP solves; ~0.03 s each at N=1e3, ~0.08 s at 1e4, ~1.2 s at 1e5, ~40 s for the single 1e6 point; ~11 min total`.
The re-run took 67 s for `closed_form.py` on a shared container.)*

- **The N = 10^6 plateau was not located and is not claimed.** `sweep.py` has
  `E > 0` at `y = 1000` and `E = 0` at `y = 1995`, so the plateau is somewhere
  between. Each solve at that size is about 40 s and the bracket is 995 wide, so
  a scan is roughly 11 hours. It was not run and no closed form is asserted at
  that size. An earlier draft of this hunt carried a value of `123.83310675500282`
  for `N = 10^6` with no run behind it in this tree; it is withdrawn rather than
  repeated, because nothing here reproduces it.
- The rationals are recovered from the solution and not fitted to the answer.
  `limit_denominator(64)` is applied to `e_q`, the excess in the one weighted
  cell, and only then is `(a/b) log p` formed and compared to `E`. Fitting a
  rational to `E` directly would have found *something* at every `N` and would
  have shown nothing.

```runmanifest
id: quotient_exponent-2026-10-10-landing
hunt: quotient_exponent
started: 2026-10-10T16:42+00:00
finished: 2026-10-10T17:27+00:00
ran:
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/lp.py --N 1000 10000 100000 --out lp_small.json
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/lp.py --N 1000000 3000000 10000000 --out lp_large.json
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/sweep.py --N 10000 100000 1000000 --alpha 0.30 0.35 0.40 0.45 0.50 0.55 0.60 0.65
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/sweep.py --N 1000000 --alpha 0.50 0.55 0.575 0.60 0.65 --out sweep_1e6.json
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/sweep.py --N 10000000 --alpha 0.40 0.45 0.50 --out sweep_1e7_partial.json
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/threshold.py --N 1000 10000 100000 1000000
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/staircase.py --N 1000
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/staircase.py --N 10000
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/closed_form.py
  - OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/quotient_exponent/free_support.py
  - .venv/bin/python -m pytest -q hunts/quotient_exponent
outcome: every artifact the ten commands write came back equal to the committed one to 1e-9 relative or better, most of them identical, including the 10^7 diagonal row (30297.73676825234) and the 3 x 10^6 identity defect of 1.6e-16 that RESULTS.md prints as 0; the factorial-form table of RESULTS.md section 2 re-solved to every printed digit; the 10^5 plateau runs 538 to 588 rather than the 545 to 580 that closed_form.py scanned; at 10^6, y = 1937 the excess is 123.83310675500282 with two weighted cells
artifacts:
  - hunts/quotient_exponent/test_quotient_exponent.py
  - hunts/quotient_exponent/RESULTS.md
  - docs/42-a-law-read-off-a-diagonal.md
```

Every command above was run on 2026-10-10 in a scratch copy of this directory,
in two parallel chains on a 4-vCPU container shared with other jobs, and the
outputs were compared field by field with the committed artifacts. Two scratch
scripts that are not part of the hunt did the checks the hunt had no script
for: the factorial-form LP at the four diagonal cutoffs (56.7 s at `10^6`) and
the plateau anatomy at every support of the three plateaus and at
`(10^6, 1937)`. Measured: about 20 minutes for `lp_large` (the `10^7` solve 989
s), 25 for the `10^7` sweep, 7 for the threshold bisections, a minute each for
the staircases, `closed_form.py` and the factorial forms, 11 s for
`free_support.py`.

- **Landed on main and renumbered #121 to #130, 2026-10-10.** On main #121 is
  `qrh_conditional`; #127 is `euler_defect_axis`, #128 `li_dh_onset` (#298)
  and #129 `epstein_height` (#299). The front door, numbered 39 on the branch,
  is `docs/42`; main uses 39 for the page on the quasi-Riemann theorem.
- **Not so: "no run behind it in this tree".** The note above withdraws the
  `N = 10^6` value `123.83310675500282` because "nothing here reproduces it".
  `artifacts/threshold.json` stores it as the last positive excess at
  `y = 1937`, and `artifacts/threshold.log` shows the bisection hitting
  `1.238331e+02` at `y = 1812, 1921, 1934, 1937`; the landing re-run reproduces
  it. The value was in the tree all along. Whether the `10^6` plateau has a
  closed form is a separate question, and at `y = 1937` it does not have a
  single-carrier one (two weighted cells; `RESULTS.md` section 6b).
- **Not reproduced as stated.** The reformulation manifest says the identities
  "hold to 8.3e-16 relative at every cutoff": that is the `10^6` value; at
  `3 x 10^6` and `10^7` the factorial telescope's defect is `2.3e-15` and
  `2.4e-15`. The note "3.2 GB at `N = 10^8`" is twice what its own formula gives
  (`2 sqrt(N) x y` float64 is 1.6 GB; `lp.py`'s CSR copy doubles it), which
  `RESULTS.md` door 2 already says correctly. The surface manifest's "free fit
  a = 1.150, b = 0.878" and "falls by 2.3 to 2.8" were measured on the rows that
  existed at the time; on the artifacts now in the tree they are `1.159, 0.874`
  and 2.1 to 2.8.
- **Names and manifests.** The note above calls the `10^7` rows
  `sweep_1e7.json`; the file is `sweep_1e7_partial.json`. `free_support.json`,
  `lp_check.json` and `lp_N1000.json` have no manifest; the last two are single
  rows identical to `lp_small.json`'s, and `free_support.py` is re-run in the
  landing manifest above. `closed_form.py` sets `mp.dps = 40` at import, a
  global precision change the repository's rule forbids; it changes nothing
  here, and the test restores the precision after every case.
