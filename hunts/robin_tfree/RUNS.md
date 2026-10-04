# RUNS: robin_tfree

Estimate before spending: the whole computation is a few hundred Arb operations
(under 1 s); the test file sieves to `3 * 10^6` and sums logarithms at 30-40 digits
(about 35 s on the M4). Nothing here needs CI or paid compute.

```runmanifest
id: robin_tfree-2026-10-04-session1
hunt: robin_tfree
started: 2026-10-03T23:30-05:00
finished: 2026-10-04T05:30-05:00
ran:
  - .venv/bin/python hunts/robin_tfree/bound.py
  - .venv/bin/python -m pytest -n0 -q hunts/robin_tfree/test_bound.py
outcome: both routes bound E at most 2.481e-8 past the verified range, deciding t = 25 and refusing t = 26; 30 tests pass
artifacts:
  - hunts/robin_tfree/results.json
```

## Notes

- First test pass: 7 failures, all from one bug in the test helper (it subtracted
  `log theta(x)` where `log log theta(x)` was meant) and from a robustness pin set at
  the wrong threshold (`+0.2` on Table 1 keeps `t = 25`; the measured threshold is
  between `+0.55` and `+0.6`). The module was unchanged by the fix.
- Rendering of Buthe 2018 page 14 compared with the transcribed Table 1 before use.
