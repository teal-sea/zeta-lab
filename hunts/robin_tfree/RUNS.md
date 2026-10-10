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
- Session 1's "30 tests" is the count at that run. Commit `6e7a714` added a 31st (the
  far-range deficit envelope) and the 2026-10-10 session six more (37).

```runmanifest
id: robin_tfree-2026-10-10-session2
hunt: robin_tfree
started: 2026-10-10T01:10Z
finished: 2026-10-10T01:35Z
ran:
  - .venv/bin/python -m pytest -n0 -q hunts/robin_tfree
  - mechanical comparison of bound.py's Table 1, Table 8 and Table 9 values with text extracted from arXiv:1511.02032v2 and arXiv:2002.11068v2
  - literature search on web, arXiv API, zbMATH Open API and Semantic Scholar citations
outcome: all transcribed table values agree with the arXiv versions; the search found 21-free as the best published t-free result; 37 tests pass, six of them new pins of every derived number RESULTS.md states
artifacts:
  - hunts/robin_tfree/test_bound.py
  - hunts/robin_tfree/RESULTS.md
```

## Notes, session 2 (2026-10-10)

- Morrill-Platt's *Integers* version numbers the verified range as Theorem 5 and
  Corollary 2; Theorem 13 and Corollary 14 are arXiv v4's numbering. The printed
  `10^(10^13.11485)` is below `x0#`, so the top of the range is the corollary; the
  comment in `bound.py` that said otherwise was corrected (comments only; `results.json`
  is unchanged).
- The hunt's own bound is now "Claim 1", not "Theorem 1": the lab says theorem only for
  kernel-checked or published results.
- `|d| <= 1.955/sqrt(x0)` in RESULTS.md section 5 was below the module's own envelope
  (`1.9564`); it now reads `1.957` and is pinned.
