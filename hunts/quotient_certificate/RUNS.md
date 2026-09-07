# Runs

Input baseline: main d393e1a, GitHub Actions tests run 34088036566 and checks
run 34088036541 both passed. Use the installed repository environment with
one BLAS thread and small local cases. Large optimizations belong in CI.

Initial estimate: at N=1000,y=31 the quotient matrix has at most 62 by 31
entries (under 16 KB of float data), smaller than the already tested dense
1000 by 31 LP. Measure this unit before scaling. The next N=10000,y=100
matrix has at most 200 by 100 entries (under 160 KB); stop local scaling if
a unit exceeds 30 seconds. No detached jobs.

## Exploratory measurements

The first relaxation retained d=1 as well: excesses 41.28804467,
227.00655874 and 1074.61790502 at N=1000,10000,100000 with square-root
support. LP solve times were 0.016, 0.052 and 1.42 seconds. The
N=1000000,y=1000 case reached the explicit 30-second solver limit
(30.60 seconds including setup), status 1. No value is reported for it,
and no local increase of the limit was attempted.

The final Q_N omits d=1, whose Lambda value is identically zero. The three
completed runs include rational repair and independent evaluations:

| N | y | exact cells checked | wall seconds | coefficient denominator | c_1 numerator repair |
|---:|---:|---:|---:|---:|---:|
| 1000 | 31 | 61 | 0.051 | 10^12 | 0 |
| 10000 | 100 | 198 | 0.148 | 10^12 | 0 |
| 100000 | 316 | 630 | 2.731 | 10^12 | 1 |

No solved case is silently discarded. The final result file has status
complete and completed=3 of requested=3.

## Verification

The starting focused suite passed 40 tests, including the previous LP
regressions and hunt/document discipline. Arb and mpmath.iv are both
available. The initial new-test run passed eight tests and failed one
because its test-only product indexed a zero-prime-weight cell absent from
the factorization dictionary. Iterating over the explicitly computed
prime-bearing cells repairs the test; the row relation and witness had
already passed in that run.

The exact counterexample, all 889 retained constraints, 400 covariance
pairs, and four balanced coefficient families are tested in
tests/test_quotient_certificate.py. Independent review and final CI
results are reported with the pull request.

Independent verification passed all ten focused tests and independently
recomputed each candidate using SymPy prime enumeration and 80-digit
logarithms. All 889 constraints pass; the largest independent
factorial/prime identity defect is below 2.8e-75. Separate source review
confirmed the NB hypotheses and prompted an explicit Mellin convention
in the write-up.

```runmanifest
id: quotient-certificate-2026-09-07
hunt: quotient_certificate
started: 2026-09-07T15:54:36.435781+00:00
finished: 2026-09-07T15:54:39.368869+00:00
ran:
  - OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv/bin/python hunts/quotient_certificate/probe.py --N 1000 10000 100000 --output hunts/quotient_certificate/results.json
  - .venv/bin/python -m pytest -q -n 2 tests/test_quotient_certificate.py
outcome: Three finite ceilings improved, all 889 retained cells passed exact arithmetic, and an exact counterexample refuted the dimension-count claim; no asymptotic bound established
artifacts:
  - hunts/quotient_certificate/results.json
  - hunts/quotient_certificate/RESULTS.md
```
