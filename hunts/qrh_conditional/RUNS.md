# Runs

## 2026-10-08, probe.py, exponents, crossovers and the Li illustration

**Estimate written before the run.** Section A is exact rational arithmetic
(microseconds). Section B scans two functions of one variable on a grid of
pitch 1/4 over [log 2, 5000], 20,000 evaluations each, at dps 30, for four
convention constants and two strips: 16 scans, priced at about one second
each from mpmath's per-evaluation cost. Section C is a dozen evaluations.
Priced at under a minute in all, no memory to speak of, nothing to checkpoint.

**Measured.** 17.9 s wall, user 17.6 s, on the cloud container (no
operator machine was used). Section B is all of it.

```runmanifest
id: qrh_conditional-2026-10-08-probe
hunt: qrh_conditional
started: 2026-10-08T02:58Z
finished: 2026-10-08T02:59Z
ran:
  - /home/user/zeta-lab/.venv/bin/python hunts/qrh_conditional/probe.py
outcome: Under QRH(7/8) the q = 1 component of UPPER_BOUND.md (1) moves from N^3 L^{-2H} to N^{11/4} L^4 and stays 3/4 of a power short of (31); the completed bound moves to N^{35/12} L^6 by widening the arcs to N^{1/12}; Theorem A becomes N^{7/4} L^4; the strip-shaped bound overtakes Johnston and Yang's explicit remainder at log x = 35.11 (theta = 7/8) and 98.22 (theta = 11/12) with the strip-side constant set to 1; a strip multiplies the per-zero Li growth exponent by 2 theta - 1 and nothing else.
artifacts:
  - hunts/qrh_conditional/results.json
```

## 2026-10-08, the gate command and the context check

**Estimate written before the run.** The hunt's own tests take about four
seconds (two root searches); the doors tests run the learn and refute door
scripts, which `tests/test_doors.py` prices at minutes. Under three minutes
in all.

**Measured.** 111.6 s wall for the pytest command, under a second for the
context check, on the cloud container. One of the hunt's own pins failed on
the first pass and was corrected: the log-ratio at gamma_1 is 0.7504, not
within 2e-4 of 3/4, because of the second-order term of log(1 + x); the
tolerance and the table digit were wrong, the arithmetic was not. A second
pin compared a value stored to 12 digits against 1e-20 and was loosened to
1e-9. Both corrections are recorded here rather than overwritten.

```runmanifest
id: qrh_conditional-2026-10-08-gate
hunt: qrh_conditional
started: 2026-10-08T03:10Z
finished: 2026-10-08T03:16Z
ran:
  - /home/user/zeta-lab/.venv/bin/python -m pytest -q -n0 hunts/qrh_conditional tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py tests/test_hunt_doors.py tests/test_huntspec.py tests/test_hunt_numbering.py
  - /home/user/zeta-lab/.venv/bin/python scripts/make_context.py --check
outcome: 72 passed, 3 xfailed (the three doors sections tests/test_hunt_doors.py already lists as known incomplete, none of them this hunt's), CONTEXT.md up to date; two of this hunt's own pins were corrected on the first pass as recorded above.
artifacts:
