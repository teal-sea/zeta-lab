# RUNS: compute spent on this hunt

The original stages ran on the authoring host on 2026-08-07; their wall-clock
times are the `seconds` fields of `results.json`. This file starts with the
2026-10-19 correction (NOTES.md, "Correction").

## 2026-10-19: re-run with the relative cutoff (with hunts/jensen_clock)

**Unit, timed on this host before spending.** One `DHFlow.H_and_dH`
evaluation: 0.035 s at dps 54 (pair 1, 1300 nodes) and 0.67 s at dps 165
(pair 9, 12096 nodes). A contour evaluation is 96 of them (3.4 s and 64 s);
a landing time takes 8 to 12 contour evaluations, plus polishing the zero.

**Multiply.** The recorded stage times sum to 118 minutes on the authoring
host: survey 78.2 (pair 9 alone 18.8), precision 6.9, pair1 4.3, lesions 1.9,
validate 0.02, and the three jensen_clock stages 26.9 (additivity 9.5, shift
13.1, additivity2 4.3). On a GitHub runner at about half that speed, the
longest chain (pair1 and precision, then jensen_clock shift + additivity2) is
about 50 minutes wall, over 13 parallel jobs.

**Where it ran.** `.github/workflows/dh-floor-rerun.yml`, on push to the
correction branch. mpmath pinned to 1.3.0 (the authoring host's), Python 3.12.
Not run: `ode` and `figure`, which evaluate no DH weight and read only the
polished zeros and the PDE t\* values.

**Outcome.** Run 39355357518 (commit 36d6b19f), all 15 jobs green,
25 minutes wall (01:47 to 02:12 UTC, 2026-10-20). The runner ran at about
the authoring host's speed (pair1 245 s against 256 s recorded), so the
estimate's factor of two was pessimistic. Its validate output equals this
host's re-run bit for bit. Comparison: flow_repair 12 stages, 370 fields,
364 identical, 6 changed (validate's evenness defect, NOTES.md
"Correction"); jensen_clock 4 stage blocks, 71 fields, all identical.
Reports: `rerun_2026-10-19.json` here and in `hunts/jensen_clock/`.
