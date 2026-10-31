# RUNS: ccm_arithmetic (hunt #150, mechanism 1)

The 2026-10-21 runs were single-process Python on the campaign box (`<box>`), at most four
processes of the session alive at once. They were written up on 2026-10-26, so their
times are reconstructed: each `finished` is the modification time (UTC, to the minute) of
the run's last-written file in `data/`, and each `started` is that time minus the summed
per-cell `elapsed_s` the run recorded, so a `started` is approximate. Commands are run
from the repository root with `.venv/bin/python`; stdout went to the `data/log_*.txt` file
named in each block.

**Provenance caveat.** `measure.py` was last modified at 22:35Z, after the inferred starts
of the zeta, DH, Dedekind and W_{1/4} runs. On 2026-10-26 three cells were recomputed with
the current code, one per run that could have been affected (last block below), and every
recorded field came back identical. Cells not recomputed are covered by that check only to
the extent that the edit was not cell-specific.

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-21-measure-wa
hunt: rh_moonshot
started: 2026-10-21T22:30Z
finished: 2026-10-21T22:31Z
ran:
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/measure.py wa > hunts/rh_moonshot/ccm_arithmetic/data/log_measure_wa.txt
outcome: 18 cells (c in 2..31, N in 32, 64), 45 s summed; lambda_1 positive at c = 2 and negative from c = 3, and the ground state leaves the radical subspace from c = 3
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/data/measure_wa.json
  - hunts/rh_moonshot/ccm_arithmetic/data/xi_cache_wa.json
  - hunts/rh_moonshot/ccm_arithmetic/data/log_measure_wa.txt
```

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-21-measure-dedekind
hunt: rh_moonshot
started: 2026-10-21T22:30Z
finished: 2026-10-21T22:35Z
ran:
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/measure.py dedekind > hunts/rh_moonshot/ccm_arithmetic/data/log_measure_dedekind.txt
outcome: 26 cells (c in 13..60, N in 64, 128), 312 s summed; lambda_1 positive on every cell (3.4e-9 at c = 60) and radical misfit at most 0.040
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/data/measure_dedekind.json
  - hunts/rh_moonshot/ccm_arithmetic/data/xi_cache_dedekind.json
  - hunts/rh_moonshot/ccm_arithmetic/data/log_measure_dedekind.txt
```

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-21-measure-zeta
hunt: rh_moonshot
started: 2026-10-21T22:27Z
finished: 2026-10-21T22:54Z
ran:
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/measure.py zeta > hunts/rh_moonshot/ccm_arithmetic/data/log_measure_zeta.txt
outcome: 30 cells (c in 6..60, N in 32, 64, 128), 1603 s summed, 700 to 1600 bits; lambda_1 positive with lambda_2 / lambda_1 at least 1.6e6, Sturm counts 0, 1, 2, dist^2 to R_4 at most 8.3e-11, and every zero below 100 matched to 7.8e-16 on the cells with N >= 64 and c >= 13; the m = 2 capture bound exceeds 2.8e4 on every cell
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/data/measure_zeta.json
  - hunts/rh_moonshot/ccm_arithmetic/data/xi_cache_zeta.json
  - hunts/rh_moonshot/ccm_arithmetic/data/zeta_zeros_T200.json
  - hunts/rh_moonshot/ccm_arithmetic/data/log_measure_zeta.txt
```

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-21-measure-dh
hunt: rh_moonshot
started: 2026-10-21T22:27Z
finished: 2026-10-21T23:14Z
ran:
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/measure.py dh > hunts/rh_moonshot/ccm_arithmetic/data/log_measure_dh.txt
outcome: 42 cells (c in 6..60, N in 32, 64, 128), 2804 s summed; lambda_1 negative from c = 31 at N = 64 and 128, capture kept at c = 31 and lost by c = 33, and F_v1 carries a real zero near 85.73 inside the on-line gap around the off-line pair
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/data/measure_dh.json
  - hunts/rh_moonshot/ccm_arithmetic/data/xi_cache_dh.json
  - hunts/rh_moonshot/ccm_arithmetic/data/log_measure_dh.txt
```

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-21-measure-epstein
hunt: rh_moonshot
started: 2026-10-21T22:37Z
finished: 2026-10-21T23:13Z
ran:
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/measure.py epstein > hunts/rh_moonshot/ccm_arithmetic/data/log_measure_epstein.txt
outcome: 11 cells (c in 13..50, N = 64), 2145 s summed (1038 s of it the first cell, filling the Xi cache); lambda_1 negative from c = 59/2 and the radical misfit jumps from 0.09 to 0.986 there
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/data/measure_epstein.json
  - hunts/rh_moonshot/ccm_arithmetic/data/xi_cache_epstein.json
  - hunts/rh_moonshot/ccm_arithmetic/data/log_measure_epstein.txt
```

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-21-rigidity
hunt: rh_moonshot
started: 2026-10-21T22:40Z
finished: 2026-10-21T22:45Z
ran:
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/rigidity.py 13 32 2
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/rigidity.py 31 64 2 > hunts/rh_moonshot/ccm_arithmetic/data/log_rigidity_31_64.txt
outcome: 73 s and 188 s at 700 bits; moving the atom at log 2 loses positivity at eps about 4.2e-49 (c = 13) and 1.5e-103 (c = 31) while capture survives to the gap scale 6.6e-45 and 8.6e-99; LDL^T inertia conclusive at c = 13, mostly inconclusive at c = 31
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/data/rigidity_13_32_2.json
  - hunts/rh_moonshot/ccm_arithmetic/data/rigidity_31_64_2.json
  - hunts/rh_moonshot/ccm_arithmetic/data/log_rigidity_31_64.txt
```

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-21-wa
hunt: rh_moonshot
started: 2026-10-21T22:43Z
finished: 2026-10-21T22:46Z
ran:
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/wa_threshold.py
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/wa_dial.py > hunts/rh_moonshot/ccm_arithmetic/data/log_wa_dial.txt
outcome: 22 s and 45 s; W_{1/4} is negative at c = 19581/8192 (N = 32) and 4893/2048 (N = 64) with conclusive pivots on every bisection step, and the first negative window grows from about 2.39 to 3.01 as a falls from 1/4 to 1/64, with the a = 0 form equal to 2 Q_zeta to 3.9e-180
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/data/wa_threshold.json
  - hunts/rh_moonshot/ccm_arithmetic/data/wa_dial.json
  - hunts/rh_moonshot/ccm_arithmetic/data/log_wa_dial.txt
```

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-26-reproduce
hunt: rh_moonshot
started: 2026-10-26T12:55Z
finished: 2026-10-26T12:57Z
ran:
  - nice -n 10 .venv/bin/python <scratch>/repro_ccm.py (measure.measure_cell for (wa, 3, 32), (dedekind, 19, 64), (zeta, 13, 32) with an in-memory Xi cache, compared field by field with data/)
outcome: 5 s, 31 s and 17 s; lambda_1, misfit, R_m distances, a2 fit, compact errors, Sturm counts and capture quantities identical to the recorded cells
artifacts:
```

## The capture bound at m = 4

Asked for: kappa, mu, eta and the bound eta / (mu - lambda_1) on dist(v_1, R_4) at
(c, N) = (43, 128), (50, 128), (60, 128), zeta, at 1600 bits. Estimate written before any
run, from the recorded full-cell times (which include a matrix build, two 129 x 129
eigendecompositions at 1600 bits, the zero scans and the m = 2 capture): 183 s, 118 s and
105 s, so a capture-only rerun at m = 4 is bounded by about 410 s on one core, about
0.11 core-hour (memory not measured). The task brief estimated it near one
core-hour; this record's estimate is lower, and the run waits for the coordinator either
way. Prediction, pre-registered: still vacuous (bound above 1), because the second and
third eigenvectors are also radical times a polynomial.

The coordinator approved the run on 2026-10-26 (one process, `nice 10`). It took 145 s,
inside the estimate. **The prediction held**: the bound is 5.9e96, 1.1e108 and 5.4e120 at
c = 43, 50, 60. Against m = 2 at the same cells, mu rose by about 13 orders of magnitude
on each cell (3.0e-145 to 4.1e-132 at c = 43; 9.2e-157 to 1.4e-143 at c = 50; 1.2e-169 to
1.7e-156 at c = 60), but the leakage eta stays
about 1e-35, far above mu. dist^2(v_1, R_4) came back equal to `measure.py`'s recorded
value on all three cells.

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-26-capture-m4
hunt: rh_moonshot
started: 2026-10-26T13:14Z
finished: 2026-10-26T13:17Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/capture_m4.py > hunts/rh_moonshot/ccm_arithmetic/data/log_capture_m4.txt
outcome: 48 s, 51 s and 47 s at 1600 bits, 1-minute load about 34; the m = 4 perturbation bound is 5.9e96, 1.1e108 and 5.4e120 against actual distances 1.1e-13, 8.2e-14 and 1.6e-12, vacuous as predicted
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/capture_m4.py
  - hunts/rh_moonshot/ccm_arithmetic/data/capture_m4.json
  - hunts/rh_moonshot/ccm_arithmetic/data/log_capture_m4.txt
```
