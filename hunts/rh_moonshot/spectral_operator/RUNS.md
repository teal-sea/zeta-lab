# RUNS: spectral_operator (hunt #150, mechanism 5)

Single-process Python on the campaign box (`<box>`), commands from the repository root with
`.venv/bin/python`, at `nice 10`, at most four processes of this session alive at once
(two of them are this mechanism's). Times are UTC from the session clock.

## Estimate written before the cell runs (2026-10-26)

Timed unit: zeta at (c, N) = (13, 50), 38 s in all (assembly 0.4 s at 1356 bits, five
Arb LDL^T inertias 0.3 s, eigenvalues of the 101 x 101 operator by acb_mat.eig at 500
bits 6.9 s, secular zeros 8.3 s, the rest computing the first 100 zeta zeros at 45 digits
once). Scaling the eigensolver by n^3, the inertias by n^3 times the precision, and the
secular route by terms times precision times range: about 2 minutes for a cell at
N = 100 and about 10 minutes at N = 200. Cells: zeta (13, 100), (13, 200), (60, 100),
(60, 200) and DH (13, 100), (13, 200), (60, 100), (60, 200): about 50 minutes of one
core, run as two processes, under one core-hour, so it runs without asking.

Revision before the runs (2026-10-26T13:47Z): the first second route (sign changes of the
secular function with a step skipped whenever it contained a pole) missed one zero at DH
(13, 100), 47 against 48 eigenvalues. Both background runs were stopped, their partial
outputs deleted, and route 2 replaced by the real zeros of the transform F_xi (no poles in
the band). DH (13, 100) then took 70 s, with 48 against 48. The transform route is about
2.5 times slower than the secular one, so the (60, 200) cells were dropped. Revised
estimate: about 12 minutes per N = 200 cell and 1 to 2 minutes per N = 100 cell, so
zeta (13, 50), (13, 100), (60, 100), (13, 200) and DH (13, 100), (60, 100), (13, 200)
come to about 30 minutes of one core.

```runmanifest
id: rh_moonshot-spectral_operator-2026-10-26-units
hunt: rh_moonshot
started: 2026-10-26T13:38Z
finished: 2026-10-26T13:47Z
ran:
  - .venv/bin/python -c (spo_common at (13, 16) for zeta and DH: Lemma key (ii), spectrum by eig and by F_xi; the b-structure of T at (13, 8))
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/spectral_operator/spo_run.py zeta 13:50 (twice; the first run, with the zeros at 28 digits and the eigensolver at the assembly precision, was deleted)
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/spectral_operator/spo_run.py dh 13:100 (with the secular second route, 47 against 48; deleted)
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/spectral_operator/spo_run.py dh 13:100 (with the F_xi second route, 48 against 48, 70 s; kept)
outcome: W D' = D'^T W holds to 0 (zeta) and 1.7e-156 (DH) relative once xi is normalized at the working precision (at 15 digits zeta's tiny sum of components gave 4.1); T has the (b_i - b_j)/(i - j) structure to 1e-180; the timings of the estimate above
artifacts:
  - hunts/rh_moonshot/spectral_operator/data/cell_dh_13_100.json
```

```runmanifest
id: rh_moonshot-spectral_operator-2026-10-26-cells
hunt: rh_moonshot
started: 2026-10-26T13:47Z
finished: 2026-10-26T14:10Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/spectral_operator/spo_run.py zeta 13:50 13:100 60:100 13:200 > hunts/rh_moonshot/spectral_operator/data/log_zeta.txt
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/spectral_operator/spo_run.py dh 13:100 60:100 13:200 > hunts/rh_moonshot/spectral_operator/data/log_dh.txt
outcome: 37 s, 172 s, 212 s and 890 s (zeta) and 93 s and 464 s (DH) against the estimate of 1 to 2 minutes at N = 100 and 12 minutes at N = 200; every cell even-simple by conclusive Arb LDL^T, the spectrum real, the two routes equal in number and within 2e-26, except zeta (60, 100), where the F_xi route's last step passed the cutoff and found one zero more (rerun below)
artifacts:
  - hunts/rh_moonshot/spectral_operator/data/cell_zeta_13_50.json
  - hunts/rh_moonshot/spectral_operator/data/cell_zeta_13_100.json
  - hunts/rh_moonshot/spectral_operator/data/cell_zeta_13_200.json
  - hunts/rh_moonshot/spectral_operator/data/cell_dh_60_100.json
  - hunts/rh_moonshot/spectral_operator/data/cell_dh_13_200.json
  - hunts/rh_moonshot/spectral_operator/data/zeta_zeros_100.json
  - hunts/rh_moonshot/spectral_operator/data/log_zeta.txt
  - hunts/rh_moonshot/spectral_operator/data/log_dh.txt
```

```runmanifest
id: rh_moonshot-spectral_operator-2026-10-26-rerun-60-100
hunt: rh_moonshot
started: 2026-10-26T14:11Z
finished: 2026-10-26T14:18Z
ran:
  - nice -n 10 .venv/bin/python -c (zeta (60, 100): the eigenvalues near 138 at 500 and 1000 bits)
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/spectral_operator/spo_run.py zeta 60:100 > hunts/rh_moonshot/spectral_operator/data/log_zeta_60_100_rerun.txt (after filtering the F_xi zeros to the cutoff)
outcome: the eigenvalue 138.116042055 is present at both precisions, just above the cutoff 0.9 omega_N = 138.114; the rerun gives 46 against 46 within 2.0e-26 and all 46 zeros below 138 matched to within 4.6e-40, 180 s
artifacts:
  - hunts/rh_moonshot/spectral_operator/data/cell_zeta_60_100.json
  - hunts/rh_moonshot/spectral_operator/data/log_zeta_60_100_rerun.txt
```
