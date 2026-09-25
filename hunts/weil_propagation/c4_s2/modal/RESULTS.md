# RESULTS: modal/, the compute follow-up (2026-09-24)

## Follow-up 2 (2026-09-24, 14:08 to 14:49 -0500): every checker/ unit under the QR rho

1. **What ran: all eleven checker/ units, all with status ok, on Modal, from a clean clone of the tree at e2b46a5 whose T_S input digest is b2e7787bce7a, the same as the local call.** The seven of `run_checker_ts.UNITS` ((80, 1200, 8) with dps 40 and 60, (120, 1600, 16), (200, 2400, 32), (80, 1600, 16), (120, 1200, 16), (80, 1200, 16), (160, 1600, 16)) and the four N = 32 units of the first follow-up ((240, 2400), (280, 2266.10), (319, 2633.16), (364, 3060.08)), one Modal call each, all three cells per call. **None timed out**; the longest, 364 modes, took 2120 s against its 10800 s limit.
2. **Calibration passed: max abs difference 7.1e-15 against the 1e-10 threshold** fixed by the brief, (80, 1200, 8) on Modal against the same unit built on the laptop with the same code, all six row keys. It holds for the N = 8 unit (cond_F about 17); no platform floor was measured for the N = 16 and N = 32 units.
3. **Cost: 0.568 USD billed** (`modal billing report`, read 14:49 -0500, the four `c4s2-modal-rho` apps), against 0.527 USD computed and a worst case of 5.01 USD written and committed before launch (82bb613, 14:12:49; batch launched 14:13:10). With the first follow-up, 1.309 USD of the 25 USD cap is spent.
4. **Where: one file per unit in `modal/out_rho/<unit>.json`** in `checker_ts_snapshot.json`'s shape (`meta`, `T_S` {unit_key: rows}, `units` {nv|S|N: role, seconds, kmax, diag, S_exact}), plus the local half of the calibration, `out_rho/local_checker_80_1200_8.json`. The Volume `c4s2-modal-rho-out` holds the same eleven results.
5. **The numbers are produced and not yet graded, and no eigenvalue of T_S or R_S was computed here.** checker/ commits its criterion reading first and grades the rows in its own folder. Batch 2 (the default-rule rows at S/nvec^2 = 0.04) was not run; it waits for the coordinator.

| file | unit key | status | Kmax | limit (s) | child wall (s) | container wall (s) | CPU (s) | peak (MiB) | cond_Fz | cond_Fb | BLAS |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `out_rho/checker_80_1200_8.json` (calibration) | 80\|1200\|8 | ok | 10 | 1200 | 34.2 | 39.3 | 100.1 | 472 | 1.65e+01 | 1.67e+01 | SkylakeX |
| `out_rho/checker_120_1600_16.json` | 120\|1600\|16 | ok | 12 | 1200 | 123.2 | 127.5 | 283.4 | 852 | 5.10e+02 | 5.17e+02 | Haswell |
| `out_rho/checker_200_2400_32.json` | 200\|2400\|32 | ok | 13 | 2400 | 428.4 | 432.7 | 983.6 | 1581 | 8.71e+05 | 6.23e+04 | Haswell |
| `out_rho/checker_80_1600_16.json` | 80\|1600\|16 | ok | 10 | 1200 | 56.7 | 63.9 | 144.2 | 530 | 5.38e+00 | 5.45e+00 | Haswell |
| `out_rho/checker_120_1200_16.json` | 120\|1200\|16 | ok | 12 | 1200 | 99.4 | 104.5 | 234.5 | 782 | 8.98e+03 | 4.88e+03 | Haswell |
| `out_rho/checker_80_1200_16.json` | 80\|1200\|16 | ok | 10 | 1200 | 39.7 | 43.3 | 97.6 | 475 | 1.65e+01 | 1.67e+01 | Haswell |
| `out_rho/checker_160_1600_16.json` | 160\|1600\|16 | ok | 12 | 1200 | 147.8 | 154.8 | 345.1 | 936 | 4.42e+05 | 2.95e+04 | Haswell |
| `out_rho/checker_240_2400_32.json` | 240\|2400\|32 | ok | 14 | 3600 | 754.1 | 759.1 | 1627.7 | 2425 | 1.14e+09 | 2.21e+06 | Haswell |
| `out_rho/checker_280_2266_32.json` | 280\|2266\|32 | ok | 14 | 3600 | 752.6 | 756.1 | 1454.1 | 2562 | 1.90e+13 | 4.14e+08 | Haswell |
| `out_rho/checker_319_2633_32.json` | 319\|2633\|32 | ok | 14 | 5400 | 1378.3 | 1382.0 | 2354.9 | 2813 | 2.09e+13 | 4.37e+09 | Haswell |
| `out_rho/checker_364_3060_32.json` | 364\|3060\|32 | ok | 15 | 10800 | 2120.3 | 2124.0 | 4234.2 | 5150 | 2.06e+13 | 7.66e+10 | Haswell |

cond_Fz and cond_Fb are copied from each unit's `diag` (build_unit's own
diagnostics), not computed here; two_adic/ s10.4 and its INTERFACE state how
they are read. Container wall is the Modal function; child wall is the unit's
own process.

- **Guard, every unit:** HEAD e2b46a5, whole-tree `git status --porcelain
  --untracked-files=all` empty, `checker_glue.ts_key()` =
  (`b2e7787b...0eaa`, []) before and after the build, in `meta.guard_before`
  and `meta.guard_after`; `loaded_inputs_outside_key()` empty in the child.
- **The route is checker/'s own code, called as a library:**
  `run_checker_ts.build_unit(nvec, S, N, dps_list)` with dps (40, 60) at
  N = 8 and (40,) otherwise, as `snapshot()` builds them; the default-rule S
  are passed as the same floats as in the first follow-up (`units.*.S_exact`).
- **A new app and a new Volume** (`c4s2-modal-rho`, `c4s2-modal-rho-out`):
  the old Volume holds results and start markers under five of the same unit
  names. `modal/out/` and `test_modal_outputs.py` are untouched and still
  pass; they are the record of the old route (digest 1dcab230).
- **Nothing of this folder's is running on Modal.** `modal app list` at
  14:49 -0500: the four `c4s2-modal-rho` apps stopped with 0 tasks;
  `claude-scie...` and `specimen-v1...` deployed and untouched. Nothing
  pushed.
- **Tests:** `modal/test_modal_outputs_rho.py` pins each file's tree, digest,
  guard, shape (six row keys at N = 8, three otherwise; `diag` carries
  cond_Fz and cond_Fb), the calibration against the local build at 1e-10 and
  its record in every file, the eleven units against `run_checker_ts.UNITS`
  and `two_adic/ta_ts.py`'s rule at e2b46a5, and that no output carries an
  eigenvalue-shaped key. It pins no mathematical conclusion.
- **Grade:** operational record only. The rows are checker/'s float64 route
  run elsewhere: measured grade at most, and ungraded until checker/ reads
  them. Details: `RUNS.md` s7.

## The first follow-up (tree 284eff6, digest 1dcab230, the inverse route)

1. **What ran: all 12 units, all with status ok, on Modal, from the tree at 284eff6 with the local T_S input digest.** 2 calibration units, 1 sensitivity probe, 4 checker/ units at N = 32 ((240, 2400), and the default rule's (280, 2266.10), (319, 2633.16), (364, 3060.08)), and 5 two_adic/ Gram probe units ((140, 4800), (160, 4800), (180, 4800), (200, 4800), (160, 9600)). **None timed out**; the longest, 364 modes, took 1784 s against its 14400 s limit.
2. **Cost: 0.741 USD billed** (Modal's billing report, read 2026-09-24 11:12 -0500, all six apps of this folder), against 0.709 USD computed from the unit log and a worst case of 6.73 USD written before launch. The cap was 25 USD.
3. **Where: one file per unit in `modal/out/<unit>.json`** (table below); the Volume `c4s2-modal-out` holds the same files. checker/ units are in `checker_ts_snapshot.json`'s shape (`meta`, `T_S` {unit_key: rows}, `units`), two_adic/ units in `ta_gram_probe.json`'s shape (`c`, `N`, `Q_low`, `runs` {"nvec,S": run}) plus `meta`.
4. **The checker calibration missed the brief's 1e-10 by 2.3e-7, and the threshold was changed to 1e-6 after the measurement** (coordinator's option B). A probe that changed only OpenBLAS's kernels moved the same unit by up to 3.3e-7, Modal against Modal, so that unit reproduces only to about 3e-7 under last-digit arithmetic changes. The two_adic calibration met 1e-10 (8.2e-15). Every checker output carries both bounds in `meta.calibration` (Weyl bound 2.93e-7, arithmetic floor 3.39e-7). Details: `RUNS.md` s3.1, s4.1, s4.3.
5. **The numbers are produced and not yet graded.** checker/ re-grades the R_S counts from the new N = 32 rows and two_adic/ grades its accuracy run, each in its own folder. This folder states no mathematical result; nothing here is a claim about R_S, T_S or RH.

## The units

Status, times and cost per unit (container wall is the Modal function; child
wall is the unit's own process; cost is computed at the reserved rate, not
billed per unit). The BLAS column is the OpenBLAS kernel family the child
loaded: Modal placed units on different hosts.

| file | unit key | status | Kmax | limit (s) | child wall (s) | container wall (s) | CPU (s) | peak (MiB) | computed USD | BLAS |
|---|---|---|---|---|---|---|---|---|---|---|
| `out/checker_200_2400_32.json` (calibration) | 200\|2400\|32 | ok | 13 | 1800 | 432.3 | 438.7 | 976.4 | 1580 | 0.0386 | not recorded |
| `out/gram_80_4800.json` (calibration) | 80,4800 | ok | 10 | 1200 | 180.6 | 184.5 | 426.3 | 847 | 0.0162 | not recorded |
| `out/checker_200_2400_32_sandybridge.json` (probe) | 200\|2400\|32 | ok | 13 | 1800 | 394.5 | 397.3 | 1017.9 | 1578 | 0.0349 | Sandybridge |
| `out/gram_140_4800.json` | 140,4800 | ok | 12 | 2400 | 275.4 | 278.0 | 643.6 | 1281 | 0.0244 | SkylakeX |
| `out/gram_160_4800.json` | 160,4800 | ok | 12 | 2400 | 299.7 | 303.3 | 636.8 | 1336 | 0.0267 | Haswell |
| `out/gram_180_4800.json` | 180,4800 | ok | 13 | 3600 | 472.9 | 475.9 | 980.4 | 1772 | 0.0418 | Haswell |
| `out/gram_200_4800.json` | 200,4800 | ok | 13 | 3600 | 624.7 | 627.9 | 1253.7 | 1822 | 0.0552 | SkylakeX |
| `out/gram_160_9600.json` | 160,9600 | ok | 12 | 7200 | 794.6 | 797.2 | 1858.2 | 2064 | 0.0701 | SkylakeX |
| `out/checker_240_2400_32.json` | 240\|2400\|32 | ok | 14 | 3600 | 887.3 | 890.4 | 1665.3 | 2422 | 0.0783 | SkylakeX |
| `out/checker_280_2266_32.json` | 280\|2266\|32 | ok | 14 | 3600 | 843.9 | 846.6 | 1551.8 | 2559 | 0.0744 | SkylakeX |
| `out/checker_319_2633_32.json` | 319\|2633\|32 | ok | 14 | 5400 | 1036.2 | 1042.4 | 2204.9 | 2815 | 0.0916 | Haswell |
| `out/checker_364_3060_32.json` | 364\|3060\|32 | ok | 15 | 14400 | 1784.1 | 1786.5 | 3697.3 | 5142 | 0.1571 | SkylakeX |

## What the owners should know before grading

- **Arithmetic floor of the checker units.** The calibration unit ran on a
  kernel family this folder did not record (the readout was added after it),
  and the batch ran on SkylakeX and Haswell hosts. The probe shows a kernel
  change alone moves the (200, 2400, 32) unit by up to 3.39e-7 in spectral
  norm. Whether the larger units have the same floor was not measured; their
  `diag.cond_Gb` is in each file. `meta.calibration` in every checker file
  carries the per-cell differences and both bounds, so checker/ can flag any
  R_S eigenvalue within that distance of its threshold.
- **The default rule's S** is `max(1200.0, 12.0 * 2 * math.pi * N / L)`,
  read from `two_adic/ta_ts.py` line 147 (`KernelProvider.delta_T`), with
  nvec from line 146. The exact float S was passed to the build (`units.*.S_exact`);
  the unit key uses `int(S)`, as `run_checker_ts.unit_key` does. Each unit
  builds all three cells at one (nvec, S); the rule's value at c = 2.9 is used
  for c = 2.2 and 2.5 too in `checker_280_2266_32`, and likewise for the others.
- **The route is the owners' own code, called as a library:** checker units
  are `run_checker_ts.build_unit(nvec, S, N)` inside `run_checker_ts._guard`
  before and after, with `checker_glue.loaded_inputs_outside_key()` empty;
  two_adic units are `ta_gram_probe.run(nvec, S)` and `q_low()` (not `main`,
  which writes into the tracked `ta_gram_probe.json`). Kmax is what the code
  chose (`ta_prolate.kmax_for`).
- **Guard, every unit:** HEAD 284eff6, whole-tree `git status --porcelain
  --untracked-files=all` empty, `checker_glue.ts_key()` =
  (`1dcab230...fb9a`, []) before and after the build, recorded in
  `meta.guard_before` and `meta.guard_after`.

## Close-out

- **Nothing of this folder's is running on Modal.** Each app stopped when its
  entrypoint completed; `modal app list` at 11:11 -0500 shows all six
  `c4s2-modal-compute` apps stopped with 0 tasks, and the two pre-existing
  deployed apps (`claude-scie...`, `specimen-v1...`) untouched.
- The Volume `c4s2-modal-out` is kept (12 result files and 12 start markers,
  storage at 0.09 USD per GiB-month). Deleting it is the operator's call.
- Nothing pushed; no GitHub Actions; no workflow file. Commits in this folder
  only, with pathspecs.

## Tests

`modal/test_modal_outputs.py` pins: every unit's file exists with the 284eff6
tree and the local digest, and the guard passing; the owners' shapes; the
default rule read from `two_adic/ta_ts.py`; the two calibrations against the
committed local values (two_adic at 1e-10, checker at the changed 1e-6); the
probe's configuration and that its differences are the ones recorded in every
checker file. It pins no mathematical conclusion.

## Grade

Operational record only. The outputs are the owners' float64 routes run
elsewhere: measured grade at most, and ungraded until checker/ and two_adic/
read them. The threshold change is a procedural decision recorded with its
evidence, not a result.
