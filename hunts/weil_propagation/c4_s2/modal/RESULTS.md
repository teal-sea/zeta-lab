# RESULTS: modal/, the compute follow-up (2026-09-24)

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
