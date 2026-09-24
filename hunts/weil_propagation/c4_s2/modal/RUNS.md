# RUNS: modal/, the compute log

Every run of `run_modal.py` on Modal, with the estimate written before the
spend it covers (AGENTS.md compute discipline, rule 3). Hard cap: 25 USD.
Outputs and cost only; nothing here is graded.

## 1. The tree and the image

- Tree: a standalone clone in the session scratchpad,
  `git clone --no-local --depth 1 -b teal-sea/weil-c4-s2 <worktree> <scratch>/tree`,
  deepened by 3 commits, then `git checkout 284eff6`. `rev-parse HEAD` =
  284eff64b32cbcbd8b99f0198b129e90cc940623, `status --porcelain
  --untracked-files=all` empty. It enters the image as a tarball,
  `COPYFILE_DISABLE=1 tar --no-xattrs --no-mac-metadata -czf <scratch>/tree.tgz tree`
  (45.5 MB, `.git` included, symlinks kept), extracted to `/tree` at build
  time with `--no-same-owner`; the build step fails unless HEAD is 284eff6
  and `git status --porcelain --untracked-files=all` is empty.
  `PYTHONPATH=/tree`.
- First route, abandoned: `add_local_dir(<scratch>/tree, /tree, copy=True)`.
  It resolves symlinks, so `AGENTS.md` (a symlink to `CLAUDE.md`) arrived as a
  file and the container's porcelain read ` T AGENTS.md`. checker_glue's own
  guard passed there (digest equal, dirty list empty, since `AGENTS.md` is
  outside T_S's inputs), but the whole-tree check in `run_modal.py` refused,
  so nothing was computed on that image.
- Local T_S input digest (`checker_glue.ts_key()` in this worktree, at
  284eff6 and at e43a7a9): `1dcab23022a36c1b75c1f23379c1549bf7be9d4be7f526a5257bb3004577fb9a`,
  dirty list empty.
- Image: `debian_slim`, Python 3.12, `apt_install("git")`, `git config
  --global --add safe.directory '*'` (the files in the image are not owned
  by the container user, and `checker_glue._git` runs with `check=True`),
  `pip_install` numpy 2.5.1, scipy 1.18.0, mpmath 1.3.0, python-flint 0.9.0,
  sympy 1.14.0 (the local venv's versions; sympy is imported by
  `two_adic/ta_data.py`). `requirements.txt` is not installed. BLAS threads
  set to 4: the container sees 4 CPUs.
- **Smoke (2026-09-24, app ap-qeApZXN87zNOq1Z5uxkR8J): PASS.** In the
  container: HEAD 284eff6, whole-tree porcelain empty, `ts_key()` =
  (`1dcab230...fb9a`, []), equal to the local call; `import run_checker_ts`
  and `import ta_gram_probe` both load (the latter reaches
  `hunts/rogue_frontier/weil_trunc/galerkin.py` through `ta_es`), and the
  tree is still clean after them. Container: Python 3.12.10, Linux 4.19
  gVisor x86_64, glibc 2.36; `os.cpu_count()` = sched affinity = 4.
  numpy 2.5.1, scipy 1.18.0, mpmath 1.3.0, python-flint 0.9.0, sympy 1.14.0
  (equal to the local venv's; local Python is 3.13.14, macOS arm64).
- **CPU model: not exposed.** gVisor's `/proc/cpuinfo` reads "unknown".
  numpy's SIMD detection reports AVX, AVX2, FMA3, BMI2, VAES, VPCLMULQDQ,
  X86_V3 and no AVX-512. Each unit's output records the same fields for its
  own container, since Modal may place units on different hosts.

## 2. Rates and resources

Read on 2026-09-24 from modal.com/pricing (not from memory):

- CPU: 0.0000131 USD per physical core per second (1 physical core = 2 vCPU
  equivalent; minimum 0.125 cores per container).
- Memory: 0.00000222 USD per GiB per second.
- A 1.15x to 1.75x regional multiplier applies only to a pinned region (none
  is pinned here), and non-preemptible execution costs 3x (not used).

Per container: `cpu=(4.0, 4.0)` (request, hard limit), `memory=(16384,
32768)` MiB (request, hard limit). Billing takes the larger of reservation
and use, and the limits cap use, so the bound rate is
4 x 0.0000131 + 32 x 0.00000222 = **0.00012344 USD/s (0.444 USD/h)** per
container.

Each unit runs in a single-use container, in a child process with the unit's
own timeout; the container's Modal timeout is that plus 600 s. A restarted
input (preemption) finds its start marker on the Volume and computes
nothing, so no unit can bill more than one container timeout.

## 3. Before any unit: smoke and calibration bound

| call | container timeout (s) | bound (USD) |
|---|---|---|
| smoke (guard, versions, import chains) | 900 | 0.111 |
| checker_200_2400_32 (unit limit 1800 s) | 2400 | 0.296 |
| gram_80_4800 (unit limit 1200 s) | 1800 | 0.222 |
| **total** | | **0.63** |

Laptop times: 246.8 s (checker/ snapshot, unit 200|2400|32) and 107.0 s
(two_adic/ `ta_gram_probe.json`, run 80,4800).

### 3.1 Calibration result (app ap-0JPiceMca78mFevFf9x2Mv, 2026-09-24 09:22 to 09:30 -0500)

Both units ran with the guard passing before and after (HEAD 284eff6,
whole-tree porcelain empty, digest `1dcab230...fb9a`). Computed cost of both:
0.055 USD.

| unit | child wall (s) | CPU (s) | peak (MiB) | laptop (s) | Modal / laptop | max abs difference | threshold |
|---|---|---|---|---|---|---|---|
| gram_80_4800 | 180.6 | 426.3 | 847 | 107.0 | 1.69 | **8.2e-15** (dT; every scalar field at most 7.6e-15; Kmax equal) | 1e-10: **met** |
| checker_200_2400_32 | 432.3 | 976.4 | 1580 | 246.8 | 1.75 | **2.28e-7 / 1.98e-7 / 1.93e-7** (c = 2.2 / 2.5 / 2.9) | 1e-10: **not met** |

The checker unit's differences, spectral norm: 2.3e-7, 2.6e-7, 2.9e-7, on
entries up to 3.7 (relative 6e-8). Its diagnostics agree: `gram_z_offI`
equal to 1e-16, `cond_Gb` 3875494354.4 here against 3875494350.7 locally
(relative 1e-9). The gram unit's Gram matrix is well conditioned; this
unit's `Gb` has condition number 3.9e9, and `ta_mellin.rho` inverts it
(`np.linalg.inv`). A last-digit difference between the two platforms'
arithmetic (macOS arm64 Accelerate, Python 3.13, against Linux x86_64
OpenBLAS, Python 3.12) amplified by 3.9e9 is of order 1e-16 x 3.9e9 = 4e-7,
the size observed. That is the likely cause; it is not demonstrated.

**Per the brief, the run stopped here** and the question went to the
coordinator before the batch.

## 4. The batch estimate

Written after the calibration and the coordinator's answer, before any batch
unit launches.

### 4.1 The coordinator's ruling on the calibration miss (2026-09-24)

Option B of the question in s3.1: (1) run one sensitivity probe on Modal,
the checker calibration unit again with `OPENBLAS_CORETYPE=Sandybridge`
(OpenBLAS's AVX kernels without FMA, so only last-digit arithmetic changes),
compared Modal against Modal; (2) launch the two_adic family now, since its
calibration passed at 8.2e-15; (3) launch the four checker units with the
calibration threshold set to 1e-6 max abs **only if** the probe moves the
checker unit by about 1e-7; if it moves it by less than 1e-10, hold the
checker family and ask again. The threshold in the brief is 1e-10; the
measured miss is 2.28e-7 / 1.98e-7 / 1.93e-7 (c = 2.2 / 2.5 / 2.9); `Gb`'s
condition number is 3.9e9. A 1e-6 threshold, if adopted, is set after the
measurement and is justified by the probe, not by checker/'s band. Until the
probe says otherwise, "likely cause" stays the wording. Each checker output
carries the calibration's spectral differences as a Weyl bound
(`meta.calibration.weyl_bound` = 2.93e-7), so checker/ can flag any R_S
eigenvalue within that distance of its threshold when it re-grades.

### 4.2 Per-unit estimates, timeouts and the worst case

Modal / laptop speed ratio from s3.1: **1.75** (checker unit) and **1.69**
(gram unit); Modal is slower per unit (4 cores, AVX2, no AVX-512, against the
laptop's M4). Estimates scale the Modal calibration time by the larger of
two work ratios, taken from the grids the code builds (`ta_mellin.s_grid`,
`ta_mellin.w_nodes` with `ta_prolate.kmax_for(nvec)`): complex exponentials
(s-nodes x w-nodes) and the mode matmul (s-nodes x w-nodes x nvec). The
prolate-mode setup in mpmath is not in the model, and checker/ s7.6 records
that a scaling model already failed once (the 240-mode unit passed 9.2
CPU-min on the loaded laptop against an estimate of 320 s). The timeouts,
not the estimates, hold the cap: each is 3 to 4.6 times its estimate.

Default rule (derived from `two_adic/ta_ts.py` lines 146 and 147,
`KernelProvider.delta_T`): `nvec = max(80, int(8 N / L) + 40)`,
`S = max(1200.0, 12.0 * 2 * math.pi * N / L)`, L = log c; at N = 32 it gives
(280, 2266.10) at c = 2.9, (319, 2633.16) at 2.5, (364, 3060.08) at 2.2.
S is passed as that float; the unit key uses `int(S)`, as `unit_key` does.
Each unit builds all three cells at its (nvec, S).

| unit | Kmax | estimate (s) | unit timeout (s) | container timeout (s) | bound (USD) |
|---|---|---|---|---|---|
| checker_200_2400_32_sandybridge (probe) | 13 | 605 | 1800 | 2400 | 0.296 |
| gram_140_4800 | 12 | 523 | 2400 | 3000 | 0.370 |
| gram_160_4800 | 12 | 597 | 2400 | 3000 | 0.370 |
| gram_180_4800 | 13 | 969 | 3600 | 4200 | 0.518 |
| gram_200_4800 | 13 | 1077 | 3600 | 4200 | 0.518 |
| gram_160_9600 | 12 | 1921 | 7200 | 7800 | 0.963 |
| checker_240_2400_32 | 14 | 896 | 3600 | 4200 | 0.518 |
| checker_280_2266_32 | 14 | 976 | 3600 | 4200 | 0.518 |
| checker_319_2633_32 | 14 | 1329 | 5400 | 6000 | 0.741 |
| checker_364_3060_32 | 15 | 3260 | 14400 | 15000 | 1.852 |
| **all ten** | | **12148** | | | **6.666** |

- **Worst case = sum over units of container timeout x (4 cores x
  0.0000131 + 32 GiB x 0.00000222) = 6.67 USD.** With the smoke and
  calibration already spent (computed 0.06 USD), **6.73 USD against the
  25 USD cap.** The 364-mode unit fits, and the coordinator accepted it.
- Expected: 12148 s x (4 x 0.0000131 + 16 x 0.00000222) = **1.07 USD**
  (the probe's estimate assumes the no-FMA kernels are 1.4x slower).
- Memory, scaled from the calibration peaks (1.58 GiB checker, 0.85 GiB gram)
  by w-nodes x nvec: at most about 9 GiB (364 modes), under the 16 GiB
  request; the 32 GiB limit caps it.
- Launch order: the probe and the five gram units now, in one detached app;
  the four checker units only after the probe, per 4.1.

### 4.3 The probe, and the checker threshold (2026-09-24 09:40 -0500)

Estimate committed 09:33:01 (76d13a9); probe and gram units launched 09:33:12
(app ap-JRlZr1RjuHFd8xDrZ9Rz85, the spawned rows in s5).

The probe `checker_200_2400_32_sandybridge` ran with the guard passing before
and after, and its child read OpenBLAS's kernel family as `Sandybridge` (the
override took; the calibration unit predates this readout and records none).
Against the Modal calibration unit, same image, same code, same inputs:

| c | max abs, Modal vs Modal | spectral | max abs, probe vs laptop |
|---|---|---|---|
| 2.2 | 2.84e-7 | 2.97e-7 | 2.33e-7 |
| 2.5 | 3.01e-7 | 3.15e-7 | 2.32e-7 |
| 2.9 | 3.29e-7 | 3.39e-7 | 2.25e-7 |

Changing only the BLAS kernels moves this unit by 2.8e-7 to 3.3e-7, the same
order as the 1.9e-7 to 2.3e-7 cross-platform miss. **Shown by this probe:
the checker unit reproduces only to about 3e-7 under last-digit changes in
arithmetic**, consistent with `Gb`'s condition number 3.9e9 inverted in
`ta_mellin.rho` (the probe shows the sensitivity; which step amplifies it is
not isolated). `cond_Gb` itself reads 3875494700.2 in the probe, against
3875494354.4 and 3875494350.7.

**The checker calibration threshold is changed from 1e-10 (the brief) to
1e-6 max abs, on 2026-09-24, after the measurement**, per the coordinator's
option B. The justification is the probe (arithmetic alone moves the unit by
up to 3.3e-7), not checker/'s band. At 1e-6 the calibration passes (2.28e-7).
The two_adic calibration keeps 1e-10 (8.2e-15). Every checker output carries
`meta.calibration`: the calibration's per-cell differences, its Weyl bound
2.93e-7 (spectral, Modal against laptop) and the probe's 3.39e-7
(`arithmetic_floor_bound`, Modal against Modal), so checker/ can flag any
R_S eigenvalue within that distance of its threshold when it re-grades.

The four checker units launch next, under the timeouts of 4.2.

## 5. Unit log

Appended by `run_modal.py` as each unit lands. Wall is the container
function's wall time; cost is computed (wall x (4 cores x core rate +
max(16 GiB, peak) x GiB rate)), not read from Modal's billing.

| unit | status | wall s | CPU s | peak MiB | computed cost USD | CPU model | landed |
|---|---|---|---|---|---|---|---|
| gram_80_4800 | ok | 184.5 | 426.3 | 846.6 | 0.0162 | unknown | 2026-09-24 09:25:26 -0500 |
| checker_200_2400_32 | ok | 438.7 | 976.4 | 1580.2 | 0.0386 | unknown | 2026-09-24 09:29:45 -0500 |
| checker_200_2400_32_sandybridge | spawned fc-01M39XBCX93VHSD92T79TANEE4 | | | | | | 2026-09-24 09:33:12 -0500 |
| gram_140_4800 | spawned fc-01M39XBD8Z0M2TCM9FE3XB6X1D | | | | | | 2026-09-24 09:33:13 -0500 |
| gram_160_4800 | spawned fc-01M39XBDDAEMZRRWS4VBTQCEA6 | | | | | | 2026-09-24 09:33:13 -0500 |
| gram_180_4800 | spawned fc-01M39XBDS38BQ1KV7WNE8N5THH | | | | | | 2026-09-24 09:33:13 -0500 |
| gram_200_4800 | spawned fc-01M39XBDXT24JNXZDY2RJ562FV | | | | | | 2026-09-24 09:33:13 -0500 |
| gram_160_9600 | spawned fc-01M39XBE9XJEBM3KQCQJCC314T | | | | | | 2026-09-24 09:33:14 -0500 |
| gram_140_4800 | ok | 278.0 | 643.6 | 1281.2 | 0.0244 | unknown | 2026-09-24 09:38:02 -0500 |
| gram_160_4800 | ok | 303.3 | 636.8 | 1336.0 | 0.0267 | unknown | 2026-09-24 09:38:34 -0500 |
| checker_200_2400_32_sandybridge | ok | 397.3 | 1017.9 | 1578.1 | 0.0349 | unknown | 2026-09-24 09:40:09 -0500 |
| checker_240_2400_32 | spawned fc-01M39XT31YB94RK5CGH07ZRAEF | | | | | | 2026-09-24 09:41:14 -0500 |
| checker_280_2266_32 | spawned fc-01M39XT37PFD1FP79RMDFXG545 | | | | | | 2026-09-24 09:41:14 -0500 |
| checker_319_2633_32 | spawned fc-01M39XT3N8C1ZRJ2H9JK5ERY8R | | | | | | 2026-09-24 09:41:14 -0500 |
| checker_364_3060_32 | spawned fc-01M39XT42G5YHCQ14G2P9ZVQ09 | | | | | | 2026-09-24 09:41:15 -0500 |
| gram_180_4800 | ok | 475.9 | 980.4 | 1771.8 | 0.0418 | unknown | 2026-09-24 09:41:27 -0500 |
| gram_200_4800 | ok | 627.9 | 1253.7 | 1822.1 | 0.0552 | unknown | 2026-09-24 09:44:00 -0500 |
| gram_160_9600 | ok | 797.2 | 1858.2 | 2064.0 | 0.0701 | unknown | 2026-09-24 09:46:47 -0500 |
| checker_280_2266_32 | ok | 846.6 | 1551.8 | 2559.1 | 0.0744 | unknown | 2026-09-24 09:55:26 -0500 |
| checker_240_2400_32 | ok | 890.4 | 1665.3 | 2421.8 | 0.0783 | unknown | 2026-09-24 09:56:14 -0500 |
| checker_319_2633_32 | ok | 1042.4 | 2204.9 | 2814.8 | 0.0916 | unknown | 2026-09-24 09:58:49 -0500 |
| checker_364_3060_32 | ok | 1786.5 | 3697.3 | 5142.2 | 0.1571 | unknown | 2026-09-24 10:11:18 -0500 |

## 6. Close-out (2026-09-24 11:12 -0500)

- All 12 units landed with status ok; none timed out, none restarted.
  Launches: calibration 09:22 (app ap-0JPiceMca78mFevFf9x2Mv), probe and
  two_adic family 09:33:12 (ap-JRlZr1RjuHFd8xDrZ9Rz85), checker family
  09:41 (ap-aqasUO4OPbf2wQ7SudOKcg), each after the commit of the estimate it
  ran under (76d13a9 at 09:33:01, bb50c73 at 09:41:01). ap-6KyRUDzcVl1xoUQiVDAJuf
  re-shaped two files from the Volume (no containers, no cost).
- **Billed: 0.741 USD** (`modal billing report --for today`, all six apps of
  this folder: 0.001 and 0.001 smoke, 0.055 calibration, 0.269 probe and
  two_adic family, 0.415 checker family). Computed from the unit log above:
  0.709 USD. Worst case written before launch: 6.73 USD. Cap: 25 USD.
  `modal billing rates` reads 0.0473 USD per core-hour and 0.008 USD per
  GiB-hour, the same as the pricing page in s2.
- Estimates against actuals (child wall, s): gram 140 / 160 / 180 / 200 at
  S = 4800: 523 / 597 / 969 / 1077 estimated, 275 / 300 / 473 / 625 actual;
  gram (160, 9600): 1921, 795; checker 240 / 280 / 319 / 364: 896 / 976 /
  1329 / 3260, 887 / 844 / 1036 / 1784. Peak memory at most 5.0 GiB (364
  modes), under the 16 GiB request.
- The OpenBLAS kernel family varied by host: SkylakeX for 6 batch units,
  Haswell for 3 (RESULTS.md table). The calibration units predate the
  readout.
- `modal app list` at 11:11 -0500: all six `c4s2-modal-compute` apps stopped,
  0 tasks; `claude-scie...` and `specimen-v1...` deployed and untouched. The
  Volume `c4s2-modal-out` is kept (12 results, 12 start markers).

## 7. Follow-up 2 (2026-09-24): every checker/ unit under the QR rho

BRIEF.md "Follow-up 2". two_adic/ replaced the explicit inverse in
`ta_mellin.rho` by a QR of the Gram factor (c3dca00, eea7eab), so T_S's
input digest moved from 1dcab230 to b2e7787b and checker/'s guard refuses
every old row. This section rebuilds all eleven checker/ units on Modal.
Sections 1 to 6 above are the record of the old route and are not edited;
`modal/out/` and `test_modal_outputs.py` are untouched. Driver:
`run_modal_rho.py` (a copy of `run_modal.py`'s machinery; the old file keeps
its constants because its pins read them). Outputs: `modal/out_rho/`.
No eigenvalue of T_S or R_S is computed here.

### 7.1 The tree and the image

- Tree: `git clone --no-local --depth 1 -b teal-sea/weil-c4-s2 <worktree>
  <scratch>/tree_rho` at 14:02 -0500. `rev-parse HEAD` =
  e2b46a5a82f365469a814f80c94b5232cf8bee46 (the branch HEAD, after eea7eab),
  `status --porcelain --untracked-files=all` empty. Tarball as in s1:
  `COPYFILE_DISABLE=1 tar --no-xattrs --no-mac-metadata -czf
  <scratch>/tree_rho.tgz tree_rho` (47.7 MB), extracted to `/tree` at build
  time; the build fails unless HEAD is e2b46a5 and the porcelain is empty.
- Local T_S input digest (`checker_glue.ts_key()`, in this worktree and in the
  clone): `b2e7787bce7a77db4a1a81b9311fc75a2b9326649b88a49883bd4d737ca70eaa`,
  dirty list empty.
- Image: as in s1 (debian_slim, Python 3.12, git, `safe.directory '*'`,
  numpy 2.5.1, scipy 1.18.0, mpmath 1.3.0, python-flint 0.9.0, sympy 1.14.0,
  the local venv's versions read again today; BLAS threads 4).
- A new app, `c4s2-modal-rho`, and a new Volume, `c4s2-modal-rho-out`. The old
  Volume `c4s2-modal-out` holds finished results and start markers under five
  of the same unit names (`checker_200_2400_32`, `_240_`, `_280_`, `_319_`,
  `_364_`), which `unit_remote` would return without computing.
- Units: the seven of `run_checker_ts.UNITS` and the four N = 32 units of the
  first follow-up, one Modal call each, all three cells per call, built by
  `run_checker_ts.build_unit(nvec, S, N, dps_list)` with dps (40, 60) at
  N = 8 and (40,) otherwise, as `snapshot()` builds them. The default-rule S
  are passed as the same floats as in the first follow-up (s4.2).
- Calibration, threshold fixed by the brief before the run: (80, 1200, 8) on
  Modal against the same unit built locally with the new code
  (`local_rho_calibration.py`, `out_rho/local_checker_80_1200_8.json`,
  41.3 s on the laptop at load average 24; digest b2e7787b, HEAD e2b46a5),
  max abs difference over all six row keys at most **1e-10**. If it misses,
  the run stops and the question goes to the coordinator. The Modal
  calibration unit is also the eleven's (80, 1200, 8) unit: one call serves
  both.

### 7.2 Rates, resources, and the bound before any call

Rates read on 2026-09-24 at 14:05 -0500 with `modal billing rates`: CPU
0.0473 USD per core-hour (1.314e-5 per core-second), memory 0.008 USD per
GiB-hour (2.22e-6 per GiB-second), the same as s2. Per container, as before:
`cpu=(4.0, 4.0)`, `memory=(16384, 32768)` MiB, so the bound rate is
4 x 1.314e-5 + 32 x 2.22e-6 = **1.2367e-4 USD/s (0.445 USD/h)**. Container
timeout = unit timeout + 600 s. A restarted input finds its start marker and
computes nothing.

| call | unit timeout (s) | container timeout (s) | bound (USD) |
|---|---|---|---|
| smoke (guard, versions, import chain) | | 900 | 0.111 |
| checker_80_1200_8 (calibration, and unit 1 of 11) | 1200 | 1800 | 0.223 |
| **total before the batch** | | | **0.334** |

Remaining cap for both batches of this follow-up: 25 - 0.741 = 24.26 USD.

### 7.3 Calibration log

Appended by `run_modal_rho.py` as each call lands. Wall is the container
function's wall time; cost is computed (wall x (4 cores x core rate +
max(16 GiB, peak) x GiB rate)), not billed. The BLAS column is the OpenBLAS
kernel family the child loaded.

| unit | status | wall s | CPU s | peak MiB | computed cost USD | BLAS | landed |
|---|---|---|---|---|---|---|---|
| checker_80_1200_8 | spawned fc-01M3AD6RGP4B31ZSTGQDWBB9GB | | | | | | 2026-09-24 14:10:18 -0500 |
| checker_80_1200_8 | ok | 39.3 | 100.1 | 471.7 | 0.0035 | SkylakeX | 2026-09-24 14:11:19 -0500 |

### 7.4 Smoke and calibration results (2026-09-24 14:08 to 14:12 -0500)

- **Smoke (app ap-ERd4Y6ruZrBdFLlCPZAujJ): PASS.** The image build checked
  HEAD e2b46a5 and an empty whole-tree porcelain. In the container, before
  and after importing `run_checker_ts`: HEAD e2b46a5, porcelain empty,
  `ts_key()` = (`b2e7787bce7a...0eaa`, []), equal to the local call. Python
  3.12.10, Linux 4.19 gVisor x86_64, glibc 2.36, 4 CPUs; numpy 2.5.1,
  scipy 1.18.0, mpmath 1.3.0, python-flint 0.9.0, sympy 1.14.0. CPU model not
  exposed ("unknown"); this host's numpy reports AVX-512 (X86_V4).
- **Calibration (app ap-r0YfOJE3NKR8yfoGTpakcI): PASS.** `checker_80_1200_8`
  on Modal (OpenBLAS SkylakeX, child 34.2 s, container 39.3 s, 100.1 CPU s,
  472 MiB) against `out_rho/local_checker_80_1200_8.json` (laptop 41.3 s at
  load average 24), all six row keys (three cells, dps 40 and 60):

  | cell | max abs difference, dps 40 | dps 60 |
  |---|---|---|
  | 2.2 | 5.8e-15 | 5.8e-15 |
  | 2.5 | 4.9e-15 | 4.9e-15 |
  | 2.9 | 7.1e-15 | 7.1e-15 |

  **Max 7.1e-15 against the threshold 1e-10: met.** The diagnostics agree:
  cond_Fz 16.514603709784 both, cond_Fb 16.735960732146 both, cond_Gb
  280.0923816279 both (relative 1e-13). Recorded in `run_modal_rho.py`
  `CHECKER_CALIBRATION` and carried in every output's `meta.calibration`
  (the calibration file was re-shaped from the Volume with `fetch --no-log`,
  app ap-W1DBc8WmUr8jqNdJ9AizI0, no containers). This is the N = 8 unit at
  cond_F about 17; no platform floor is measured here for the N = 16 and
  N = 32 units.

### 7.5 The batch estimate (written before launch)

Speed: the QR route costs about what the inverse did on Modal. The old route
has no Modal build of (80, 1200, 8); at the first follow-up's Modal / laptop
ratio of 1.75 it would take 20.8 x 1.75 = 36 s, against 34.2 s measured now.
two_adic/ regenerated (200, 2400) locally in 302 s under the QR route against
246.8 s for checker/'s old build of the same unit (two SVDs of F added). The
estimate takes the old unit times x 1.3: the first follow-up's Modal child
times for the N = 32 units, and the laptop times x 1.75 for the N = 16 units.
two_adic/ s10.5's estimate for the five N = 32 units (4980 s, 0.45 USD) is
this at x 1.0.

| unit | old time (s) | estimate (s) | unit timeout (s) | container timeout (s) | bound (USD) |
|---|---|---|---|---|---|
| checker_120_1600_16 | 73.7 laptop | 168 | 1200 | 1800 | 0.223 |
| checker_200_2400_32 | 432.3 Modal | 562 | 2400 | 3000 | 0.371 |
| checker_80_1600_16 | 28.5 laptop | 65 | 1200 | 1800 | 0.223 |
| checker_120_1200_16 | 50.4 laptop | 115 | 1200 | 1800 | 0.223 |
| checker_80_1200_16 | 20.8 laptop | 47 | 1200 | 1800 | 0.223 |
| checker_160_1600_16 | 107.6 laptop | 245 | 1200 | 1800 | 0.223 |
| checker_240_2400_32 | 887.3 Modal | 1153 | 3600 | 4200 | 0.519 |
| checker_280_2266_32 | 843.9 Modal | 1097 | 3600 | 4200 | 0.519 |
| checker_319_2633_32 | 1036.2 Modal | 1347 | 5400 | 6000 | 0.742 |
| checker_364_3060_32 | 1784.1 Modal | 2319 | 10800 | 11400 | 1.410 |
| **the ten** | | **7118** | | | **4.674** |

- **Worst case = sum over units of container timeout x (4 cores x 1.314e-5 +
  32 GiB x 2.22e-6) = 4.67 USD** for the ten. With the smoke and the
  calibration unit (bound 0.334, computed about 0.005), **at most 5.01 USD for
  batch 1, against the 24.26 USD remaining.** Every unit timeout is at least
  3.1 times its estimate and at least 4.0 times the old unit's time; the
  364-mode unit's is 6.1 times its old 1784 s (the brief asks for at least 3).
- Expected: 7118 s x (4 x 1.314e-5 + 16 x 2.22e-6) = **0.63 USD**.
- Memory: the first follow-up peaked at 5.0 GiB (364 modes), under the 16 GiB
  request; the 32 GiB limit caps it.
- Batch 2 (the default-rule rows at S/nvec^2 = 0.04) is not launched; it runs
  only if the coordinator sends it.
- Launch: all ten in one detached app (`batch`), each unit one Modal call,
  landed into `out_rho/` as it returns and logged in s7.6.

### 7.6 Unit log

Same columns as s7.3.

| unit | status | wall s | CPU s | peak MiB | computed cost USD | BLAS | landed |
|---|---|---|---|---|---|---|---|
| checker_120_1600_16 | spawned fc-01M3ADC1Q11461A3V2SXW2WEHT | | | | | | 2026-09-24 14:13:11 -0500 |
| checker_200_2400_32 | spawned fc-01M3ADC22VDPC856PTDBRT3WSK | | | | | | 2026-09-24 14:13:11 -0500 |
| checker_80_1600_16 | spawned fc-01M3ADC28MWMEB521C0ZZTYJ0K | | | | | | 2026-09-24 14:13:12 -0500 |
| checker_120_1200_16 | spawned fc-01M3ADC2DSR7BVAMBNJXG6JW12 | | | | | | 2026-09-24 14:13:12 -0500 |
| checker_80_1200_16 | spawned fc-01M3ADC2KPFJPETGHPAXFT42E5 | | | | | | 2026-09-24 14:13:12 -0500 |
| checker_160_1600_16 | spawned fc-01M3ADC2RRRGM5NEQ1Y6B7AWPD | | | | | | 2026-09-24 14:13:12 -0500 |
| checker_240_2400_32 | spawned fc-01M3ADC34X549NPD78BTC2Q9GN | | | | | | 2026-09-24 14:13:12 -0500 |
| checker_280_2266_32 | spawned fc-01M3ADC39S21KXZ0W9EKKYGHWP | | | | | | 2026-09-24 14:13:13 -0500 |
| checker_319_2633_32 | spawned fc-01M3ADC3NJG7ANH70K917XHQ79 | | | | | | 2026-09-24 14:13:13 -0500 |
| checker_364_3060_32 | spawned fc-01M3ADC40Y3B89CS0HE79PTBHV | | | | | | 2026-09-24 14:13:13 -0500 |
| checker_80_1200_16 | ok | 43.3 | 97.6 | 474.9 | 0.0038 | Haswell | 2026-09-24 14:14:05 -0500 |
| checker_80_1600_16 | ok | 63.9 | 144.2 | 530.3 | 0.0056 | Haswell | 2026-09-24 14:14:38 -0500 |
| checker_120_1200_16 | ok | 104.5 | 234.5 | 782.0 | 0.0092 | Haswell | 2026-09-24 14:15:11 -0500 |
| checker_120_1600_16 | ok | 127.5 | 283.4 | 852.5 | 0.0112 | Haswell | 2026-09-24 14:15:30 -0500 |
| checker_160_1600_16 | ok | 154.8 | 345.1 | 935.8 | 0.0136 | Haswell | 2026-09-24 14:16:03 -0500 |
| checker_200_2400_32 | ok | 432.7 | 983.6 | 1580.8 | 0.0381 | Haswell | 2026-09-24 14:20:34 -0500 |
| checker_240_2400_32 | ok | 759.1 | 1627.7 | 2425.1 | 0.0669 | Haswell | 2026-09-24 14:26:04 -0500 |
| checker_280_2266_32 | ok | 756.1 | 1454.1 | 2562.3 | 0.0666 | Haswell | 2026-09-24 14:26:06 -0500 |
| checker_319_2633_32 | ok | 1382.0 | 2354.9 | 2812.9 | 0.1218 | Haswell | 2026-09-24 14:36:36 -0500 |
