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

Written after the calibration, before the batch launches.

## 5. Unit log

Appended by `run_modal.py` as each unit lands. Wall is the container
function's wall time; cost is computed (wall x (4 cores x core rate +
max(16 GiB, peak) x GiB rate)), not read from Modal's billing.

| unit | status | wall s | CPU s | peak MiB | computed cost USD | CPU model | landed |
|---|---|---|---|---|---|---|---|
| gram_80_4800 | ok | 184.5 | 426.3 | 846.6 | 0.0162 | unknown | 2026-09-24 09:25:26 -0500 |
| checker_200_2400_32 | ok | 438.7 | 976.4 | 1580.2 | 0.0386 | unknown | 2026-09-24 09:29:45 -0500 |
