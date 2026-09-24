# BRIEF: modal/, the compute follow-up (2026-09-24)

You are the **compute** worker. This folder runs the two compute proposals the
mission left open (`c4_s2/RESULTS.md` line 4 (a) and (b)) on Modal. The
operator approved it on 2026-09-24 with a **hard cap of 25 USD**. You run and
record; you do not interpret. checker/ and two_adic/ grade the results in
their own folders afterwards.

## Rules that apply to you

- `hunts/weil_propagation/MISSION.md` and `c4_s2/MISSION.md` apply in full.
  Read `AGENTS.md` (= `CLAUDE.md`): hard rules, compute discipline, the
  certainty ladder, and the lexical ban under `hunts/` (the reserved word of
  `zeta/rigor.py` may not appear in any file here, not even in a sentence
  that disclaims it). No em dashes in prose you write.
- **Write only in `hunts/weil_propagation/c4_s2/modal/`.** Do not edit
  checker/, two_adic/, kernel/, cutoff/, `zeta/`, `ontology/`, `harness/`.
  Import their code; never modify it.
- **Never push. No GitHub Actions. No workflow file.** Commit with pathspecs
  (`git commit -- <paths>`), and only your own paths.
- Local Python: `/Users/thomas/zeta-lab/.venv/bin/python` with
  `PYTHONPATH=<worktree root>`. Nothing heavy on this laptop: anything over a
  few minutes runs on Modal.
- Modal: CLI `modal` (client 1.5.5), profile `teal-sea`, authenticated.
  The CLI imports `run_modal.py` in its own interpreter, so keep numpy,
  mpmath and repo imports **inside** the remote functions.
- `modal app list` already shows two deployed apps (`claude-scie...`,
  `specimen-v1...`). **They belong to other work. Never stop, touch or
  redeploy them.** Stop only the app this folder creates.
- Questions inside this brief: `orchestration ask`. Anything that would
  exceed the cap, change scope, or touch another folder: ask, and wait.

## Deliverables

`modal/run_modal.py`, `modal/RUNS.md`, `modal/out/*.json` (one file per
unit), `modal/test_modal_outputs.py`, `modal/RESULTS.md`.

## Step 1. The image and the tree (the guard must pass inside the container)

checker/'s snapshot guard (`checker_glue._git`, `ts_key`, `_guard`) runs
`git` with `check=True` and refuses on any dirty input. So the container
needs a **real git checkout** of the committed tree, clean.

- This worktree's `.git` is a pointer file and the branch is not pushed, so
  the image cannot clone from GitHub and cannot copy `.git` from here. Make a
  standalone local clone in the session scratchpad:
  `git clone --no-local --depth 1 -b teal-sea/weil-c4-s2 <worktree> <scratch>/tree`,
  then `git -C <scratch>/tree checkout 284eff6` (deepen the clone if needed).
  Confirm `rev-parse HEAD` is 284eff6... and `status --porcelain` is empty.
  284eff6 is the tree the approval names; your later commits add only
  `modal/`, which is outside T_S's import closure, so the digest is the same.
- Image: `debian_slim` with **python 3.12**, `apt_install("git")`, and
  `pip_install` of mpmath, numpy, scipy, python-flint (pin the versions the
  local venv has: read them with the venv's pip). Do **not** install
  `requirements.txt` (it carries cypari2, inspect_ai and anthropic, none
  needed, and the cypari2 wheel trap). Add anything else kernel/ or two_adic/
  imports, found by trying. Add the clone with `add_local_dir(..., copy=True)`
  including `.git`, and set `PYTHONPATH` to its root.
- **Before any timed unit**, run a remote smoke function that prints
  `checker_glue.ts_key()` and requires an empty dirty list, and records the
  digest. The digest must equal what the same call returns locally. If the
  guard fails in the container, stop there and report: nothing else counts.
- Record the numpy, scipy, mpmath, python-flint versions and the container
  CPU model in RUNS.md.

## Step 2. Calibrate and estimate BEFORE the batch (compute discipline rule 3)

Two calibration units, which are also positive controls of the pipeline:

1. **checker family:** `(nvec, S, N) = (200, 2400, 32)`, all three cells, built
   exactly as `checker/run_checker_ts.py build_unit(nv, S, N)` builds it
   (call it as a library; the new units are not in its `UNITS` list, so
   `--units` cannot reach them). Laptop time: 246.8 s. Its rows must match the
   existing entries in `checker/checker_ts_snapshot.json` (keys
   `unit_key(c, 32, 40, 200, 2400)`). State the max abs difference. If it
   exceeds 1e-10, stop and report.
2. **two_adic family:** `two_adic/ta_gram_probe.py` at `(nvec, S) = (80, 4800)`
   (one process per (nvec, S), see its `main(argv)`). Laptop time about
   107 s. Compare with the committed `two_adic/ta_gram_probe.json` entry for
   that pair; same threshold.

Then write the estimate to `modal/RUNS.md` **before launching the batch**:

- the Modal rates you are using, read **now** from Modal's pricing page or
  the dashboard (not from memory), per CPU-core-second and per GiB-second;
- the CPU and memory reserved per function;
- the laptop-to-Modal speed ratio from the two calibration units;
- per unit: estimated time, and the explicit `timeout=` you set;
- **worst case = sum over units of timeout x (cores x core rate + GiB x GiB
  rate)**. This worst case, not the extrapolation, is what is checked against
  25 USD. checker/ s7.6 records that the scaling model already failed once
  (the 240-mode unit passed 9.2 CPU-min against an estimate of 320 s), so the
  timeouts are what hold the cap.

If the worst case exceeds 25 USD, lower the timeouts only if the estimate
still fits comfortably under them; otherwise `orchestration ask` and wait.
Set `memory=` high enough (two_adic measured 2 to 5 GB at S = 4800; the
N = 32 units at 240 modes and above are unmeasured, so start at 16 GiB and
record the peak).

## Step 3. The batch: one Modal call per unit, in parallel, checkpointed

**checker family** (N = 32, all three cells per unit, one `build_unit` call):

| unit | why |
|---|---|
| (240, 2400, 32) | `run_checker_ts.py` `CI_UNITS`: the N = 32 row against more modes |
| (280, S_rule(2.9), 32) | two_adic's default mode rule at c = 2.9 (the "280-mode check") |
| (319, S_rule(2.5), 32) | the same rule at c = 2.5; part of the approved proposal (checker/ s7.6 "the default-rule rows at N = 32") |
| (364, S_rule(2.2), 32) | the same rule at c = 2.2; run only if the worst case still fits under the cap |

The mode rule is `nvec = max(80, int(8 N / L) + 40)`, L = log c
(`checker/test_checker_ts.py::test_default_mode_rule_counts`). S_rule is the
S of the same default rule (checker/ s7.6 writes S = 24 pi N / L); **derive
it from two_adic/'s code, do not take it from this brief**, and state where
you found it.

**two_adic family** (`ta_gram_probe.py`, one process per unit): nvec 140,
160, 180, 200 at S = 4800, and 160 at S = 9600 (two_adic/ RESULTS s7b; Kmax
is whatever the script chooses; record it).

Checkpointing: each remote function writes its result to a Modal Volume and
commits it before returning, and the local entrypoint writes each result to
`modal/out/<unit>.json` **as it lands** (`map(..., order_outputs=False,
return_exceptions=True)` or `spawn` plus polling). A dropped session must not
lose a finished unit. Output shape: checker units in the snapshot's shape
(`{unit_key: rows}` plus `diag`, the digest, the tree commit, versions,
wall and CPU seconds, peak memory); two_adic units in exactly the shape
`ta_gram_probe.py` writes for one (nvec, S).

Run attached (`modal run`), watch it, and append to RUNS.md as units finish:
wall time, CPU time, peak memory, cost so far. A unit that hits its timeout
is recorded as "timed out at X s", not retried blindly; ask before any retry
that raises a timeout.

## Step 4. Close out

- `modal app stop` **this app only**, then `modal app list` to show nothing of
  yours is running. Record the final cost from Modal's billing/usage view if
  the CLI or dashboard shows it; otherwise the computed cost, labelled as
  computed.
- `modal/test_modal_outputs.py`: pins that every `out/*.json` exists, carries
  the 284eff6 tree and the local T_S digest, and that the two calibration
  units match the committed local values to the stated threshold. Pin no
  mathematical conclusion: grading belongs to checker/ and two_adic/.
- `modal/RESULTS.md`, first lines: what ran, what timed out, total cost,
  where each output file is. Say plainly that the numbers are produced and
  not yet graded.
- Run your test, `tests/test_hunt_probe_discipline.py`,
  `tests/test_docs_numbering.py`. Commit with pathspecs. No push.

## Acceptance

- The guard passes in the container, with the local digest.
- Both calibration units match within 1e-10, or the run stopped there.
- RUNS.md has the estimate, rates and worst case, committed **before** the
  batch's launch time recorded in it.
- Every unit is in `out/` or recorded as timed out; total spend at or under
  25 USD; nothing of yours left running on Modal.

## Follow-up 2, 2026-09-24: rebuild every checker/ unit under the fixed rho

*Added by the coordinator.* MISSION.md follow-up 2. two_adic/ replaced the
explicit inverse in `ta_mellin.rho` by a QR of the Gram factor (c3dca00,
eea7eab; its RESULTS s10). T_S's input digest moved from 1dcab230 to
**b2e7787bce7a**, so checker/'s guard now refuses every old snapshot row.
Everything above in this brief still applies unless changed here.

**What changes.**
- Tree: a clean standalone clone at the current HEAD of
  `teal-sea/weil-c4-s2` (at or after eea7eab), not 284eff6. The guard in
  the container must report digest b2e7787bce7a... and an empty dirty list,
  equal to the local call. If it does not, stop there.
- Outputs go to **`modal/out_rho/`**. Do not edit or delete `modal/out/` or
  its pins: it is the record of the old route. Pin the new outputs in a new
  test file; extend `RUNS.md` with new sections, never rewrite the old ones.
- **Do not compute any eigenvalue of T_S or R_S.** checker/ commits its
  criterion reading before any eigenvalue is seen, as in ee4a1ff. Raw rows,
  diagnostics already in `diag` (cond_Fz, cond_Fb), times and costs only.

**Units (batch 1): all eleven checker/ units, one Modal call each, all three
cells per call, built exactly as `run_checker_ts.build_unit` builds them
(including dps (40, 60) at N = 8, as `snapshot()` does):**
the seven of `run_checker_ts.UNITS` ((80, 1200, 8), (120, 1600, 16),
(200, 2400, 32), (80, 1600, 16), (120, 1200, 16), (80, 1200, 16),
(160, 1600, 16)) and the four N = 32 units of the first follow-up
((240, 2400), (280, 2266.10), (319, 2633.16), (364, 3060.08), S as passed
then). The N = 8 and 16 units are needed because the guard now refuses
their old rows; they are cheap.

**Calibration, threshold fixed now:** build (80, 1200, 8) locally with the
new code (seconds to a minute) and on Modal, and compare: max abs difference
at most **1e−10**. two_adic/'s A3 measured the platform-type drift under the
new route at 3e−12; if the calibration misses 1e−10, stop and ask.

**Estimate before launch, in RUNS.md:** two_adic/ s10.5 estimates the five
N = 32 units at about 4980 s wall and 0.45 USD; add the N = 8 and 16 units
from their old wall times. Set per-unit timeouts well above the old unit
times (the 364-mode unit took 1784 s; give it at least 3x). Worst case at the
timeouts must fit the remaining cap: **25 − 0.741 = 24.26 USD** for both
batches together.

**Batch 2 is not yours to decide.** If checker/ finds the falsifier fails at
319 or 364 modes by about 1e−2, the coordinator will send the default-rule
rows at S/nvec² = 0.04 (two_adic/ s10.5, about 0.59 USD). Do not run them
unless asked.

Close-out as before: stop only your own app, record the billed cost from
`modal billing report --for today -r h --tz local --json`, commit with
pathspecs, no push. Ownership this time: `modal/` only.
