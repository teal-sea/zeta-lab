# RUNS: numerics lane (oob_envelope)

Every run that costs more than a local 10-minute, 2 GB slot is estimated here
before launch. Nothing below has been launched remotely.

## Local runs so far (Ghost, all under 10 min and well under 2 GB)

| run | wall | artifact |
|---|---|---|
| `envelope.py` full grid | 134 s | `envelope.json` |
| `assemble.py` L=0.8 N=200 curve | 354 s | `run_L08_N200.json` |
| `assemble.py` N scan 24..60 | < 60 s each | `run_L08_N*.json` |
| `k3.py` | 1 s | `k3.json`, `k3.out` |
| `harden.py` L=0.8 T#=100 sine:16 N=96 | 28 s | `harden_L08_T100_sine16*.json` |
| `harden.py` L=0.8 T#=200 H=0 N=200 | 188 s | `harden_L08_T200_none.json` |
| `unit_cost.py` | 6 s | `unit_cost.out` |

## Proposed: L = 1.19 (support 2.38) on Modal, two stages

### Parameters (chosen from phase 1 and 2, not tuned to a result)

- Envelope sine:16, S = 3.86347732... (enclosure-carrying, `envelope.json`).
  Envelope threshold 2π e^S = 299.6. D = 16 rather than 64 because the
  quadrature bound grows like cosh(b_e · D log 7): at D = 64 the Bernstein
  bound with GL-96 lands near 1e-52 per entry, too close to the expected
  floor; at D = 16 it is near 1e-62. D = 64 would only lower T# by 7%.
- T# = 500: β* = log(500/2π) − 1/500 − S = 0.5115. Resolution height
  T* = 2π e^{2.38} = 67.9, so T# ≈ 7.4 T*. At L = 0.8 the reduced form with H
  turned positive near 2.1 T* and reached 70% of the window floor by 3.2 T*,
  so positivity of R_H at T# = 500 is expected but **not known**: stage A
  measures it before stage B pays for the bounds.
- Expected λ_min: near Zhu's measured 1e-48 to 1e-46 (his 950-mode run, §7).
  Working precision 384 bits (115 digits).
- x = T# L = 595. Hardened tail bound (Zhu (12), x^n/(2n+1)!!) needs
  2N ≈ 2 x for ε_B ≈ e^-460: **N = 640** (orders 0..1278). Measured-only
  convergence at L = 0.8 needed 2N ≈ 1.15 x: **N = 360** for stage A.
- Panels h = 1/2 on [0, 500]: 1000 panels.

### Measured unit costs (Ghost, M1, 384 bits, `unit_cost.out`)

| item | cost |
|---|---|
| spherical Bessel column, K = 1259, x = 540 | 151 ms / node |
| spherical Bessel column, K = 629, x = 500 | 33 ms / node |
| symbol Ψ + H at one node | 0.5 ms |
| panel product N = 630, q = 96 | 1.4 s (two per panel) |
| panel product N = 315, q = 96 | 0.3 s |
| full N = 630 product (residual check) | 2.9 s |

### Stage A: measured scout (λ_min(R_H) vs T#, no error bounds)

**Approved by the supervisor 2026-09-27 (stage A only).**
N = 360, q = 64, prec 384, sine:16, panels of 1/2 on [0, 525].
Checkpoints T# = 320, 350, 400, 450, 500, 525 (β* = 0.06 ... 0.56; 300 is
dead since 2π e^S = 299.6). Units are t-ranges with checkpoints on their
boundaries: [0,80], [80,160], [160,240], [240,320], [320,350], [350,400],
[400,450], [450,500], [500,525], so 9 units, the largest 160 panels. Each
returns the lower triangles of its partial sums G, C_Ψ, C_H (exact Arb
midpoints plus radii) and writes them to a Modal volume on completion.
Per node ≈ 45 ms (Bessel K = 719, interpolated from the measured 33 and
151 ms) → 67 200 nodes ≈ 3 000 s; products ≈ 1050 × 3 × 0.2 s ≈ 630 s.
**≈ 1.0 core-hour**; largest unit ≈ 10 min. The reduction (sums, LDL,
inverse iteration at each checkpoint) runs locally, under 10 min.

### Stage B: hardened run (only if stage A shows λ_min(R_H(500)) > 0)

N = 500 (harden.py's own tail arithmetic at x = 595: ε_B ≈ 8e-88, against
6.7e+08 at N = 400 and 2e-37 at N = 450), q = 96, prec 384. Bessel cost at
K = 999 interpolated ≈ 100 ms per node: 96 000 nodes ≈ 9 600 s; products
1000 × 2 × 0.9 s ≈ 1 800 s. **≈ 3.2 core-hours.** Needs a fresh approval
after stage A. Plus the final
positivity step on one container, < 0.1 core-hour.

**Positivity step and endpoint (audited after referee REVIEW §5; stage A
showed interval LDL undecided at cond ~1e48, so no interval LDL here).**

1. Ã: the assembled N × N leading block as Arb balls; E_ij := rad(Ã_ij) +
   ε_Q,ij bounds |A_ij − mid(Ã_ij)| for the exact block A.
2. Measure first: midpoint inverse iteration on the N = 500 block gives
   λ_meas (adding modes can only lower λ_min, so stage A's N = 360 value is
   not used). Choose λ₀ = 0.99 λ_meas, an exact dyadic.
3. L̃: 384-bit Cholesky of mid(Ã) − λ₀I, rounded to exact dyadics.
4. Residual in `arb_mat`: Rres = mid(Ã) − λ₀I − L̃L̃ᵀ, every operand exact,
   so Rres is a rigorous ball matrix; r := max_i Σ_j |Rres_ij|, taken as an
   Arb upper bound. Then λ_min(mid(Ã) − λ₀I) ≥ −r (L̃L̃ᵀ ⪰ 0, Weyl).
5. ‖A − mid(Ã)‖₂ ≤ e := max_i Σ_j E_ij (upper bound). Hence
   λ_min(A) ≥ λ₀ − r − e (Weyl).
6. Full space, Zhu (13): λ_min(R_H) ≥ min(λ₀ − r − e, β* − ε_D) − ε_B.
7. **Report only the Arb lower endpoint** of step 6, as an exact dyadic
   and as a decimal rounded down (`harden.py` now does this). Never a
   float(), never a display midpoint.

Acceptance: the endpoint of step 6 is positive. Expected sizes from the
L = 0.8 run and stage A: r ~ 1e-110, e ~ 1e-60, ε_B ~ 1e-87, against
λ₀ ~ 5.7e-48, so each subtraction is 12 or more orders below λ₀; every
term is still written out and subtracted. Before any run, the reducer is
also tested on the L = 0.8 case (N = 96), on Modal, where it must return an
endpoint ≤ the LDL-based 1.158e-17 − ε_B and positive.
Units: 50 containers × 20 panels (10 t-units each), ≈ 6.5 min each.

**Total both stages ≈ 4.2 core-hours, under the 20 core-hour cap.** Wall time
with 10 to 50 parallel containers: under 15 minutes per stage. Dollar cost
not estimated here (Modal's current CPU rate not checked).

### Checkpointing (compute rule 4)

One unit = a contiguous block of panels. Each unit writes, on completion, the
lower triangle of its partial sums (stage A: G, C_Ψ, C_H separately so the
T# curve can be read at every checkpoint; stage B: the single matrix
C_{Ψ+H−β*}) as exact Arb midpoint mantissa/exponent plus radius (≈ 60 bytes
per entry, ≈ 12 MB per matrix at N = 640), and its quadrature-bound
contribution. A restarted unit starts from zero; no unit exceeds 7 minutes,
so preemption costs at most one unit. The reducer sums units in Arb and runs
the positivity step. Memory per container < 1 GB.

### Owner

The session that launches it watches it to a terminal state (compute rule 5).

## Proposed: K2 on Davenport-Heilbronn (`k2_modal.py`), one container

L = (log 47)/2 = 1.925 (DH form negative there, λ ≈ −0.3, even sector, per
`hunts/rogue_frontier/weil_trunc/dhneg_log.md`). H = 0, valid
S_DH = Σ 2|Λ_f(n)|/√n; the job reports the least T# at which any valid β*
could be positive (expected astronomically large, so the valid pipeline
cannot return a bound). Lesion part: λ_min and LDL inertia of R(T#) at
T# = 100, 150 (both past the off-line ordinate 85.7) with β* forced to 0.05,
0.5, 2. N = 150, GL-32, panels 1/2, 256 bits: 9600 nodes × ~8 ms (Bessel
K = 299) ≈ 80 s, products and six N = 150 LDLs ≈ 60 s. **≈ 0.05 core-hour**,
one unit, result written to the volume and to `k2_dh.json`.

## Remote run ledger (Modal, profile teal-sea, 2026-09-27, all apps now stopped)

| app | what | outcome | compute |
|---|---|---|---|
| ap-mucAZVkQ7RThKhLbUB9CuN | stage A: 9 units + first reducer | 9/9 units written to volume `oob-envelope-stages`; reducer ran; one client heartbeat warning | units 2776 container-s (273, 267, 316, 401, 146, 323, 425, 420, 206); reducer ≈ 110 s; wall 535 s |
| ap-u5ihCmzqiW28DuFqefg6Tx | stage A reducer rerun 1 (adds midpoint inertia) | **failed** in seconds: the unit glob matched the reducer's own `stageA_L119_reduced.json` | ≈ 0 |
| ap-G9iIG9H1qGBRi3h6GPtRmj | stage A reducer rerun 2 | success; wrote `stageA_L119_reduced.json` to the volume (read back with `modal volume get`) | wall 154 s |
| ap-WbdVjMHe1JYCD0rXtfV4LO | K2 first launch (18:50:50Z) | **failed**: container import raised IndexError (repo path evaluated inside the container) and **crash-looped** until stopped from the CLI at about 18:59Z. I read the local "Runner failed" as the app being dead and did not check its state; that was the error. Logs: `k2_crashloop_ap-WbdVjMHe1JYCD0rXtfV4LO.log` (8 import tracebacks retrieved) | failed container starts only; upper bound 8.5 min wall, container time not reported by the CLI |
| ap-unujT9tiLNIeJTQf2v1RKm | K2 relaunch (18:53:38Z, under the K2 approval, before the "do not rerun" message) | success; `k2_dh.json` identical to the volume copy | 70 s |

Totals: stage A ≈ 0.85 core-hours (estimate 1.0); K2 ≈ 0.02 core-hour
plus the crash-loop's failed starts (estimate 0.05). Dollar cost not read
from Modal billing. Local log `k2.log` is interleaved: the crash-looping
process kept writing at its old offset into the file the relaunch had
truncated; it contains the successful run's output, but the authoritative
record is `k2_dh.json`. Future launches use a fresh log file per app and
check `modal app list` for the terminal state instead of the local exit.

### Readback of remote outputs (exact grades)

- `stageA_L119_reduced.json` (from the volume). N = 360 leading block of
  R_H, L = 1.19, sine:16, 384 bits, **measured** (no quadrature, tail or
  coupling bound). Midpoint LDL (plain 384-bit, measured): one negative
  pivot at T# = 320, none at 350 to 525. Inverse iteration λ: 1.65e-48,
  4.15e-48, 5.17e-48, 5.776e-48, 6.00e-48 at T# = 350, 400, 450, 500, 525.
  Arb interval LDL: undecided (304 to 306 of 360 pivots) at every
  checkpoint. So there is no enclosure-grade statement about the sign of
  even this block, and none at all about the whole form.
- `k2_dh.json` (volume copy identical). Measured. Valid gate: S_DH = 25.59,
  β* > 0 needs T# ≳ e^25.82, so no bound (inconclusive, as required).
  Forced-β lesion rows: interval LDL undecided in all six; shifted inverse
  iteration at T# = 150, β forced 0.5: λ = −0.288, eigenvector beamed at
  t = 84.5 (76% of |F|² within ±6 of 85.699).

No further Modal run until a separate estimate and approval (K2 rerun,
stage B).

## Stage B (approved by Thomas, 2026-09-27: build, validate, execute)

Code: `stage_b_modal.py` (units + reducer; positivity step 1 to 7 above,
error terms are `harden.py` steps 2 and 3 called verbatim). Plan as
estimated above: N = 500, GL-96, 384 bits, T# = 500, sine:16, 50 units of
20 panels, ≈ 3.2 core-hours.

### Validation on Modal (config `val`, L = 4/5, T# = 100, N = 96, GL-64, 256 bits)

App ap-8ektPW0uhAr2FHdT1Tn6RJ, 2 units (12 s, 18 s) + reducer (1.6 s),
wall 30 s. Result `stage_b_val_result.json` (volume readback).

- Residual route, λ₀ = 0.99 λ_meas: λ_min(R_H) ≥ 1.14675686334e-17
  (exact dyadic stored). r = 3.3e-76, e = 3.7e-42 (row sum of entry radius
  + ε_Q), ε_B = 3.03e-44. λ₀ = 0.9999 λ_meas: ≥ 1.15822443198e-17.
- Consistency: positive, below 1.158e-17 − ε_B (the LDL-proved value), and
  the tight run lies above the referee's 1.1579e-17, below the measured
  λ_meas = 1.15834026601e-17 (referee's midpoint Ritz value
  1.15834026600857…e-17: agrees). The harden.py interval-LDL route on the
  same unit data passes at 1.158e-17 (0 negative, 0 undecided).
- Lesion that discriminates: midpoint Cholesky at 1.01 λ_meas fails
  (negative pivot at index 29) in every row, so the step cannot pass above
  λ_min(mid A).
- Lesions that do NOT discriminate here (recorded, not claimed as passes):
  dropping H or flipping its sign still leaves a positive form at L = 0.8,
  T# = 100 (λ 1.150e-17, 1.141e-17), because H is small in band at this L.
  The H-sign gate remains `envelope_check.py`.

### Stage B run (L = 119/100, T# = 500), terminal

| app | what | outcome | compute |
|---|---|---|---|
| ap-ikiEy2RRqhkbWbVwRYFErU | one-unit measurement, panels 980..1000 | success, 210 s (estimate 6.5 min) | 218 s wall |
| ap-meQWMiDM3O33eRTJRUHoji | 50 units (unit 49 skipped: already on volume) + reducer | success, 50/50 unit files, one client heartbeat warning, no unit failure | units 4849 container-s (max 249 s), reducer 88 s, wall 502 s |

Total stage B ≈ **1.4 core-hours** (estimate 3.2). All three stage B apps
`stopped` in `modal app list`. Result read back from the volume:
`stage_b_result.json`, log `stage_b.log`.

Numbers (all in the JSON as Arb strings or exact dyadics):
β* = 0.511253705003064…, ε_Q,max = 6.9e-66, node shift ≤ 7.3e-113,
e = 2.29e-63, λ_meas = 5.77564879389e-48 (N = 500, GL-96; stage A N = 360,
GL-64 gave 5.775648793894e-48, same to 12 digits), λ₀ = 0.99 λ_meas,
r = 1.42e-113, ε_D = 1.8e-184, ε_B = 1.44e-87.
**λ_min(R_H) ≥ 5.71789230595e-48** (decimal rounded down from the exact
dyadic lower endpoint). Cholesky at 1.01 λ_meas fails (pivot 209), as it
must.

### Negative controls (Modal, 2026-09-27, after stage B)

| app | what | outcome | compute |
|---|---|---|---|
| ap-TtQ0os4EX4HAAgTufDgD97 | `val` rerun with planted in-band lesions, L = 4/5, T# = 100 | success | units 20 s + 23 s, reducer 2 s |
| ap-OuY0B2T8yRU4DsA21MDAIc | `val60`: L = 4/5, T# = 60, where R_H was measured indefinite | success | units 10 s + 10 s, reducer < 5 s |

Results read back from the volume: `stageBval2_L08_result.json`,
`stageBval60_L08_result.json`. Total ≈ 0.02 core-hours.

- **T# = 60 negative control fires.** β* = 0.6845 > 0 there, so the valid
  gate is open, yet the positivity step returns no bound: the midpoint
  Cholesky of A itself breaks (pivot 19, −1.07), and the harden.py
  interval LDL on the same data finds exactly one negative eigenvalue
  (0 undecided). This matches the measured indefiniteness at T# = 60 in
  `run_L08_N200.json`. So the step does refuse a form that is truly
  indefinite, with every error term in place.
- **Planted in-band constant (−2e-17 · G) fires**: no bound (pivot 19).
- **Planted in-band cos(0.95·2L·t), amplitude ±1e-16: does not
  discriminate.** λ moves in the 12th digit. The amplitude is too small
  against the form's floor; recorded, not claimed as a pass.
- Main row reproduced bit for bit (≥ 1.14675686334e-17 at 0.99 λ_meas;
  ≥ 1.15822443198e-17 at 0.9999).

## Odd sector, 2026-09-28: authorized four-core-hour task

Owner: this foreground Codex session, branch teal-sea/oob-odd, starting
46c896b0. Thomas explicitly authorized validation and main run, Modal only,
4 core-hours total, local edits and tiny checks only, no push. This supersedes
older HOLD text for this odd task alone. Writes remain in numerics: new
filenames contain odd; existing RUNS/RESULTS/PROGRESS are append-only.

Runner: stage_b_odd_modal.py. Derivation: odd_derivation.md. The original
even runner and theory inputs remain untouched. Every checkpoint records
SHA-256 of runner, assemble.py, harden.py and envelope.json; the reducer
refuses a mismatch. Odd tags are isolated from even checkpoints.

Pre-validation estimate from the even measurement (N=96, 200 panels,
2 units in 30 core-seconds): N=200, 300 panels scales conservatively as
30*(200/96)^2*(300/200)=196 core-seconds, plus 30 s for the reducer and
pole-sign control. Allow 0.10 core-hour for Zhu, 0.05 for envelope validation
and low-T control. Actual timings replace these estimates below.

Zhu gate: L=4/5, T#=150, H=0, N=200, GL-64, 256 bits, h=1/2, six units.
The source uses 200 odd modes and reports 9.1183e-15 measured, with a lower
bound 8.2065e-15. The runner blocks later configurations unless the measured
value agrees to 1 percent and the enclosed lower endpoint is positive.
Next: val at L=4/5, T#=100, sine:16, N=96; val40 is a prospective negative
control, not presumed to be indefinite. Wrong pole sign must raise the
measured floor. A failed approximate pivot is followed by a ball-enclosed
Rayleigh witness, so a refusal alone is not called proof of indefiniteness.

Main remains N=500, T#=500, GL-96, 384 bits, h=1/2, 50 units. Only after
validation, time unit 49 on Modal and multiply by 50, add validation and
reducer allowance, then append that estimate BEFORE launching the main job.
No detached apps, retries disabled, at most 12 one-CPU unit containers.
Each unit checkpoints to oob-envelope-stages; reducer has one CPU.

Tiny local check (1.1 s): first three odd Legendre modes, direct Fourier
and sinh integrals, orthonormality, double factorial indices and actual
cut ratios pass. Maximum measured direct-integral defect 1.02e-56 at 55 dps.
All four configurations have both tail ratios below one (largest 0.08807).
The exact checks and measured checks are distinguished in check_odd.py.

### Odd Zhu validation, terminal

App ap-uvTBLRYDv5KdLXmzacpTWr, command:
`modal run hunts/oob_envelope/numerics/stage_b_odd_modal.py --cfg zhu`.
Six units 111.432 core-seconds, reducer 9.186 s; app wall 48 s.
Volume readback odd_zhu_result.json; app confirmed stopped.
Measured 9.11833845450e-15, source 9.1183e-15 (ratio 1.0000042173).
Lower endpoint rounded down 9.02715506995e-15, above source 8.2065e-15.
Wrong positive pole gives 6.40880126462e-10, a measured 70284.75-fold
increase. The sign-direction check fires; positivity does not reject this
wrong sign, as expected since it adds a positive rank-one matrix.
The 1.01-times overshift is refused in both rows.

### Odd envelope validation and negative control, terminal

val: app ap-Lfjwjx0GIZ20PL1zZkL1AI, units 36.802 core-seconds, reducer
1.781 s, wall 34 s; odd_val_result.json. Measured 9.50644182948e-15;
lower endpoint 9.41137741118e-15. Wrong positive pole raises the measured
floor to 7.36487811883e-10. Drop-H and flip-H stay positive
(9.40521108856e-15 and 9.28959833914e-15), so these lesions do not
discriminate at this window. The 1.01 overshift fails in all four rows.

val40: app ap-mHTe5wmfzkcIiwJ9nSWS4c, units 11.322 core-seconds, reducer
2.199 s, wall 21 s; odd_val40_result.json. The valid beta gate opens,
but the main head is indefinite: a Schur witness has enclosed Rayleigh
upper endpoint < -1.35054e-7 after quadrature error. No positive endpoint
is returned. All three altered forms also fail, with enclosed negative
witnesses. Their witnesses differ, so these values are not eigenvalue
comparisons; the JSON pole comparison is unevaluated (null ratio) here.
Both apps confirmed stopped. Validation total is below 0.05 timed core-hour.

Next authorized run is ONLY main unit 49 (panels 980:1000). The even run
timed that unit at 210 s; reserve 300 s for the odd pilot, then estimate
the complete run from its actual duration before proceeding.

### Odd main run estimate, written before launch

Pilot app ap-ng9DiaREARkLBjGwtAMuO1 completed and stopped: unit 49,
panels 980:1000, 223.455382 core-seconds, 229 s app wall. Checkpoint is already
on the volume and will be skipped by the complete run.

Conservative extrapolation: 50 * 223.455382 = 11172.769 core-seconds for all units
(including the pilot once), plus 172.723 validation core-seconds, 180 s for
the reducer, and 300 s startup/serialization allowance = 3.285 core-hours.
This is below the authorized 4.0 core-hours. No parameter changes: N=500,
T#=500, sine:16, GL-96, 384 bits, h=1/2. Launching all remaining units and
the reducer in one foreground app, watching checkpoints and stopping the
app at terminal state. Invocation:
`modal run hunts/oob_envelope/numerics/stage_b_odd_modal.py --cfg B`.
No claim yet about the main odd eigenvalue or lower endpoint.

### Odd main run, terminal and read back

App ap-OlmaObfN0y2EzyA3R6lFcm, foreground, source runner from 93f1fc6;
launch commit 710b7a8. All 50 units present, including skipped pilot unit 49.
Units total 5134.263733 core-seconds, including the pilot exactly once;
reducer 128.776208 s; main app wall 649 s. Two client heartbeat timeouts
were logged, with no unit failure, retry or restart. Longest unit 253.664 s.
Result downloaded from volume oob-envelope-stages, path
odd_stageB_L119_v1_result.json, to odd_main_result.json. All source/input
hashes match the local files. The original even runner is unchanged.

Result: measured lambda_min 3.46316654753e-44; full odd-space lower endpoint
rounded DOWN 3.42853488205e-44. The exact dyadic lower endpoint is in JSON.
The 1.01-times overshift fails at pivot 179. Numerical step is
single-route enclosure-carrying; the complete fixed-window claim is a
candidate pending independent reproduction, including its ordinary reduction.

Total task compute: 5435.763058 timed one-CPU function-seconds =
1.509934183 core-hours, versus the 3.285 estimate and 4.0 allowance.
This timer excludes checkpoint serialization/commit and container startup.
For a conservative budget check, sum each app's entire lifetime times the
maximum possible one-CPU containers in that app: 51*7 + 40*4 + 30*4 +
236*2 + 655*14 = 10279 core-seconds, or 2.855277778 core-hours. This even
counts idle gate containers and non-overlapping reducers simultaneously.
All five owned apps have state stopped and zero tasks, recorded in
odd_apps_terminal.json. No billing dollar estimate or invoice was queried.

Post-run checks: 50 distinct panel blocks; source SHA-256 matches for all
four reducers; positive decimals do not exceed exact rational endpoints;
all positive main rows refuse the 1.01 overshift; even and odd L/H match;
odd endpoint exceeds even endpoint. Source/doc/JSON whitespace check passes.
Raw CLI logs retain their emitted whitespace. No broad local numerical
suite was run: local work was edits, compilation, tiny formula and artifact
checks. No push. A computation manifest records the result and artifact hashes.
