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
