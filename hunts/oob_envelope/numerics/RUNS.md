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

N = 360, q = 64, checkpoints T# = 300, 350, 400, 450, 500.
Per node ≈ 45 ms (Bessel K = 719, interpolated) → 64 000 nodes ≈ 2 900 s;
products ≈ 1000 × 2 × 0.4 s ≈ 800 s. **≈ 1.0 core-hour.**
Units: 10 containers × 100 panels (50 t-units each), ≈ 6 min each.

### Stage B: hardened run (only if stage A shows λ_min(R_H(500)) > 0)

N = 640, q = 96, prec 384. 96 000 nodes × 0.155 s ≈ 14 900 s; products
1000 × 2 × 1.4 s ≈ 2 800 s. **≈ 4.9 core-hours.** Plus the final
positivity step on one container: LDL in Arb, or, if interval LDL radii blow
up at cond ~1e47, a midpoint Cholesky with an Arb residual (Zhu Lemma 5.2) in
a few 640³ products: < 0.1 core-hour.
Units: 50 containers × 20 panels (10 t-units each), ≈ 6.5 min each.

**Total both stages ≈ 6 core-hours, under the 20 core-hour cap.** Wall time
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
