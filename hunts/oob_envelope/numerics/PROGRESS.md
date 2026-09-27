# numerics PROGRESS (oob_envelope)

K2 on Modal approved by the supervisor (one container, ~0.05 core-hour, as
in `RUNS.md`); QUESTION cleared. Stage B remains unapproved.

Stage A on Modal approved by the supervisor 2026-09-27 (stage A only; stage
B needs a fresh approval after A). QUESTION cleared. Interim `RESULTS.md`
written for the referee.

Worker: Claude Code, Opus. Branch `teal-sea/oob-cert`. Writes only in
`hunts/oob_envelope/numerics/`. Local runs capped at 10 min and 2 GB.

## Status

| phase | state | grade reached | rests on |
|---|---|---|---|
| 1. H with enclosures, L = 0.8, 1.0, 1.19 | done (separable); joint LP/SDP not done | enclosure-carrying | `envelope.json`, ca41ce2 |
| 2a. K3 orthogonality | done, passes, lesion breaks it | measured (float64) | `k3.json`, commit after f1696cd |
| 2b. L = 0.8 replication with H | done | leading block + all Zhu error terms enclosure-carrying; Q ≥ R_H step is ordinary derivation (theory lane) | `harden_L08_T100_sine16*.json` |
| 3. L = 1.19 | stage A approved, starting | estimate | `RUNS.md`, `unit_cost.out` |
| 4. K2 on a rival without Euler product | not started (after phase 3 answer) | | |

### Phase 2 result at L = 0.8, stated with its grade

- **K3 (measured, float64, `k3.py`).** For 3 random smooth even f at
  L = 0.8 and 1.19, every H frequency (all k log p with k > m_p) gives
  (1/π)∫|F|² cos(λt) ≤ 5e-13 relative to ‖f‖² (the truncation floor), and the
  whole H gives ≤ 3e-13. Planted in-band frequencies m_p log p reproduce the
  time-domain autocorrelation g(λ) to 10 digits (nonzero, up to 0.14). Lesion:
  one H term moved to 0.95·2L breaks the identity by exactly the predicted
  b·g(0.95·2L). The in-band/out-of-band split itself is decided in Arb
  (`envelope.py`, gaps logged per prime).
- **Hardened leading block with all Zhu error terms (`harden.py`).**
  L = 0.8, T# = 100, envelope sine:16 (S = 1.5552528467, enclosure-carrying),
  β* = 1.2020, N = 96, GL-64 on panels of 1/2, 256-bit Arb:
  quadrature radius (Bernstein ellipse ρ = 1 + √2, rectangle bounds for
  Bessel, cosine and digamma) ≤ 5.8e-44 per entry, added to every entry;
  node-shift term included; tail ε_D ≤ 2.8e-95; coupling ε_B ≤ 3.0e-44
  (Schur test); Arb LDL of A − λ₀I passes at λ₀ = 1.158e-17 and provably
  fails at 1.1585e-17. Hence λ_min(R_H) ≥ 1.158e-17 on all of L²_even[−0.8, 0.8]
  (Zhu (13)). **K1 holds**: 1.158e-17 < 2.27e-17, and below the measured
  window floor 1.656e-17.
- **Same pipeline, Zhu's own configuration** (H = 0, T# = 200, N = 200):
  λ_min(R) ≥ 1.02e-17, provably < 1.028e-17; his published λ₀ = 9e-18 also
  passes. Calibration of the hardened pipeline.
- **What Q ≥ 1.158e-17 ‖f‖² additionally rests on:** Q ≥ R_H, i.e. Zhu's
  Theorem 1.1 with A_L replaced by S and H added in band [0, T#]. That is an
  ordinary derivation (theory lane RESULTS §1, self-reviewed, no referee
  yet). So the composite statement is a **candidate**, weakest step an
  unrefereed ordinary derivation; the numerical steps are enclosure-carrying.
  It sharpens Zhu's constant (8.9e-18) at the same support 1.6 with half the
  matrix; it is not a new support.
- **Measured-only numbers** (no quadrature/tail/coupling bound): the whole
  λ_min(R_H) vs T# table in the log below and the N scan.

Not done, optional: theory §1.7's sampled B_T at L = 0.8, T = 30..70.

## Log

- 2026-09-27. Read MISSION, AGENTS, BRIEF, the seed probes, and Zhu
  arXiv:2608.24827v2 sections 1 to 5 and 7 (pdf fetched to scratch, not
  committed). Plan for phase 1: per prime, build the Fejér-smoothed
  Carathéodory-Toeplitz correction in float, freeze its out-of-band
  coefficients as exact dyadic rationals, raise `M_p` by a small margin, and
  prove `Φ_p = M_p − φ_p + h_p ≥ 0` on `[0, π]` by adaptive Arb evaluation
  with a second-derivative remainder. The float construction is only a
  proposal: the enclosure step checks the explicit trigonometric polynomial,
  so nothing depends on the float roots or weights being accurate.
- 2026-09-27. **Phase 1, separable constant: done (enclosure-carrying).**
  `envelope.py` (134 s, 256-bit Arb), raw data `envelope.json`. Per prime,
  `Φ_p = M_p − φ_p + h_p ≥ 10^-8` is proved by an exact decomposition into a
  nonnegative kernel sum plus an Arb-bounded residual, and independently by an
  adaptive θ-scan with a third-derivative remainder; both pass for every row.
  Prime sets and `m_p` decided in Arb. The sine (Fejér-Korovkin) kernel
  converges like 1/D², the Fejér kernel like 1/D; Fejér D = 64 reproduces the
  seed probe (1.5493, 3.0273, 3.8385).

  | L | A_L | S_inf (float) | S sine D=16 | S sine D=64 | S sine D=128 | max freq D=128 |
  |---|---|---|---|---|---|---|
  | 0.8 | 2.94197 | 1.52205 | 1.55525 | 1.52450 | 1.52268 | 140.6 |
  | 1.0 | 5.85247 | 2.97730 | 3.03295 | 2.98139 | 2.97835 | 249.1 |
  | 1.19 | 7.07501 | 3.76708 | 3.86348 | 3.77417 | 3.76891 | 249.1 |

  Joint LP/SDP (stretch) deferred until phase 2 shows whether the envelope
  threshold is the operating point at all (the reduced form may go negative
  well above it).
- 2026-09-27. **Phase 2, L = 0.8 curve, N = 200 (measured).** `assemble.py`,
  256-bit Arb throughout (no float64 anywhere in the matrix), GL-32 on panels
  of width 1/2, one pass with cumulative sums. `run_L08_N200.json`. The Arb
  radii below are radii of the assembled *quadrature-rule* matrix: quadrature
  error, Legendre tail and two-block coupling are **not** bounded yet, so every
  number here is measured, not a bound on Q.

  Calibration against Zhu (H = 0): λ_min(R_150) = 1.3564e-18 (Zhu 1.356e-18),
  λ_min(R_200) = 1.0277e-17 (Zhu: ≥ 9e-18 enclosure-carrying). K1 check: every
  value below is ≤ 1.43e-17 < 2.27e-17, and below the window floor 1.656e-17.

  | T# | β* (H=0) | λ_min H=0 | λ_min sine16 | λ_min sine32 | λ_min sine64 | neg. eigenvalues with H |
  |---|---|---|---|---|---|---|
  | 40 | <0 | n/a | 6.7e-17 | 9.7e-17 | 1.1e-16 | 3 |
  | 50 | <0 | n/a | 2.2e-17 | 3.9e-17 | 4.8e-17 | 2 |
  | 60 | <0 | n/a | -3.4e-18 | -1.6e-18 | -1.2e-18 | 1 |
  | 65 | <0 | n/a | 1.23e-18 | 2.00e-18 | 2.20e-18 | 0 |
  | 70 | <0 | n/a | 4.53e-18 | 4.85e-18 | 4.93e-18 | 0 |
  | 80 | <0 | n/a | 8.06e-18 | 8.23e-18 | 8.28e-18 | 0 |
  | 100 | <0 | n/a | 1.158e-17 | 1.163e-17 | 1.162e-17 | 0 |
  | 120 | -0.001 | n/a | 1.253e-17 | 1.259e-17 | 1.261e-17 | 0 |
  | 150 | 0.224 | 1.356e-18 | 1.338e-17 | 1.343e-17 | 1.345e-17 | 0 |
  | 200 | 0.513 | 1.028e-17 | 1.419e-17 | 1.422e-17 | 1.423e-17 | 0 |

  (At T# ≤ 50 the listed λ is the eigenvalue nearest 0, not the minimum; the
  LDL inertia count is the decisive column.) Reading: the envelope threshold
  (T# ≈ 30) is not the operating point, as theory warned: R_H is indefinite
  up to T# = 60 and positive from T# = 65. With H the reduced form at T# = 100
  already beats Zhu's T# = 200 floor. Next: K3, then the smallest N that
  holds λ_min at T# = 65 to 80, then the hardened budget.

  Implementation traps met (both fixed, both would have been silent in
  mpmath): arb's Bessel J at large order needs +512 bits of working
  precision, and it amplifies an input radius by about e^x, so the Bessel
  argument is snapped to an exact dyadic and the node shift (~1e-77) is
  recorded for the error budget.
- 2026-09-27. K3 passes (details in Status). N scan at L = 0.8, sine:32
  (measured): N = 32 reproduces N = 200 to all digits for T# ≤ 70, N = 40 for
  T# ≤ 100. Hardened bounds need more (2N ≈ 2.4 x) because Zhu's tail bound
  x^n/(2n+1)!! is crude near n ≈ x.
- 2026-09-27. Hardened L = 0.8 results (Status). Two more implementation
  traps met: acb digamma returns nan on wide boxes (replaced by a
  center-plus-derivative bound, checked against a grid), and at L = 1.19
  sizes arb's Bessel J needs up to ~1400 bits at order 1259.5 (seed call now
  retries with more bits until the ball is relatively tight; the L = 0.8
  hardened run reproduces unchanged after the fix).
- 2026-09-27. Phase 3: unit costs measured, estimate in `RUNS.md`, QUESTION
  at top. Stopped.
- 2026-09-27. Advisor-requested gates added. `envelope_check.py`: the sign
  of H in the matrix code path is right (Ψ + H above the envelope at 4000 Arb
  points and a 1.2M-point grid; flipped-H and S → S_opt lesions fire), and
  `harden.py` now asserts the quadrature radius is inside every LDL entry.
  Stage B shrinks to N = 500 (tail arithmetic). Stage A approved.
- 2026-09-27T18:43:33Z. **Stage A launched on Modal** (supervisor-approved,
  stage A only): app ap-mucAZVkQ7RThKhLbUB9CuN, 9 units, volume
  `oob-envelope-stages`, tag `stageA_L119`, log `stage_a.log`. This
  session owns it and watches it to a terminal state. Routing rule received:
  no compute on Ghost from now on; the reducer runs on Modal too.
