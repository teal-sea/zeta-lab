# numerics PROGRESS (oob_envelope)

Worker: Claude Code, Opus. Branch `teal-sea/oob-cert`. Writes only in
`hunts/oob_envelope/numerics/`. Local runs capped at 10 min and 2 GB.

## Status

| phase | state | grade reached | rests on |
|---|---|---|---|
| 1. H with enclosures, L = 0.8, 1.0, 1.19 | started 2026-09-27 | none yet | |
| 2. K3, then L = 0.8 replication with H | not started | | |
| 3. L = 1.19 cost estimate, then stop and ask | not started | | |
| 4. K2 on a rival without Euler product | not started | | |

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
