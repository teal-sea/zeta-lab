# RUNS: estimates written before launch

Machine: operator laptop (M-series, 16 GB). Every run is single-process,
under 10 minutes, under 1 GB, checkpointed per unit (resumable).

| run | unit cost (measured) | units | estimate | actual |
|---|---|---|---|---|
| `repro.py` | 0.03-0.8 s per cell | 19 cells | < 30 s | 5.5 s |
| `transport.py dh 64` | ~0.4 s per c incl. pairs + HF | 49 c | ~30 s | 22 s |
| `transport.py dh 128` | ~1.3 s per c | 49 c | ~70 s | 74 s |
| `transport.py zeta 64` | ~2 s per c | 49 c | ~2 min | 74 s |
| `transport.py zeta 128` | ~8 s per c (prec 900, HF at 1600) | 49 c | ~7 min | 241 s |

Unit costs from 2-5 cell smoke runs in the scratchpad (DH N=128 c in
[30, 30.25]: 5 s for 5 c; zeta N=128 c in [30, 30+1/16]: 4.9 s for 2 c).
| `crossing.py 64 96 128 192 256` | 13 eigen-solves + 3 ball LDL per N; ~0.5 s (N=128) to ~5 s (N=256) per solve | 5 N | ~3 min | 129 s |
| `edge.py dh` | ~0.5-4 s per cell | 24 cells | ~1 min | 30 s |
| `edge.py zeta` | ~1 s (N<=128) to ~60 s (N=256, HF at 3600 bits) per cell | 18 cells | ~6 min | 171 s |
| `harden.py dh 64`, `dh 128` | Temple + ball LDL per cell, 0.2-0.7 s | 98 cells | ~1 min | 8 s + 32 s |
| `harden.py zeta 64`, `zeta 128` | build at 1600 bits + LDL, ~1-3 s per cell | 98 cells | ~3 min | 28 s + 104 s |
| `precision_check.py` | 3 recomputations per cell at up to 2x precision, zeta N=128 HF at 3200 bits dominates | 4 cells | ~3 min | 27 s |
| `factA_check.py` (N' ladder 64..384) | one build at c' per rung, 0.1-6 s | 14 rungs | ~30 s | ~15 s |
| `factA_check.py` extra rungs N' = 512, 768, 1024 (DH) | build ~N'^2 entry calls at 400 bits; ~10-60 s per rung, < 1 GB | 3 rungs | ~2 min | |
| Task A `epstein_scan.py 64`, `128` (handoff from theory, 2026-09-23) | Epstein (1,1,6) both sectors at 400 bits: probe (c = 47, N = 128) 3.2 s for two sectors with double assembly; one assembly per cell, ~1.5 s (N=128), ~0.5 s (N=64) | 93 c in [2, 48] step 1/2 | ~1 min + ~2.5 min | 57 s + (N=128 running, ~4.5 s per cell: ~7 min) |
| Task A `epstein_crossing.py` | bisection to 2^-10 per (N, sector), ~13 solves + 2 ball LDL | <= 4 (N, sector) | ~1 min | |
| Task B `zeta_pole.py 64`, `128` | zeta at 900 bits + ball LDL at 1600: first run 1.4 s per cell (N=64); mu_1 by approximate spectrum adds ~0.3 s (N=64), ~2.3 s (N=128) | 117 c in [2, 60] step 1/2 | ~3 min + ~10 min (N=128 in two resumable runs under the 580 s guard) | 164 s (first N=64 run, mu_1 defect: rerun), rerun ~200 s; N=128 580 s (guard) + ~150 s |
| Task A control `epstein_scan.py 64 dedekind` | same as Epstein N=64 | 93 c | ~1 min | 59 s |
| Task A `epstein_offline.py` (box count [0.51,1.3]x[14,20] + findroot) | epstein_completed 1.1 s per evaluation at dps 20; ~100-200 boundary samples; findroot ~20 evaluations per seed | 1 box, <= 4 seeds | ~5 min | 242 s + 16 s |
| Task A `epstein_offline.py` lower boxes [0.51,1.3]x[0.5,7] and x[7,14] (two runs) | as above, perimeter ~15 each | 2 boxes | ~4 min each | 159 s, 273 s |
| Task A `epstein_crossing.py` | as estimated above | 4 (N, sector) | ~5 min | ~4 min |
| Task B `zeta_pole_fixup.py 128` (ball LDL at 3200 bits where 1600 was inconclusive) | one build at 3200 bits + two LDL, ~8-10 s per cell | 55 cells | ~8 min, two resumable passes | one pass, under the 580 s guard |
| Task A `epstein_mu2_cross.py` (bisect the pole-free even second eigenvalue's zero on [29, 29.5]) | one Epstein assembly + ball LDL per step, 0.5 s (N=64) to ~3 s (N=128) | 2 x 10 steps | ~1 min | < 1 min |

Both handoff tasks sit under the 10-minute, few-GB local limit, so no CI
proposal is needed for them.

The first launch of the four transport runs used `timeout`, which macOS does
not ship, and zsh did not word-split the loop variable: nothing ran (exit
127, 0 s). Relaunched under bash with `perl -e 'alarm 580; exec ...'` as the
per-run guard.

## Proposed CI job (not run locally): boundary-adapted window ground states

Written 2026-09-23 at the supervisor's request; RESULTS s7 names it. It
must not run on the laptop.

**The exact question.** Does the continuum ground state of the window Weil
form have a boundary amplitude A(L) that is the same in three different
Galerkin families, such that dλ/dL = −K·A(L)² with one constant K shared
by zeta and DH? The band-N edge law (RESULTS s4 row 7, s5) cannot answer
it: there κ drifts with N and μ₀ → 0 slowly, so the split between them is
basis-dependent and only dλ/dL is invariant. Theory s5 already reads
μ₀²/λ as a reformulation, so this job does not estimate that ratio. It
asks whether the boundary object theory would have to bound exists at all.

**Families**, all from the validated weil_trunc assembly, with no new
closed forms:
- m = 0: V_N(c) itself.
- m = 1: its subspace μ₀ = 0, one Householder reflection. The function
  vanishes at the edge.
- m = 2: μ₀ = μ₂ = 0, two reflections. It also vanishes to second order.

Each constraint is a fixed linear functional of the coefficient vector,
independent of L, so the Hellmann-Feynman derivative is the unconstrained
one evaluated on the embedded vector. Each family is dense in the form
domain, so all three converge to λ_∞(c) (ordinary argument, unreviewed).

**One unit** = one (kind, c, N, m) cell: assembly, projection, the lowest
two eigenpairs by inverse iteration, the HF derivative (two more
assemblies), and the edge profile f(y) at y = L·2^-j, j = 4..12.

**Measured units** (`ci_unit_probe.py`, `ci_unit_probe.json`, m = 1,
c = 30.5):

| kind, N, precision | assemble | project | eigen | HF | total |
|---|---|---|---|---|---|
| DH, 256, 600 bits | 0.31 s | 0.07 s | 3.05 s | 0.82 s | 4.3 s |
| DH, 512, 600 bits | 0.74 s | 0.29 s | 17.9 s | 2.45 s | 21.4 s |
| zeta, 256, 2000 bits (HF 3600) | 2.64 s | 0.22 s | 16.4 s | 17.7 s | 37.0 s |

The eigen stage scales as N^2.55 (256 → 512), and precision costs about
p^1.6.

**Multiplied estimate.**

| part | grid | units | per-unit cost (extrapolated) | total |
|---|---|---|---|---|
| DH | c ∈ {13.5, 20.5, 29.5, 30.5, 31.5} × m ∈ {0,1,2} × N ∈ {256, 384, 512, 768, 1024}, 600 bits | 75 | 4 s, 11 s, 21 s, ~60 s, ~115 s (sum ~210 s per (c, m)) | ~53 min |
| zeta | c ∈ {13.5, 20.5, 30.5} × m ∈ {0,1,2} × N ∈ {256, 384, 512}; 2000 / 3000 / 4000 bits, HF at 1.8× | 27 | 37 s, ~150 s, ~480 s (sum ~670 s per (c, m)) | ~100 min |
| **total** | | 102 | | **~2.6 runner-hours** |

Zeta at N = 1024 would need about 6000 bits and roughly an hour per unit,
so it is left out; zeta saturates at c = 13.5 and 20.5 by N = 256 (s5).

**Layout.** A GitHub Actions matrix of 24 jobs, one per (kind, c, m),
with a 60-minute timeout each. The longest slice, a zeta N-ladder, is
~11 min. Standard runners are free here and not preempted. Setup:
`pip install -r requirements.txt && pip install -e .`, then a driver
`ci_edge_job.py KIND C M` that loops over N (to be written from
`ci_unit_probe.py`; it is the same unit).

**Checkpointing.** Per unit: each finished (N) row is written to
`ci_edge_<kind>_<c>_<m>.json` by atomic replace, and completed rows are
skipped on restart. Each job uploads its JSON as an artifact on success
and on failure (`if: always()`), so a cancelled job keeps every finished
unit.

**What each result means.**
- **Door open:** for each (kind, c), the three families' λ and dλ/dL
  converge to common limits (N-extrapolation). The edge profiles also
  converge to a common shape with a nonzero fitted amplitude A(L), and
  K = −(dλ/dL)/A² agrees across m within 10% and across zeta and DH
  within their N-drift. Then a basis-independent edge law exists and
  theory has a well-defined boundary quantity to bound with the Euler
  product.
- **Kill (close this door, no follow-up job):** λ and dλ/dL converge to
  the same limits in every family, while the fitted amplitude of the
  constrained families goes to 0 with N, or the families' edge profiles
  disagree at the finest N beyond fit error. The continuum ground state
  then has no finite boundary trace. The edge law is a band-N
  representation only, and "bound the boundary trace by the margin" has
  no object to bound.
- **Neither, reported as found:** K differs between zeta and DH by more
  than the N-drift. The law is then not universal, which is itself worth
  handing to theory.

**Grade of what it can produce:** measured (ball Rayleigh upper bounds,
float fits of the edge profile). No positivity claim, and no RH claim.
