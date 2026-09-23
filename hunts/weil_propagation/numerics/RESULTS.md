1. **Found:** no transport quantity measured here breaks where DH turns negative: the zero-extended DH ground state continues smoothly (1 − overlap ≤ 2e-7 per unit c on 29 ≤ c′ ≤ 31.5, i.e. through the crossing at c ≈ 30.65), the arch/prime split of dλ/dL is smooth, and dλ/dL ≈ −κμ₀² (μ₀ the band-N edge amplitude, κ = O(1) but basis-dependent) holds straight through the crossing.
2. **Found:** DH's continuum Weil form is negative on every window c ≥ 30.617188 (hardened cell (30.617188, N = 256) plus nesting), strictly between the coefficients n = 30 and 31, so positivity is lost with no new arithmetic term entering; c*(N) = 30.818, 30.696, 30.647, 30.629, 30.617 for N = 64..256, extrapolating to ≈ 30.61.
3. **Grade:** crossing brackets, zeta controls and all 196 grid eigenvalues are hardened (ball Rayleigh quotients, ball LDLᵀ, Temple); the continuum consequences add a two-line nesting argument (ordinary, unreviewed); transports, decompositions, the edge law and the zero-side split are measured.
4. **What refutes it:** of my seven candidates (s4), five hold for DH across 30 → 31, one is false for DH, one fails at finite N, so none is a mechanism; and the theory worker's C2 ("Markov + one pole") is refuted by Epstein (1,1,6), whose form is negative on every window c ≥ 27.7417 although Λ_Q ≥ 0 below 48, with its off-line zero 0.953 + 16.290i located independently and the Dedekind control positive (s9, hardened).
5. **Next step:** whatever keeps zeta positive is more than Λ ≥ 0 plus a pole: Epstein's even pole capacity fails at c = 29.304 and C2's condition (a) at 29.318, while zeta holds (a) with μ₂/λ₂ ≈ 0.64 on c ∈ [5, 60] (s9.4), and the Epstein/Dedekind pair points at prime-power support (s9.3); theory should find what in the Euler product pins that ratio, or bounds the ground state's boundary trace (band-N proxy μ₀) by its margin; one numerics job is worth funding (boundary-adapted basis, s7).

# RESULTS: ground-state transport across window size (numerics worker)

Worker: numerics, branch `teal-sea/weil-propagation`, 2026-09-23. Scope and
kill-control: `../MISSION.md`, brief: `BRIEF.md`. Nothing here is a claim
about RH. Every number quoted is in a JSON beside this file; `summary.json`
collects the quoted ones (`summarize.py`).

## 0. Setup and the two exact facts everything leans on

Assembly: imported unchanged from `hunts/rogue_frontier/weil_trunc`
(`enclosures.BallTruncation`, Arb; `galerkin.Truncation`, mpmath). Even
sector throughout (the sector where DH goes negative). Window parameter c is
an exact dyadic rational, so fractional windows mean the same thing in both
assemblies (checked, s1). Ground pair: inverse iteration on the midpoint
matrix, then every number about the resulting exact vector (Rayleigh
quotient, residual, overlaps, energies) in balls. Helpers: `wp_common.py`.

**Fact A (window-free form).** The truncated form at window c on
L²[0, L], L = log c, is the restriction of one window-independent quadratic
form, Q(f) = W(f ⋆ f̃), where W is the explicit-formula functional (pole,
archimedean, and −Σ Λ(n) n^{-1/2}(g(log n) + g(−log n))). The truncation
only reflects that g = f ⋆ f̃ is supported in [−L, L], so only n ≤ c
contribute. Q is translation invariant. This is how the construction is
defined (weil_trunc `SOURCE.md` s2; DH: `THEOREM_FEASIBILITY.md` OBL-3).

**Fact B (nesting).** Extension by zero embeds L²[0, L] in L²[0, L′]
isometrically and Q-preservingly for L < L′, and the band-N space V_N(c)
sits inside L²[0, L]. Hence, with λ_∞(c) the infimum of Q/‖·‖² over the
whole window:

    λ(c, N) ≥ λ_∞(c) ≥ λ_∞(c′)   for all c′ ≥ c and all N,
    λ(c, N) is nonincreasing in N at fixed c.

Two lines, ordinary argument, not externally reviewed. Consequence used
below: a hardened negative cell (c, N) proves λ_∞(c′) < 0 for every
c′ ≥ c. It also fixes the direction of the problem: positivity is
inherited *downward* in window size for free, and a propagation mechanism
has to go against that.

The two transports measured (both isometries of L²):

- **Zero extension (ZE)**, centred: f unchanged, placed in the larger
  window. Q-preserving exactly (Fact A). Its entire transform F_v on the
  real line is literally unchanged (up to the L^{-1/2} normalisation), so
  ZE is the "common entire-function space" of the brief. In band-N
  coordinates the transported vector is the projection w = Gᵀv onto
  V_N(c′), G the closed-form centred Gram matrix (`gram_zero_ext`).
- **Dilation (DIL)**: the same coefficient vector read in the c′ basis,
  f ↦ √(L/L′) f(·L/L′). This is the Galerkin-natural map and the one in
  which "archimedean change / new prime-power terms / rescaling" is a
  meaningful split. It rescales F_v(z) → F_v(zL′/L) up to normalisation,
  moving the real zeros of F_v off the ordinates they were tuned to.

## 1. Task 1: reproduction (`repro.py`, `repro.json`)

| check | cells | result |
|---|---|---|
| recorded λ_min, read from weil_trunc JSON (not retyped) | zeta (6,32), (13,4/8/16/32), (29,32), (31,60); DH (13,32), (29,32), (29,128), (30,128), (31,59), (31,60), (31,128) | all 14 agree to ≤ 4.3e-22 relative (the recorded strings carry ~22 digits); Temple/LDL bracket conclusive at every cell |
| independent route: mpmath assembly + `mp.eigsy` vs Arb route | zeta (13,8), (61/2,16); DH (13,16), (61/2,24), (497/16,32) | agree to ≤ 3.8e-22 relative, including the three fractional windows the record never used |

Hardened: the recorded signs and magnitudes, and that fractional c is
handled identically by both assemblies. New cell on the way: zeta
λ_min(31, 128) = 2.8557147127e-141 (Temple bracket at LDL precision 1600
bits; at 900 bits the ball LDL stalls at pivot 67, recorded as the reason
`ldl_prec` exists).

## 2. Task 2: transport on a fine c-grid (`transport.py`, `grid_*.json`)

Grid c ∈ [29, 32] step 1/16 (49 windows), N ∈ {64, 128}, zeta and DH; pairs
(c, c + h) for h ∈ {1/16, 1/4, 1}. Every DH grid λ carries a Temple bracket
whose LDL step also proves it is the minimum (`harden.py`), zeta and DH alike: all 196 cells conclusive.

| quantity, over pairs with c′ ≤ 31.5 | DH N=128 | DH N=64 | zeta N=128 | zeta N=64 |
|---|---|---|---|---|
| ZE: 1 − \|⟨v(c′), Gᵀv(c)⟩\|, h = 1/16 | 1.3e-12 .. 8.8e-10 | 8.2e-13 .. 8.8e-10 | 3.9e-11 .. 1.6e-9 | 3.6e-11 .. 3.9e-8 |
| ZE: same, h = 1 | 1.4e-8 .. 1.9e-7 | 2.9e-8 .. 1.9e-7 | 1.4e-7 .. 1.7e-7 | 4.3e-7 .. 9.1e-7 |
| DIL: 1 − \|v(c)·v(c′)\|, h = 1/16 | 1.2e-7 .. 1.4e-7 | 1.1e-7 .. 1.4e-7 | 7.0e-8 .. 1.0e-7 | 1.5e-8 .. 1.8e-7 |
| DIL: energy overshoot C = [R_c′(v(c)) − λ(c)] / ΔL², all h | 0.047 .. 0.052 | 0.047 .. 0.052 | 2.2e-4 .. 2.6e-4 | 1.6e-4 .. 2.0e-4 |
| ZE: RQ_c′(Gᵀv) − λ(c) (continuum value: exactly 0) | −7.1e-29 .. +2.3e-32 | −5.0e-29 .. +6e-33 | +9e-141 .. +1.5e-130 | +1.3e-96 .. +4.7e-88 |
| \|λ(c′) − λ(c)\|, largest | 5.6e-28 | 5.9e-28 | 4.7e-135 | 5.9e-101 |
| λ₂ (smallest) and λ₂/\|λ₁\| (smallest), c ≤ 31.5 | 1.1e-22, 1.3e7 | 1.4e-22, 1.3e7 | 2.6e-134, 2.3e8 | 3.3e-97, 2.0e7 |

Beyond c = 31.5 the DH N = 128 form runs steeply into c = 32: λ falls
from −2.7e-29 at 31.9375 to −8.4480e-28 at 32, continuously
(λ(32 − 2^-20) = −8.4436e-28), with μ₀ growing to −3.4e-12, and there
1 − overlap reaches 2.3e-3. The table stops at 31.5 so that this does not
dominate the ranges.

Readings (measured):

- **ZE keeps the tuning, DIL destroys it.** The dilated ground state's
  energy overshoots λ by 0.05·ΔL² (DH) or 2e-4·ΔL² (zeta): for h = 1/16 that
  is 2e-7 against λ ~ 1e-28 (DH) and 1e-9 against 1e-138 (zeta), i.e.
  21 and 129 orders too coarse. The overshoot scales as ΔL²: C agrees to
  within 5% across h = 1/16, 1/4 and 1. The exact sandwich
  R_c′(v′) − R_c(v′) ≤ λ(c′) − λ(c) ≤ R_c′(v) − R_c(v) held at all 504
  pairs (no rigorous violation), but both brackets are ~10^20 times
  |Δλ| wide or more, so the dilation picture cannot see the change it
  brackets.
- **The ground state is continuous under ZE, for zeta and for DH through
  its crossing.** DH N=128 across c* ≈ 30.65: 30.5 → 30.75 has
  1 − overlap = 4.2e-9, and 30 → 31 has 9.0e-8. The negative-energy state
  at c > c* is the same bulk state continued, not a new state
  crossing in (λ₂ ≥ 1.1e-22 on c ≤ 31.5, gap ratio ≥ 1.3e7).
- **At finite N the ZE projection is not exact, and for zeta the error
  swamps λ.** For DH the projection's energy differs from λ(c) by up to
  7e-29, the same size as the changes being measured; for zeta by up to
  10^10 times λ (N = 128) and 10^13 times λ (N = 64). Checked rather than
  assumed (`factA_check.py`): projecting v(30, 64) into window 31 at
  N′ = 64 .. 1024, the deviation falls as −13.9%, −21.2%, −9.8%, −9.2%,
  −8.2%, −6.5%, −5.1% of λ(30) and equals the missing norm 1 − ‖Gᵀv‖²
  times a coefficient 7.5 .. 8.4 (N′ ≥ 256) that grows like log N′ (the archimedean
  weight at the band edge does the same). Two more DH cases give the same
  coefficient (7.6 to 7.7 at N′ = 256, 384). So the deviation is the
  truncated tail of a function with jumps, going to 0 as the missing
  norm does (Parseval), not a window-dependent term in the assembly:
  Fact A survives the basis-size check (measured). ZE energies are still
  not used below as numbers at finite N, only overlaps.

## 3. Task 3: what drives the change (decomposition)

### 3.1 First order: Hellmann-Feynman pieces in the dilation picture

dλ/dL = vᵀ(∂E/∂L)v at fixed coefficients, split into pole / arch / prime,
by central differences with ε = 2^-64 (DH, 600 bits) or 2^-250 (zeta, 1600
bits), at every non-integer grid window (`hf` blocks).

| window | kind, N | pole | arch | prime | sum = dλ/dL | cancellation |
|---|---|---|---|---|---|---|
| c = 30.5 | DH, 128 | 0 | −0.180087 | +0.180087 | −2.600e-27 | 26 digits |
| c = 30.5 | zeta, 128 | +0.462283 | −0.344443 | −0.117840 | −1.706e-137 | 136 digits |
| c = 30.5 | zeta, 64 | +0.470310 | −0.345185 | −0.125125 | −3.332e-101 | 100 digits |

Across the grid the pieces vary by less than 3% and cancel to 25 to 30 digits (DH)
and 98 to 140 digits (zeta). **No single term drives the ground-state
energy**: each piece is O(0.1) per unit L and the drive is a residual 26
to 136 orders smaller. The piece signs differ between zeta (primes push
down with arch, the pole pushes up) and DH (primes push up against arch),
but DH has no pole, so this is the three-way confound of weil_trunc s4
item 4 and says nothing about the Euler product.

### 3.2 New prime-power terms

- At first order they contribute exactly nothing at non-integer c (no index
  enters the stencil), and a new index n enters continuously
  (q_nm(L) = 0), so no jump in λ can come from one.
- Finite steps that cross an integer: on the new ground state (the lower
  bracket, which is the physically relevant one) the new-term energy is,
  for DH, between 1e-31 and 2e-25 in size and of either sign (zeta:
  9e-103 to 4e-91, all negative, against |Δλ| ≤ 6e-101 at N = 64), e.g. DH 30.5 → 31.5
  (Λ_f(31) enters): +4.3e-30 at N=128 and −2.1e-29 at N=64, against
  Δλ = −1.8e-29 and −2.5e-29. It is not systematically in the direction
  of the change.
- **DH turns negative between integers.** `crossing.py`, bisection over
  dyadic c ∈ [30, 31] to 2^-10, both ends hardened:

| N | c_pos (ball LDLᵀ at 0: no negative pivot) | c_neg (ball Rayleigh upper bound < 0) | zeta at c_neg, same N (ball LDLᵀ) |
|---|---|---|---|
| 64 | 30.817383 | 30.818359 | (65, 0), positive |
| 96 | 30.695312 | 30.696289 | (97, 0), positive |
| 128 | 30.646484 | 30.647461 | (129, 0), positive |
| 192 | 30.628906 | 30.629883 | (193, 0), positive |
| 256 | 30.616211 | 30.617188 | (257, 0), positive |

  By Fact B the N = 256 row makes λ_∞,DH(c) < 0 for every c ≥ 30.617188,
  and windows in [30, 31) use exactly the coefficient set n ≤ 30. Hardened
  (negativity) plus the nesting argument. The positive side of each row
  is a finite-N statement only; λ(30, N) > 0 up to N = 256 in the record,
  and the c*(N) sequence extrapolates (c* ≈ c∞ + a N^{-p} through the
  bracket midpoints at N = 64, 128, 256: p = 2.50, c∞ = 30.610; the same
  fit predicts 30.686 and 30.624 at N = 96 and 192 against the measured
  30.696 and 30.629) to c*(∞) ≈ 30.61 (measured). So "positivity can only
  be lost when a new coefficient enters" is false for DH.

### 3.3 Across DH's crossing: what changes and what does not

DH, N = 128 (`grid_dh_N128.json`):

| c | λ (hardened) | μ₀ | dλ/dL | −dλ/dL / μ₀² | Q₁ | on-line S(T ≤ 120) | rest |
|---|---|---|---|---|---|---|---|
| 29.0625 | +6.031e-28 | 1.435e-13 | −2.510e-26 | 1.22 | −1.109e-27 | +1.587e-27 | +1.26e-28 |
| 29.8125 | +1.564e-28 | 9.836e-14 | −1.123e-26 | 1.16 | +2.0e-31 | +9.13e-29 | +6.66e-29 |
| 30.25 | +4.072e-29 | 6.411e-14 | −5.051e-27 | 1.23 | −9.417e-29 | +1.021e-28 | +3.47e-29 |
| 30.625 | +1.099e-30 | 3.646e-14 | −1.580e-27 | 1.19 | −1.284e-28 | +1.185e-28 | +1.19e-29 |
| 30.6875 | −1.692e-30 | 3.157e-14 | −1.172e-27 | 1.18 | −1.261e-28 | +1.156e-28 | +9.5e-30 |
| 31.0625 | −7.899e-30 | 1.117e-14 | −1.341e-28 | 1.08 | −1.011e-28 | +9.10e-29 | +2.55e-30 |

(Q₁ = 4 Re g_v(γ₁ − iδ₁) at the first off-line pair, S = Σ 2g_v(γ) over the
64 cached on-line ordinates below 120, rest = λ − Q₁ − Q₂ − S, i.e. on-line
zeros above 120 plus farther off-line pairs. Float ordinates: measured.)

- **Arithmetic side: nothing happens at c*.** The pieces of 3.1 are smooth,
  dλ/dL is smooth and strictly negative through λ = 0 (a transversal
  crossing), the edge ratio is flat, and the ground state continues (s2).
- **Zero side: the sign change is the balance of Q₁ against the on-line
  sum.** Q₁ is not monotone in c (it passes through 0 near c ≈ 29.81, where
  |Q₁|/S ≈ 0.002, and was −1.1e-27 at c = 29.06 with λ still positive), and
  the crossing is where |Q₁| overtakes S + rest. That is information about
  where the zeros are, i.e. the RH-analogue itself, not a transport
  estimate.

## 4. Task 4: candidate relations, tested on DH

| # | candidate | range tested | grade | on DH | verdict |
|---|---|---|---|---|---|
| 1 | λ_∞(c′) ≤ λ_∞(c) for c′ ≥ c | all c (argument) | ordinary argument (Fact B), unreviewed | holds (it must) | not a mechanism; points the wrong way |
| 2 | λ(c, N) nonincreasing in c at fixed N | c ∈ [29, 32], N = 64, 128 | hardened counterexamples | fails: DH N=128 λ(31.25) = −8.2301e-30 < λ(31.3125) = −8.2211e-30 < λ(31.375) = −8.2162e-30; DH N=64 three steps in [31.44, 31.63]; zeta N=64 four steps (e.g. 30.0625 → 30.125), zeta N=128 one (31.875 → 31.9375) | false at finite N; the DH increases sit exactly where μ₀ crosses 0 (N=128: μ₀ = 2.8e-15, 5.5e-16, −1.8e-15 over 31.25 .. 31.375), i.e. the edge law's own prediction dλ/dL → 0; zeta's increases sit at no μ₀ zero and are the band-edge effect of the unsaturated form (s5); only the continuum statement 1 is true |
| 3 | ZE ground-state continuity, 1 − overlap ≤ ~2e-7 per unit c | [29, 31.94], both N | measured, exact vectors in balls | holds through c* | holds for DH: refuted as a mechanism |
| 4 | DIL energy bound R_c′(v(c)) ≤ λ(c) + C ΔL² (C ≈ 0.05 DH, 2.6e-4 zeta) | all pairs | measured (balls) | holds | an upper bound; holds for DH; useless by 22+ orders |
| 5 | positivity can be lost only where a new coefficient n enters | DH c ∈ [30, 31] | hardened negativity + Fact B | fails: λ_∞ < 0 on [30.6172, 31), data n ≤ 30 | refuted |
| 6 | margin/rate propagation: λ(L + δ) ≥ λ(L) e^{−Kδ} with K the locally observed log-rate, or any rule reading only λ(L) and dλ/dL | c ∈ [29, 32] | measured | at c = 30.25, N = 128, DH has 110 more orders of margin than zeta (4.07e-29 vs 3.37e-139) and a slower log-rate (K = 124 vs zeta's grid median 199), then crosses 0.013 later in L | refuted: the margin and its rate give no warning |
| 7 | edge law: dλ/dL = −κ μ₀², κ = O(1) | DH grids; N-ladders 32..256 at c = 13.5, 20.5, 30.5 (both kinds) and 31.5 (DH) | measured | holds through c* (κ ∈ [1.04, 1.29] at N=128 away from zeros of μ₀); zeta at saturation κ ≈ 1.3 to 1.5 | holds for DH and zeta alike: structural, refuted as a mechanism; κ itself is basis-dependent (s5) |

Candidate 7 is the closest thing to a transport relation the data show, so
it deserves its reading. λ decreases at a rate set by the squared value of
the ground state at the window's edge. DH's crossing is transversal
because μ₀ ≠ 0 there (μ₀ ≈ 3.5e-14 at c*, so μ₀² ≈ 1.3e-27 while λ = 0).
For positivity to propagate, the edge amplitude must go to zero at least as
fast as the margin: μ₀² ≲ λ/(κδ) on each step. Stated without an estimate
that is the same as positivity (λ reaches 0 only if μ₀²/λ blows up), so
per the mission's kill conditions it is a **reformulation, not progress**.
What it contributes is the target: an Euler-product bound on the boundary
trace of the window ground state is what a propagation proof would need,
and DH shows it cannot come from anything DH shares.

## 5. Caveats and incidents

- **The shift-0 trap.** Inverse iteration at shift 0 returns the eigenvalue
  of smallest *magnitude*. Just above c = 32 at N = 128 the eigenvalues
  +7.3e-28 and −2.06e-25 coexist, and the solver would have reported the
  first as λ_min. Caught while probing the steep drop into c = 32 (λ is
  continuous there: λ(32 − 2^-20) = −8.4436e-28, λ(32) = −8.4480e-28).
  Every grid cell was then re-checked by a Temple bracket
  whose LDL step proves the reported value is the minimum (`harden.py`);
  none of the 98 DH cells had been affected.
- **κ is a basis-dependent split.** At c = 13.5 (DH λ saturated at
  ≈ 2.1e-11), κ rises 1.04, 1.10, 1.28, 1.44, 1.70, 1.88 for N = 32 .. 256
  while μ₀ falls from 3.19e-6 to 2.02e-6 and the product κμ₀² converges
  (1.06e-11, 8.5e-12, 8.0e-12, 7.8e-12, 7.7e-12, 7.7e-12). So the band-N
  edge amplitude is a proxy for a continuum boundary quantity that tends
  to zero slowly with N; the invariant is dλ/dL, and "κ ≈ 1.2" fails the
  basis-size check as a constant. Zeta on the same ladders: κ = 1.70, 1.52,
  1.56, 1.46, 1.50 (c = 13.5, N = 64 .. 256) and 1.19, 1.20, 1.51, 1.45,
  1.42 (c = 20.5), i.e. flatter than DH once saturated; at c = 30.5 zeta
  only saturates near N = 256 (λ = 2.6e-69, 5.0e-103, 1.7e-125, 8.0e-140,
  3.1e-152, 6.6e-153 for N = 32 .. 256) and κ settles from scatter
  (3.55, 0.58, 2.34) to 1.15, 1.27, 1.31. The fine-grid zeta scatter
  (κ from 0.03 to 5.6 at N = 128) is the unsaturated regime.
- **Zeta is far from N-saturation at c ≈ 30.** λ(31, 60) = 4.8e-100,
  λ(31, 128) = 2.9e-141. Zeta numbers at fixed N describe the band-N form,
  whose c-dependence mixes window growth (down) with the band edge
  2πN/L moving down (up): that is why zeta's λ(c, 64) is non-monotone in c
  and zeta's κ scatters. Comparisons with DH are at matched N.
- **Zero-side split is float grade**: 64 on-line ordinates from
  `data/dh_zeros_online_T120.json` (float64), ρ₁ to 50 digits, ρ₂ to 10;
  completeness of the list is not checked here (THEOREM_FEASIBILITY
  OBL-4/5). The rest column is not signed.
- **Launch incident**: the first launch of the transport runs used
  `timeout`, which macOS does not ship; nothing ran (`RUNS.md`).
- The HF stencil truncation O(ε²) is not inside the balls; `precision_check.py`
  moves ε by 2^-24 and doubles precision (s6).

## 6. Hardening coverage, precision response, basis-size response

- **Hardening**: all 196 grid cells (DH and zeta, N = 64 and 128) carry a
  conclusive Temple bracket whose ball LDLᵀ step also proves the reported
  eigenvalue is the minimum (`hardened` blocks; `meta.hardened_all` true in
  all four grids). Lower and upper ends agree to all 20 printed digits
  everywhere (residuals 1e-57 to 1e-181). The crossing table (s3.2) and
  its zeta controls are hardened as stated there.
- **Precision response** (`precision_check.json`; doubling the working
  precision, and moving the HF stencil ε by 2^-24, the one error not
  carried in a ball): largest relative change of λ, μ₀ and dλ/dL at DH
  (30.5, 128), DH (31.25, 128), zeta (30.5, 64), zeta (30.5, 128) is
  8e-91 (precision) and 7e-13 (stencil; DH (31.25, 128), where dλ/dL is
  itself small, 5e-31). None of the quantities moves: they are not
  precision artifacts.
- **Basis-size response**: λ(c, N) ladders (`edge_*.json`, the record's
  ladders), c*(N) (s3.2), Fact A (s2) and κ (s5). The quantities used as
  findings (signs, c*(N) brackets, dλ/dL, overlaps) respond to N the way a
  converging quantity does; κ as a constant and the finite-N ZE energy do
  not, and are reported as basis-dependent.

## 7. The doors

Not a ceiling hunt, but the objects frozen here are the ones a follow-up
would unfreeze:

1. **Binding at c*:** nothing on the arithmetic side binds; the sign is
   set by Q₁ against the on-line sum (zero side).
2. **Frozen choices:** the periodic Fourier basis on the window (its edge
   amplitude μ₀ is the only proxy for the boundary trace, and it is
   basis-dependent, s5); the even sector (DH's crossing is even; the odd
   sector stays positive at 31 in the record); the transport (ZE vs DIL,
   s2); dyadic grids at 1/16 and bisection to 2^-10.
3. **Information class:** every quantity measured reads only the form
   restricted to one window at a time. The edge-trace door needs a basis
   that resolves the boundary behaviour of the continuum ground state
   (for example functions vanishing at the edge to a chosen order, or a
   basis adapted to the log-symbol archimedean part), which is new
   information beyond the band-N family.

**Proposed job (not run; too large for the laptop by the brief's limits).**
A boundary-trace study: for c on [29, 31] step 1/32 and DH and zeta,
compute the window ground state in a basis of edge-vanishing functions
(e.g. sin(πk y/L) products) at N up to 1024 with 3000 to 6000 bits for
zeta, and measure whether the continuum boundary behaviour
f_L(y) ~ A(L)·φ(y) near y = 0 has an amplitude A(L) with
dλ/dL = −K·A(L)² for a basis-independent K. Estimate from the unit costs
here (N = 1024 assembly 3 s at 400 bits, eigen-solve and LDL growing as
N³): ~30 s per DH cell and ~10 min per zeta cell at 6000 bits, so
~130 cells ≈ 12 to 20 runner-hours: a GitHub Actions matrix of 20 jobs,
one c-slice each, checkpointing per cell. Only worth funding if theory
first says what A(L) should be compared against.

## 8. Reproduction

From the worktree root (all runs single-process, under 10 minutes each,
estimates and actuals in `RUNS.md`):

    P=/Users/thomas/zeta-lab/.venv/bin/python; cd hunts/weil_propagation/numerics
    $P repro.py                                   # task 1
    for a in "dh 64" "dh 128" "zeta 64" "zeta 128"; do $P transport.py $a; done
    for a in "dh 64" "dh 128" "zeta 64" "zeta 128"; do $P harden.py $a; done
    $P crossing.py 64 96 128 192 256
    $P edge.py dh; $P edge.py zeta
    $P precision_check.py
    $P factA_check.py
    $P summarize.py                               # summary.json

## 9. Theory handoff: C2 against Epstein (1,1,6), and zeta's pole-free spectrum

Handoff from the theory worker (branch `teal-sea/weil-propagation-theory`,
commit 7d9636b, candidate C2 "Levy-Markov + pole"): C2 is outside DH's reach
(DH's jump measure is signed at n = 3 and DH has no pole), so the live
control is ζ_Q for Q = x² + xy + 6y² (discriminant −23, class number 3),
which has a pole, off-line zeros, a Γ(s) factor with positive Lévy density,
and Λ_Q(n) ≥ 0 for every n ≤ 47. Task A: its window floor on c ∈ [2, 48].
Task B: zeta's pole-free μ₂ against the full form's λ₁, λ₂ on c ∈ [2, 60].
Conventions as in the theory worker's s0; everything below is in the CCM
basis of s0 here.

### 9.1 The Epstein assembly, and why it can be trusted

No new closed forms. The lab's completion is
(√23/2π)^s Γ(s) ζ_Q(s) (`zeta.epstein.epstein_completed`, validated there by
the class-group identity), which equals 23^{s/2} Γ_R(s) Γ_R(s+1) ζ_Q(s)/2.
By the duplication formula its archimedean density is
log 23 + [Re ψ(1/4 + ir/2) − log π] + [Re ψ(3/4 + ir/2) − log π], so the
matrix is the weil_trunc zeta block (a = 1/4, pole block included; the
completion has simple poles at 0 and 1) plus the DH archimedean block
(a = 3/4) plus log(23/5)·I plus the prime block of Λ_Q
(`wp_common.epstein_matrices`). Checks:

| check | result |
|---|---|
| density identity (duplication formula) at r = 0.3, 7, 55.5 | 0, 4e-31, 8e-31 |
| normalisation: `epstein_zeta(3)` against the direct sum Σ r_Q(n) n^{-3} | agree to 4e-10 (the tail estimate of the direct sum) |
| Λ_Q from my recursion against `zeta.epstein.log_derivative_coefficients` | identical; first negative Λ_Q(48) = −7.742 |
| **control**: Dedekind zeta of Q(√−23) = ζ(s)L(s, χ₋₂₃), same completion, pole and archimedean blocks, coefficients from the class-group sum (1,1,6) + 2·(2,1,3) | Λ_K = Λ(n)(1 + χ(p)^k) to 2e-59; **positive definite in both sectors on all 93 windows c ∈ [2, 48]** (N = 64, ball LDLᵀ conclusive everywhere; smallest λ 8.6e-8 even, 6.8e-5 odd) |

The control is the load-bearing one: an error in the shared archimedean,
pole or conductor blocks would show in a GRH function with an Euler
product, and it does not. What differs between the two runs is the prime
block alone.

### 9.2 Task A result: the Epstein form goes negative well below c = 48

Grid c ∈ [2, 48] step 1/2, N = 64 and 128, both sectors (`epstein_scan.py`,
`epstein_N64.json`, `epstein_N128.json`): ball LDLᵀ inertia conclusive at
all 372 (cell, sector) pairs and a conclusive Temple bracket at every one.
At both N the odd sector is negative at every grid window from c = 28 on
and the even sector from c = 29.5 on, with exactly one negative eigenvalue
per sector and no return to positivity on the grid. Bisection to 2^-10
with every step a conclusive ball LDLᵀ sign, and the negative end also
carried by a ball Rayleigh upper bound < 0 (`epstein_crossing.py`):

| N | sector | last positive c | first negative c | λ_min at first negative (ball RQ) | Dedekind there |
|---|---|---|---|---|---|
| 64 | odd | 27.804688 | 27.805176 | −7.932242799e-7 | positive definite |
| 128 | odd | 27.741211 | 27.741699 | −1.292835817e-6 | positive definite |
| 64 | even | 29.340820 | 29.341309 | −1.236643810e-6 | positive definite |
| 128 | even | 29.303711 | 29.304199 | −4.219861683e-6 | positive definite |

By Fact B the N = 128 odd row makes the continuum Epstein form negative on
every window c ≥ 27.741699, and every such window below 48 has Λ_Q(n) ≥ 0
for all n ≤ c. Depth grows to λ_min = −0.898 (even) and −1.065 (odd) at
c = 48, N = 128. Grade: **hardened** (two rigorous routes per sign) plus the
nesting argument.

**Where the negative states point.** The even negative ground states have
their coefficient mass peaked at frequency 16.7 to 18.5 (c ≥ 29.5), and the
odd ones at 15.3 to 16.6 once deep (c ≥ 34); the mode spacing there is
2π/L ≈ 1.6 to 1.9. At the marginal odd windows (c = 28 to 30) the state is
the bulk low-frequency one (peak 1.9), as for DH at (31, 60). Independent
check with code that shares nothing with the Galerkin route
(`epstein_offline.py`: the lattice-sum completion and the lab's
argument-principle counter): **exactly one zero of the completed ζ_Q in
[0.51, 1.3] × [14, 20]**, polished by findroot to

    ρ₁ = 0.953260474794661 + 16.2902157203904 i,   |Λ_Q(ρ₁)| = 1.4e-32 (dps 20),

an off-line zero at δ = β − 1/2 = 0.453, exactly where the beams point.
Grade: the zero count is measured (float argument principle, integrality
guard 1e-6); the root is measured.

Two more boxes, same route: **no zeros in [0.51, 1.3] × [0.5, 7] and none in
[0.51, 1.3] × [7, 14]** (159 s and 273 s). So ρ₁ is the only zero of the
completed ζ_Q with 0.51 ≤ σ ≤ 1.3 and 0.5 ≤ t ≤ 20: the lowest off-line zero
in that strip, in the role DH's first pair at 85.7 played for DH (measured;
zeros with 1/2 < σ < 0.51 or σ > 1.3 are outside what these boxes check).

### 9.3 Which part of C2 breaks (`epstein_polefree.py`, N = 64)

The theory worker's reduction: Q_e ≥ 0 ⟺ (a) μ₂(Q°_e) ≥ 0 and (b) the even
pole capacity; Q_o ≥ 0 ⟺ Q°_o ≥ 0 and the odd pole capacity (the odd pole
term is negative). Ball LDLᵀ inertia of the pole-free and full Epstein
matrices, conclusive at every cell:

| c | even full | even pole-free | odd full | odd pole-free |
|---|---|---|---|---|
| 27 | (65, 0) | (64, 1): μ₁ = −7.22, μ₂ = +0.497 | (64, 0) | (64, 0) |
| 28 | (65, 0) | (64, 1) | (63, 1) | (64, 0) |
| 29 | (65, 0) | (64, 1): μ₂ = +0.0415 | (63, 1) | (64, 0) |
| 29.5 | (64, 1) | **(63, 2)**: μ₂ = −0.0142 | (63, 1) | (64, 0) |
| 30 | (64, 1) | (63, 2) | (63, 1) | (64, 0) |
| 34, 40, 48 | (64, 1) | (63, 2) | (63, 1) | (63, 1) |

- **Even sector: the pole capacity (b) fails first, then (a).** The full
  even form turns negative at c = 29.3042 (N = 128; 29.3413 at N = 64),
  while the killed Epstein jump process acquires its second even
  eigenvalue below C_ℓ (μ₂ < 0) only at c = 29.3179 (N = 128; 29.3555 at
  N = 64), bisected on the pole-free inertia to 2^-10
  (`epstein_mu2_cross.py`, `epstein_mu2_cross.json`). So on
  (29.304, 29.318] condition (a) still holds and the even pole capacity is
  what breaks; from 29.318 on, (a) fails too. Interlacing μ₁ ≤ λ₁ ≤ μ₂
  holds at every cell. Markov structure plus one pole stops neither.
- **Odd sector: the odd pole capacity fails first.** The pole-free odd form
  stays positive until c ≈ 34 while the full odd form is negative from
  27.74, so the odd crossing is the negative odd pole term; C2's Markov
  structure is not what is tested there.

**Verdict on C2 (per the supervisor's criterion): refuted as a propagation
mechanism.** Every hypothesis it uses holds for ζ_Q on windows c < 48
(nonnegative jump measure, Γ-class Lévy density, one pole) and the form
goes negative at c = 27.74 (odd) and 29.30 (even). Proposition M's
unconditional structural consequences are not touched by this; only the
use of "Markov + one pole" to carry positivity forward is. Any C2-based
argument must use more of the Euler product than Λ ≥ 0 on the window.

**What the Epstein/Dedekind pair isolates.** The two runs share the
completion, the pole, the Γ(s) Lévy density and Λ ≥ 0 on every window
below 48; they differ only in the prime block. Dedekind's atoms sit on
prime powers alone (Λ_K(p^k) = log p (1 + χ₋₂₃(p)^k)), as an Euler product
forces. Epstein's vanish at 2, 3, 5, 7, 11 but sit on composites and on
higher powers of those primes (Λ_Q(4) = 1.386, Λ_Q(6) = 3.584,
Λ_Q(8) = 4.159, Λ_Q(9) = 2.197, Λ_Q(12) = 4.970). One form is positive on
every window, the other negative from 27.74. That is the prime-power-support
condition the theory worker named as the next thing C2 would need
(its s4, C2 "DH test"), now measured as the difference between a positive
and a negative case. It is one matched pair, so it shows the condition
matters here; it does not show that it suffices.

### 9.4 Task B: zeta's pole-free μ₂ against λ₁, λ₂ (`zeta_pole.py`)

Even sector, c ∈ [2, 60] step 1/2 (117 windows), N = 64 and 128
(`zeta_pole_N64.json`, `zeta_pole_N128.json`). E is the full matrix, E° = E − W02
the pole-free one from the same assembly; λ₁, λ₂ of E and μ₁, μ₂ of E° as
ball Rayleigh quotients of inverse-iteration vectors (μ₁ shifted at the
lowest approximate eigenvalue).

| c | λ₁ (N=128) | λ₂ (N=128) | μ₁ | μ₂/λ₂ N=64 | μ₂/λ₂ N=128 | μ₂/λ₁ (N=128) |
|---|---|---|---|---|---|---|
| 2 | 1.330e-3 | 0.661 | −1.286 | 0.88087 | 0.88086 | 4.4e2 |
| 3 | 5.55e-8 | 1.46e-3 | −2.171 | 0.6481 | 0.64812 | 1.7e4 |
| 5 | 9.68e-18 | 5.01e-12 | −3.334 | 0.63945 | 0.63949 | 3.3e5 |
| 10 | 1.74e-43 | 2.45e-36 | −5.119 | 0.6399 | 0.63987 | 9.0e6 |
| 13 | 3.30e-59 | 1.29e-51 | −5.851 | 0.64019 | 0.64019 | 2.5e7 |
| 20 | 2.18e-96 | 5.98e-88 | −7.216 | 0.64094 | 0.64052 | 1.8e8 |
| 30 | 2.15e-138 | 6.49e-130 | −8.659 | 0.64172 | 0.64088 | 1.9e8 |
| 40 | 5.88e-163 | 1.33e-154 | −9.824 | 0.64222 | 0.64118 | 1.4e8 |
| 60 | 1.21e-192 | 2.31e-184 | −11.679 | 0.64299 | 0.64163 | 1.2e8 |

- **μ₂ tracks λ₂ at a nearly fixed ratio.** μ₂/λ₂ = 0.6394 to 0.6430 on
  every window with c ≥ 5 at both N, drifting up slowly with c; N = 64 and
  N = 128 agree to 0.001 even where λ₂ itself differs by 64 orders of
  magnitude between the two bases (c = 60). So the ratio is basis-stable
  while the eigenvalues are nowhere near N-converged for c ≳ 15 (measured).
  It confirms the theory worker's 0.64 at c = 13 and 31 and extends it to
  [5, 60]. Below c = 5 the ratio is larger (0.88 at c = 2).
- **Interlacing μ₁ ≤ λ₁ ≤ μ₂ ≤ λ₂ holds at all 234 (c, N) cells** (midpoint
  comparison), and μ₂/λ₁ ranges from 4e2 (c = 2) to 2e8: condition (a)'s
  margin μ₂ sits 2.6 to 8.3 orders of magnitude above λ₁, so for zeta, as the theory worker
  measured at two cells, the even pole capacity (b) is the tight condition
  and (a) holds with room, on this whole range.
- **Hardened at every one of the 234 cells**: the full even form is
  positive definite (ball LDLᵀ inertia (N+1, 0)), and the pole-free even
  form has exactly one negative eigenvalue (inertia (N, 1)), which is the
  shape Proposition M plus positivity require. 1600 bits sufficed for
  c ≲ 30 at N = 128; the other cells were redone at 3200 bits
  (`zeta_pole_fixup.py`), all conclusive.
- Set against 9.3: Epstein breaks the condition that zeta satisfies with
  room here. Its μ₂ crosses zero at c = 29.318 (N = 128) while zeta's μ₂
  stays at 0.64 λ₂ > 0. Whatever keeps zeta's μ₂ positive is not "Λ ≥ 0 on the
  window plus one pole", since Epstein has both.

Grade for 9.4: measured (ball upper bounds for all four eigenvalues,
inverse-iteration vectors with residuals recorded; interlacing on
midpoints), except the inertia statements, which are hardened where the
ball LDLᵀ is conclusive.

### 9.5 Observations raised, not pursued

- `zeta/epstein.py` (`claim_euler_product_positivity` docstring) says the
  principal Epstein form fails at n = 48 "(−19.88)". The lab's own
  `log_derivative_coefficients` gives Λ_Q(48) = −7.742; −19.879 is
  Λ_Q(144), the most negative value for n ≤ 200. The first-failure index
  48 is right; the quoted value belongs to another n. Issue candidate
  (outside this hunt's write scope).
- `zeta_pole_N64_firstrun_mu1defect.json` is the first Task B run at
  N = 64, kept as the record of a defect: μ₁ came from inverse iteration at
  a fixed shift −20, which converges slowly (ratio ≈ 0.7) and at small c
  landed on the wrong eigenvalue (μ₁ > 0 at c = 2 while the ball LDLᵀ said
  exactly one negative eigenvalue). Caught by the interlacing check (7
  cells failed). The rerun uses the lowest approximate eigenvalue as the
  shift; λ₁, λ₂, μ₂ and every inertia in the first run were unaffected.
- The Dedekind control's floor sits far above zeta's: at (c, N) = (46, 64)
  its even λ_min is 1.4e-7 against zeta's 1.4e-118 (same N). Dedekind has
  everything C2 asks for plus a genuine Euler product, so the depth of
  zeta's floor is not explained by C2's ingredients either. A plausible
  reading (not tested): L(s, χ₋₂₃)'s own pole-free component sets the
  Dedekind floor, as DH's did at 1e-10 near c = 13, which would say the
  pole does the heavy lifting in zeta's depth. A thread for theory.
- Where ζ_Q's first off-line zero sits relative to all on-line zeros, and
  whether the even and odd crossings are both carried by ρ₁ through the
  dictionary (as DH's was by its first pair), is the natural next check.
  It needs Epstein on-line zeros to ~T = 60 and the odd-sector dictionary.

Reproduction (from this directory, each under 10 minutes):

    $P epstein_scan.py 64; $P epstein_scan.py 128; $P epstein_scan.py 64 dedekind
    $P epstein_crossing.py; $P epstein_polefree.py; $P epstein_mu2_cross.py
    $P epstein_offline.py; $P epstein_offline.py 0.51,1.3,7,14; $P epstein_offline.py 0.51,1.3,0.5,7
    $P zeta_pole.py 64; $P zeta_pole.py 128; $P zeta_pole_fixup.py 128

## 10. Theory's C4 prerequisite (U-S), checked from coefficients

Theory RESULTS s7.1 (branch `teal-sea/weil-propagation-theory`, commit
8188609) names the step Dedekind ζ_{Q(√−23)} passes and Epstein (1,1,6)
fails: (1) atoms only at prime powers; (2) unitary local roots, checkable
as |s_k(p)| ≤ d with s_k(p) = Λ(p^k)/log p and d = 2. My own
implementation (`us_check.py`, `us_check.json`) uses exact arithmetic.
Every Λ(n) is kept as a rational combination of log p, so "Λ(n) = 0"
means all rational coefficients vanish. It covers n ≤ 200, with
coefficients from `zeta.epstein.epstein_representation_count`.

| | Dedekind Q(√−23) | Epstein (1,1,6) |
|---|---|---|
| composite atoms, n ≤ 200 | none | 31; first **n = 6**; ≤ 60: 6, 12, 18, 26, 39, 48, 52, 58 |
| prime-power atoms off the log p axis | none | none |
| towers s_k(p) | split p (2, 3, 13, …): 2; inert p (5, 7, 11, …): 0 for odd k, 2 for even k; ramified 23: s₁ = 1 | s_k(2) = 0, 2, **6**, 2, 0, 2, 0 (k = 1..7); s_k(3) = 0, 2, **6**, 2 |
| \|s_k(p)\| > 2 | never | exactly twice for n ≤ 200: **n = 8** (s₃(2) = 6) and n = 27 (s₃(3) = 6) |
| (1) and (2) | **both pass** | **both fail**, at n = 6 and n = 8 as claimed |

Grade: exact arithmetic, an independent implementation of theory's check
K; it agrees with their table entry for entry on the overlap (n ≤ 60).
Both failures sit inside Epstein's negative windows (c ≥ 27.74 contains
n = 6, 8 and 27), consistent with the reading in s9.3. As theory notes,
this makes (U-S) the separating step for this pair. It does not test C4,
because no available rival satisfies (U-S).
