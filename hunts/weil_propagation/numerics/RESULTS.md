1. **Found:** no transport quantity measured here breaks where DH turns negative: the zero-extended DH ground state continues smoothly (1 − overlap ≤ 2e-7 per unit c on 29 ≤ c′ ≤ 31.5, i.e. through the crossing at c ≈ 30.65), the arch/prime split of dλ/dL is smooth, and dλ/dL ≈ −κμ₀² (μ₀ the band-N edge amplitude, κ = O(1) but basis-dependent) holds straight through the crossing.
2. **Found:** DH's continuum Weil form is negative on every window c ≥ 30.617188 (hardened cell (30.617188, N = 256) plus nesting), strictly between the coefficients n = 30 and 31, so positivity is lost with no new arithmetic term entering; c*(N) = 30.818, 30.696, 30.647, 30.629, 30.617 for N = 64..256, extrapolating to ≈ 30.61.
3. **Grade:** crossing brackets, zeta controls and all 196 grid eigenvalues are hardened (ball Rayleigh quotients, ball LDLᵀ, Temple); the continuum consequences add a two-line nesting argument (ordinary, unreviewed); transports, decompositions, the edge law and the zero-side split are measured.
4. **What refutes it:** of the seven candidates in s4, five hold for DH across 30 → 31 (1, 3, 4, 6, 7), one is false outright for DH (5) and one fails at finite N for a basis reason (2), so none is a propagation mechanism; the only quantity that changes sign at c* is the zero-side balance (off-line quadruple Q₁ ≈ −1.28e-28 overtaking the on-line sum), which is RH-analogue information, not a transport estimate.
5. **Next step:** propagation would need an Euler-product bound on the ground state's boundary trace (band-N proxy μ₀) by its margin, μ₀² ≲ λ/(κδ), which DH violates at c*; stated without an estimate that is a reformulation, so the next move is theory's (does the Euler product constrain that boundary trace?), plus one numerics job worth funding: a boundary-adapted basis (s7).

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
