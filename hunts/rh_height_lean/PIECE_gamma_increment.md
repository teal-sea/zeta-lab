# PIECE `gamma_increment` (hunt #137): the Gamma side of the count, enclosed

**Written 2026-10-21 by the `gamma_increment` role of the campaign workflow.** Grades as in
`MISSION.md`. **Status: closed.** The theorem below is kernel-checked at the root package's
pins (Lean v4.35.0-rc2, Mathlib 0653561, vendored `zeta23`), with zero `sorry` and only the
axioms `propext`, `Classical.choice` and `Quot.sound`. Nothing is committed: the two Lean
files and this note are untracked in the worktree. No second kernel (NanoDa, Comparator) and
no CI run has checked them yet.

It is one of the four hypotheses of `rhHeight50_of_four` (`lean/RHHeight/Assembly.lean`). It
does not prove the target `RHHeight50`; `horizontal_legs`, `exact_argument` and `low_height`
are other roles' pieces, and this role did not check their state.

## The statement

The plan's signature (`PLAN.md` section 4.1), unchanged:

```lean
theorem RHHeight.gamma_increment :
    (92 / 10 : ℝ) ≤ ∫ t in (3 : ℝ)..52, Zeta23.mu t ∧
      ∫ t in (3 : ℝ)..52, Zeta23.mu t ≤ 109 / 10

theorem RHHeight.gamma_increment_holds : RHHeight.GammaIncrement
```

`Zeta23.mu τ = (1/2π) Re ψ(1/4 + iτ/2) - log π/(2π)`, with `ψ = Complex.digamma`.
`lean/RHHeight/CheckGammaIncrement.lean` pins `GammaIncrement` and `mu` to this text by `rfl`
and checks that `count_eq_ten_of gamma_increment hH hE : Ncount 3 52 = 10` typechecks.

The analytic content is also proved at any two heights, so the `T = 100` analogue
(`PLAN.md` section 7, top height `99.85`) needs only new numerics:

```lean
theorem RHHeight.GammaSide.abs_integral_mu_sub_le {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ ≤ T₂) :
    |(∫ t in T₁..T₂, Zeta23.mu t) - (muPrim T₂ - muPrim T₁)| ≤ 6 / Real.pi * (1 / T₁ - 1 / T₂)
```

## The proof

`lean/RHHeight/GammaIncrement.lean`, about 360 lines with its documentation. The plan's route
went through as written:

1. `abs_mu_sub_muMain_le`. For `|t| ≥ 1` and `w = 1/4 + it/2`, the vendored
   `digamma_stirling` gives `‖ψ(w) - log w + 1/(2w)‖ ≤ 3/(Im w)² = 12/t²`. With
   `Re log w = (1/2) log((1 + 4t²)/16)` and `Re 1/(2w) = 2/(1 + 4t²)` kept exactly, this is
   `|μ t - m t| ≤ 6/(π t²)`, `m t = (1/2π)((1/2) log((1 + 4t²)/16) - 2/(1 + 4t²) - log π)`.
2. `hasDerivAt_muPrim`. `F t = (1/2π)((t/2) log((1 + 4t²)/16) - t - (1/2) arctan 2t - t log π)`
   has derivative `m t` everywhere.
3. `abs_integral_mu_sub_le`. `intervalIntegral.integral_mono_on` against `m ± 6/(π t²)`, and
   `integral_eq_sub_of_hasDerivAt` with the primitives `F ∓ 6/(π t)`. `μ` is integrable as a
   continuous function (`Zeta23.mu_smooth.continuous`), so `GammaFacts.Complete` and its
   `IntMu` are not imported.
4. `gamma_increment`. `two_pi_mul_muPrim_sub` evaluates `2π (F 52 - F 3)` as
   `26 log(10817/16) - (3/2) log(37/16) - 49 - (1/2)(arctan 104 - arctan 6) - 49 log π`; the
   error at `(3, 52)` is `(49/13)/(2π)`. Rational bounds `log(10817/16) ∈ [6.516, 6.517]`,
   `log(37/16) ∈ [0.838, 0.839]` and `log π ∈ [1.1446, 1.1449]` come from Mathlib's series
   bound `Real.abs_log_sub_add_sum_range_le` after splitting off powers of 2
   (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`), with `log π` squeezed by monotonicity
   between `log 3.1415` and `log 3.1416` (`Real.pi_gt_d4`, `Real.pi_lt_d4`). The arctangent
   difference is only placed in `[0, π/2]`, by monotonicity. `linarith` closes both sides.

Two choices differ from the plan's options, neither in the statement. The logarithms use
Mathlib's series lemma directly instead of `ZetaLean.Interval.logQ`, which wraps the same lemma
but imports all of Mathlib through `ZetaLean.IntervalExp` and is not in `build.sh`'s skeleton
stage. And `Real.pi_gt_d4`/`Real.pi_lt_d4` suffice where the plan named the `d6` bounds.

## Numbers (measured, not the proof)

mpmath at 30 digits, one route, not pinned by a test of this role:

| quantity | value |
|---|---|
| `∫_3^52 μ` (quadrature), and `(θ(52) - θ(3))/π` | `10.042613`, `10.042613` |
| `F 52 - F 3`, and `∫_3^52 m` (quadrature) | `10.026188`, `10.026188` |
| error budget `(6/π)(1/3 - 1/52)` | `0.599892` |
| interval from step 3 | `[9.4263, 10.6261]` |
| interval from the rational bounds of step 4 | `[9.3109, 10.6429]` |
| slack against the stated `[9.2, 10.9]` | `0.111` below, `0.257` above |
| largest `abs(μ - m) / (6/(π t²))` over 401 points of `[3, 52]` | `0.028` |

The first and fourth rows agree with the sibling numeric plan's Arb values (`NUMERIC_PLAN.md`
section 3: `10.0426130` and `[9.4263, 10.6261]`; its `test_numeric_plan.py` pins the route's
room `0.2263` above `9.2`). The last row says the width of the step-3 interval comes from the
constant `3` of `digamma_stirling`, which overstates the true error about 36-fold on `[3, 52]`,
not from the main term `m`. The series tails used in step 4 are below `6e-6`.

## Build (no lake)

The piece imports `RHHeight.Skeleton` and `Zeta23.GammaFacts.StirlingVert`: 12 `zeta23`
modules, the skeleton stage's seven plus `GammaFacts`, `GammaFacts.Series`,
`Analytic.Stirling`, `GammaFacts.Mu` and `GammaFacts.StirlingVert`. `build.sh` has no stage for
the extra five, so they are compiled by hand with `zeta23`'s lakefile options:

```bash
cd <worktree> && export PATH="$HOME/.elan/bin:$PATH" && OUT=$(mktemp -d)
LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh "$OUT"
LP="$OUT"; for p in "$PWD"/lean/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
for m in GammaFacts GammaFacts/Series Analytic/Stirling GammaFacts/Mu GammaFacts/StirlingVert; do
  mkdir -p "$(dirname "$OUT/Zeta23/$m")"
  ( cd lean/vendor/zeta23 && LEAN_PATH="$LP" lean --root=. -DrelaxedAutoImplicit=false \
      -Dpp.unicode.fun=true "Zeta23/$m.lean" -o "$OUT/Zeta23/$m.olean" )
done
LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh \
  --file RHHeight/GammaIncrement.lean "$OUT"
( cd hunts/rh_height_lean/lean && LEAN_PATH="$LP" lean RHHeight/CheckGammaIncrement.lean )
```

**Receipt.** This recipe ran end to end into a fresh directory on the campaign box on
2026-10-21, one `lean` process at a time, at load averages near 75 on 32 vCPU: the skeleton
stage in 78 s, the five `zeta23` modules in 73 s, `RHHeight.GammaIncrement` in 18 s (peak
resident memory about 2.1 GB) and the check in 7 s. The piece's compile printed nothing. The
log holds no error and no `sorry`; its only other messages are the vendored files' existing
deprecation warnings and `ring_nf` suggestions from `GammaFacts/Mu.lean` and
`GammaFacts/StirlingVert.lean`. A scratch copy of `check_axioms.py` with this piece's fourteen
names added accepted the log (25 reports, standard axioms only), and refused it with `sorryAx`
planted in one report and with one report deleted.

**Planted faults in the proof.** Raising the lower constant to `98/10`, or lowering the upper
one to `104/10`, makes the final `linarith` of that side fail. Both altered statements are
true of the measured value `10.0426`. They fail because `98/10` and `104/10` lie strictly
inside the interval `[9.3109, 10.6429]` that the route's rational bounds reach, so the route
cannot separate them from the integral.

This role edited no shared file. To fold the piece into the package: add the five modules and
`RHHeight.GammaIncrement` to `build.sh`, run `CheckGammaIncrement.lean` there, and add its
fourteen names to `check_axioms.py`'s expected set if its output lands in the audited log.

## Axioms

From `lean/RHHeight/CheckGammaIncrement.lean`:

```
'RHHeight.GammaSide.abs_mu_sub_muMain_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.hasDerivAt_muPrim' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.continuous_muMain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.hasDerivAt_six_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.abs_integral_mu_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.log_one_sub_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.log_10817_div_16_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.log_37_div_16_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.pi_gt_6283_div_2000' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.pi_lt_3927_div_1250' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.log_pi_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.GammaSide.two_pi_mul_muPrim_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.gamma_increment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.gamma_increment_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
