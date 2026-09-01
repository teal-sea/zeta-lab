/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Erdős problem 359

The statement below is vendored **verbatim** from `formal-conjectures/359.lean`:
`IsGoodFor` and `erdos_359.parts.i`, copied exactly, with the literal `sorry`
kept. The `sorry` is the advertised open statement, not an uncertified step in
a proof: do not restate, generalise, weaken or specialise it, and do not
"fix" it in this file.

Only the surrounding scaffolding (the header, `import Mathlib`, and the
`open Filter Asymptotics` needed for `atTop` and `~[·]`) is ours; every line
of the vendored declarations is upstream's.

Below the vendored statements sits *our* material: the reduction of
`erdos_359.parts.ii` to Andrews' conjectured asymptotic
`A k ~ k * log k / log (log k)`. Those lemmas are ours, and they are proved:
the only `sorry`s left in this file are the three advertised statements above,
and `#print axioms` on `tendsto_log_div_loglog_mul_rpow_atTop_nhds_zero` and
`parts_ii_of_andrews_asymptotic` reports no `sorryAx`.
-/

open Filter Asymptotics

def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)



theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry



theorem erdos_359.parts.ii (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c):
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) := by
  sorry



theorem erdos_359.variants.isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log) := by
  sorry

/-!
## Reduction of `erdos_359.parts.ii` to Andrews' asymptotic

Everything from here down is ours, not upstream's.

`erdos_359.variants.isGoodFor_1_asymptotic` above is Andrews' conjecture, that
a good sequence satisfies `A k ~ k * log k / log (log k)`. It implies
`erdos_359.parts.ii` on the nose, because the comparison function itself
already tends to `0` after dividing by `k ^ (1 + c)`:

`(k * log k / log (log k)) / k ^ (1 + c) = log k / (log (log k) * k ^ c) → 0`

for every `c > 0`, the `k ^ c` beating `log k` and the `log (log k)` only
helping. So the reduction is two steps: the scalar limit
`tendsto_log_div_loglog_mul_rpow_atTop_nhds_zero`, and then transporting it
along the `IsEquivalent` in `parts_ii_of_andrews_asymptotic`.

Note what `parts_ii_of_andrews_asymptotic` does *not* take: it has no
`IsGoodFor A 1` hypothesis. The asymptotic alone carries the whole statement,
so the lemma is stated for an arbitrary `A : ℕ → ℕ`; goodness enters only when
it is composed with Andrews' conjecture.
-/

/-- The scalar half of the reduction: for `c > 0`,
`log k / (log (log k) * k ^ c) → 0` along `atTop`.

This is `(k * log k / log (log k)) / k ^ (1 + c)` after cancelling one factor
of `k`, i.e. exactly the limit that Andrews' comparison function has. -/
theorem tendsto_log_div_loglog_mul_rpow_atTop_nhds_zero (c : ℝ) (hc : 0 < c) :
    atTop.Tendsto (fun k : ℕ ↦ (k : ℝ).log / ((k : ℝ).log.log * (k : ℝ) ^ c)) (nhds 0) := by
  -- No squeeze and no explicit threshold: the quotient factors as a product of
  -- two things that *each* tend to `0`, so `0 * 0 = 0` does all the work and
  -- the junk values at small `k` (where `log (log k)` is `0` or negative) never
  -- have to be excluded.
  -- `log k / k ^ c → 0`: `log =o[atTop] (· ^ c)` for `c > 0`, read along `ℕ`.
  have h1 : Tendsto (fun k : ℕ ↦ (k : ℝ).log / (k : ℝ) ^ c) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  -- `1 / log (log k) → 0`: `log ∘ log ∘ (↑·)` tends to `atTop`, so its inverse
  -- tends to `0`.
  have h2 : Tendsto (fun k : ℕ ↦ ((k : ℝ).log.log)⁻¹) atTop (nhds 0) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have h3 := h1.mul h2
  rw [mul_zero] at h3
  -- `(log k / k ^ c) * (log (log k))⁻¹ = log k / (log (log k) * k ^ c)`,
  -- an identity of the `⁻¹`s alone, so no denominator has to be nonzero.
  refine h3.congr fun k ↦ ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_comm ((k : ℝ).log.log)⁻¹]
  ring

/-- **Andrews' conjectured asymptotic implies `erdos_359.parts.ii`.**

If `A k ~ k * log k / log (log k)` then `A k / k ^ (1 + c) → 0` for every
`c > 0`. The conclusion is `erdos_359.parts.ii`'s verbatim, so
`erdos_359.variants.isGoodFor_1_asymptotic` composed with this lemma closes
part (ii). -/
theorem parts_ii_of_andrews_asymptotic (A : ℕ → ℕ)
    (hAsymp : (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log))
    (c : ℝ) (hc : 0 < c) :
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) := by
  -- `A k / k ^ (1 + c) → 0` is exactly `A k =o[atTop] k ^ (1 + c)`, and the
  -- side condition of `isLittleO_iff_tendsto'` is free because `k ^ (1 + c)`
  -- is positive for `k ≥ 1`.
  have hpos : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (k : ℝ) ^ (1 + c) := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact Real.rpow_pos_of_pos (by exact_mod_cast hk) _
  have hne : ∀ {f : ℕ → ℝ}, ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ (1 + c) = 0 → f k = 0 :=
    hpos.mono fun _ h h0 ↦ absurd h0 h.ne'
  -- Andrews' comparison function is itself `o(k ^ (1 + c))`: dividing it by
  -- `k ^ (1 + c) = k * k ^ c` cancels the `k` and leaves the scalar limit above.
  have hg : (fun k : ℕ ↦ (k : ℝ) * (k : ℝ).log / (k : ℝ).log.log) =o[atTop]
      fun k : ℕ ↦ (k : ℝ) ^ (1 + c) := by
    refine (isLittleO_iff_tendsto' hne).mpr ?_
    refine (tendsto_log_div_loglog_mul_rpow_atTop_nhds_zero c hc).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hkp : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [Real.rpow_add hkp, Real.rpow_one, mul_div_assoc, mul_div_mul_left _ _ hkp.ne',
      div_div]
  -- `A ~ g` gives `A =O[atTop] g`, and `O(g)` inside `o(k ^ (1 + c))` is
  -- `o(k ^ (1 + c))`.
  exact (isLittleO_iff_tendsto' hne).mp (hAsymp.isBigO.trans_isLittleO hg)

/-- The composite, for the record: goodness plus Andrews' conjecture gives
part (ii). This is `erdos_359.parts.ii` with its proof outsourced, and is the
only declaration here that is not open in its own right once the two inputs
are discharged. -/
theorem parts_ii_of_isGoodFor_of_andrews (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c) :
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) :=
  parts_ii_of_andrews_asymptotic A (erdos_359.variants.isGoodFor_1_asymptotic A hA) c hc
