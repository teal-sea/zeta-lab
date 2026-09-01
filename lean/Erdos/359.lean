/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Erdős problem 359

The *statements* below are vendored **verbatim** from `formal-conjectures/359.lean`:
`IsGoodFor`, `erdos_359.parts.i` and `erdos_359.variants.isGoodFor_1_low_values`,
copied exactly. Upstream's `@[category ..., AMS ...]` attributes are dropped,
because they come from `FormalConjecturesUtil`, which is not vendored here.

`erdos_359.parts.i` keeps upstream's literal `sorry`. That `sorry` is the
advertised open statement, not an uncertified step in a proof: do not restate,
generalise, weaken or specialise it, and do not "fix" it in this file.

`isGoodFor_1_low_values` is upstream's finite partial result: it is
`@[category test]` there rather than `research open`, and pins the first eight
terms of the sequence, [OEIS A002048](https://oeis.org/A002048). Upstream leaves
it as a `sorry` too; here it is **proved**, by unwinding the greedy `IsLeast`
recursion once per `j = 0, ..., 6`. Only that proof body and the surrounding
scaffolding (this header, `import Mathlib`, and the `open Filter` needed for
`atTop`) are ours.

## How the low-values proof goes

For each `j` the recursion pins `A (j + 1)` between two bounds, both finite:

* **upper.** `IsLeast.2` applied to the candidate `v` gives `A (j + 1) ≤ v`,
  once `v` is shown to be a member of the set: `A j < v`, and `v` is not any
  consecutive sum `∑ i ∈ Finset.Icc a b, A i` with `Finset.Icc a b ⊆ Finset.Iic j`.
  Such a subset forces `a ≤ b ≤ j` (or an empty `Icc`, whose sum is `0`), so
  `interval_cases` on `a` and then `b` reduces this to the finitely many sums
  over `A 0, ..., A j`, each evaluated by `Finset.sum_Icc_succ_top`.
* **lower.** `IsLeast.1` gives `A j < A (j + 1)` and, for every consecutive sum
  `m`, `A (j + 1) ≠ m`. Naming the sums that land strictly between `A j` and `v`
  closes the gap, and `omega` finishes `A (j + 1) = v`.

The gaps that have to be excluded by hand are `3` at `j = 1`, `6` and `7` at
`j = 3`, `9` at `j = 4`, and `11, 12, 13` at `j = 5`; at `j = 0, 2, 6` the
candidate is `A j + 1` and there is nothing in between.
Only the surrounding scaffolding (the header, `import Mathlib`, and the
`open Filter` needed for `atTop`) is ours; every line of the two declarations
is upstream's.

Below the vendored block, and clearly separated from it, sits `IsGoodFor.exists_sum_Icc`:
the classical MacMahon completeness lemma that `IsGoodFor` encodes but never states.
That one is ours and it is proved, so the only `sorry` left in this file is the
vendored one on `erdos_359.parts.i`.
`open Filter Asymptotics` needed for `atTop` and `~[·]`) is ours; every line
of the two declarations is upstream's.

Below those, `erdos_359.parts.i_of_isGoodFor_1_asymptotic` is **ours**: a
reduction saying that Andrews' conjectured asymptotic implies part (i). Its
hypothesis is the conclusion of upstream's
`erdos_359.variants.isGoodFor_1_asymptotic`, copied verbatim, and its
conclusion is the conclusion of `erdos_359.parts.i`, copied verbatim. It also
carries a `sorry`: the reduction is stated here, not proved here.
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

/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then the first few terms of $A$ are $1,2,4,5,8,10,14,15,...$. -/
theorem erdos_359.variants.isGoodFor_1_low_values (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15} := by
  obtain ⟨h0, -, hkey⟩ := hA
  -- `Finset.Icc a b ⊆ Finset.Iic j` with `a ≤ b` puts the whole block below `j`.
  have hbound : ∀ {a b j : ℕ}, Finset.Icc a b ⊆ Finset.Iic j → a ≤ b → b ≤ j :=
    fun h hab => by simpa using h (Finset.mem_Icc.2 ⟨hab, le_rfl⟩)
  -- j = 0 : the sums of `A 0 = 1` alone are `0, 1`, so `A 1 = 2`.
  have h1 : A 1 = 2 := by
    have hle : A 1 ≤ 2 := (hkey 0).2 ⟨by omega, by
      intro a b hab
      by_cases hab' : a ≤ b
      · have hb := hbound hab hab'
        have ha : a ≤ 0 := le_trans hab' hb
        interval_cases a
        interval_cases b
        simp [h0]
      · rw [Finset.Icc_eq_empty (by omega)]; simp⟩
    have hgt : A 0 < A 1 := (hkey 0).1.1
    omega
  -- j = 1 : the sums are `0, 1, 2, 3`, so `A 2 = 4`.
  have h2 : A 2 = 4 := by
    have hle : A 2 ≤ 4 := (hkey 1).2 ⟨by omega, by
      intro a b hab
      by_cases hab' : a ≤ b
      · have hb := hbound hab hab'
        have ha : a ≤ 1 := le_trans hab' hb
        interval_cases a <;> interval_cases b <;> simp [Finset.sum_Icc_succ_top, h0, h1]
      · rw [Finset.Icc_eq_empty (by omega)]; simp⟩
    have hgt : A 1 < A 2 := (hkey 1).1.1
    have e01 : ∑ i ∈ Finset.Icc 0 1, A i = 3 := by
      simp [Finset.sum_Icc_succ_top, h0, h1]
    have n3 : A 2 ≠ 3 := by have h := (hkey 1).1.2 0 1 (by decide); rwa [e01] at h
    omega
  -- j = 2 : `5` is the first gap above `A 2 = 4`.
  have h3 : A 3 = 5 := by
    have hle : A 3 ≤ 5 := (hkey 2).2 ⟨by omega, by
      intro a b hab
      by_cases hab' : a ≤ b
      · have hb := hbound hab hab'
        have ha : a ≤ 2 := le_trans hab' hb
        interval_cases a <;> interval_cases b <;> simp [Finset.sum_Icc_succ_top, h0, h1, h2]
      · rw [Finset.Icc_eq_empty (by omega)]; simp⟩
    have hgt : A 2 < A 3 := (hkey 2).1.1
    omega
  -- j = 3 : `6 = A 1 + A 2` and `7 = A 0 + A 1 + A 2` are blocked, so `A 4 = 8`.
  have h4 : A 4 = 8 := by
    have hle : A 4 ≤ 8 := (hkey 3).2 ⟨by omega, by
      intro a b hab
      by_cases hab' : a ≤ b
      · have hb := hbound hab hab'
        have ha : a ≤ 3 := le_trans hab' hb
        interval_cases a <;> interval_cases b <;> simp [Finset.sum_Icc_succ_top, h0, h1, h2, h3]
      · rw [Finset.Icc_eq_empty (by omega)]; simp⟩
    have hgt : A 3 < A 4 := (hkey 3).1.1
    have e12 : ∑ i ∈ Finset.Icc 1 2, A i = 6 := by
      simp [Finset.sum_Icc_succ_top, h1, h2]
    have e02 : ∑ i ∈ Finset.Icc 0 2, A i = 7 := by
      simp [Finset.sum_Icc_succ_top, h0, h1, h2]
    have n6 : A 4 ≠ 6 := by have h := (hkey 3).1.2 1 2 (by decide); rwa [e12] at h
    have n7 : A 4 ≠ 7 := by have h := (hkey 3).1.2 0 2 (by decide); rwa [e02] at h
    omega
  -- j = 4 : `9 = A 2 + A 3` is blocked, so `A 5 = 10`.
  have h5 : A 5 = 10 := by
    have hle : A 5 ≤ 10 := (hkey 4).2 ⟨by omega, by
      intro a b hab
      by_cases hab' : a ≤ b
      · have hb := hbound hab hab'
        have ha : a ≤ 4 := le_trans hab' hb
        interval_cases a <;> interval_cases b <;>
          simp [Finset.sum_Icc_succ_top, h0, h1, h2, h3, h4]
      · rw [Finset.Icc_eq_empty (by omega)]; simp⟩
    have hgt : A 4 < A 5 := (hkey 4).1.1
    have e23 : ∑ i ∈ Finset.Icc 2 3, A i = 9 := by
      simp [Finset.sum_Icc_succ_top, h2, h3]
    have n9 : A 5 ≠ 9 := by have h := (hkey 4).1.2 2 3 (by decide); rwa [e23] at h
    omega
  -- j = 5 : `11, 12, 13` are all blocked, so `A 6 = 14`.
  have h6 : A 6 = 14 := by
    have hle : A 6 ≤ 14 := (hkey 5).2 ⟨by omega, by
      intro a b hab
      by_cases hab' : a ≤ b
      · have hb := hbound hab hab'
        have ha : a ≤ 5 := le_trans hab' hb
        interval_cases a <;> interval_cases b <;>
          simp [Finset.sum_Icc_succ_top, h0, h1, h2, h3, h4, h5]
      · rw [Finset.Icc_eq_empty (by omega)]; simp⟩
    have hgt : A 5 < A 6 := (hkey 5).1.1
    have e13 : ∑ i ∈ Finset.Icc 1 3, A i = 11 := by
      simp [Finset.sum_Icc_succ_top, h1, h2, h3]
    have e03 : ∑ i ∈ Finset.Icc 0 3, A i = 12 := by
      simp [Finset.sum_Icc_succ_top, h0, h1, h2, h3]
    have e34 : ∑ i ∈ Finset.Icc 3 4, A i = 13 := by
      simp [Finset.sum_Icc_succ_top, h3, h4]
    have n11 : A 6 ≠ 11 := by have h := (hkey 5).1.2 1 3 (by decide); rwa [e13] at h
    have n12 : A 6 ≠ 12 := by have h := (hkey 5).1.2 0 3 (by decide); rwa [e03] at h
    have n13 : A 6 ≠ 13 := by have h := (hkey 5).1.2 3 4 (by decide); rwa [e34] at h
    omega
  -- j = 6 : `15` is the first gap above `A 6 = 14`.
  have h7 : A 7 = 15 := by
    have hle : A 7 ≤ 15 := (hkey 6).2 ⟨by omega, by
      intro a b hab
      by_cases hab' : a ≤ b
      · have hb := hbound hab hab'
        have ha : a ≤ 6 := le_trans hab' hb
        interval_cases a <;> interval_cases b <;>
          simp [Finset.sum_Icc_succ_top, h0, h1, h2, h3, h4, h5, h6]
      · rw [Finset.Icc_eq_empty (by omega)]; simp⟩
    have hgt : A 6 < A 7 := (hkey 6).1.1
    omega
  have hIic : Set.Iic 7 = ({0, 1, 2, 3, 4, 5, 6, 7} : Set ℕ) := by
    ext x; simp [Set.mem_Iic]; omega
  rw [hIic]
  simp [Set.image_insert_eq, h0, h1, h2, h3, h4, h5, h6, h7]
/- ---------------------------------------------------------------------------
End of the vendored block. Everything below is ours.
--------------------------------------------------------------------------- -/

/-- **MacMahon completeness.** The greedy condition in `IsGoodFor A n` never says outright
that `A` represents everything, but it forces exactly that above its first term: if
`IsGoodFor A n`, then every `N ≥ n` is a sum of a nonempty block of *consecutive* terms
of `A`.

The reason is the third clause of `IsGoodFor`, read in both directions. `A (j + 1)` is a
*least* element of the set of non-representable numbers above `A j`, so on the one hand
every `m` with `A j < m < A (j + 1)` fails membership, and since `A j < m` holds that
failure can only be representability, `m = ∑ i ∈ Finset.Icc a b, A i` for some block
inside `Finset.Iic j`; on the other hand each `A k` is its own one-term block
`Finset.Icc k k`, and `A 0 = n`. A strictly monotone `A : ℕ → ℕ` is unbounded, so every
`N ≥ n` is caught by one of those cases.

Stated with `a ≤ b` so that `Finset.Icc a b` is nonempty and the sum is a genuine
consecutive run rather than the empty sum. -/
theorem IsGoodFor.exists_sum_Icc {A : ℕ → ℕ} {n : ℕ} (hA : IsGoodFor A n) {N : ℕ}
    (hN : n ≤ N) : ∃ a b : ℕ, a ≤ b ∧ N = ∑ i ∈ Finset.Icc a b, A i := by
  obtain ⟨hA0, hmono, hleast⟩ := hA
  -- The induction is on the index `j`, not on `N`: what has to be climbed is the ladder
  -- `A 0 < A 1 < ⋯`, and every `N` below `A j` is settled in one step from the `j`-th rung.
  -- Unboundedness (`j ≤ A j`, from strict monotonicity on `ℕ`) then puts every `N` under
  -- some rung, namely the `N`-th.
  suffices H : ∀ j N, n ≤ N → N ≤ A j → ∃ a b : ℕ, a ≤ b ∧ N = ∑ i ∈ Finset.Icc a b, A i from
    H N N hN hmono.le_apply
  intro j
  induction j with
  | zero =>
    -- Nothing below the bottom rung: `n ≤ N ≤ A 0 = n`, so `N = A 0` is the one-term block.
    intro N hn hle
    rw [hA0] at hle
    refine ⟨0, 0, le_rfl, ?_⟩
    rw [Finset.Icc_self, Finset.sum_singleton, hA0]
    omega
  | succ j ih =>
    intro N hn hle
    rcases le_or_gt N (A j) with h | h
    · exact ih N hn h
    rcases eq_or_lt_of_le hle with rfl | hlt
    · -- `N = A (j + 1)`: its own one-term block `Finset.Icc (j + 1) (j + 1)`.
      exact ⟨j + 1, j + 1, le_rfl, by rw [Finset.Icc_self, Finset.sum_singleton]⟩
    -- `A j < N < A (j + 1)`. `A (j + 1)` is a *lower* bound on the non-representables above
    -- `A j`, so `N` is not one of them; as `A j < N` does hold, the failure is representability.
    have hNS : ¬(A j < N ∧ ∀ a b : ℕ, Finset.Icc a b ⊆ Finset.Iic j →
        N ≠ ∑ i ∈ Finset.Icc a b, A i) := fun hmem =>
      absurd ((hleast j).2 hmem) (not_le.mpr hlt)
    push Not at hNS
    obtain ⟨a, b, -, heq⟩ := hNS h
    refine ⟨a, b, ?_, heq⟩
    -- The block is nonempty: an empty `Finset.Icc a b` would force `N = 0`, yet `A j < N`.
    by_contra hab
    rw [Finset.Icc_eq_empty hab, Finset.sum_empty] at heq
    omega


set_option linter.unusedVariables false in
/-- **Andrews' conjecture implies part (i).** If `A` is good for `1` and
satisfies the conjectured asymptotic $a_k \sim \frac{k \log k}{\log\log k}$
-- i.e. the conclusion of `erdos_359.variants.isGoodFor_1_asymptotic`, stated
here verbatim as a hypothesis -- then $a_k / k \to \infty$, which is the
conclusion of `erdos_359.parts.i`.

This is a reduction, not a proof of either: it is what turns the open
asymptotic into the open part (i). The reduction itself is a genuine (if far
easier) piece of work, proved below: from `A k ~ k log k / log log k` and
`log k / log log k → ∞` one gets `A k / k → ∞`.

Note that `hA` is not used: the reduction is pure real-analysis asymptotics
and needs nothing combinatorial about `A` beyond `hasymp`. It is kept so the
statement reads as "part (i) for a set good for 1, given the asymptotic":
hence the `set_option` above rather than renaming it to `_hA`. -/
theorem erdos_359.parts.i_of_isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1)
    (hasymp : (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log)) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  -- `x / log x → ∞`, read off `exp z / z → ∞` at `z = log x`.
  have hdiv : Tendsto (fun x : ℝ ↦ x / x.log) atTop atTop := by
    refine ((Real.tendsto_exp_div_pow_atTop 1).comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Real.exp_log hx]
  -- hence `log k / log log k → ∞` along the naturals, `log` and `↑·` both tending to `atTop`.
  have hlog : Tendsto (fun k : ℕ ↦ (k : ℝ).log / (k : ℝ).log.log) atTop atTop :=
    (hdiv.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  -- which is exactly the conjectured model divided by `k`, once `k ≠ 0`.
  have hmodel :
      Tendsto (fun k : ℕ ↦ (k * (k : ℝ).log / (k : ℝ).log.log) / k) atTop atTop := by
    refine hlog.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with k hk
    rw [div_right_comm, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hk)]
  -- `A k / k ~ (k log k / log log k) / k`, and `~` transfers a limit `atTop`.
  exact (hasymp.div (IsEquivalent.refl (u := fun k : ℕ ↦ (k : ℝ)))).symm.tendsto_atTop hmodel


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
