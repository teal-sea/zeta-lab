/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Helpers_finite

/-!
# S11: the block energy bound  ([A] Lemma 4.2, eq:block-energy)

`E_m + (6/p)(y_m − y_1) ≥ c(m − 6)` for `y_1 < ⋯ < y_m`, `m ≥ 7`, from the accepted seven-point
inequality `F6 ≥ c` (S10) summed over the `m − 6` consecutive seven-point windows.  The `1/500` of the
paper is `6/p` at `p = 3000` ([A] line 348: "each single gap occurs at most six times").

Proved here (bridge/finite).  The proof is the paper's, made explicit: the points are sorted by
`Finset.orderEmbOfFin`; the `m − 6` window gap vectors are nonnegative so `hCert` applies to each;
the linear terms telescope to `Σ_{i<6} (y_{m−6+i} − y_i) ≤ 6 (y_{m−1} − y_0)`; the quadratic terms
are regrouped by the pair `(i+a, i+b)` they mention (`Finset.sum_fiberwise_of_maps_to`), each fibre
has at most `7 − r` elements (`r = b − a`, injecting on `a`) of common value `(2/(7−r)) w`, and the
resulting `2 w(y_v − y_u)` per pair `u < v` is dominated by the two terms `(u,v), (v,u)` of the
energy (`w` is even).
-/

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pair-coefficient of `F6`, as a function of the gap count `r = b − a`. -/
def pairCoef (r : ℕ) : ℝ := 2 / ((7 : ℝ) - (r : ℝ))

/-- The energy of the sorted ordinates, over `Fin m × Fin m`. -/
lemma energyOn_eq_sorted {m : ℕ} (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m) :
    energyOn x univ = ∑ r : Fin m × Fin m,
      if r.1 = r.2 then 0 else wfun ((univ.image x).orderEmbOfFin hS r.1
        - (univ.image x).orderEmbOfFin hS r.2) := by
  classical
  set S := univ.image x with hSdef
  set y := S.orderEmbOfFin hS with hydef
  have hy : Function.Injective y := y.injective
  have hSy : univ.image y = S := by
    apply Finset.coe_injective
    rw [coe_image, coe_univ, Set.image_univ]
    exact Finset.range_orderEmbOfFin S hS
  unfold energyOn
  have h1 : ∀ i j : ι, (if i = j then (0 : ℝ) else wfun (x i - x j))
      = (if x i = x j then 0 else wfun (x i - x j)) := by
    intro i j; simp [hx.eq_iff]
  simp_rw [h1]
  have e1 : ∀ i : ι, ∑ j, (if x i = x j then (0 : ℝ) else wfun (x i - x j))
      = ∑ t ∈ S, (if x i = t then 0 else wfun (x i - t)) := fun i =>
    (sum_image (f := fun t => if x i = t then (0 : ℝ) else wfun (x i - t))
      (fun a _ b _ h => hx h)).symm
  simp_rw [e1]
  rw [← sum_image (f := fun s => ∑ t ∈ S, (if s = t then (0 : ℝ) else wfun (s - t)))
    (fun a _ b _ h => hx h)]
  rw [← hSdef, ← hSy, sum_image (fun a _ b _ h => hy h)]
  simp_rw [sum_image (fun a _ b _ h => hy h)]
  simp only [hy.eq_iff]
  exact (Fintype.sum_prod_type' (f := fun k l => if k = l then (0 : ℝ) else wfun (y k - y l))).symm

/-- The quadratic part of the summed window functionals is dominated by the energy. -/
lemma window_pairs_le_energy {m : ℕ} (hm : 7 ≤ m) (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - 6), ∑ a : Fin 7, ∑ b : Fin 7,
        (if (a : ℕ) < (b : ℕ) then
          pairCoef ((b : ℕ) - (a : ℕ))
            * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ energyOn x univ := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega
  -- the triple index set and the summand
  set T : Finset (ℕ × (Fin 7 × Fin 7)) :=
    (range (m - 6) ×ˢ (univ : Finset (Fin 7 × Fin 7))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin 7 × Fin 7) → ℝ := fun t =>
    pairCoef ((t.2.2 : ℕ) - (t.2.1 : ℕ)) * wfun (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
  have hLHS : ∑ i ∈ range (m - 6), ∑ a : Fin 7, ∑ b : Fin 7,
      (if (a : ℕ) < (b : ℕ) then
        pairCoef ((b : ℕ) - (a : ℕ)) * wfun (Y (i + b) - Y (i + a)) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin 7) => if (a : ℕ) < (b : ℕ) then
      pairCoef ((b : ℕ) - (a : ℕ)) * wfun (Y (i + b) - Y (i + a)) else 0)).symm
  rw [hLHS]
  -- the pair map and its image
  set φ : ℕ × (Fin 7 × Fin 7) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
  set I := T.image φ with hIdef
  have hmem : ∀ t ∈ T, t.1 < m - 6 ∧ (t.2.1 : ℕ) < t.2.2 := by
    intro t ht
    simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
    exact ht
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < 7 := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨h1, h2⟩ := hmem t ht
    have hb := t.2.2.2
    simp only [hφdef]
    omega
  -- fibrewise regrouping
  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]
  -- each fibre contributes at most `2 w(Y q.2 − Y q.1)`
  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q), f t = pairCoef r * wfun (Y q.2 - Y q.1) := by
      intro t ht
      rw [mem_filter] at ht
      obtain ⟨ht, hφt⟩ := ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
      simp only [hfdef]
      rw [e1, e2, hrdef, ← e1, ← e2, Nat.add_sub_add_left]
    rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]
    -- the fibre has at most `7 − r` elements
    have hcard : (T.filter (fun t => φ t = q)).card ≤ 7 - r := by
      rw [← card_range (7 - r)]
      refine card_le_card_of_injOn (fun t => (t.2.1 : ℕ)) ?_ ?_
      · intro t ht
        rw [mem_coe, mem_filter] at ht
        obtain ⟨ht, hφt⟩ := ht
        have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
        have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
        have hb := t.2.2.2
        simp only [coe_range, Set.mem_Iio]
        omega
      · intro t ht t' ht' hee
        rw [mem_coe, mem_filter] at ht ht'
        have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
        have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
        have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
        have e2' : t'.1 + (t'.2.2 : ℕ) = q.2 := congrArg Prod.snd ht'.2
        simp only at hee
        have ha : t.2.1 = t'.2.1 := Fin.ext hee
        have hi : t.1 = t'.1 := by omega
        have hb : t.2.2 = t'.2.2 := Fin.ext (by omega)
        exact Prod.ext hi (Prod.ext ha hb)
    have hr7 : (r : ℝ) < 7 := by exact_mod_cast hq3
    have hcoef : 0 ≤ pairCoef r := by
      unfold pairCoef; apply div_nonneg (by norm_num); linarith
    have hcardR : ((T.filter (fun t => φ t = q)).card : ℝ) ≤ 7 - (r : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      rwa [Nat.cast_sub hq3.le] at this
    calc ((T.filter (fun t => φ t = q)).card : ℝ) * (pairCoef r * wfun (Y q.2 - Y q.1))
        ≤ (7 - (r : ℝ)) * (pairCoef r * wfun (Y q.2 - Y q.1)) :=
          mul_le_mul_of_nonneg_right hcardR (mul_nonneg hcoef (wfun_nonneg _))
      _ = 2 * wfun (Y q.2 - Y q.1) := by
          have h7 : (7 : ℝ) - (r : ℝ) ≠ 0 := by linarith
          unfold pairCoef
          field_simp
  refine (sum_le_sum hfib).trans ?_
  -- the pairs `(u,v)` and `(v,u)` of the energy
  rw [energyOn_eq_sorted x hx hS, ← hydef]
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else wfun (y r.1 - y r.2) with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), wfun_sub_comm]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [hG1 q hq, hG2 q hq]; ring
  have hinj₁ : Set.InjOn ψ₁ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.1 h.2
  have hinj₂ : Set.InjOn ψ₂ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
    rw [disjoint_left]
    intro r hr1 hr2
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
    obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
    omega
  have hGnn : ∀ r, 0 ≤ G r := by
    intro r; simp only [hGdef]; split_ifs
    · exact le_rfl
    · exact wfun_nonneg _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r

/-- **S11** ([A] Lemma 4.2).  For `m ≥ 7` points with distinct ordinates `x`,
`c(m − 6) ≤ Σ_{i≠j} w(xᵢ − xⱼ) + (6/p)·span`, given the certificate `F6 ≥ c` on `g ≥ 0`.
PROVED (bridge/finite); see the module docstring for the argument. -/
theorem block_energy {c : ℝ} {p : ℕ} (hp : 0 < p)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g)
    {m : ℕ} (hm : 7 ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - 6) ≤ energyOn x univ + (6 / (p : ℝ)) * spanOf x univ := by
  classical
  -- sort the points
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega
  -- the certificate on every window
  have hwin : ∀ i ∈ range (m - 6), c ≤ F6 p (windowGaps Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - 6) ≤ ∑ i ∈ range (m - 6), F6 p (windowGaps Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - 6 : ℕ) : ℝ) = (m : ℝ) - 6 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast] at h
    linarith
  simp_rw [F6_windowGaps] at hsum
  rw [sum_add_distrib, ← mul_sum] at hsum
  -- the linear term
  have hlin : ∑ i ∈ range (m - 6), (Y (i + 6) - Y i) ≤ 6 * spanOf x univ := by
    rw [sum_shift_six_sub]
    have hterm : ∀ i ∈ range 6, Y (m - 6 + i) - Y i ≤ Y (m - 1) - Y 0 := by
      intro i hi
      rw [mem_range] at hi
      have h1 := sortedExt_mono hymono (a := m - 6 + i) (b := m - 1) (by omega) (by omega)
      have h2 := sortedExt_mono hymono (a := 0) (b := i) (by omega) (by omega)
      linarith
    have hspan : Y (m - 1) - Y 0 ≤ spanOf x univ := by
      obtain ⟨i₀, -, hi₀⟩ := mem_image.mp (hymem ⟨m - 1, by omega⟩)
      obtain ⟨j₀, -, hj₀⟩ := mem_image.mp (hymem ⟨0, hm0⟩)
      rw [hYdef, sortedExt_of_lt y (by omega : m - 1 < m), sortedExt_of_lt y hm0, ← hi₀, ← hj₀]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ i₀) (mem_univ j₀))
    calc ∑ i ∈ range 6, (Y (m - 6 + i) - Y i)
        ≤ ∑ i ∈ range 6, (Y (m - 1) - Y 0) := sum_le_sum hterm
      _ = 6 * (Y (m - 1) - Y 0) := by simp; ring
      _ ≤ 6 * spanOf x univ := by linarith
  -- the quadratic term
  have hquad := window_pairs_le_energy hm x hx hS
  simp only [pairCoef] at hquad
  rw [← hydef, ← hYdef] at hquad
  have hp' : 0 ≤ 1 / (p : ℝ) := by positivity
  calc c * ((m : ℝ) - 6)
      ≤ _ := hsum
    _ ≤ (1 / (p : ℝ)) * (6 * spanOf x univ) + energyOn x univ := by
        gcongr
    _ = energyOn x univ + (6 / (p : ℝ)) * spanOf x univ := by ring

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms energyOn_eq_sorted
#print axioms window_pairs_le_energy
#print axioms block_energy

end Zeta23Ext.Bridge
