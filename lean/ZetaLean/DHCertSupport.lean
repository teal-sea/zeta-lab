/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.DHAssembly
import ZetaLean.DHZeroCriterion

/-!
# Support layer for the generated rung-3 certificate

The offline certification of the Davenport–Heilbronn off-line zero covers
the frontier of `dhSquare` with sub-boxes and certifies, per box, a lower
bound on `‖DH‖ over the whole box`.  The generated per-box proofs should be
long lists of *instances*, not of *arguments* — so every piece of reasoning
that can be proved once, parametrically, lives here:

* `ComplexInterval.invC` / `contains_invC` — the inverse of a complex box
  bounded away from `0`, via `1/z = conj z / |z|²` in real interval
  arithmetic.  Needed because the antiderivative correction `dhAnti`
  divides by `5(1−s)` with `s` ranging over a box.
* `rpow_neg_div_le` — certify `x^{-(a/b)} ≤ P` by the single rational
  inequality `1 ≤ P^b · x^a`: the `b`-th-root trick that turns the tail
  radius's real power into `norm_num` arithmetic.
* `DH_mem_of_partial_enclosure_order2_boxed` — the boxed-`s` assembly
  theorem: every hypothesis beyond the two structural containments is a
  rational inequality a generated `norm_num` can discharge.
* `dhSumBoxes` / `contains_dhSumBoxes` — the partial-sum box as a fold,
  with containment by induction, so a generated file only supplies the
  per-term facts.
* `contains_dhBlock_of_terms` / `contains_dhAnti_of_terms` /
  `contains_inv5sBox` / `contains_half_of` / `contains_corrected` — the
  correction terms of the order-2 bound, assembled from term boxes once.
* `norm_lt_of_enclosure` / `le_norm_of_enclosure` — reading the two square
  criterion inequalities off computed boxes.
-/

open Complex Finset

namespace ZetaLean

namespace ComplexInterval

/-- The squared-norm interval of a complex box: contains `normSq z` for
every `z` in the box. -/
def normSqI (x : ComplexInterval) : Interval :=
  (x.re.mul x.re).add (x.im.mul x.im)

theorem contains_normSqI {x : ComplexInterval} {z : ℂ} (hz : x.contains z) :
    (x.normSqI).contains (Complex.normSq z) := by
  have h := Interval.contains_add (Interval.contains_mul hz.1 hz.1)
    (Interval.contains_mul hz.2 hz.2)
  rwa [show z.re * z.re + z.im * z.im = Complex.normSq z from
    (Complex.normSq_apply z).symm] at h

/-- Inverse of a complex box whose squared norm is bounded away from zero:
`1/z = conj z / |z|²`, componentwise in real interval arithmetic. -/
def invC (x : ComplexInterval) (hx : 0 < x.normSqI.lo) : ComplexInterval :=
  { re := x.re.mul (x.normSqI.inv' hx),
    im := (x.im.neg).mul (x.normSqI.inv' hx) }

theorem contains_invC {x : ComplexInterval} (hx : 0 < x.normSqI.lo)
    {z : ℂ} (hz : x.contains z) : (x.invC hx).contains z⁻¹ := by
  have hd := contains_normSqI hz
  have hinv := Interval.contains_inv' hx hd
  constructor
  · show (x.re.mul (x.normSqI.inv' hx)).contains (z⁻¹).re
    rw [show (z⁻¹).re = z.re * (Complex.normSq z)⁻¹ by
      rw [Complex.inv_re, div_eq_mul_inv]]
    exact Interval.contains_mul hz.1 hinv
  · show ((x.im.neg).mul (x.normSqI.inv' hx)).contains (z⁻¹).im
    rw [show (z⁻¹).im = -z.im * (Complex.normSq z)⁻¹ by
      rw [Complex.inv_im, div_eq_mul_inv, neg_mul]]
    exact Interval.contains_mul (Interval.contains_neg hz.2) hinv

end ComplexInterval

/-- **The `b`-th-root trick.**  A rational upper bound on `x^{-(a/b)}`
follows from the single rational inequality `1 ≤ P^b · x^a` — which
`norm_num` checks — for `1 ≤ x`, `0 < P`. -/
theorem rpow_neg_div_le {x : ℝ} (hx : 1 ≤ x) {a b : ℕ} (hb : 0 < b) {P : ℚ}
    (hP : 0 < P) (hpow : 1 ≤ (P : ℝ) ^ b * x ^ a) :
    x ^ (-((a : ℝ) / (b : ℝ))) ≤ (P : ℝ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hP' : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hxr : (0 : ℝ) < x ^ ((a : ℝ) / (b : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hxb : (x ^ ((a : ℝ) / (b : ℝ))) ^ b = x ^ a := by
    rw [← Real.rpow_natCast (x ^ ((a : ℝ) / (b : ℝ))) b, ← Real.rpow_mul hx0.le,
      div_mul_cancel₀ _ (by exact_mod_cast hb.ne' : (b : ℝ) ≠ 0),
      Real.rpow_natCast]
  have key : (1 : ℝ) ≤ (P : ℝ) * x ^ ((a : ℝ) / (b : ℝ)) := by
    have h1 : (1 : ℝ) ≤ ((P : ℝ) * x ^ ((a : ℝ) / (b : ℝ))) ^ b := by
      rw [mul_pow, hxb]
      exact hpow
    by_contra hlt
    push_neg at hlt
    have h2 : ((P : ℝ) * x ^ ((a : ℝ) / (b : ℝ))) ^ b < 1 :=
      pow_lt_one₀ (by positivity) hlt hb.ne'
    linarith
  have hfin : (x ^ ((a : ℝ) / (b : ℝ)))⁻¹ ≤ (P : ℝ) := by
    have h := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hxr.le)
    rw [mul_one] at h
    calc (x ^ ((a : ℝ) / (b : ℝ)))⁻¹
        ≤ (x ^ ((a : ℝ) / (b : ℝ)))⁻¹ * ((P : ℝ) * x ^ ((a : ℝ) / (b : ℝ))) := h
      _ = (P : ℝ) := by
          rw [mul_comm (P : ℝ), ← mul_assoc, inv_mul_cancel₀ hxr.ne', one_mul]
  rw [Real.rpow_neg hx0.le]
  exact hfin

namespace DH

/-! ### Coefficient boxes, public -/

/-- The κ coefficient box, in `ℂ` (public twin of `DHDemo`'s). -/
def kappaCBox : ComplexInterval := { re := kappaI, im := ZetaLean.Interval.exact 0 }

theorem contains_kappaCBox : kappaCBox.contains ((dh_kappa : ℝ) : ℂ) :=
  ⟨by rw [Complex.ofReal_re]; exact contains_kappaI,
   by rw [Complex.ofReal_im]; simpa [kappaCBox] using ZetaLean.Interval.contains_exact 0⟩

theorem contains_natCBox (n : ℕ) :
    (ComplexInterval.exact n 0).contains ((n : ℕ) : ℂ) := by
  have h := ComplexInterval.contains_exact (n : ℚ) 0
  rwa [show (⟨(((n : ℚ)) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = ((n : ℕ) : ℂ) by
    apply Complex.ext <;> push_cast <;> simp] at h

/-- The DH coefficient box for index `m`, following the period-5 pattern. -/
def coeffBox (m : ℕ) : ComplexInterval :=
  match m % 5 with
  | 1 => ComplexInterval.exact 1 0
  | 2 => kappaCBox
  | 3 => kappaCBox.neg
  | 4 => ComplexInterval.exact (-1) 0
  | _ => ComplexInterval.exact 0 0

theorem contains_oneBox : (ComplexInterval.exact 1 0).contains ((1 : ℝ) : ℂ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [ComplexInterval.exact, ZetaLean.Interval.exact, ZetaLean.Interval.contains]

theorem contains_negOneBox :
    (ComplexInterval.exact (-1) 0).contains ((-1 : ℝ) : ℂ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [ComplexInterval.exact, ZetaLean.Interval.exact, ZetaLean.Interval.contains]

theorem contains_negKappaCBox : kappaCBox.neg.contains ((-dh_kappa : ℝ) : ℂ) := by
  have h := ComplexInterval.contains_neg contains_kappaCBox
  rwa [show -((dh_kappa : ℝ) : ℂ) = ((-dh_kappa : ℝ) : ℂ) by push_cast; ring] at h

/-- A vanishing-coefficient series term is contained in the zero box. -/
theorem contains_coeff_term_zero {s : ℂ} (m : ℕ) (h : dh_coeff m = 0) :
    (ComplexInterval.exact 0 0).contains ((dh_coeff m : ℂ) * (m : ℂ) ^ (-s)) := by
  rw [h]
  simpa using ComplexInterval.contains_zero

/-- A nonvanishing series term from its power box: the coefficient box is
read off `m % 5`. -/
theorem contains_coeff_term_ne {s : ℂ} (m : ℕ) (h : m % 5 ≠ 0)
    {t : ComplexInterval} (ht : t.contains ((m : ℂ) ^ (-s))) :
    ((coeffBox m).mul t).contains ((dh_coeff m : ℂ) * (m : ℂ) ^ (-s)) := by
  have hm5 : m % 5 < 5 := Nat.mod_lt m (by norm_num)
  have hj : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  rcases hj with h1 | h1 | h1 | h1
  · have hc : dh_coeff m = 1 := by unfold dh_coeff; rw [h1]; rfl
    have hcb : coeffBox m = ComplexInterval.exact 1 0 := by unfold coeffBox; rw [h1]; rfl
    rw [hc, hcb]
    exact ComplexInterval.contains_mul contains_oneBox ht
  · have hc : dh_coeff m = dh_kappa := by unfold dh_coeff; rw [h1]; rfl
    have hcb : coeffBox m = kappaCBox := by unfold coeffBox; rw [h1]; rfl
    rw [hc, hcb]
    exact ComplexInterval.contains_mul contains_kappaCBox ht
  · have hc : dh_coeff m = -dh_kappa := by unfold dh_coeff; rw [h1]; rfl
    have hcb : coeffBox m = kappaCBox.neg := by unfold coeffBox; rw [h1]; rfl
    rw [hc, hcb]
    exact ComplexInterval.contains_mul contains_negKappaCBox ht
  · have hc : dh_coeff m = -1 := by unfold dh_coeff; rw [h1]; rfl
    have hcb : coeffBox m = ComplexInterval.exact (-1) 0 := by unfold coeffBox; rw [h1]; rfl
    rw [hc, hcb]
    exact ComplexInterval.contains_mul contains_negOneBox ht

/-! ### The partial-sum box as a fold -/

/-- Left fold of term boxes over `range N`. -/
def dhSumBoxes (t : ℕ → ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 0 0
  | N + 1 => (dhSumBoxes t N).add (t N)

theorem dhSumBoxes_zero (t : ℕ → ComplexInterval) :
    dhSumBoxes t 0 = ComplexInterval.exact 0 0 := rfl

theorem dhSumBoxes_succ (t : ℕ → ComplexInterval) (N : ℕ) :
    dhSumBoxes t (N + 1) = (dhSumBoxes t N).add (t N) := rfl

theorem contains_dhSumBoxes {s : ℂ} {t : ℕ → ComplexInterval} (N : ℕ)
    (ht : ∀ m < N, (t m).contains ((dh_coeff m : ℂ) * (m : ℂ) ^ (-s))) :
    (dhSumBoxes t N).contains
      (∑ n ∈ range N, (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)) := by
  induction N with
  | zero => simpa [dhSumBoxes] using ComplexInterval.contains_zero
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact ComplexInterval.contains_add
        (ih fun m hm => ht m (by omega)) (ht N (by omega))

/-! ### The order-2 correction terms, assembled once -/

/-- Splitting `m^{1−s} = m·m^{−s}` for a positive natural base. -/
theorem cpow_one_sub_natCast {m : ℕ} (hm : 0 < m) (s : ℂ) :
    ((m : ℕ) : ℂ) ^ ((1 : ℂ) - s) = ((m : ℕ) : ℂ) * ((m : ℕ) : ℂ) ^ (-s) := by
  rw [show (1 : ℂ) - s = 1 + -s by ring,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hm.ne'), Complex.cpow_one]

/-- `dhAnti` in terms of the four `n^{-s}` values it reuses. -/
theorem dhAnti_eq_terms (s : ℂ) (K : ℕ) :
    dhAnti s (K : ℝ)
      = (((K * 5 + 1 : ℕ) : ℂ) * ((K * 5 + 1 : ℕ) : ℂ) ^ (-s)
          - ((K * 5 + 4 : ℕ) : ℂ) * ((K * 5 + 4 : ℕ) : ℂ) ^ (-s)
          + (dh_kappa : ℂ) * (((K * 5 + 2 : ℕ) : ℂ) * ((K * 5 + 2 : ℕ) : ℂ) ^ (-s)
            - ((K * 5 + 3 : ℕ) : ℂ) * ((K * 5 + 3 : ℕ) : ℂ) ^ (-s)))
        * (5 * (1 - s))⁻¹ := by
  rw [dhAnti, dhPair, div_eq_mul_inv]
  congr 1
  have h1 : ((5 * ((K : ℕ) : ℝ) + 1 : ℝ) : ℂ) = ((K * 5 + 1 : ℕ) : ℂ) := by
    push_cast; ring
  have h2 : ((5 * ((K : ℕ) : ℝ) + 2 : ℝ) : ℂ) = ((K * 5 + 2 : ℕ) : ℂ) := by
    push_cast; ring
  have h3 : ((5 * ((K : ℕ) : ℝ) + 3 : ℝ) : ℂ) = ((K * 5 + 3 : ℕ) : ℂ) := by
    push_cast; ring
  have h4 : ((5 * ((K : ℕ) : ℝ) + 4 : ℝ) : ℂ) = ((K * 5 + 4 : ℕ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, h3, h4, cpow_one_sub_natCast (m := K * 5 + 1) (by omega) s,
    cpow_one_sub_natCast (m := K * 5 + 2) (by omega) s,
    cpow_one_sub_natCast (m := K * 5 + 3) (by omega) s,
    cpow_one_sub_natCast (m := K * 5 + 4) (by omega) s]

/-- The `K`-th block box from its four term boxes. -/
theorem contains_dhBlock_of_terms {s : ℂ} (K : ℕ)
    {t1 t2 t3 t4 : ComplexInterval}
    (h1 : t1.contains (((K * 5 + 1 : ℕ) : ℂ) ^ (-s)))
    (h2 : t2.contains (((K * 5 + 2 : ℕ) : ℂ) ^ (-s)))
    (h3 : t3.contains (((K * 5 + 3 : ℕ) : ℂ) ^ (-s)))
    (h4 : t4.contains (((K * 5 + 4 : ℕ) : ℂ) ^ (-s))) :
    ((t1.add t4.neg).add (kappaCBox.mul (t2.add t3.neg))).contains
      (dhBlock s K) := by
  rw [dhBlock_eq_pair]
  have hp1 := ComplexInterval.contains_add h1 (ComplexInterval.contains_neg h4)
  have hp2 := ComplexInterval.contains_add h2 (ComplexInterval.contains_neg h3)
  have h := ComplexInterval.contains_add hp1
    (ComplexInterval.contains_mul contains_kappaCBox hp2)
  rwa [show ((K * 5 + 1 : ℕ) : ℂ) ^ (-s) + -(((K * 5 + 4 : ℕ) : ℂ) ^ (-s))
      + ((dh_kappa : ℝ) : ℂ)
        * (((K * 5 + 2 : ℕ) : ℂ) ^ (-s) + -(((K * 5 + 3 : ℕ) : ℂ) ^ (-s)))
      = (((K * 5 + 1 : ℕ) : ℂ) ^ (-s) - ((K * 5 + 4 : ℕ) : ℂ) ^ (-s))
        + (dh_kappa : ℂ)
          * (((K * 5 + 2 : ℕ) : ℂ) ^ (-s) - ((K * 5 + 3 : ℕ) : ℂ) ^ (-s)) by
    ring] at h

/-- The box for `5(1−s)`, from a box for `s`. -/
def inv5sBox (S : ComplexInterval) : ComplexInterval :=
  (ComplexInterval.exact 5 0).mul ((ComplexInterval.exact 1 0).add S.neg)

theorem contains_inv5sBox {S : ComplexInterval} {s : ℂ} (hS : S.contains s)
    (h : 0 < (inv5sBox S).normSqI.lo) :
    ((inv5sBox S).invC h).contains ((5 * (1 - s))⁻¹) := by
  refine ComplexInterval.contains_invC h ?_
  have h5 : (ComplexInterval.exact 5 0).contains ((5 : ℕ) : ℂ) := contains_natCBox 5
  have h1 : (ComplexInterval.exact 1 0).contains ((1 : ℕ) : ℂ) := contains_natCBox 1
  have hsub := ComplexInterval.contains_add h1 (ComplexInterval.contains_neg hS)
  have h := ComplexInterval.contains_mul h5 hsub
  rwa [show ((5 : ℕ) : ℂ) * (((1 : ℕ) : ℂ) + -s) = 5 * (1 - s) by push_cast; ring]
    at h

/-- The antiderivative box from the four term boxes and an inverse box. -/
theorem contains_dhAnti_of_terms {s : ℂ} (K : ℕ)
    {t1 t2 t3 t4 V : ComplexInterval}
    (h1 : t1.contains (((K * 5 + 1 : ℕ) : ℂ) ^ (-s)))
    (h2 : t2.contains (((K * 5 + 2 : ℕ) : ℂ) ^ (-s)))
    (h3 : t3.contains (((K * 5 + 3 : ℕ) : ℂ) ^ (-s)))
    (h4 : t4.contains (((K * 5 + 4 : ℕ) : ℂ) ^ (-s)))
    (hV : V.contains ((5 * (1 - s))⁻¹)) :
    (((((ComplexInterval.exact (K * 5 + 1 : ℕ) 0).mul t1).add
        (((ComplexInterval.exact (K * 5 + 4 : ℕ) 0).mul t4).neg)).add
      (kappaCBox.mul (((ComplexInterval.exact (K * 5 + 2 : ℕ) 0).mul t2).add
        (((ComplexInterval.exact (K * 5 + 3 : ℕ) 0).mul t3).neg)))).mul V).contains
      (dhAnti s (K : ℝ)) := by
  rw [dhAnti_eq_terms]
  have e1 := ComplexInterval.contains_mul (contains_natCBox (K * 5 + 1)) h1
  have e2 := ComplexInterval.contains_mul (contains_natCBox (K * 5 + 2)) h2
  have e3 := ComplexInterval.contains_mul (contains_natCBox (K * 5 + 3)) h3
  have e4 := ComplexInterval.contains_mul (contains_natCBox (K * 5 + 4)) h4
  have hsum := ComplexInterval.contains_add
    (ComplexInterval.contains_add e1 (ComplexInterval.contains_neg e4))
    (ComplexInterval.contains_mul contains_kappaCBox
      (ComplexInterval.contains_add e2 (ComplexInterval.contains_neg e3)))
  have h := ComplexInterval.contains_mul hsum hV
  rwa [show ((K * 5 + 1 : ℕ) : ℂ) * ((K * 5 + 1 : ℕ) : ℂ) ^ (-s)
        + -(((K * 5 + 4 : ℕ) : ℂ) * ((K * 5 + 4 : ℕ) : ℂ) ^ (-s))
        + ((dh_kappa : ℝ) : ℂ)
          * (((K * 5 + 2 : ℕ) : ℂ) * ((K * 5 + 2 : ℕ) : ℂ) ^ (-s)
            + -(((K * 5 + 3 : ℕ) : ℂ) * ((K * 5 + 3 : ℕ) : ℂ) ^ (-s)))
      = ((K * 5 + 1 : ℕ) : ℂ) * ((K * 5 + 1 : ℕ) : ℂ) ^ (-s)
        - ((K * 5 + 4 : ℕ) : ℂ) * ((K * 5 + 4 : ℕ) : ℂ) ^ (-s)
        + (dh_kappa : ℂ)
          * (((K * 5 + 2 : ℕ) : ℂ) * ((K * 5 + 2 : ℕ) : ℂ) ^ (-s)
            - ((K * 5 + 3 : ℕ) : ℂ) * ((K * 5 + 3 : ℕ) : ℂ) ^ (-s)) by ring] at h

/-- Halving a contained value. -/
theorem contains_half_of {X : ComplexInterval} {z : ℂ} (h : X.contains z) :
    (X.mul (ComplexInterval.exact (1 / 2) 0)).contains (z / 2) := by
  have h2 := ComplexInterval.contains_mul h (ComplexInterval.contains_exact (1 / 2) 0)
  rwa [show z * (⟨((1 / 2 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = z / 2 by
    rw [show (⟨((1 / 2 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = (2⁻¹ : ℂ) by
      apply Complex.ext <;> push_cast <;> simp]
    ring] at h2

/-- The corrected centre `p + b − a` from its three boxes. -/
theorem contains_corrected {P B A : ComplexInterval} {p b a : ℂ}
    (hP : P.contains p) (hB : B.contains b) (hA : A.contains a) :
    ((P.add B).add A.neg).contains (p + b - a) := by
  have h := ComplexInterval.contains_add (ComplexInterval.contains_add hP hB)
    (ComplexInterval.contains_neg hA)
  rwa [show p + b + -a = p + b - a by ring] at h

/-! ### The boxed-`s` assembly theorem -/

/-- **Assembly at the order-2 bound, `s` ranging over a box.**  Beyond the
two structural containments (`hS`, `hB`), every hypothesis is a rational
inequality: the box's own corners give `0 < Re s` and `s ≠ 1`, rational
norm bounds `NS ≥ normBound S` (etc.) dominate the norms, and the tail
radius is certified through the `b`-th-root trick — `σlo + 2 = a/b` and
`1 ≤ P^b (5K+1)^a` make `P ≥ (5K+1)^{-σlo-2}`.  This is the theorem every
generated boundary-box (and centre) proof instantiates. -/
theorem DH_mem_of_partial_enclosure_order2_boxed
    {S : ComplexInterval} {s : ℂ} (hS : S.contains s)
    (hσ0 : 0 < S.re.lo) (him : 0 < S.im.lo)
    {K : ℕ} (hK : 1 ≤ K) {B : ComplexInterval}
    (hB : B.contains (∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
      + dhBlock s K / 2 - dhAnti s (K : ℝ)))
    {σlo : ℚ} (hσlo : 0 < σlo) (hσle : σlo ≤ S.re.lo)
    {a b : ℕ} (hb : 0 < b) (hab : σlo + 2 = (a : ℚ) / (b : ℚ))
    {P : ℚ} (hP : 0 < P) (hpow : 1 ≤ P ^ b * (5 * (K : ℚ) + 1) ^ a)
    {NS NS1 NS2 : ℚ}
    (hNS : ComplexInterval.normBound S ≤ NS)
    (hNS1 : ComplexInterval.normBound (S.add (ComplexInterval.exact 1 0)) ≤ NS1)
    (hNS2 : ComplexInterval.normBound (S.add (ComplexInterval.exact 2 0)) ≤ NS2)
    {r : ℚ}
    (hr : 5 / 8 * ((3 + 2840794 / 10000000) * NS * NS1 * NS2) * P / (σlo + 2) ≤ r) :
    (B.inflate r).contains (DH s) := by
  -- the box corners give the strip hypotheses
  have hsre : 0 < s.re := lt_of_lt_of_le (by exact_mod_cast hσ0) hS.1.1
  have hsim : 0 < s.im := lt_of_lt_of_le (by exact_mod_cast him) hS.2.1
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsim
    simp at hsim
  have htail := DH_tail_bound_order2 hsre hs1 hK
  -- rational norm bounds
  have hNSr : ‖s‖ ≤ (NS : ℝ) :=
    (ComplexInterval.norm_le_normBound hS).trans (by exact_mod_cast hNS)
  have hS1 : (S.add (ComplexInterval.exact 1 0)).contains (s + 1) := by
    have h := ComplexInterval.contains_add hS (contains_natCBox 1)
    rwa [show s + ((1 : ℕ) : ℂ) = s + 1 by push_cast; ring] at h
  have hS2 : (S.add (ComplexInterval.exact 2 0)).contains (s + 2) := by
    have h := ComplexInterval.contains_add hS (contains_natCBox 2)
    rwa [show s + ((2 : ℕ) : ℂ) = s + 2 by push_cast; ring] at h
  have hNS1r : ‖s + 1‖ ≤ (NS1 : ℝ) :=
    (ComplexInterval.norm_le_normBound hS1).trans (by exact_mod_cast hNS1)
  have hNS2r : ‖s + 2‖ ≤ (NS2 : ℝ) :=
    (ComplexInterval.norm_le_normBound hS2).trans (by exact_mod_cast hNS2)
  -- κ's rational upper bound
  have hκ : dh_kappa ≤ ((2840794 / 10000000 : ℚ) : ℝ) := contains_kappaI.2
  -- the rpow bound, via the b-th-root trick
  have hbase : (1 : ℝ) ≤ 5 * (K : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hPr : (5 * (K : ℝ) + 1) ^ (-((a : ℝ) / (b : ℝ))) ≤ (P : ℝ) := by
    refine rpow_neg_div_le hbase hb hP ?_
    have h := hpow
    have hcast : ((P ^ b * (5 * (K : ℚ) + 1) ^ a : ℚ) : ℝ)
        = (P : ℝ) ^ b * (5 * (K : ℝ) + 1) ^ a := by push_cast; ring
    calc (1 : ℝ) = ((1 : ℚ) : ℝ) := by norm_num
      _ ≤ ((P ^ b * (5 * (K : ℚ) + 1) ^ a : ℚ) : ℝ) := by exact_mod_cast h
      _ = _ := hcast
  have hab' : ((σlo : ℝ)) + 2 = (a : ℝ) / (b : ℝ) := by
    have h := congrArg (Rat.cast (K := ℝ)) hab
    push_cast at h
    exact h
  have hexp : -s.re - 2 ≤ -((a : ℝ) / (b : ℝ)) := by
    have hσler : (σlo : ℝ) ≤ (S.re.lo : ℝ) := by exact_mod_cast hσle
    have := hS.1.1
    linarith
  have hrpow : (5 * (K : ℝ) + 1) ^ (-s.re - 2) ≤ (P : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hbase hexp).trans hPr
  -- the σlo denominator
  have hden : ((σlo : ℝ)) + 2 ≤ s.re + 2 := by
    have hσler : (σlo : ℝ) ≤ (S.re.lo : ℝ) := by exact_mod_cast hσle
    have := hS.1.1
    linarith
  have hσ2 : (0 : ℝ) < (σlo : ℝ) + 2 := by
    have : (0 : ℝ) < (σlo : ℝ) := by exact_mod_cast hσlo
    linarith
  -- chain everything
  have hnn : (0 : ℝ) ≤ 3 + dh_kappa := by linarith [dh_kappa_nonneg]
  have hκh : (0 : ℝ) ≤ 3 + ((2840794 / 10000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hNS0 : (0 : ℝ) ≤ (NS : ℝ) := le_trans (norm_nonneg s) hNSr
  have hNS10 : (0 : ℝ) ≤ (NS1 : ℝ) := le_trans (norm_nonneg _) hNS1r
  have hNS20 : (0 : ℝ) ≤ (NS2 : ℝ) := le_trans (norm_nonneg _) hNS2r
  have hP0 : (0 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP.le
  have hA : (3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖
      ≤ (3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ) * (NS2 : ℝ) := by
    have h1 : 3 + dh_kappa ≤ 3 + ((2840794 / 10000000 : ℚ) : ℝ) := by linarith
    have m1 := mul_le_mul h1 hNSr (norm_nonneg _) hκh
    have m2 := mul_le_mul m1 hNS1r (norm_nonneg _)
      (mul_nonneg hκh hNS0)
    exact mul_le_mul m2 hNS2r (norm_nonneg _)
      (mul_nonneg (mul_nonneg hκh hNS0) hNS10)
  have hnum : 5 / 8 * ((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
      * (5 * (K : ℝ) + 1) ^ (-s.re - 2)
      ≤ 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
          * (NS2 : ℝ)) * (P : ℝ) := by
    have h := mul_le_mul hA hrpow (Real.rpow_nonneg (by linarith) _)
      (mul_nonneg (mul_nonneg (mul_nonneg hκh hNS0) hNS10) hNS20)
    calc 5 / 8 * ((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
          * (5 * (K : ℝ) + 1) ^ (-s.re - 2)
        = 5 / 8 * (((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
            * (5 * (K : ℝ) + 1) ^ (-s.re - 2)) := by ring
      _ ≤ 5 / 8 * (((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
            * (NS2 : ℝ)) * (P : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
            * (NS2 : ℝ)) * (P : ℝ) := by ring
  have hchain : 5 / 8 * ((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
      * (5 * (K : ℝ) + 1) ^ (-s.re - 2) / (s.re + 2)
      ≤ 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
          * (NS2 : ℝ)) * (P : ℝ) / ((σlo : ℝ) + 2) := by
    refine div_le_div₀ ?_ hnum hσ2 hden
    exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 5/8)
      (mul_nonneg (mul_nonneg (mul_nonneg hκh hNS0) hNS10) hNS20)) hP0
  have hrr : 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
      * (NS2 : ℝ)) * (P : ℝ) / ((σlo : ℝ) + 2) ≤ (r : ℝ) := by
    have h := hr
    have : ((5 / 8 * ((3 + 2840794 / 10000000) * NS * NS1 * NS2) * P / (σlo + 2)
        : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ) := by exact_mod_cast h
    calc 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
          * (NS2 : ℝ)) * (P : ℝ) / ((σlo : ℝ) + 2)
        = ((5 / 8 * ((3 + 2840794 / 10000000) * NS * NS1 * NS2) * P / (σlo + 2)
          : ℚ) : ℝ) := by push_cast; ring
      _ ≤ (r : ℝ) := this
  exact ComplexInterval.contains_inflate hB (htail.trans (hchain.trans hrr))

/-! ### Reading the two square-criterion inequalities off boxes -/

theorem norm_lt_of_enclosure {B : ComplexInterval} {z : ℂ} {q : ℚ}
    (hB : B.contains z) (h : ComplexInterval.normBound B < q) : ‖z‖ < (q : ℝ) :=
  lt_of_le_of_lt (ComplexInterval.norm_le_normBound hB) (by exact_mod_cast h)

theorem norm_le_of_enclosure {B : ComplexInterval} {z : ℂ} {q : ℚ}
    (hB : B.contains z) (h : ComplexInterval.normBound B ≤ q) : ‖z‖ ≤ (q : ℝ) :=
  le_trans (ComplexInterval.norm_le_normBound hB) (by exact_mod_cast h)

theorem le_norm_of_enclosure {B : ComplexInterval} {z : ℂ} {q : ℚ}
    (hB : B.contains z) (h : q ≤ ComplexInterval.normLower B) : (q : ℝ) ≤ ‖z‖ :=
  le_trans (by exact_mod_cast h) (ComplexInterval.normLower_le_norm hB)

/-! ### From frontier upper bounds to a Lipschitz constant: maximum modulus
plus Cauchy's derivative estimate

Interval enclosures over a boxed `s` have widths that *add* across the
series — fatal for lower bounds, harmless for upper bounds.  So the
boundary certificate takes the long way round: boxed evaluation gives
`‖DH‖ ≤ M` on the frontier of a *large* square, the maximum principle
extends `M` to its closure, Cauchy's estimate turns `M` into a derivative
bound `L = M/(w₂−w)` on the small frontier, and the mean value theorem
propagates certified lower bounds at grid points to whole segments. -/

/-- Maximum principle on the square: a frontier bound is a closure bound. -/
theorem norm_DH_le_on_closure {cre cim w2 : ℚ} {M : ℝ}
    (hM : ∀ z ∈ frontier (dhSquare cre cim w2), ‖DH z‖ ≤ M) :
    ∀ z ∈ closure (dhSquare cre cim w2), ‖DH z‖ ≤ M := fun z hz =>
  Complex.norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _))
    (DH_differentiable.diffContOnCl) hM hz

/-- **Cauchy's estimate from the big square.**  Any point within `w` of the
centre (componentwise) has its derivative bounded by `M/(w₂−w)`. -/
theorem norm_deriv_DH_le {cre cim w w2 : ℚ} (hw : 0 < w) (hww : w < w2) {M : ℝ}
    (hM : ∀ z ∈ frontier (dhSquare cre cim w2), ‖DH z‖ ≤ M)
    {z : ℂ} (hzre : |z.re - (cre : ℝ)| ≤ (w : ℝ))
    (hzim : |z.im - (cim : ℝ)| ≤ (w : ℝ)) :
    ‖deriv DH z‖ ≤ M / ((w2 : ℝ) - (w : ℝ)) := by
  have hw2 : (0 : ℚ) < w2 := lt_trans hw hww
  have hR : (0 : ℝ) < (w2 : ℝ) - (w : ℝ) := by
    have : (w : ℝ) < (w2 : ℝ) := by exact_mod_cast hww
    linarith
  have hcl := norm_DH_le_on_closure hM
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
    (DH_differentiable.diffContOnCl) ?_
  intro y hy
  refine hcl y ?_
  have hdist : ‖y - z‖ = (w2 : ℝ) - (w : ℝ) := by
    have := Metric.mem_sphere.mp hy
    rwa [dist_eq_norm] at this
  have hyre : |y.re - z.re| ≤ (w2 : ℝ) - (w : ℝ) := by
    have h := Complex.abs_re_le_norm (y - z)
    rw [Complex.sub_re] at h
    rw [← hdist]
    exact h
  have hyim : |y.im - z.im| ≤ (w2 : ℝ) - (w : ℝ) := by
    have h := Complex.abs_im_le_norm (y - z)
    rw [Complex.sub_im] at h
    rw [← hdist]
    exact h
  have hre : (((cre - w2 : ℚ) : ℝ)) < (((cre + w2 : ℚ) : ℝ)) := by
    push_cast
    have : (0 : ℝ) < (w2 : ℝ) := by exact_mod_cast hw2
    linarith
  have him : (((cim - w2 : ℚ) : ℝ)) < (((cim + w2 : ℚ) : ℝ)) := by
    push_cast
    have : (0 : ℝ) < (w2 : ℝ) := by exact_mod_cast hw2
    linarith
  rw [dhSquare, Complex.closure_reProdIm, closure_Ioo hre.ne, closure_Ioo him.ne,
    Complex.mem_reProdIm]
  obtain ⟨h1, h2⟩ := abs_le.mp hzre
  obtain ⟨h3, h4⟩ := abs_le.mp hzim
  obtain ⟨h5, h6⟩ := abs_le.mp hyre
  obtain ⟨h7, h8⟩ := abs_le.mp hyim
  constructor
  · constructor <;> · push_cast; linarith
  · constructor <;> · push_cast; linarith

/-! ### The mean value theorem along frontier segments -/

private lemma hasDerivAt_horiz (y : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => DH ⟨t, y⟩) (deriv DH ⟨x, y⟩) x := by
  have hg : HasDerivAt (fun w : ℂ => DH (w + (y : ℝ) * Complex.I))
      (deriv DH ((x : ℝ) + (y : ℝ) * Complex.I)) ((x : ℝ) : ℂ) := by
    have hinner : HasDerivAt (fun w : ℂ => w + (y : ℝ) * Complex.I) 1
        ((x : ℝ) : ℂ) := (hasDerivAt_id _).add_const _
    have houter := (DH_differentiable ((x : ℝ) + (y : ℝ) * Complex.I)).hasDerivAt
    simpa [Function.comp_def] using houter.comp ((x : ℝ) : ℂ) hinner
  have h := hg.comp_ofReal
  have hfun : (fun t : ℝ => DH ((t : ℂ) + (y : ℝ) * Complex.I))
      = fun t : ℝ => DH ⟨t, y⟩ :=
    funext fun t => congrArg DH (Complex.mk_eq_add_mul_I t y).symm
  have hpt : ((x : ℝ) : ℂ) + (y : ℝ) * Complex.I = (⟨x, y⟩ : ℂ) :=
    (Complex.mk_eq_add_mul_I x y).symm
  rw [hfun, hpt] at h
  exact h

private lemma hasDerivAt_vert (x : ℝ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => DH ⟨x, t⟩)
      (deriv DH ⟨x, y⟩ * Complex.I) y := by
  have hg : HasDerivAt (fun w : ℂ => DH ((x : ℝ) + w * Complex.I))
      (deriv DH ((x : ℝ) + (y : ℝ) * Complex.I) * Complex.I) ((y : ℝ) : ℂ) := by
    have hinner : HasDerivAt (fun w : ℂ => ((x : ℝ) : ℂ) + w * Complex.I)
        Complex.I ((y : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((y : ℝ) : ℂ)).mul_const Complex.I).const_add
        (((x : ℝ)) : ℂ)
    have houter := (DH_differentiable
      ((x : ℝ) + (y : ℝ) * Complex.I)).hasDerivAt
    simpa [Function.comp_def] using houter.comp ((y : ℝ) : ℂ) hinner
  have h := hg.comp_ofReal
  have hfun : (fun t : ℝ => DH ((x : ℝ) + (t : ℂ) * Complex.I))
      = fun t : ℝ => DH ⟨x, t⟩ :=
    funext fun t => congrArg DH (Complex.mk_eq_add_mul_I x t).symm
  have hpt : ((x : ℝ) : ℂ) + (y : ℝ) * Complex.I = (⟨x, y⟩ : ℂ) :=
    (Complex.mk_eq_add_mul_I x y).symm
  rw [hfun, hpt] at h
  exact h

/-- **A horizontal grid cell.**  Between abscissae `p ≤ q` at height `y`,
certified lower bounds at both endpoints propagate to every point between:
`ε ≤ ‖DH z‖` whenever both endpoint bounds clear `ε + L·(q−p)/2`. -/
theorem DH_lower_on_hcell {p q y : ℝ} (hpq : p ≤ q) {L : ℝ} (hL0 : 0 ≤ L)
    (hderiv : ∀ x ∈ Set.Icc p q, ‖deriv DH ⟨x, y⟩‖ ≤ L)
    {βp βq ε : ℝ}
    (hβp : βp ≤ ‖DH ⟨p, y⟩‖) (hβq : βq ≤ ‖DH ⟨q, y⟩‖)
    (hcellp : ε + L * ((q - p) / 2) ≤ βp) (hcellq : ε + L * ((q - p) / 2) ≤ βq)
    {z : ℂ} (hzim : z.im = y) (hzre : z.re ∈ Set.Icc p q) :
    ε ≤ ‖DH z‖ := by
  have hz : z = (⟨z.re, y⟩ : ℂ) := Complex.ext rfl hzim
  rcases le_total z.re ((p + q) / 2) with hle | hle
  · have hmvt := (convex_Icc p q).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hasDerivAt_horiz y t).hasDerivWithinAt) hderiv
      (Set.left_mem_Icc.mpr hpq) hzre
    have hd : ‖z.re - p‖ ≤ (q - p) / 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hzre.1])]
      linarith [hzre.1]
    have h2 : ‖DH ⟨z.re, y⟩ - DH ⟨p, y⟩‖ ≤ L * ((q - p) / 2) :=
      hmvt.trans (mul_le_mul_of_nonneg_left hd hL0)
    have h3 := norm_sub_norm_le (DH ⟨p, y⟩) (DH ⟨z.re, y⟩)
    rw [norm_sub_rev] at h3
    rw [hz]
    linarith
  · have hmvt := (convex_Icc p q).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hasDerivAt_horiz y t).hasDerivWithinAt) hderiv
      (Set.right_mem_Icc.mpr hpq) hzre
    have hd : ‖z.re - q‖ ≤ (q - p) / 2 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hzre.2])]
      linarith [hzre.2]
    have h2 : ‖DH ⟨z.re, y⟩ - DH ⟨q, y⟩‖ ≤ L * ((q - p) / 2) :=
      hmvt.trans (mul_le_mul_of_nonneg_left hd hL0)
    have h3 := norm_sub_norm_le (DH ⟨q, y⟩) (DH ⟨z.re, y⟩)
    rw [norm_sub_rev] at h3
    rw [hz]
    linarith

/-- **A vertical grid cell**, mirror of `DH_lower_on_hcell`. -/
theorem DH_lower_on_vcell {p q x : ℝ} (hpq : p ≤ q) {L : ℝ} (hL0 : 0 ≤ L)
    (hderiv : ∀ y ∈ Set.Icc p q, ‖deriv DH ⟨x, y⟩‖ ≤ L)
    {βp βq ε : ℝ}
    (hβp : βp ≤ ‖DH ⟨x, p⟩‖) (hβq : βq ≤ ‖DH ⟨x, q⟩‖)
    (hcellp : ε + L * ((q - p) / 2) ≤ βp) (hcellq : ε + L * ((q - p) / 2) ≤ βq)
    {z : ℂ} (hzre : z.re = x) (hzim : z.im ∈ Set.Icc p q) :
    ε ≤ ‖DH z‖ := by
  have hz : z = (⟨x, z.im⟩ : ℂ) := Complex.ext hzre rfl
  have hderiv' : ∀ y ∈ Set.Icc p q, ‖deriv DH ⟨x, y⟩ * Complex.I‖ ≤ L := by
    intro y hy
    rw [norm_mul, Complex.norm_I, mul_one]
    exact hderiv y hy
  rcases le_total z.im ((p + q) / 2) with hle | hle
  · have hmvt := (convex_Icc p q).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hasDerivAt_vert x t).hasDerivWithinAt) hderiv'
      (Set.left_mem_Icc.mpr hpq) hzim
    have hd : ‖z.im - p‖ ≤ (q - p) / 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hzim.1])]
      linarith [hzim.1]
    have h2 : ‖DH ⟨x, z.im⟩ - DH ⟨x, p⟩‖ ≤ L * ((q - p) / 2) :=
      hmvt.trans (mul_le_mul_of_nonneg_left hd hL0)
    have h3 := norm_sub_norm_le (DH ⟨x, p⟩) (DH ⟨x, z.im⟩)
    rw [norm_sub_rev] at h3
    rw [hz]
    linarith
  · have hmvt := (convex_Icc p q).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hasDerivAt_vert x t).hasDerivWithinAt) hderiv'
      (Set.right_mem_Icc.mpr hpq) hzim
    have hd : ‖z.im - q‖ ≤ (q - p) / 2 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hzim.2])]
      linarith [hzim.2]
    have h2 : ‖DH ⟨x, z.im⟩ - DH ⟨x, q⟩‖ ≤ L * ((q - p) / 2) :=
      hmvt.trans (mul_le_mul_of_nonneg_left hd hL0)
    have h3 := norm_sub_norm_le (DH ⟨x, q⟩) (DH ⟨x, z.im⟩)
    rw [norm_sub_rev] at h3
    rw [hz]
    linarith

end DH

end ZetaLean
