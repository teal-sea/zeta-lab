/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Numeric
import ZetaLean.Pub1.Aristotle.A

/-!
# Pub 1 strong closure: the explicit `C³` endpoint ramp

The ramp `η` of `hunts/wide_search/RESULTS-xiprime-admissible-closure.md`,
section "Explicit source-admissible sequence":

```
η(x) = 0                                    x ≤ 0
       35x⁴ - 84x⁵ + 70x⁶ - 20x⁷            0 < x < 1
       1                                    x ≥ 1
```

Its derivative on `(0,1)` is `140x³(1-x)³ ≥ 0`, which vanishes to order three at
both endpoints; that is exactly why the piecewise extension is `C³` and why the
window `φ_L` built from it lands in `C_c²`.

This file carries the order- and value-theoretic content: `η` is monotone, takes
values in `[0,1]`, is `0` exactly on `(-∞,0]`, and is `1` on `[1,∞)`.  Those are
the properties the source admissibility conditions (support, amplitude, radial
monotonicity) are read off from.
-/

namespace ZetaLean.Pub1

/-! ### The degree-7 smoothstep -/

/-- The quintic-order smoothstep polynomial `35x⁴ - 84x⁵ + 70x⁶ - 20x⁷`. -/
noncomputable def rampPoly (x : ℝ) : ℝ :=
  35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7

/-- The endpoint ramp `η`, extended by `0` on the left and `1` on the right. -/
noncomputable def eta (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else rampPoly x

@[simp] theorem rampPoly_zero : rampPoly 0 = 0 := by norm_num [rampPoly]

@[simp] theorem rampPoly_one : rampPoly 1 = 1 := by norm_num [rampPoly]

/-- **The derivative identity.**  `η'(x) = 140x³(1-x)³` on `(0,1)`; it vanishes
to order three at both endpoints, which is the whole reason the glued function is
`C³`. -/
theorem hasDerivAt_rampPoly (x : ℝ) :
    HasDerivAt rampPoly (140 * x ^ 3 * (1 - x) ^ 3) x := by
  have h : HasDerivAt (fun y : ℝ => 35 * y ^ 4 - 84 * y ^ 5 + 70 * y ^ 6 - 20 * y ^ 7)
      (35 * ((4 : ℕ) * x ^ 3) - 84 * ((5 : ℕ) * x ^ 4) + 70 * ((6 : ℕ) * x ^ 5)
        - 20 * ((7 : ℕ) * x ^ 6)) x :=
    ((((hasDerivAt_pow 4 x).const_mul 35).sub ((hasDerivAt_pow 5 x).const_mul 84)).add
      ((hasDerivAt_pow 6 x).const_mul 70)).sub ((hasDerivAt_pow 7 x).const_mul 20)
  have h' : HasDerivAt rampPoly
      (35 * ((4 : ℕ) * x ^ 3) - 84 * ((5 : ℕ) * x ^ 4) + 70 * ((6 : ℕ) * x ^ 5)
        - 20 * ((7 : ℕ) * x ^ 6)) x := h
  convert h' using 1
  push_cast
  ring

theorem differentiable_rampPoly : Differentiable ℝ rampPoly := fun x =>
  (hasDerivAt_rampPoly x).differentiableAt

theorem continuous_rampPoly : Continuous rampPoly :=
  differentiable_rampPoly.continuous

theorem deriv_rampPoly (x : ℝ) : deriv rampPoly x = 140 * x ^ 3 * (1 - x) ^ 3 :=
  (hasDerivAt_rampPoly x).deriv

/-- `η'` is nonnegative on `[0,1]`: the ramp is nondecreasing, as the source
requires of `ϱ`. -/
theorem rampPoly_deriv_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ 140 * x ^ 3 * (1 - x) ^ 3 := by
  obtain ⟨h0, h1⟩ := hx
  have : (0 : ℝ) ≤ 1 - x := by linarith
  positivity

/-- `η'` is strictly positive on the open interval. -/
theorem rampPoly_deriv_pos {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < 140 * x ^ 3 * (1 - x) ^ 3 := by
  obtain ⟨h0, h1⟩ := hx
  have h2 : (0 : ℝ) < 1 - x := by linarith
  positivity

/-- The smoothstep is strictly increasing across `[0,1]`. -/
theorem strictMonoOn_rampPoly : StrictMonoOn rampPoly (Set.Icc (0 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) continuous_rampPoly.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_rampPoly]
  exact rampPoly_deriv_pos hx

theorem rampPoly_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ rampPoly x := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · simp [← h]
  · exact le_of_lt (by
      simpa using strictMonoOn_rampPoly (Set.left_mem_Icc.mpr zero_le_one) hx h)

theorem rampPoly_le_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : rampPoly x ≤ 1 := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · simp [h]
  · exact le_of_lt (by
      simpa using strictMonoOn_rampPoly hx (Set.right_mem_Icc.mpr zero_le_one) h)

theorem rampPoly_pos {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) : 0 < rampPoly x := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  simpa using strictMonoOn_rampPoly h0 hx' hx.1

/-! ### The glued ramp -/

theorem eta_of_nonpos {x : ℝ} (hx : x ≤ 0) : eta x = 0 := by simp [eta, hx]

theorem eta_of_one_le {x : ℝ} (hx : 1 ≤ x) : eta x = 1 := by
  have hx0 : ¬ x ≤ 0 := by linarith
  simp [eta, hx0, hx]

theorem eta_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : eta x = rampPoly x := by
  have h0 : ¬ x ≤ 0 := by linarith [hx.1]
  have h1 : ¬ (1 : ℝ) ≤ x := by linarith [hx.2]
  simp [eta, h0, h1]

@[simp] theorem eta_zero : eta 0 = 0 := eta_of_nonpos le_rfl

@[simp] theorem eta_one : eta 1 = 1 := eta_of_one_le le_rfl

/-- `0 ≤ η` everywhere: the amplitude floor of the source admissibility class. -/
theorem eta_nonneg (x : ℝ) : 0 ≤ eta x := by
  rcases le_or_gt x 0 with h | h
  · simp [eta_of_nonpos h]
  rcases le_or_gt 1 x with h1 | h1
  · simp [eta_of_one_le h1]
  · rw [eta_of_mem_Ioo ⟨h, h1⟩]
    exact rampPoly_nonneg ⟨h.le, h1.le⟩

/-- `η ≤ 1` everywhere: the amplitude ceiling `0 ≤ φ ≤ 1`. -/
theorem eta_le_one (x : ℝ) : eta x ≤ 1 := by
  rcases le_or_gt x 0 with h | h
  · simp [eta_of_nonpos h]
  rcases le_or_gt 1 x with h1 | h1
  · simp [eta_of_one_le h1]
  · rw [eta_of_mem_Ioo ⟨h, h1⟩]
    exact rampPoly_le_one ⟨h.le, h1.le⟩

/-- `η > 0` exactly to the right of the origin.  With evenness this is what makes
`supp φ_L` exactly `[-L/2, L/2]` rather than a proper subset. -/
theorem eta_pos {x : ℝ} (hx : 0 < x) : 0 < eta x := by
  rcases le_or_gt 1 x with h1 | h1
  · simp [eta_of_one_le h1]
  · rw [eta_of_mem_Ioo ⟨hx, h1⟩]
    exact rampPoly_pos ⟨hx, h1.le⟩

theorem eta_eq_zero_iff {x : ℝ} : eta x = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    by_contra hx
    push_neg at hx
    exact absurd h (ne_of_gt (eta_pos hx))
  · exact eta_of_nonpos

/-- `η` is nondecreasing on all of `ℝ`.  Together with evenness of `|u|` this is
the radial monotonicity of the taper factor. -/
theorem eta_monotone : Monotone eta := by
  intro a b hab
  rcases le_or_gt b 0 with hb | hb
  · rw [eta_of_nonpos (hab.trans hb), eta_of_nonpos hb]
  rcases le_or_gt a 0 with ha | ha
  · rw [eta_of_nonpos ha]
    exact eta_nonneg b
  rcases le_or_gt 1 a with ha1 | ha1
  · rw [eta_of_one_le ha1, eta_of_one_le (ha1.trans hab)]
  rcases le_or_gt 1 b with hb1 | hb1
  · rw [eta_of_one_le hb1, eta_of_mem_Ioo ⟨ha, ha1⟩]
    exact rampPoly_le_one ⟨ha.le, ha1.le⟩
  · rw [eta_of_mem_Ioo ⟨ha, ha1⟩, eta_of_mem_Ioo ⟨hb, hb1⟩]
    exact strictMonoOn_rampPoly.monotoneOn ⟨ha.le, ha1.le⟩ ⟨hb.le, hb1.le⟩ hab

/-- The ramp takes values in `[0,1]`. -/
theorem eta_mem_Icc (x : ℝ) : eta x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨eta_nonneg x, eta_le_one x⟩

/-- `η` is continuous: the two glue points match, `rampPoly 0 = 0` and
`rampPoly 1 = 1`. -/
theorem continuous_eta : Continuous eta := by
  have hinner : Continuous fun x : ℝ => if (1 : ℝ) ≤ x then (1 : ℝ) else rampPoly x := by
    refine Continuous.if_le continuous_const continuous_rampPoly continuous_const
      continuous_id ?_
    intro x hx
    rw [← hx]
    simp
  refine Continuous.if_le continuous_const hinner continuous_id continuous_const ?_
  intro x hx
  subst hx
  norm_num

/-- **`η ∈ C³`.**  The first three derivatives glue to zero at both endpoints;
the fourth jumps by `840` at the origin, so `C³` is sharp.  Proof imported from
`Aristotle/A.lean` and kernel-checked on this toolchain. -/
theorem eta_contDiff : ContDiff ℝ 3 eta := AristotleA.eta_contDiff

/-- `C²` is what the window construction actually consumes. -/
theorem eta_contDiff_two : ContDiff ℝ 2 eta :=
  eta_contDiff.of_le (by norm_num)

/-- `η` composed with a continuous function is continuous. -/
theorem Continuous.eta_comp {α : Type*} [TopologicalSpace α] {f : α → ℝ} (hf : Continuous f) :
    Continuous fun a => eta (f a) := continuous_eta.comp hf

end ZetaLean.Pub1
