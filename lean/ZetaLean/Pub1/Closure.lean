/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Pub 1 strong closure: the variational engine

The abstract half of the source-admissible strong-closure theorem, over a real
inner product space.  Nothing here knows about `F₁`, about the interval, or
about windows; it is the argument of the section "Closing the quotient" of
`hunts/wide_search/RESULTS-xiprime-admissible-closure.md`, stated once so that
the concrete development only has to supply objects.

The two halves are:

* `inner_sq_le_energy`: Cauchy-Schwarz in the energy inner product
  `⟪x, y⟫_A = ⟪A x, y⟫`, which gives the *upper* bound `c(v) ≤ c*` for every
  `v` whatsoever, admissible or not;
* `tendsto_quotient`: the quotient is continuous along any norm-convergent
  sequence with nonvanishing limiting energy, which gives the *lower* bound for
  the supremum from an approximating sequence inside the class.

`isLUB_quotient` puts them together, and `isGLB_reciprocal` records the same
statement for the reciprocal quotient.  The orientation is load-bearing and is
pinned by the pair: the maximizing quotient is `⟪1,v⟫^2 / ⟪Av,v⟫`, and it is its
reciprocal `⟪Av,v⟫ / ⟪1,v⟫^2` that is *minimized*.
-/

open scoped InnerProductSpace
open Filter Topology

namespace ZetaLean.Pub1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bounded operator which is self-adjoint and coercive with constant `m`.
For the Pub 1 kernel `A = I + T_{F₁}` the constant is `m = 5/9`. -/
structure IsCoerciveSA (A : E →L[ℝ] E) (m : ℝ) : Prop where
  /-- `A` is symmetric for the real inner product. -/
  symm : ∀ x y : E, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ
  /-- `A` is coercive: `⟪Ax, x⟫ ≥ m‖x‖²`. -/
  coercive : ∀ x : E, m * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ

namespace IsCoerciveSA

variable {A : E →L[ℝ] E} {m : ℝ}

/-- The energy form is symmetric. -/
theorem energy_comm (hA : IsCoerciveSA A m) (x y : E) : ⟪A x, y⟫_ℝ = ⟪A y, x⟫_ℝ := by
  rw [hA.symm x y, real_inner_comm]

/-- The energy form is nonnegative when the coercivity constant is. -/
theorem energy_nonneg (hA : IsCoerciveSA A m) (hm : 0 ≤ m) (x : E) : 0 ≤ ⟪A x, x⟫_ℝ :=
  le_trans (by positivity) (hA.coercive x)

/-- The energy form is strictly positive off zero when the coercivity constant is. -/
theorem energy_pos (hA : IsCoerciveSA A m) (hm : 0 < m) {x : E} (hx : x ≠ 0) :
    0 < ⟪A x, x⟫_ℝ := by
  refine lt_of_lt_of_le ?_ (hA.coercive x)
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  positivity

/-- The energy form expanded along a line: this is the quadratic in `t` whose
nonnegativity is the whole content of energy Cauchy-Schwarz. -/
theorem energy_line (hA : IsCoerciveSA A m) (x y : E) (t : ℝ) :
    ⟪A (x - t • y), x - t • y⟫_ℝ
      = ⟪A y, y⟫_ℝ * (t * t) + (-2 * ⟪A x, y⟫_ℝ) * t + ⟪A x, x⟫_ℝ := by
  have hxy : ⟪A y, x⟫_ℝ = ⟪A x, y⟫_ℝ := (hA.energy_comm y x)
  simp only [map_sub, ContinuousLinearMap.map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hxy]
  ring

/-- **Cauchy-Schwarz in the energy inner product.**  This is the inequality that
gives the upper bound `c(v) ≤ c*` for every `v`, with equality exactly on the
optimizing ray. -/
theorem inner_sq_le_energy (hA : IsCoerciveSA A m) (hm : 0 ≤ m) (x y : E) :
    ⟪A x, y⟫_ℝ ^ 2 ≤ ⟪A x, x⟫_ℝ * ⟪A y, y⟫_ℝ := by
  have hnn : ∀ t : ℝ,
      0 ≤ ⟪A y, y⟫_ℝ * (t * t) + (-2 * ⟪A x, y⟫_ℝ) * t + ⟪A x, x⟫_ℝ := by
    intro t
    rw [← hA.energy_line x y t]
    exact hA.energy_nonneg hm _
  have hd := discrim_le_zero hnn
  unfold discrim at hd
  nlinarith [hd]

end IsCoerciveSA

/-! ### The variational quotient -/

/-- The maximizing quotient `c(v) = ⟪1, v⟫² / ⟪Av, v⟫`.  The orientation is
load-bearing: this is the quantity whose *supremum* is `c*`. -/
noncomputable def quotient (A : E →L[ℝ] E) (one v : E) : ℝ :=
  ⟪one, v⟫_ℝ ^ 2 / ⟪A v, v⟫_ℝ

/-- The reciprocal quotient `⟪Av, v⟫ / ⟪1, v⟫²`, whose *infimum* is `1/c*`. -/
noncomputable def reciprocalQuotient (A : E →L[ℝ] E) (one v : E) : ℝ :=
  ⟪A v, v⟫_ℝ / ⟪one, v⟫_ℝ ^ 2

variable {A : E →L[ℝ] E} {m : ℝ} {one w : E}

/-- With `A w = 1`, the constant `c* = ⟪1, w⟫` is also the energy of `w`. -/
theorem energy_w_eq (hw : A w = one) : ⟪A w, w⟫_ℝ = ⟪one, w⟫_ℝ := by rw [hw]

/-- `w ≠ 0` as soon as `1 ≠ 0`. -/
theorem w_ne_zero (hw : A w = one) (hone : one ≠ 0) : w ≠ 0 := by
  rintro rfl
  exact hone (by simpa using hw.symm)

/-- `c* = ⟪1, w⟫` is strictly positive. -/
theorem cStar_pos (hA : IsCoerciveSA A m) (hm : 0 < m) (hw : A w = one) (hone : one ≠ 0) :
    0 < ⟪one, w⟫_ℝ := by
  rw [← energy_w_eq hw]
  exact hA.energy_pos hm (w_ne_zero hw hone)

/-- **The upper bound.**  Every `v` at all, admissible or not, has
`c(v) ≤ c* = ⟪1, A⁻¹1⟫`.  This is the ambient variational theorem, and it is what
makes the source-admissible supremum an equality rather than only a lower bound. -/
theorem quotient_le (hA : IsCoerciveSA A m) (hm : 0 < m) (hw : A w = one) (v : E) :
    quotient A one v ≤ ⟪one, w⟫_ℝ := by
  rcases eq_or_ne v 0 with rfl | hv
  · have hz : quotient A one (0 : E) = 0 := by simp [quotient]
    rw [hz, ← energy_w_eq hw]
    exact hA.energy_nonneg hm.le w
  · have hden : 0 < ⟪A v, v⟫_ℝ := hA.energy_pos hm hv
    have key : ⟪one, v⟫_ℝ ^ 2 ≤ ⟪one, w⟫_ℝ * ⟪A v, v⟫_ℝ := by
      have h1 : ⟪one, v⟫_ℝ = ⟪A w, v⟫_ℝ := by rw [hw]
      calc ⟪one, v⟫_ℝ ^ 2 = ⟪A w, v⟫_ℝ ^ 2 := by rw [h1]
        _ ≤ ⟪A w, w⟫_ℝ * ⟪A v, v⟫_ℝ := hA.inner_sq_le_energy hm.le w v
        _ = ⟪one, w⟫_ℝ * ⟪A v, v⟫_ℝ := by rw [energy_w_eq hw]
    rw [quotient, div_le_iff₀ hden]
    exact key

/-- The quotient of `w` itself is exactly `c*`. -/
theorem quotient_self (hA : IsCoerciveSA A m) (hm : 0 < m) (hw : A w = one) (hone : one ≠ 0) :
    quotient A one w = ⟪one, w⟫_ℝ := by
  have hpos : 0 < ⟪one, w⟫_ℝ := cStar_pos hA hm hw hone
  rw [quotient, energy_w_eq hw]
  field_simp

/-! ### Continuity of the quotient along an approximating sequence -/

/-- **`L²` continuity of the maximizing quotient.**  Norm convergence
`v i → w` forces `c(v i) → c(w) = c*`.  This is the step that converts the
`L²`-convergence of the induced profiles into convergence of the quotient. -/
theorem tendsto_quotient {ι : Type*} {l : Filter ι} (hA : IsCoerciveSA A m) (hm : 0 < m)
    (hw : A w = one) (hone : one ≠ 0) (v : ι → E) (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => quotient A one (v i)) l (𝓝 (⟪one, w⟫_ℝ)) := by
  have hpos : 0 < ⟪one, w⟫_ℝ := cStar_pos hA hm hw hone
  have hnum : Tendsto (fun i => ⟪one, v i⟫_ℝ ^ 2) l (𝓝 (⟪one, w⟫_ℝ ^ 2)) :=
    ((tendsto_const_nhds.inner hv).pow 2)
  have hden : Tendsto (fun i => ⟪A (v i), v i⟫_ℝ) l (𝓝 (⟪A w, w⟫_ℝ)) := by
    exact ((A.continuous.tendsto w).comp hv).inner hv
  have hden' : Tendsto (fun i => ⟪A (v i), v i⟫_ℝ) l (𝓝 (⟪one, w⟫_ℝ)) := by
    rwa [energy_w_eq hw] at hden
  have := hnum.div hden' (ne_of_gt hpos)
  have hval : ⟪one, w⟫_ℝ ^ 2 / ⟪one, w⟫_ℝ = ⟪one, w⟫_ℝ := by
    field_simp
  rwa [hval] at this

/-! ### The supremum -/

/-- **The strong-closure supremum, abstractly.**  If a set `S` admits a sequence
converging in norm to `w = A⁻¹1`, then the supremum of the maximizing quotient
over `S` is exactly `c* = ⟪1, w⟫`.  The upper bound holds for every `v` in `E`,
so no property of `S` beyond containing the sequence is used. -/
theorem isLUB_quotient (hA : IsCoerciveSA A m) (hm : 0 < m) (hw : A w = one) (hone : one ≠ 0)
    (S : Set E) (v : ℕ → E) (hmem : ∀ n, v n ∈ S) (hlim : Tendsto v atTop (𝓝 w)) :
    IsLUB (quotient A one '' S) ⟪one, w⟫_ℝ := by
  constructor
  · rintro q ⟨x, -, rfl⟩
    exact quotient_le hA hm hw x
  · intro b hb
    have hle : ∀ n, quotient A one (v n) ≤ b := fun n => hb ⟨v n, hmem n, rfl⟩
    exact le_of_tendsto (tendsto_quotient hA hm hw hone v hlim) (Eventually.of_forall hle)

/-- The supremum as an `sSup`. -/
theorem sSup_quotient (hA : IsCoerciveSA A m) (hm : 0 < m) (hw : A w = one) (hone : one ≠ 0)
    (S : Set E) (v : ℕ → E) (hmem : ∀ n, v n ∈ S) (hlim : Tendsto v atTop (𝓝 w)) :
    sSup (quotient A one '' S) = ⟪one, w⟫_ℝ :=
  (isLUB_quotient hA hm hw hone S v hmem hlim).csSup_eq
    ⟨quotient A one (v 0), ⟨v 0, hmem 0, rfl⟩⟩

/-- **The reciprocal orientation.**  On a set where `⟪1, v⟫ ≠ 0`, the reciprocal
quotient is pointwise `1 / c(v)`, so its infimum is `1/c*`.  Recording both
statements pins the orientation: the quotient with `⟪1,v⟫²` in the numerator is
the one that is maximized. -/
theorem reciprocalQuotient_eq_inv (hA : IsCoerciveSA A m) (hm : 0 < m) {v : E} (hv : v ≠ 0) :
    reciprocalQuotient A one v = (quotient A one v)⁻¹ := by
  rw [reciprocalQuotient, quotient, inv_div]

/-- The infimum of the reciprocal quotient is `1/c*`. -/
theorem isGLB_reciprocal (hA : IsCoerciveSA A m) (hm : 0 < m) (hw : A w = one) (hone : one ≠ 0)
    (S : Set E) (hS0 : ∀ x ∈ S, x ≠ 0) (hSpos : ∀ x ∈ S, ⟪one, x⟫_ℝ ≠ 0)
    (v : ℕ → E) (hmem : ∀ n, v n ∈ S) (hlim : Tendsto v atTop (𝓝 w)) :
    IsGLB (reciprocalQuotient A one '' S) (⟪one, w⟫_ℝ)⁻¹ := by
  have hpos : 0 < ⟪one, w⟫_ℝ := cStar_pos hA hm hw hone
  have hqpos : ∀ x ∈ S, 0 < quotient A one x := by
    intro x hx
    have hden : 0 < ⟪A x, x⟫_ℝ := hA.energy_pos hm (hS0 x hx)
    have hnum : 0 < ⟪one, x⟫_ℝ ^ 2 := by
      have := hSpos x hx
      positivity
    exact div_pos hnum hden
  constructor
  · rintro q ⟨x, hx, rfl⟩
    rw [reciprocalQuotient_eq_inv hA hm (hS0 x hx)]
    have := one_div_le_one_div_of_le (hqpos x hx) (quotient_le hA hm hw x)
    simpa [one_div] using this
  · intro b hb
    have hle : ∀ n, b ≤ (quotient A one (v n))⁻¹ := by
      intro n
      have := hb ⟨v n, hmem n, rfl⟩
      rwa [reciprocalQuotient_eq_inv hA hm (hS0 _ (hmem n))] at this
    have htend : Tendsto (fun n => (quotient A one (v n))⁻¹) atTop (𝓝 (⟪one, w⟫_ℝ)⁻¹) :=
      (tendsto_quotient hA hm hw hone v hlim).inv₀ (ne_of_gt hpos)
    exact ge_of_tendsto htend (Eventually.of_forall hle)

end ZetaLean.Pub1
