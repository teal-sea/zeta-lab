import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# A grid-incidence identity for compactly supported windows

Let `phi : ℝ → ℝ` be supported in `[-1/2, 1/2]` and set

  `phihat x = ∫ u, phi u * exp (I * x * u)`  (unnormalised `e^{i x u}` convention).

## Results

* `GridIncidence.hasSum_phihat_mul_phihat` (general form). For every measurable `phi` that is
  bounded and vanishes outside `[-1/2, 1/2]`, and for all real `x, y`, the family
  `n ↦ phihat (x - n) * phihat (y - n)` is summable over `ℤ` with

    `∑' n : ℤ, phihat (x-n) * phihat (y-n) = 2 * π * ∫ u, phi u * phi (-u) * exp (I * (x-y) * u)`.

* `GridIncidence.tsum_phihat_mul_phihat_even` (the form asked for in `PROBLEM.md`). If in
  addition `phi` is even, then

    `∑' n : ℤ, phihat (x-n) * phihat (y-n) = 2 * π * ∫ u, (phi u)^2 * exp (I * (x-y) * u)`,

  i.e. `2 π` times the transform of `phi ^ 2` evaluated at `x - y`.

* `GridIncidence.tsum_phihat_windowA`, `GridIncidence.tsum_phihat_windowB` and
  `GridIncidence.tsum_phihat_of_continuous` instantiate this for exactly the three windows
  required in `PROBLEM.md`: `u ↦ cos (√2 u)` and `u ↦ √(cos (√2 u))` on `[-1/2, 1/2]` extended
  by `0` (both of which jump at `±1/2`), and any continuous — in particular `C³`
  ramp-mollified — even window supported in `[-1/2, 1/2]`.

* `GridIncidence.grid_incidence_needs_even` shows that the evenness hypothesis cannot be dropped
  from the `phi ^ 2` form: for the indicator of `(0, 1/2]` and `x = y = 0` the grid sum is `0`
  while `2 π ∫ phi ^ 2 = π`. The `phi u * phi (-u)` version above is the correct general form
  (as it must be: the grid sum only sees the autocorrelation `∫ phi(u) phi(u+t)` through
  `phi ⋆ phǐ`).

## Hypotheses and why the required windows satisfy them

The hypotheses carried by the main theorems are:

* `Measurable phi`;
* `∀ u, |phi u| ≤ C` for some real constant `C`;
* `∀ u, 1/2 < |u| → phi u = 0`;
* (for the `phi ^ 2` form only) `∀ u, phi (-u) = phi u`.

No continuity is assumed anywhere — in particular the windows (a) `cos (√2 u)` and
(b) `√(cos (√2 u))` truncated to `[-1/2, 1/2]`, which jump at `±1/2`, are allowed; they are
continuous on `[-1/2, 1/2]` hence measurable, bounded by `1` (for (b), `cos ≤ 1` and
`√ t ≤ 1` for `t ≤ 1`), and even. A `C³` ramp-mollified version of either is continuous and
supported in `[-1/2, 1/2]`, hence bounded and measurable, and is even when the mollification is
symmetric.

## Method

No Poisson summation is needed: since `phi` is supported in an interval of length `1 < 2π`, the
numbers `phihat (x - n)`, `n ∈ ℤ`, are (up to the factor `2π`) exactly the Fourier coefficients
on the circle `ℝ / 2πℤ` of the modulated window `u ↦ phi u * exp (I x u)`. The identity is then
a polarised Parseval identity for the Hilbert basis `fourierBasis` of `L² (AddCircle (2π))`,
which is why mere square-integrability (here: bounded and measurable) suffices.
-/

noncomputable section

open MeasureTheory Complex AddCircle Real
open scoped ComplexConjugate

namespace GridIncidence

/-- The (unnormalised) Fourier transform of a real window `phi`,
`phihat x = ∫ u, phi u * exp (I * x * u)`. -/
noncomputable def phihat (phi : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, (phi u : ℂ) * Complex.exp (Complex.I * x * u)

/-! ### A polarised Parseval identity for Fourier coefficients on an interval -/

/-- Polarised Parseval identity on `AddCircle T`: for `f g : L²`, the sums of
`conj (fourierCoeff f i) * fourierCoeff g i` converge to the `L²` inner product. -/
theorem hasSum_inner_fourierCoeff {T : ℝ} [hT : Fact (0 < T)]
    (f g : Lp ℂ 2 (@haarAddCircle T hT)) :
    HasSum (fun i : ℤ => conj (fourierCoeff (f : AddCircle T → ℂ) i) *
        fourierCoeff (g : AddCircle T → ℂ) i)
      (∫ t : AddCircle T, conj (f t) * g t ∂haarAddCircle) := by
  have h := HilbertBasis.hasSum_inner_mul_inner (fourierBasis (T := T)) f g
  have e1 : ∀ i : ℤ, (inner ℂ f (fourierBasis (T := T) i) : ℂ) *
      (inner ℂ (fourierBasis (T := T) i) g) =
      conj (fourierCoeff (f : AddCircle T → ℂ) i) * fourierCoeff (g : AddCircle T → ℂ) i := by
    intro i
    rw [← inner_conj_symm (𝕜 := ℂ) f (fourierBasis (T := T) i),
      ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply, fourierBasis_repr,
      fourierBasis_repr]
  simp_rw [e1] at h
  have key : (∫ t : AddCircle T, conj (f t) * g t ∂haarAddCircle) = (inner ℂ f g : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    simp only [RCLike.inner_apply]
    exact integral_congr_ae (.of_forall fun a => by ring)
  rw [key]
  exact h

/-- Polarised Parseval identity for the Fourier coefficients of functions on an interval
`(a, b]`. -/
theorem hasSum_inner_fourierCoeffOn {a b : ℝ} {f g : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a b))) :
    HasSum (fun i : ℤ => conj (fourierCoeffOn hab f i) * fourierCoeffOn hab g i)
      ((b - a)⁻¹ • ∫ x in a..b, conj (f x) * g x) := by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [← add_sub_cancel a b] at hf hg
  have hf' := hf.memLp_liftIoc.haarAddCircle
  have hg' := hg.memLp_liftIoc.haarAddCircle
  convert hasSum_inner_fourierCoeff hf'.toLp hg'.toLp using 2 with i
  · rw [fourierCoeff_congr_ae hf'.coeFn_toLp, fourierCoeff_congr_ae hg'.coeFn_toLp,
      fourierCoeff_liftIoc_eq, fourierCoeff_liftIoc_eq]
    norm_num
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integral_liftIoc_eq_intervalIntegral]
    simp only [← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [hf'.coeFn_toLp, hg'.coeFn_toLp] with x hx hy
    simp only [hx, hy]
    rfl

/-! ### Elementary auxiliary lemmas -/

theorem neg_pi_lt_pi : (-π : ℝ) < π := by have := Real.pi_pos; linarith

theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    conj (∫ x in a..b, f x) = ∫ x in a..b, conj (f x) := by
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  split_ifs <;> simp [integral_conj]

/-- A function vanishing outside `(-π, π]` has the same integral over `ℝ` as over `[-π, π]`. -/
theorem integral_eq_intervalIntegral (F : ℝ → ℂ) (hF : ∀ u, u ∉ Set.Ioc (-π) π → F u = 0) :
    ∫ u : ℝ, F u = ∫ u in (-π)..π, F u := by
  rw [intervalIntegral.integral_of_le neg_pi_lt_pi.le]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

/-- Points outside `(-π, π]` have absolute value bigger than `1/2`. -/
theorem half_lt_abs_of_not_mem {u : ℝ} (hu : u ∉ Set.Ioc (-π) π) : 1 / 2 < |u| := by
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  have hpi := Real.pi_gt_three
  rcases hu with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem norm_exp_I_mul (z u : ℝ) : ‖Complex.exp (Complex.I * z * u)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The Fourier monomial of `AddCircle (π - -π)` written out explicitly. -/
theorem fourier_neg_coe (n : ℤ) (u : ℝ) :
    (fourier (-n) (u : AddCircle (π - -π)) : ℂ) = Complex.exp (-(Complex.I * n * u)) := by
  rw [fourier_coe_apply]
  congr 1
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-! ### Fourier coefficients of the modulated window -/

/-- The `n`-th Fourier coefficient on `[-π, π]` of `u ↦ psi u * exp (I z u)`. -/
theorem fourierCoeffOn_window (psi : ℝ → ℝ) (z : ℝ) (n : ℤ) :
    fourierCoeffOn neg_pi_lt_pi (fun u => (psi u : ℂ) * Complex.exp (Complex.I * z * u)) n
      = ((1 : ℂ) / ((π : ℂ) - -π)) * ∫ u in (-π)..π, (psi u : ℂ) *
          Complex.exp (Complex.I * ((z : ℂ) - n) * u) := by
  rw [fourierCoeffOn_eq_integral, Complex.real_smul]
  push_cast
  congr 1
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  rw [smul_eq_mul, fourier_neg_coe,
    show (Complex.I * ((z : ℂ) - n) * u) = (Complex.I * z * u) + (-(Complex.I * n * u)) by ring,
    Complex.exp_add]
  ring

/-- Under the support hypothesis, `phihat (z - n)` is `2 π` times the `n`-th Fourier coefficient
on `[-π, π]` of the modulated window `u ↦ phi u * exp (I z u)`. -/
theorem phihat_sub_intCast (phi : ℝ → ℝ) (hsupp : ∀ u, 1 / 2 < |u| → phi u = 0) (z : ℝ) (n : ℤ) :
    phihat phi (z - n) =
      2 * π * fourierCoeffOn neg_pi_lt_pi
        (fun u => (phi u : ℂ) * Complex.exp (Complex.I * z * u)) n := by
  rw [fourierCoeffOn_window, phihat, integral_eq_intervalIntegral]
  · rw [← mul_assoc]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [show (2 : ℂ) * π * ((1 : ℂ) / ((π : ℂ) - -π)) = 1 by field_simp; ring, one_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    push_cast
    ring_nf
  · intro u hu
    rw [hsupp u (half_lt_abs_of_not_mem hu)]
    simp

/-- Reflecting the window conjugates the Fourier coefficients. -/
theorem conj_fourierCoeffOn_reflect (psi : ℝ → ℝ) (z : ℝ) (n : ℤ) :
    conj (fourierCoeffOn neg_pi_lt_pi
        (fun u => (psi (-u) : ℂ) * Complex.exp (Complex.I * z * u)) n)
      = fourierCoeffOn neg_pi_lt_pi
        (fun u => (psi u : ℂ) * Complex.exp (Complex.I * z * u)) n := by
  rw [fourierCoeffOn_window (fun u => psi (-u)) z n, fourierCoeffOn_window psi z n,
    map_mul, intervalIntegral_conj]
  have hc : conj ((1 : ℂ) / ((π : ℂ) - -π)) = (1 : ℂ) / ((π : ℂ) - -π) := by
    rw [map_div₀]; norm_num
  rw [hc]
  congr 1
  have hw : ∀ u : ℝ, conj ((psi (-u) : ℂ) * Complex.exp (Complex.I * ((z : ℂ) - n) * u))
      = (psi (-u) : ℂ) * Complex.exp ((Complex.I * ((z : ℂ) - n)) * ((-u : ℝ) : ℂ)) := by
    intro u
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
    congr 1
    simp only [map_sub, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr (g := fun u : ℝ => (psi (-u) : ℂ) *
      Complex.exp ((Complex.I * ((z : ℂ) - n)) * ((-u : ℝ) : ℂ))) (fun u _ => hw u)]
  have hrefl := intervalIntegral.integral_comp_neg (a := (-π : ℝ)) (b := (π : ℝ))
    (fun v : ℝ => (psi v : ℂ) * Complex.exp ((Complex.I * ((z : ℂ) - n)) * v))
  rw [neg_neg] at hrefl
  rw [hrefl]

/-! ### `L²` membership of the modulated windows -/

/-- A bounded measurable window, modulated, is in `L²` of a bounded interval. -/
theorem memLp_window {psi : ℝ → ℝ} (hm : Measurable psi) {C : ℝ} (hb : ∀ u, |psi u| ≤ C)
    (z : ℝ) :
    MemLp (fun u => (psi u : ℂ) * Complex.exp (Complex.I * z * u)) 2
      (volume.restrict (Set.Ioc (-π) π)) := by
  have hmeas : AEStronglyMeasurable
      (fun u => (psi u : ℂ) * Complex.exp (Complex.I * z * u))
      (volume.restrict (Set.Ioc (-π) π)) := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp hm).mul
      (Complex.measurable_exp.comp (by fun_prop))
  refine MemLp.of_bound hmeas C ?_
  filter_upwards with u
  rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact hb u

/-! ### The main theorem -/

/-- **Grid incidence law (general form).**

Hypotheses on the window `phi : ℝ → ℝ`:
* `hm : Measurable phi`;
* `hb : ∀ u, |phi u| ≤ C` for some real constant `C` (boundedness);
* `hsupp : ∀ u, 1/2 < |u| → phi u = 0` (support inside `[-1/2, 1/2]`).

No continuity whatsoever is assumed, so windows with jumps at `±1/2` are allowed.

Conclusion: the family `n ↦ phihat (x - n) * phihat (y - n)` is (unconditionally) summable
over `ℤ` with sum `2 π ∫ u, phi u * phi (-u) * exp (I (x - y) u)`. -/
theorem hasSum_phihat_mul_phihat {phi : ℝ → ℝ} (hm : Measurable phi) {C : ℝ}
    (hb : ∀ u, |phi u| ≤ C) (hsupp : ∀ u, 1 / 2 < |u| → phi u = 0) (x y : ℝ) :
    HasSum (fun n : ℤ => phihat phi (x - n) * phihat phi (y - n))
      (2 * π * ∫ u : ℝ, (phi u : ℂ) * (phi (-u) : ℂ) *
        Complex.exp (Complex.I * ((x : ℂ) - y) * u)) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the reflected modulated window and the plain one
  have hR := memLp_window (psi := fun u => phi (-u)) (hm.comp measurable_neg)
    (C := C) (fun u => hb (-u)) x
  have hG := memLp_window (psi := phi) hm (C := C) hb y
  have h := hasSum_inner_fourierCoeffOn neg_pi_lt_pi hR hG
  have h2 := h.mul_left ((2 * (π : ℂ)) * (2 * (π : ℂ)))
  -- rewrite the summand
  have hsummand : ∀ n : ℤ,
      (2 * (π : ℂ)) * (2 * (π : ℂ)) *
        (conj (fourierCoeffOn neg_pi_lt_pi
          (fun u => ((fun v => phi (-v)) u : ℂ) * Complex.exp (Complex.I * x * u)) n) *
        fourierCoeffOn neg_pi_lt_pi (fun u => (phi u : ℂ) * Complex.exp (Complex.I * y * u)) n)
        = phihat phi (x - n) * phihat phi (y - n) := by
    intro n
    rw [conj_fourierCoeffOn_reflect phi x n, phihat_sub_intCast phi hsupp x n,
      phihat_sub_intCast phi hsupp y n]
    ring
  simp only [hsummand] at h2
  -- identify the two limits
  have key : (2 * (π : ℂ) * ∫ u : ℝ, (phi u : ℂ) * (phi (-u) : ℂ) *
        Complex.exp (Complex.I * ((x : ℂ) - y) * u))
      = (2 * (π : ℂ)) * (2 * (π : ℂ)) *
        ((π - -π : ℝ)⁻¹ • ∫ u in (-π)..π, conj (((fun v => phi (-v)) u : ℂ) *
          Complex.exp (Complex.I * x * u)) * ((phi u : ℂ) * Complex.exp (Complex.I * y * u))) := by
    rw [Complex.real_smul]
    have hstep : (∫ u in (-π)..π, conj (((fun v => phi (-v)) u : ℂ) *
        Complex.exp (Complex.I * x * u)) * ((phi u : ℂ) * Complex.exp (Complex.I * y * u)))
        = ∫ u in (-π)..π, (phi u : ℂ) * (phi (-u) : ℂ) *
            Complex.exp (Complex.I * ((y : ℂ) - x) * u) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, map_mul, Complex.conj_I]
      rw [show (Complex.I * ((y : ℂ) - x) * u) = (-Complex.I * x * u) + (Complex.I * y * u) by ring,
        Complex.exp_add]
      ring
    rw [hstep]
    -- pass from the interval to the whole line, then reflect
    have hline : (∫ u in (-π)..π, (phi u : ℂ) * (phi (-u) : ℂ) *
        Complex.exp (Complex.I * ((y : ℂ) - x) * u))
        = ∫ u : ℝ, (phi u : ℂ) * (phi (-u) : ℂ) *
            Complex.exp (Complex.I * ((y : ℂ) - x) * u) := by
      refine (integral_eq_intervalIntegral _ (fun u hu => ?_)).symm
      rw [hsupp u (half_lt_abs_of_not_mem hu)]
      simp
    rw [hline]
    have hrefl : (∫ u : ℝ, (phi u : ℂ) * (phi (-u) : ℂ) *
        Complex.exp (Complex.I * ((y : ℂ) - x) * u))
        = ∫ u : ℝ, (phi u : ℂ) * (phi (-u) : ℂ) *
            Complex.exp (Complex.I * ((x : ℂ) - y) * u) := by
      rw [← integral_neg_eq_self (fun u : ℝ => (phi u : ℂ) * (phi (-u) : ℂ) *
        Complex.exp (Complex.I * ((x : ℂ) - y) * u)) volume]
      refine integral_congr_ae (.of_forall fun u => ?_)
      simp only [neg_neg]
      rw [show (Complex.I * ((x : ℂ) - y) * ((-u : ℝ) : ℂ)) = Complex.I * ((y : ℂ) - x) * u by
        push_cast; ring]
      ring
    rw [hrefl]
    push_cast
    field_simp
    ring
  rw [key]
  exact h2

/-- **Grid incidence law, the form stated in the problem.**

Hypotheses on the window `phi : ℝ → ℝ`:
* `hm : Measurable phi`;
* `hb : ∀ u, |phi u| ≤ C` for some real `C` (boundedness);
* `hsupp : ∀ u, 1/2 < |u| → phi u = 0` (support in `[-1/2, 1/2]`);
* `hev : ∀ u, phi (-u) = phi u` (evenness).

Evenness is genuinely needed for this *particular* form of the right-hand side: without it the
correct right-hand side is `2 π ∫ u, phi u * phi (-u) * exp (I (x-y) u)`
(`hasSum_phihat_mul_phihat`), see `grid_incidence_needs_even` below. All the windows listed in
the problem — `cos (√2 u)`, `√(cos (√2 u))` on `[-1/2,1/2]` extended by `0`, and any `C³`
ramp-mollified version of them — are even, bounded and measurable (indeed piecewise continuous),
so they satisfy every hypothesis; continuity on all of `ℝ` is *not* assumed. -/
theorem tsum_phihat_mul_phihat_even {phi : ℝ → ℝ} (hm : Measurable phi) {C : ℝ}
    (hb : ∀ u, |phi u| ≤ C) (hsupp : ∀ u, 1 / 2 < |u| → phi u = 0)
    (hev : ∀ u, phi (-u) = phi u) (x y : ℝ) :
    ∑' n : ℤ, phihat phi (x - n) * phihat phi (y - n)
      = 2 * π * ∫ u : ℝ, ((phi u : ℂ)) ^ 2 * Complex.exp (Complex.I * ((x : ℂ) - y) * u) := by
  rw [(hasSum_phihat_mul_phihat hm hb hsupp x y).tsum_eq]
  congr 1
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [hev u]
  ring

/-! ### The hypotheses are satisfied by the windows required in the problem statement -/

/-- Truncating an even, bounded, measurable function to `[-1/2, 1/2]` gives a window to which
`tsum_phihat_mul_phihat_even` applies. This covers all the required examples: no continuity at
`±1/2` is needed. -/
theorem tsum_phihat_indicator_even {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ u, |f u| ≤ 1)
    (hev : ∀ u, f (-u) = f u) (x y : ℝ) :
    ∑' n : ℤ, phihat (Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) f) (x - n) *
        phihat (Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) f) (y - n)
      = 2 * π * ∫ u : ℝ,
          ((Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) f u : ℝ) : ℂ) ^ 2 *
            Complex.exp (Complex.I * ((x : ℂ) - y) * u) := by
  refine tsum_phihat_mul_phihat_even (hf.indicator measurableSet_Icc) (C := 1) (fun u => ?_)
    (fun u hu => ?_) (fun u => ?_) x y
  · rw [Set.indicator_apply]
    split_ifs
    · exact hb u
    · simp
  · rw [Set.indicator_apply, if_neg]
    intro hmem
    rw [Set.mem_Icc] at hmem
    have : |u| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hmem.1], hmem.2⟩
    linarith
  · rw [Set.indicator_apply, Set.indicator_apply, hev u]
    have : (-u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) ↔ (u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
      simp only [Set.mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    by_cases hu : u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
    · rw [if_pos (this.2 hu), if_pos hu]
    · rw [if_neg (fun h => hu (this.1 h)), if_neg hu]

/-- Window (a): `u ↦ cos (√2 u)` on `[-1/2, 1/2]`, extended by `0`. It jumps at `±1/2`. -/
noncomputable def windowA : ℝ → ℝ :=
  Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun u => Real.cos (Real.sqrt 2 * u))

/-- Window (b): `u ↦ √(cos (√2 u))` on `[-1/2, 1/2]`, extended by `0`. It jumps at `±1/2`. -/
noncomputable def windowB : ℝ → ℝ :=
  Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun u => Real.sqrt (Real.cos (Real.sqrt 2 * u)))

/-- The grid incidence law for window (a). -/
theorem tsum_phihat_windowA (x y : ℝ) :
    ∑' n : ℤ, phihat windowA (x - n) * phihat windowA (y - n)
      = 2 * π * ∫ u : ℝ, ((windowA u : ℝ) : ℂ) ^ 2 *
          Complex.exp (Complex.I * ((x : ℂ) - y) * u) :=
  tsum_phihat_indicator_even (by fun_prop) (fun u => Real.abs_cos_le_one _)
    (fun u => by rw [mul_neg, Real.cos_neg]) x y

/-- The grid incidence law for window (b). -/
theorem tsum_phihat_windowB (x y : ℝ) :
    ∑' n : ℤ, phihat windowB (x - n) * phihat windowB (y - n)
      = 2 * π * ∫ u : ℝ, ((windowB u : ℝ) : ℂ) ^ 2 *
          Complex.exp (Complex.I * ((x : ℂ) - y) * u) :=
  tsum_phihat_indicator_even (by fun_prop)
    (fun u => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.2 (Real.cos_le_one _))
    (fun u => by rw [mul_neg, Real.cos_neg]) x y

/-- Case (c): any continuous (in particular `C³` ramp-mollified) even window supported in
`[-1/2, 1/2]` also satisfies the hypotheses, boundedness being automatic. -/
theorem tsum_phihat_of_continuous {phi : ℝ → ℝ} (hc : Continuous phi)
    (hsupp : ∀ u, 1 / 2 < |u| → phi u = 0) (hev : ∀ u, phi (-u) = phi u) (x y : ℝ) :
    ∑' n : ℤ, phihat phi (x - n) * phihat phi (y - n)
      = 2 * π * ∫ u : ℝ, ((phi u : ℝ) : ℂ) ^ 2 *
          Complex.exp (Complex.I * ((x : ℂ) - y) * u) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine tsum_phihat_mul_phihat_even hc.measurable (C := max C 0) (fun u => ?_) hsupp hev x y
  by_cases hu : u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC u hu) (le_max_left _ _)
  · have : 1 / 2 < |u| := by
      rw [Set.mem_Icc, not_and_or] at hu
      rcases hu with h | h
      · have h' := not_le.mp h
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have h' := not_le.mp h
        rw [abs_of_pos (by linarith)]
        linarith
    rw [hsupp u this]
    simp

/-! ### Evenness cannot be dropped from `tsum_phihat_mul_phihat_even`

The literal statement of the problem (with `phi ^ 2` on the right) is *false* for windows that
are not even; the correct general right-hand side is the one in `hasSum_phihat_mul_phihat`, with
`phi u * phi (-u)` in place of `(phi u) ^ 2`. We exhibit the one-sided box window as an explicit
counterexample. -/

/-- A one-sided window: the indicator of `(0, 1/2]`. It is measurable, bounded and supported in
`[-1/2, 1/2]`, but not even. -/
noncomputable def oneSidedWindow : ℝ → ℝ := Set.indicator (Set.Ioc (0 : ℝ) (1 / 2)) 1

theorem measurable_oneSidedWindow : Measurable oneSidedWindow :=
  measurable_const.indicator measurableSet_Ioc

theorem abs_oneSidedWindow_le_one (u : ℝ) : |oneSidedWindow u| ≤ 1 := by
  rw [oneSidedWindow, Set.indicator_apply]
  split_ifs <;> simp

theorem oneSidedWindow_eq_zero {u : ℝ} (h : 1 / 2 < |u|) : oneSidedWindow u = 0 := by
  rw [oneSidedWindow, Set.indicator_apply, if_neg]
  intro hu
  rw [Set.mem_Ioc] at hu
  rw [abs_of_pos hu.1] at h
  linarith [hu.2]

theorem oneSidedWindow_mul_reflect (u : ℝ) : oneSidedWindow u * oneSidedWindow (-u) = 0 := by
  rw [oneSidedWindow, Set.indicator_apply, Set.indicator_apply]
  split_ifs with h1 h2
  · rw [Set.mem_Ioc] at h1 h2
    linarith [h1.1, h2.1]
  all_goals simp

/-- **The evenness hypothesis is necessary.** For the one-sided window and `x = y = 0`, the grid
sum vanishes while `2 π ∫ phi ^ 2 = π ≠ 0`. -/
theorem grid_incidence_needs_even :
    ∑' n : ℤ, phihat oneSidedWindow (0 - n) * phihat oneSidedWindow (0 - n)
      ≠ 2 * π * ∫ u : ℝ, ((oneSidedWindow u : ℝ) : ℂ) ^ 2 *
          Complex.exp (Complex.I * (((0 : ℝ) : ℂ) - (0 : ℝ)) * u) := by
  have hleft : ∑' n : ℤ, phihat oneSidedWindow (0 - n) * phihat oneSidedWindow (0 - n) = 0 := by
    rw [(hasSum_phihat_mul_phihat measurable_oneSidedWindow abs_oneSidedWindow_le_one
      (fun u hu => oneSidedWindow_eq_zero hu) 0 0).tsum_eq]
    have : (∫ u : ℝ, ((oneSidedWindow u : ℝ) : ℂ) * ((oneSidedWindow (-u) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((0 : ℝ) : ℂ) - (0 : ℝ)) * u)) = 0 := by
      rw [show (0 : ℂ) = ∫ _u : ℝ, (0 : ℂ) by simp]
      refine integral_congr_ae (.of_forall fun u => ?_)
      simp only [← Complex.ofReal_mul, oneSidedWindow_mul_reflect u, Complex.ofReal_zero,
        zero_mul]
    rw [this, mul_zero]
  have hright : (∫ u : ℝ, ((oneSidedWindow u : ℝ) : ℂ) ^ 2 *
      Complex.exp (Complex.I * (((0 : ℝ) : ℂ) - (0 : ℝ)) * u)) = (1 / 2 : ℝ) := by
    have hpt : ∀ u : ℝ, ((oneSidedWindow u : ℝ) : ℂ) ^ 2 *
        Complex.exp (Complex.I * (((0 : ℝ) : ℂ) - (0 : ℝ)) * u)
        = ((oneSidedWindow u : ℝ) : ℂ) := by
      intro u
      rw [oneSidedWindow, Set.indicator_apply]
      split_ifs <;> simp
    rw [integral_congr_ae (.of_forall hpt), integral_complex_ofReal, oneSidedWindow,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      show (1 : ℝ → ℝ) = (fun _ => (1 : ℝ)) from rfl, MeasureTheory.integral_const]
    simp
  rw [hleft, hright]
  intro hcon
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have : ((π : ℝ) : ℂ) = 0 := by
    rw [← sub_eq_zero] at hcon
    field_simp at hcon
    simpa using hcon.symm
  exact hpi (by exact_mod_cast this)

end GridIncidence

/-! ### Axioms used -/

#print axioms GridIncidence.hasSum_inner_fourierCoeff
#print axioms GridIncidence.hasSum_inner_fourierCoeffOn
#print axioms GridIncidence.intervalIntegral_conj
#print axioms GridIncidence.integral_eq_intervalIntegral
#print axioms GridIncidence.half_lt_abs_of_not_mem
#print axioms GridIncidence.norm_exp_I_mul
#print axioms GridIncidence.fourier_neg_coe
#print axioms GridIncidence.fourierCoeffOn_window
#print axioms GridIncidence.phihat_sub_intCast
#print axioms GridIncidence.conj_fourierCoeffOn_reflect
#print axioms GridIncidence.memLp_window
#print axioms GridIncidence.hasSum_phihat_mul_phihat
#print axioms GridIncidence.tsum_phihat_mul_phihat_even
#print axioms GridIncidence.tsum_phihat_indicator_even
#print axioms GridIncidence.tsum_phihat_windowA
#print axioms GridIncidence.tsum_phihat_windowB
#print axioms GridIncidence.tsum_phihat_of_continuous
#print axioms GridIncidence.grid_incidence_needs_even
