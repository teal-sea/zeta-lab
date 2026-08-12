/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.HigherXi

/-!
# Logarithmic-frequency mean-value bounds

The general weighted Montgomery--Vaughan inequality gives a constant multiple
of `sum n * |c n|^2` for the frequencies `log n`.  The rebuilt level-two bridge
does not need the sharp constant: an additional harmonic factor is harmless
against its strict power saving.

This file starts an elementary application-specific route.  It proves the
exact sharp-kernel bound, the logarithmic gap estimate for arbitrary positive
integers, and the weighted two-coefficient inequality that makes the final
finite double sum harmonic rather than polynomial in its cutoff.
-/

namespace ZetaLean.HigherXi

open Complex Finset

/-! ## Sharp-block kernel -/

theorem norm_sharpBlockKernel_le (U theta : ℝ) :
    ‖sharpBlockKernel U theta‖ ≤ if theta = 0 then |U| else 2 / |theta| := by
  by_cases htheta : theta = 0
  · subst theta
    simp [sharpBlockKernel_zero]
  · rw [if_neg htheta, sharpBlockKernel_of_ne_zero U theta htheta, norm_div]
    have hnorm1 :
        ‖Complex.exp ((-Complex.I * theta) * (2 * U))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hnorm2 : ‖Complex.exp ((-Complex.I * theta) * U)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hden : ‖(-Complex.I * (theta : ℂ))‖ = |theta| := by simp
    rw [hden]
    exact div_le_div_of_nonneg_right
      ((norm_sub_le _ _).trans_eq (by rw [hnorm1, hnorm2]; norm_num)) (abs_nonneg theta)

theorem norm_sharpBlockKernel_le_of_ne (U theta : ℝ) (htheta : theta ≠ 0) :
    ‖sharpBlockKernel U theta‖ ≤ 2 / |theta| := by
  simpa [htheta] using norm_sharpBlockKernel_le U theta

/-! ## Logarithmic gaps -/

/-- The gap between two arbitrary positive logarithmic frequencies. -/
theorem nat_sub_div_le_log_sub_log (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    ((n - m : ℕ) : ℝ) / n ≤ Real.log n - Real.log m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_trans (lt_of_lt_of_le Nat.zero_lt_one hm) hmn)
  have hratio : (0 : ℝ) < (n : ℝ) / m := div_pos hnpos hmpos
  have h := Real.one_sub_inv_le_log_of_pos hratio
  rw [Real.log_div hnpos.ne' hmpos.ne'] at h
  rw [Nat.cast_sub (Nat.le_of_lt hmn)]
  convert h using 1
  field_simp

/-- Reciprocal form of the logarithmic gap estimate. -/
theorem inv_log_sub_log_le_nat_div (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    (Real.log n - Real.log m)⁻¹ ≤ (n : ℝ) / ((n - m : ℕ) : ℝ) := by
  have hgap := nat_sub_div_le_log_sub_log m n hm hmn
  have hsubpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hmn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast lt_trans (lt_of_lt_of_le Nat.zero_lt_one hm) hmn
  have hgap_pos : 0 < Real.log n - Real.log m :=
    lt_of_lt_of_le (div_pos hsubpos hnpos) hgap
  have hleft : (((n - m : ℕ) : ℝ) / n)⁻¹ =
      (n : ℝ) / ((n - m : ℕ) : ℝ) := by
    field_simp
  rw [← hleft]
  exact (inv_le_inv₀ hgap_pos (div_pos hsubpos hnpos)).2 hgap

theorem abs_log_sub_log_eq (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    |Real.log n - Real.log m| = Real.log n - Real.log m := by
  rw [abs_of_pos]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast lt_trans (lt_of_lt_of_le Nat.zero_lt_one hm) hmn
  exact sub_pos.mpr (Real.strictMonoOn_log hmpos hnpos (by exact_mod_cast hmn))

/-! ## The pairwise harmonic allocation -/

/-- Weighted Young inequality aligned with the positive integer frequencies. -/
theorem two_mul_le_weighted_squares (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (x y : ℝ) :
    2 * |x| * |y| ≤ (n : ℝ) / m * y ^ 2 + (m : ℝ) / n * x ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_trans (lt_of_lt_of_le Nat.zero_lt_one hm) hmn
  have hsquare : 0 ≤ ((m : ℝ) * |x| - (n : ℝ) * |y|) ^ 2 := sq_nonneg _
  field_simp
  nlinarith [sq_abs x, sq_abs y]

/-- A single unordered logarithmic pair is allocated to the two weighted
diagonal energies.  Summing the first coefficient over `m<n` gives
`2*n*H_(n-1)`; summing the second over `n>m` gives at most `m*H_W`.
-/
theorem log_pair_harmonic_allocation (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (x y : ℝ) :
    2 * |x| * |y| / (Real.log n - Real.log m) ≤
      (n : ℝ) ^ 2 / ((m : ℝ) * ((n - m : ℕ) : ℝ)) * y ^ 2 +
        (m : ℝ) / ((n - m : ℕ) : ℝ) * x ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_trans (lt_of_lt_of_le Nat.zero_lt_one hm) hmn
  have hgap_pos : 0 < Real.log n - Real.log m := by
    exact sub_pos.mpr
      (Real.strictMonoOn_log hmpos hnpos (by exact_mod_cast hmn))
  have hsubpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hmn
  have henergy : 0 ≤ (n : ℝ) / m * y ^ 2 + (m : ℝ) / n * x ^ 2 := by
    positivity
  calc
    2 * |x| * |y| / (Real.log n - Real.log m)
        ≤ ((n : ℝ) / m * y ^ 2 + (m : ℝ) / n * x ^ 2) /
            (Real.log n - Real.log m) := by
          exact div_le_div_of_nonneg_right
            (two_mul_le_weighted_squares m n hm hmn x y) hgap_pos.le
    _ ≤ ((n : ℝ) / m * y ^ 2 + (m : ℝ) / n * x ^ 2) *
          ((n : ℝ) / ((n - m : ℕ) : ℝ)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_log_sub_log_le_nat_div m n hm hmn) henergy
    _ = (n : ℝ) ^ 2 / ((m : ℝ) * ((n - m : ℕ) : ℝ)) * y ^ 2 +
          (m : ℝ) / ((n - m : ℕ) : ℝ) * x ^ 2 := by
        field_simp

/-! ## Finite harmonic rows -/

/-- The real harmonic mass on the positive integers through `W`.  Keeping this
as a real finite sum avoids an irrelevant coercion through Mathlib's rational
`harmonic` while the mean-value estimate is assembled. -/
noncomputable def realHarmonicMass (W : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 W, ((k : ℝ)⁻¹)

theorem realHarmonicMass_nonneg (W : ℕ) : 0 ≤ realHarmonicMass W := by
  unfold realHarmonicMass
  positivity

theorem realHarmonicMass_eq_harmonic (W : ℕ) :
    realHarmonicMass W = (harmonic W : ℝ) := by
  unfold realHarmonicMass
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Explicit logarithmic growth of the only loss in the elementary
application-specific estimate. -/
theorem realHarmonicMass_le_one_add_log (W : ℕ) :
    realHarmonicMass W ≤ 1 + Real.log W := by
  rw [realHarmonicMass_eq_harmonic]
  exact harmonic_le_one_add_log W

/-- A lower triangular row of reciprocal indices is contained in the full
harmonic mass. -/
theorem sum_lower_inv_le_realHarmonicMass (W n : ℕ) :
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n), ((m : ℝ)⁻¹) ≤
      realHarmonicMass W := by
  unfold realHarmonicMass
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (by intro i hi his; positivity)

/-- Reflection `m ↦ n-m` sends every positive lower-triangular difference
back into the same harmonic range. -/
theorem sum_lower_difference_inv_le_realHarmonicMass
    (W n : ℕ) (hnW : n ≤ W) :
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
        ((((n - m : ℕ) : ℝ))⁻¹) ≤ realHarmonicMass W := by
  let s := (Finset.Icc 1 W).filter (fun m => m < n)
  let g : ℕ → ℕ := fun m => n - m
  have hinj : Set.InjOn g (s : Set ℕ) := by
    intro a ha b hb hab
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    change n - a = n - b at hab
    omega
  have himage : s.image g ⊆ Finset.Icc 1 W := by
    intro d hd
    simp only [Finset.mem_image] at hd
    obtain ⟨m, hm, rfl⟩ := hd
    simp only [s, Finset.mem_filter, Finset.mem_Icc] at hm
    change n - m ∈ Finset.Icc 1 W
    simp only [Finset.mem_Icc]
    omega
  calc
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n), ((((n - m : ℕ) : ℝ))⁻¹)
        = ∑ m ∈ s, (((g m : ℕ) : ℝ)⁻¹) := by rfl
    _ = ∑ d ∈ s.image g, ((d : ℝ)⁻¹) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ d ∈ Finset.Icc 1 W, ((d : ℝ)⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by intro i hi his; positivity)
    _ = realHarmonicMass W := rfl

/-- Translation `n ↦ n-m` sends every positive upper-triangular difference
back into the same harmonic range. -/
theorem sum_upper_difference_inv_le_realHarmonicMass
    (W m : ℕ) :
    ∑ n ∈ (Finset.Icc 1 W).filter (fun n => m < n),
        ((((n - m : ℕ) : ℝ))⁻¹) ≤ realHarmonicMass W := by
  let s := (Finset.Icc 1 W).filter (fun n => m < n)
  let g : ℕ → ℕ := fun n => n - m
  have hinj : Set.InjOn g (s : Set ℕ) := by
    intro a ha b hb hab
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    change a - m = b - m at hab
    omega
  have himage : s.image g ⊆ Finset.Icc 1 W := by
    intro d hd
    simp only [Finset.mem_image] at hd
    obtain ⟨n, hn, rfl⟩ := hd
    simp only [s, Finset.mem_filter, Finset.mem_Icc] at hn
    change n - m ∈ Finset.Icc 1 W
    simp only [Finset.mem_Icc]
    omega
  calc
    ∑ n ∈ (Finset.Icc 1 W).filter (fun n => m < n), ((((n - m : ℕ) : ℝ))⁻¹)
        = ∑ n ∈ s, (((g n : ℕ) : ℝ)⁻¹) := by rfl
    _ = ∑ d ∈ s.image g, ((d : ℝ)⁻¹) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ d ∈ Finset.Icc 1 W, ((d : ℝ)⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by intro i hi his; positivity)
    _ = realHarmonicMass W := rfl

/-! ## Triangular summation -/

/-- The endpoint-weighted square mass for a polynomial supported on
`{1, ..., W}`. -/
noncomputable def weightedCoefficientEnergy (W : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W, (n : ℝ) * c n ^ 2

/-- The first endpoint allocation in one lower-triangular row costs at most
two harmonic masses. -/
theorem lower_allocation_row_le (W n : ℕ) (hnW : n ≤ W) (y : ℝ) :
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
        (n : ℝ) ^ 2 / ((m : ℝ) * ((n - m : ℕ) : ℝ)) * y ^ 2 ≤
      2 * realHarmonicMass W * ((n : ℝ) * y ^ 2) := by
  let s := (Finset.Icc 1 W).filter (fun m => m < n)
  have hrewrite :
      (∑ m ∈ s,
          (n : ℝ) ^ 2 / ((m : ℝ) * ((n - m : ℕ) : ℝ)) * y ^ 2) =
        ((n : ℝ) * y ^ 2) *
          ((∑ m ∈ s, ((m : ℝ)⁻¹)) +
            ∑ m ∈ s, ((((n - m : ℕ) : ℝ))⁻¹)) := by
    rw [mul_add, mul_sum, mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [s, Finset.mem_filter, Finset.mem_Icc] at hm
    have hn_split : (n : ℝ) = (m : ℝ) + ((n - m : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hm.2)]
      ring
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by omega)
    have hdiff_ne : ((n - m : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_ne_zero_of_lt hm.2)
    rw [hn_split]
    field_simp [hm_ne, hdiff_ne]
    ring
  rw [hrewrite]
  have hsum :
      (∑ m ∈ s, ((m : ℝ)⁻¹)) + ∑ m ∈ s, ((((n - m : ℕ) : ℝ))⁻¹) ≤
        2 * realHarmonicMass W := by
    dsimp only [s]
    linarith [sum_lower_inv_le_realHarmonicMass W n,
      sum_lower_difference_inv_le_realHarmonicMass W n hnW]
  have henergy : 0 ≤ (n : ℝ) * y ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum henergy]

/-- The second endpoint allocation in one upper-triangular row costs one
harmonic mass. -/
theorem upper_allocation_row_le (W m : ℕ) (x : ℝ) :
    ∑ n ∈ (Finset.Icc 1 W).filter (fun n => m < n),
        (m : ℝ) / ((n - m : ℕ) : ℝ) * x ^ 2 ≤
      realHarmonicMass W * ((m : ℝ) * x ^ 2) := by
  let s := (Finset.Icc 1 W).filter (fun n => m < n)
  have hrewrite :
      (∑ n ∈ s, (m : ℝ) / ((n - m : ℕ) : ℝ) * x ^ 2) =
        ((m : ℝ) * x ^ 2) * ∑ n ∈ s, ((((n - m : ℕ) : ℝ))⁻¹) := by
    rw [mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [s, Finset.mem_filter, Finset.mem_Icc] at hn
    field_simp
  rw [hrewrite]
  have hsum := sum_upper_difference_inv_le_realHarmonicMass W m
  have henergy : 0 ≤ (m : ℝ) * x ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left
    (by simpa only [s] using hsum) henergy]

/-- Exchange the order of a finite strict triangular sum. -/
theorem sum_strictTriangle_swap {R : Type*} [AddCommMonoid R]
    (S : Finset ℕ) (f : ℕ → ℕ → R) :
    (∑ n ∈ S, ∑ m ∈ S.filter (fun m => m < n), f m n) =
      ∑ m ∈ S, ∑ n ∈ S.filter (fun n => m < n), f m n := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]

/-- The absolute lower-triangular off-diagonal mass associated with the
logarithmic frequencies `log n`. -/
noncomputable def logarithmicOffDiagonalMass (W : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W,
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
      2 * |c m| * |c n| / (Real.log n - Real.log m)

/-- Application-specific logarithmic mean-value estimate.  The full absolute
off-diagonal mass is bounded by three harmonic masses times the natural
endpoint-weighted coefficient energy.  Unlike a generic Hilbert inequality,
this elementary version loses `H_W`; the strict power margin in the rebuilt
level-two bridge absorbs that logarithm. -/
theorem logarithmicOffDiagonalMass_le (W : ℕ) (c : ℕ → ℝ) :
    logarithmicOffDiagonalMass W c ≤
      3 * realHarmonicMass W * weightedCoefficientEnergy W c := by
  let S := Finset.Icc 1 W
  let first : ℕ → ℕ → ℝ := fun m n =>
    (n : ℝ) ^ 2 / ((m : ℝ) * ((n - m : ℕ) : ℝ)) * c n ^ 2
  let second : ℕ → ℕ → ℝ := fun m n =>
    (m : ℝ) / ((n - m : ℕ) : ℝ) * c m ^ 2
  have hpair :
      logarithmicOffDiagonalMass W c ≤
        ∑ n ∈ S, ∑ m ∈ S.filter (fun m => m < n), (first m n + second m n) := by
    unfold logarithmicOffDiagonalMass
    dsimp only [S]
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm hn
    exact log_pair_harmonic_allocation m n hm.1.1 hm.2 (c m) (c n)
  have hfirst :
      (∑ n ∈ S, ∑ m ∈ S.filter (fun m => m < n), first m n) ≤
        2 * realHarmonicMass W * weightedCoefficientEnergy W c := by
    unfold weightedCoefficientEnergy
    dsimp only [S]
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simp only [Finset.mem_Icc] at hn
    exact lower_allocation_row_le W n hn.2 (c n)
  have hsecond :
      (∑ n ∈ S, ∑ m ∈ S.filter (fun m => m < n), second m n) ≤
        realHarmonicMass W * weightedCoefficientEnergy W c := by
    rw [sum_strictTriangle_swap S second]
    unfold weightedCoefficientEnergy
    dsimp only [S]
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    exact upper_allocation_row_le W m (c m)
  calc
    logarithmicOffDiagonalMass W c
        ≤ ∑ n ∈ S, ∑ m ∈ S.filter (fun m => m < n), (first m n + second m n) := hpair
    _ = (∑ n ∈ S, ∑ m ∈ S.filter (fun m => m < n), first m n) +
          ∑ n ∈ S, ∑ m ∈ S.filter (fun m => m < n), second m n := by
      simp_rw [Finset.sum_add_distrib]
    _ ≤ 2 * realHarmonicMass W * weightedCoefficientEnergy W c +
          realHarmonicMass W * weightedCoefficientEnergy W c := add_le_add hfirst hsecond
    _ = 3 * realHarmonicMass W * weightedCoefficientEnergy W c := by ring

/-- The absolute contribution of both orientations of every strict pair to
the exact sharp-block kernel expansion. -/
noncomputable def sharpKernelOffDiagonalMass
    (U : ℝ) (W : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W,
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
      2 * |c m| * |c n| *
        ‖sharpBlockKernel U (Real.log n - Real.log m)‖

/-- Concrete sharp-block corollary for logarithmic frequencies.  The diagonal
is exact in `dirichletPolynomial_integral_expansion`; both off-diagonal
orientations together cost at most six harmonic masses of weighted energy. -/
theorem sharpKernelOffDiagonalMass_le
    (U : ℝ) (W : ℕ) (c : ℕ → ℝ) :
    sharpKernelOffDiagonalMass U W c ≤
      6 * realHarmonicMass W * weightedCoefficientEnergy W c := by
  have hkernel :
      sharpKernelOffDiagonalMass U W c ≤ 2 * logarithmicOffDiagonalMass W c := by
    unfold sharpKernelOffDiagonalMass logarithmicOffDiagonalMass
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm hn
    have hgap_pos : 0 < Real.log n - Real.log m := by
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm.1.1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1
      exact sub_pos.mpr
        (Real.strictMonoOn_log hmpos hnpos (by exact_mod_cast hm.2))
    have hk := norm_sharpBlockKernel_le_of_ne U (Real.log n - Real.log m)
      hgap_pos.ne'
    rw [abs_of_pos hgap_pos] at hk
    have hcoeff : 0 ≤ 2 * |c m| * |c n| := by positivity
    calc
      2 * |c m| * |c n| * ‖sharpBlockKernel U (Real.log n - Real.log m)‖
          ≤ 2 * |c m| * |c n| * (2 / (Real.log n - Real.log m)) :=
        mul_le_mul_of_nonneg_left hk hcoeff
      _ = 2 * (2 * |c m| * |c n| /
          (Real.log n - Real.log m)) := by ring
  calc
    sharpKernelOffDiagonalMass U W c ≤ 2 * logarithmicOffDiagonalMass W c := hkernel
    _ ≤ 2 * (3 * realHarmonicMass W * weightedCoefficientEnergy W c) :=
      mul_le_mul_of_nonneg_left (logarithmicOffDiagonalMass_le W c) (by norm_num)
    _ = 6 * realHarmonicMass W * weightedCoefficientEnergy W c := by ring

end ZetaLean.HigherXi
