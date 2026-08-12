/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.LogMeanValue

/-!
# Complex logarithmic-frequency mean values

The arithmetic coefficients in the RC2 Dirichlet polynomial are complex.
This file lifts the real harmonic logarithmic estimate through coefficient
norms and records its exact connection to the sharp-block integral expansion.
-/

namespace ZetaLean.HigherXi

open Complex Finset

/-! ## Complex coefficient norms -/

/-- Endpoint-weighted square energy for complex coefficients supported on
`{1, ..., W}`. -/
noncomputable def complexWeightedCoefficientEnergy
    (W : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W, (n : ℝ) * ‖c n‖ ^ 2

/-- Absolute lower-triangular logarithmic interaction mass for complex
coefficients.  The factor two accounts for both orientations of a pair. -/
noncomputable def complexLogarithmicOffDiagonalMass
    (W : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W,
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
      2 * ‖c m‖ * ‖c n‖ / (Real.log n - Real.log m)

/-- The real harmonic theorem applies to arbitrary complex coefficients after
passing to their norms, with exactly the same constant. -/
theorem complexLogarithmicOffDiagonalMass_le (W : ℕ) (c : ℕ → ℂ) :
    complexLogarithmicOffDiagonalMass W c ≤
      3 * realHarmonicMass W * complexWeightedCoefficientEnergy W c := by
  simpa [complexLogarithmicOffDiagonalMass, logarithmicOffDiagonalMass,
    complexWeightedCoefficientEnergy, weightedCoefficientEnergy] using
    logarithmicOffDiagonalMass_le W (fun n => ‖c n‖)

/-- Explicit logarithmic version of the complex coefficient estimate. -/
theorem complexLogarithmicOffDiagonalMass_le_one_add_log
    (W : ℕ) (c : ℕ → ℂ) :
    complexLogarithmicOffDiagonalMass W c ≤
      3 * (1 + Real.log W) * complexWeightedCoefficientEnergy W c := by
  calc
    complexLogarithmicOffDiagonalMass W c ≤
        3 * realHarmonicMass W * complexWeightedCoefficientEnergy W c :=
      complexLogarithmicOffDiagonalMass_le W c
    _ ≤ 3 * (1 + Real.log W) * complexWeightedCoefficientEnergy W c := by
      have henergy : 0 ≤ complexWeightedCoefficientEnergy W c := by
        unfold complexWeightedCoefficientEnergy
        positivity
      nlinarith [mul_le_mul_of_nonneg_right
        (realHarmonicMass_le_one_add_log W) henergy]

/-! ## Exact sharp-block pair contributions -/

/-- The norm mass of both ordered contributions attached to each unordered
strict pair in the exact sharp-block expansion. -/
noncomputable def complexSharpPairMass
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W,
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
      (‖starRingEnd ℂ (c m) * c n *
          sharpBlockKernel U (Real.log n - Real.log m)‖ +
       ‖starRingEnd ℂ (c n) * c m *
          sharpBlockKernel U (Real.log m - Real.log n)‖)

/-- Both orientations of each exact kernel term obey the harmonic
logarithmic-frequency bound. -/
theorem complexSharpPairMass_le
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) :
    complexSharpPairMass U W c ≤
      6 * realHarmonicMass W * complexWeightedCoefficientEnergy W c := by
  have hkernel :
      complexSharpPairMass U W c ≤
        2 * complexLogarithmicOffDiagonalMass W c := by
    unfold complexSharpPairMass complexLogarithmicOffDiagonalMass
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm hn
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm.1.1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hgap_pos : 0 < Real.log n - Real.log m :=
      sub_pos.mpr (Real.strictMonoOn_log hmpos hnpos (by exact_mod_cast hm.2))
    have hkforward := norm_sharpBlockKernel_le_of_ne U
      (Real.log n - Real.log m) hgap_pos.ne'
    have hback_pos : 0 < |Real.log m - Real.log n| := by
      rw [abs_pos]
      linarith
    have hkback := norm_sharpBlockKernel_le_of_ne U
      (Real.log m - Real.log n) (by linarith)
    rw [abs_of_pos hgap_pos] at hkforward
    rw [show |Real.log m - Real.log n| = Real.log n - Real.log m by
      rw [abs_of_neg (by linarith)]; ring] at hkback
    change
      ‖star (c m) * c n *
          sharpBlockKernel U (Real.log n - Real.log m)‖ +
        ‖star (c n) * c m *
          sharpBlockKernel U (Real.log m - Real.log n)‖ ≤ _
    simp only [norm_mul]
    rw [norm_star (c m), norm_star (c n)]
    have hcoeff : 0 ≤ ‖c m‖ * ‖c n‖ := by positivity
    calc
      ‖c m‖ * ‖c n‖ * ‖sharpBlockKernel U (Real.log n - Real.log m)‖ +
          ‖c n‖ * ‖c m‖ * ‖sharpBlockKernel U (Real.log m - Real.log n)‖
          ≤ ‖c m‖ * ‖c n‖ * (2 / (Real.log n - Real.log m)) +
            ‖c n‖ * ‖c m‖ * (2 / (Real.log n - Real.log m)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hkforward hcoeff)
          (mul_le_mul_of_nonneg_left hkback (by positivity))
      _ = 2 * (2 * ‖c m‖ * ‖c n‖ /
          (Real.log n - Real.log m)) := by ring
  calc
    complexSharpPairMass U W c ≤
        2 * complexLogarithmicOffDiagonalMass W c := hkernel
    _ ≤ 2 * (3 * realHarmonicMass W *
          complexWeightedCoefficientEnergy W c) :=
      mul_le_mul_of_nonneg_left
        (complexLogarithmicOffDiagonalMass_le W c) (by norm_num)
    _ = 6 * realHarmonicMass W * complexWeightedCoefficientEnergy W c := by ring

/-- The actual complex sum of the two ordered terms attached to every strict
unordered pair. -/
noncomputable def complexSharpPairSum
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 W,
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
      (starRingEnd ℂ (c m) * c n *
          sharpBlockKernel U (Real.log n - Real.log m) +
       starRingEnd ℂ (c n) * c m *
          sharpBlockKernel U (Real.log m - Real.log n))

/-- Taking the norm after adding the exact ordered pair terms costs no more
than the corresponding absolute pair mass. -/
theorem norm_complexSharpPairSum_le_mass
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) :
    ‖complexSharpPairSum U W c‖ ≤ complexSharpPairMass U W c := by
  unfold complexSharpPairSum complexSharpPairMass
  calc
    ‖∑ n ∈ Finset.Icc 1 W,
        ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
          (starRingEnd ℂ (c m) * c n *
              sharpBlockKernel U (Real.log n - Real.log m) +
           starRingEnd ℂ (c n) * c m *
              sharpBlockKernel U (Real.log m - Real.log n))‖
        ≤ ∑ n ∈ Finset.Icc 1 W,
            ‖∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
              (starRingEnd ℂ (c m) * c n *
                  sharpBlockKernel U (Real.log n - Real.log m) +
               starRingEnd ℂ (c n) * c m *
                  sharpBlockKernel U (Real.log m - Real.log n))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 W,
          ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
            ‖starRingEnd ℂ (c m) * c n *
                sharpBlockKernel U (Real.log n - Real.log m) +
             starRingEnd ℂ (c n) * c m *
                sharpBlockKernel U (Real.log m - Real.log n)‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 W,
          ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
            (‖starRingEnd ℂ (c m) * c n *
                sharpBlockKernel U (Real.log n - Real.log m)‖ +
             ‖starRingEnd ℂ (c n) * c m *
                sharpBlockKernel U (Real.log m - Real.log n)‖) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      exact norm_add_le _ _

/-- The exact paired off-diagonal complex contribution obeys the same finite
harmonic bound as its absolute majorant. -/
theorem norm_complexSharpPairSum_le
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) :
    ‖complexSharpPairSum U W c‖ ≤
      6 * realHarmonicMass W * complexWeightedCoefficientEnergy W c :=
  (norm_complexSharpPairSum_le_mass U W c).trans
    (complexSharpPairMass_le U W c)

/-! ## Direct specialization of the exact integral expansion -/

/-- The logarithmic Dirichlet polynomial on the initial segment through `W`. -/
noncomputable def logarithmicDirichletPolynomial
    (W : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  dirichletPolynomial (Finset.Icc 1 W) c (fun n => Real.log n) t

/-- Exact finite sharp-block expansion at logarithmic frequencies, before any
absolute values or off-diagonal estimate. -/
theorem logarithmicDirichletPolynomial_integral_expansion
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) :
    (∫ t in U..2 * U,
        starRingEnd ℂ (logarithmicDirichletPolynomial W c t) *
          logarithmicDirichletPolynomial W c t) =
      ∑ m ∈ Finset.Icc 1 W, ∑ n ∈ Finset.Icc 1 W,
        starRingEnd ℂ (c m) * c n *
          sharpBlockKernel U (Real.log n - Real.log m) := by
  exact dirichletPolynomial_integral_expansion
    (Finset.Icc 1 W) c (fun n => Real.log n) U

/-- The exact diagonal in the logarithmic expansion is the block length times
the ordinary coefficient square mass. -/
theorem logarithmicSharpDiagonal_eq
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 W,
        starRingEnd ℂ (c n) * c n *
          sharpBlockKernel U (Real.log n - Real.log n)) =
      (U : ℂ) * ∑ n ∈ Finset.Icc 1 W, starRingEnd ℂ (c n) * c n := by
  simp_rw [sub_self, sharpBlockKernel_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end ZetaLean.HigherXi
