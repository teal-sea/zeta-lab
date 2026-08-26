
/-! ############################################################################
    Riemann.fail submission: the three required theorems.

    candidateKappa = 672737 / 1000000 = 0.672737
    currentRecordKappa = 2 - 1/cMT = Zeta23.ThmD.HD 1 = 0.6725007036794116...

    The numeric enclosure of the record constant is `gam_bounds` above:
      8274992907/10^10 <= gam <= 8274993018/10^10,  gam = (1/sqrt 2) cot (1/sqrt 2)
    and `Zeta23.ThmD.HD_one : HD 1 = 3/2 - cot(1/sqrt 2)/sqrt 2`, so
      HD 1 <= 3/2 - 8274992907/10^10 = 0.6725007093 < 0.672737.
    ########################################################################## -/

open Filter Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge.ThreePoint

/-- `(1/sqrt 2) = sqrt 2 / 2`, reconciling `HD_one`'s form with `gam`'s. -/
private lemma inv_sqrt2_eq : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  rw [eq_div_iff (by norm_num : (2:ℝ) ≠ 0), inv_mul_eq_div, eq_div_iff
    (Real.sqrt_ne_zero'.mpr (by norm_num)), ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- The record constant equals `3/2 - gam`. -/
private lemma record_eq_gam : Zeta23.ThmD.HD 1 = 3 / 2 - gam := by
  rw [Zeta23.ThmD.HD_one, gam, inv_sqrt2_eq]
  ring

/-- A rational upper bound on the record constant, from `gam_bounds`. -/
private lemma record_lt : Zeta23.ThmD.HD 1 < (672737 : ℝ) / 1000000 := by
  rw [record_eq_gam]
  have h := gam_bounds.1
  nlinarith [h]

/-- The submitted rational is at or below the three-point constant, so the
    three-point bound implies the bound at `candidateKappa`. -/
private lemma cand_le_Phi :
    (672737 : ℝ) / 1000000
      ≤ (149000000 * Zeta23.ThmD.HD 1 - 99200) / 148800133 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 148800133), record_eq_gam]
  have h := gam_bounds.2
  nlinarith [h]

theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa := by
  show Zeta23.ThmD.HD 1 < (672737 : ℝ) / 1000000
  exact record_lt

theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := three_point_bound ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have h2 : (N0simple T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ) := by
    exact_mod_cast (Zeta23.trivial_chain zetaSeam T (2 * T)).1
  have h3 : (candidateKappa - ε) ≤ ((149000000 * Zeta23.ThmD.HD 1 - 99200) / 148800133 - ε) := by
    show ((672737:ℝ)/1000000) - ε ≤ _
    linarith [cand_le_Phi]
  have h4 : (0:ℝ) ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  calc (candidateKappa - ε) * (Ncount T (2 * T) : ℝ)
      ≤ ((149000000 * Zeta23.ThmD.HD 1 - 99200) / 148800133 - ε) * (Ncount T (2 * T) : ℝ) :=
        mul_le_mul_of_nonneg_right h3 h4
    _ ≤ (N0simple T (2 * T) : ℝ) := h1
    _ ≤ (N0star T (2 * T) : ℝ) := h2

theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := three_point_bound_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have h2 : (N0simple 0 T : ℝ) ≤ (N0star 0 T : ℝ) := by
    exact_mod_cast (Zeta23.trivial_chain zetaSeam 0 T).1
  have h3 : (candidateKappa - ε) ≤ ((149000000 * Zeta23.ThmD.HD 1 - 99200) / 148800133 - ε) := by
    show ((672737:ℝ)/1000000) - ε ≤ _
    linarith [cand_le_Phi]
  have h4 : (0:ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  calc (candidateKappa - ε) * (Ncount 0 T : ℝ)
      ≤ ((149000000 * Zeta23.ThmD.HD 1 - 99200) / 148800133 - ε) * (Ncount 0 T : ℝ) :=
        mul_le_mul_of_nonneg_right h3 h4
    _ ≤ (N0simple 0 T : ℝ) := h1
    _ ≤ (N0star 0 T : ℝ) := h2
