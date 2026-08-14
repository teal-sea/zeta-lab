import Zeta23Ext.EForm2.Bridge

/-!
# The exact reduction (`retention_gap`)

Expanding `E[F+P]` by the master identity gives an exact formula for the retention gap.
-/

open scoped BigOperators
open MeasureTheory ComplexConjugate

namespace Retention.EForm2

lemma c2_eq_zero {w : ℝ} (h : 1 < |w|) : c2 w = 0 := by
  unfold c2
  have hz : ∀ u : ℝ, gwin u * gwin (u + w) = 0 := by
    intro u
    by_cases hu : 1/2 < |u|
    · rw [gwin_eq_zero hu, zero_mul]
    · push_neg at hu
      have huw : 1/2 < |u + w| := by
        by_contra h3
        push_neg at h3
        rw [abs_le] at hu h3
        rcases abs_cases w with ⟨hw, _⟩ | ⟨hw, _⟩
        · rw [hw] at h; linarith [hu.1, h3.2]
        · rw [hw] at h; linarith [hu.2, h3.1]
      rw [gwin_eq_zero huw, mul_zero]
  simp [hz]

/-- The energy as an integral over the whole line. -/
lemma ener_full (G : ℝ → ℂ) : Ener G = (1 / Aconst ^ 2) * ∫ w : ℝ, c2 w * ‖G w‖ ^ 2 := by
  unfold Ener
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
  intro w hw
  have h1 : 1 < |w| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hw
    rcases hw with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  rw [c2_eq_zero h1, zero_mul]

/-- Expansion of the energy of a finite sum of complex exponentials. -/
lemma integral_c2_normSq_sum (S : Finset ℕ) (z : ℕ → ℂ) :
    ((∫ w : ℝ, c2 w * ‖∑ m ∈ S, Complex.exp (Complex.I * z m * (w : ℂ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ S, ∑ l ∈ S, (Phi2 (z m - conj (z l))) ^ 2 := by
  have key : ∀ (w : ℝ) (m l : ℕ),
      Complex.exp (Complex.I * z m * w) * conj (Complex.exp (Complex.I * z l * w))
        = Complex.exp (Complex.I * (z m - conj (z l)) * w) := by
    intro w m l
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hpt : ∀ w : ℝ,
      ((c2 w * ‖∑ m ∈ S, Complex.exp (Complex.I * z m * (w:ℂ))‖ ^ 2 : ℝ) : ℂ)
        = ∑ m ∈ S, ∑ l ∈ S, (c2 w : ℂ) * Complex.exp (Complex.I * (z m - conj (z l)) * w) := by
    intro w
    push_cast
    rw [show ((‖∑ m ∈ S, Complex.exp (Complex.I * z m * (w:ℂ))‖ : ℂ)) ^ 2
        = (∑ m ∈ S, Complex.exp (Complex.I * z m * (w:ℂ)))
          * conj (∑ m ∈ S, Complex.exp (Complex.I * z m * (w:ℂ))) from by
      rw [Complex.mul_conj']]
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← key w m l]
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [MeasureTheory.integral_finset_sum _
    (fun m _ => MeasureTheory.integrable_finset_sum _
      (fun l _ => integrable_c2_exp (z m - conj (z l))))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MeasureTheory.integral_finset_sum _ (fun l _ => integrable_c2_exp (z m - conj (z l)))]
  exact Finset.sum_congr rfl (fun l _ => master _)

/-- The energy of the on-line sum. -/
lemma ener_Fsum (n : ℕ) (x : ℕ → ℝ) :
    Ener (Fsum n x)
      = (1 / Aconst ^ 2) * ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, (phiR (x j - x k)) ^ 2 := by
  rw [ener_full]
  congr 1
  have h := integral_c2_normSq_sum (Finset.range n) (fun j => ((x j : ℝ) : ℂ))
  have h2 : (∑ m ∈ Finset.range n, ∑ l ∈ Finset.range n,
      (Phi2 ((x m : ℂ) - conj ((x l : ℂ)))) ^ 2)
      = ((∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, (phiR (x j - x k)) ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [Complex.conj_ofReal, ← Complex.ofReal_sub, Phi2_ofReal]
  rw [h2] at h
  exact_mod_cast h

/-- The frequencies of `F + P`: the `n` on-line points and the conjugate pair `t ± i y`. -/
noncomputable def zseq (n : ℕ) (x : ℕ → ℝ) (t y : ℝ) : ℕ → ℂ :=
  fun m => if m < n then (x m : ℂ) else if m = n then (t : ℂ) + (y : ℂ) * Complex.I
    else (t : ℂ) - (y : ℂ) * Complex.I

lemma zseq_of_lt {n : ℕ} {x : ℕ → ℝ} {t y : ℝ} {m : ℕ} (h : m < n) :
    zseq n x t y m = (x m : ℂ) := by
  simp [zseq, h]

lemma zseq_self {n : ℕ} {x : ℕ → ℝ} {t y : ℝ} :
    zseq n x t y n = (t : ℂ) + (y : ℂ) * Complex.I := by
  simp [zseq]

lemma zseq_succ {n : ℕ} {x : ℕ → ℝ} {t y : ℝ} :
    zseq n x t y (n + 1) = (t : ℂ) - (y : ℂ) * Complex.I := by
  simp [zseq]

lemma Pre_neg (y s : ℝ) : Pre (-y) s = Pre y s := by
  unfold Pre
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  rw [show -y * u = -(y * u) by ring, Real.cosh_neg]

lemma Qim_neg (y s : ℝ) : Qim (-y) s = -Qim y s := by
  unfold Qim
  rw [neg_neg]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  rw [show -y * u = -(y * u) by ring, Real.sinh_neg]
  ring

lemma Phi2_shift' (y s : ℝ) :
    Phi2 ((s : ℂ) - (y : ℂ) * Complex.I) = (Pre y s : ℂ) - (Qim y s : ℂ) * Complex.I := by
  have h := Phi2_shift (-y) s
  rw [Pre_neg, Qim_neg] at h
  push_cast at h
  rw [show (s : ℂ) - (y : ℂ) * Complex.I = (s : ℂ) + -(y : ℂ) * Complex.I by ring]
  rw [h]
  ring

/-- `F + P` is a sum of `n + 2` complex exponentials. -/
lemma Fsum_add_Ppair_eq (n : ℕ) (x : ℕ → ℝ) (t y : ℝ) (w : ℝ) :
    Fsum n x w + Ppair t y w
      = ∑ m ∈ Finset.range (n + 1 + 1), Complex.exp (Complex.I * zseq n x t y m * (w : ℂ)) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h1 : ∑ m ∈ Finset.range n, Complex.exp (Complex.I * zseq n x t y m * (w : ℂ))
      = Fsum n x w := by
    unfold Fsum
    exact Finset.sum_congr rfl (fun m hm => by rw [zseq_of_lt (Finset.mem_range.1 hm)])
  have h2 : Complex.exp (Complex.I * zseq n x t y n * (w : ℂ))
      + Complex.exp (Complex.I * zseq n x t y (n+1) * (w : ℂ)) = Ppair t y w := by
    rw [zseq_self, zseq_succ]
    unfold Ppair
    have e1 : Complex.I * ((t : ℂ) + (y : ℂ) * Complex.I) * (w : ℂ)
        = Complex.I * (t : ℂ) * (w : ℂ) + ((-(y * w) : ℝ) : ℂ) := by
      push_cast
      linear_combination ((y : ℂ) * w) * Complex.I_sq
    have e2 : Complex.I * ((t : ℂ) - (y : ℂ) * Complex.I) * (w : ℂ)
        = Complex.I * (t : ℂ) * (w : ℂ) + (((y * w) : ℝ) : ℂ) := by
      push_cast
      linear_combination (-(y : ℂ) * w) * Complex.I_sq
    rw [e1, e2, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    have : (Real.cosh (y * w) : ℂ) = ((Real.exp (-(y*w)) + Real.exp (y*w) : ℝ) : ℂ) / 2 := by
      rw [Real.cosh_eq]
      push_cast
      ring
    rw [this]
    push_cast
    ring
  rw [h1, add_assoc, h2]

lemma double_sum_eval (n : ℕ) (x : ℕ → ℝ) (t y : ℝ) :
    (∑ m ∈ Finset.range (n + 1 + 1), ∑ l ∈ Finset.range (n + 1 + 1),
        (Phi2 (zseq n x t y m - conj (zseq n x t y l))) ^ 2)
      = (((∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, (phiR (x j - x k)) ^ 2)
          + 4 * ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2)
          + 2 * (Aconst + 2 * Shq y) ^ 2 + 2 * Aconst ^ 2 : ℝ) : ℂ) := by
  set z := zseq n x t y with hzdef
  have hzn : z n = (t : ℂ) + (y : ℂ) * Complex.I := zseq_self
  have hzs : z (n + 1) = (t : ℂ) - (y : ℂ) * Complex.I := zseq_succ
  have hzm : ∀ m : ℕ, m < n → z m = (x m : ℂ) := fun m h => zseq_of_lt h
  have hcn : conj (z n) = (t : ℂ) - (y : ℂ) * Complex.I := by
    rw [hzn]; simp [Complex.conj_I]; ring
  have hcs : conj (z (n + 1)) = (t : ℂ) + (y : ℂ) * Complex.I := by
    rw [hzs]; simp [Complex.conj_I]
  -- the four blocks
  have e1 : ∀ m ∈ Finset.range n, ∀ l ∈ Finset.range n,
      (Phi2 (z m - conj (z l))) ^ 2 = (((phiR (x m - x l)) ^ 2 : ℝ) : ℂ) := by
    intro m hm l hl
    rw [hzm m (Finset.mem_range.1 hm), hzm l (Finset.mem_range.1 hl),
      Complex.conj_ofReal, ← Complex.ofReal_sub, Phi2_ofReal]
    push_cast
    ring
  have epm : ∀ m : ℕ, m < n → (Phi2 (z m - conj (z n))) ^ 2 + (Phi2 (z m - conj (z (n+1)))) ^ 2
      = ((2 * ((Pre y (x m - t)) ^ 2 - (Qim y (x m - t)) ^ 2) : ℝ) : ℂ) := by
    intro m hm
    rw [hcn, hcs, hzm m hm]
    rw [show (x m : ℂ) - ((t : ℂ) - (y : ℂ) * Complex.I)
        = ((x m - t : ℝ) : ℂ) + (y : ℂ) * Complex.I by push_cast; ring,
      show (x m : ℂ) - ((t : ℂ) + (y : ℂ) * Complex.I)
        = ((x m - t : ℝ) : ℂ) - (y : ℂ) * Complex.I by push_cast; ring,
      Phi2_shift, Phi2_shift']
    push_cast
    linear_combination (2 * (Qim y (x m - t) : ℂ) ^ 2) * Complex.I_sq
  have epl : ∀ l : ℕ, l < n → (Phi2 (z n - conj (z l))) ^ 2 + (Phi2 (z (n+1) - conj (z l))) ^ 2
      = ((2 * ((Pre y (x l - t)) ^ 2 - (Qim y (x l - t)) ^ 2) : ℝ) : ℂ) := by
    intro l hl
    rw [hzm l hl, Complex.conj_ofReal, hzn, hzs]
    rw [show (t : ℂ) + (y : ℂ) * Complex.I - (x l : ℂ)
        = -(((x l - t : ℝ) : ℂ) - (y : ℂ) * Complex.I) by push_cast; ring,
      show (t : ℂ) - (y : ℂ) * Complex.I - (x l : ℂ)
        = -(((x l - t : ℝ) : ℂ) + (y : ℂ) * Complex.I) by push_cast; ring,
      Phi2_neg, Phi2_neg, Phi2_shift, Phi2_shift']
    push_cast
    linear_combination (2 * (Qim y (x l - t) : ℂ) ^ 2) * Complex.I_sq
  have enn : (Phi2 (z n - conj (z n))) ^ 2 = (((Aconst + 2 * Shq y) ^ 2 : ℝ) : ℂ) := by
    rw [hcn, hzn, show (t : ℂ) + (y : ℂ) * Complex.I - ((t : ℂ) - (y : ℂ) * Complex.I)
        = 2 * (y : ℂ) * Complex.I by ring, Phi2_two_mul_I]
    push_cast
    ring
  have ess : (Phi2 (z (n+1) - conj (z (n+1)))) ^ 2 = (((Aconst + 2 * Shq y) ^ 2 : ℝ) : ℂ) := by
    rw [hcs, hzs, show (t : ℂ) - (y : ℂ) * Complex.I - ((t : ℂ) + (y : ℂ) * Complex.I)
        = -(2 * (y : ℂ) * Complex.I) by ring, Phi2_neg, Phi2_two_mul_I]
    push_cast
    ring
  have ens : (Phi2 (z n - conj (z (n+1)))) ^ 2 = ((Aconst ^ 2 : ℝ) : ℂ) := by
    rw [hcs, hzn, show (t : ℂ) + (y : ℂ) * Complex.I - ((t : ℂ) + (y : ℂ) * Complex.I)
        = 0 by ring, Phi2_zero]
    push_cast
    ring
  have esn : (Phi2 (z (n+1) - conj (z n))) ^ 2 = ((Aconst ^ 2 : ℝ) : ℂ) := by
    rw [hcn, hzs, show (t : ℂ) - (y : ℂ) * Complex.I - ((t : ℂ) - (y : ℂ) * Complex.I)
        = 0 by ring, Phi2_zero]
    push_cast
    ring
  -- expand the double sum
  simp only [Finset.sum_range_succ]
  have hA1 : (∑ m ∈ Finset.range n, ((∑ l ∈ Finset.range n, (Phi2 (z m - conj (z l))) ^ 2)
        + (Phi2 (z m - conj (z n))) ^ 2 + (Phi2 (z m - conj (z (n+1)))) ^ 2))
      = (∑ m ∈ Finset.range n, ∑ l ∈ Finset.range n, (Phi2 (z m - conj (z l))) ^ 2)
        + ∑ m ∈ Finset.range n, ((Phi2 (z m - conj (z n))) ^ 2
            + (Phi2 (z m - conj (z (n+1)))) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [hA1]
  have hB1 : (∑ m ∈ Finset.range n, ∑ l ∈ Finset.range n, (Phi2 (z m - conj (z l))) ^ 2)
      = ((∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, (phiR (x j - x k)) ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun l hl => by
      have := e1 m hm l hl; push_cast at this; exact this))
  have hB2 : (∑ m ∈ Finset.range n, ((Phi2 (z m - conj (z n))) ^ 2
        + (Phi2 (z m - conj (z (n+1)))) ^ 2))
      = ((2 * ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m hm => by
      have := epm m (Finset.mem_range.1 hm); push_cast at this; exact this)
  have hB3 : (∑ l ∈ Finset.range n, (Phi2 (z n - conj (z l))) ^ 2)
        + ∑ l ∈ Finset.range n, (Phi2 (z (n+1) - conj (z l))) ^ 2
      = ((2 * ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2) : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l hl => by
      have := epl l (Finset.mem_range.1 hl); push_cast at this; exact this)
  rw [hB1, hB2, enn, ess, ens, esn]
  have hfin : (∑ l ∈ Finset.range n, (Phi2 (z n - conj (z l))) ^ 2)
      + ∑ l ∈ Finset.range n, (Phi2 (z (n+1) - conj (z l))) ^ 2
      = ((2 * ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2) : ℝ) : ℂ) := hB3
  push_cast at hfin ⊢
  linear_combination hfin

/-- The energy of the on-line sum together with the off-line pair. -/
lemma ener_Fsum_add_Ppair (n : ℕ) (x : ℕ → ℝ) (t y : ℝ) :
    Ener (fun w => Fsum n x w + Ppair t y w)
      = (1 / Aconst ^ 2) *
        ((∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, (phiR (x j - x k)) ^ 2)
          + 4 * ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2)
          + 2 * (Aconst + 2 * Shq y) ^ 2 + 2 * Aconst ^ 2) := by
  rw [ener_full]
  congr 1
  have h := integral_c2_normSq_sum (Finset.range (n + 1 + 1)) (zseq n x t y)
  rw [double_sum_eval n x t y] at h
  simp_rw [← Fsum_add_Ppair_eq n x t y] at h
  exact_mod_cast h

/-- **The exact reduction.** -/
theorem retention_gap (n : ℕ) (x : ℕ → ℝ) (t y : ℝ) :
    Ener (fun w => Fsum n x w + Ppair t y w)
        - ((199/200) * Ener (Fsum n x) + (1/200) * n + 4)
      = (1 / Aconst ^ 2) *
        ((1/200) * ((∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, (phiR (x j - x k)) ^ 2)
            - n * Aconst ^ 2)
          + 4 * ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2)
          + 8 * Aconst * Shq y + 8 * (Shq y) ^ 2) := by
  rw [ener_Fsum_add_Ppair, ener_Fsum]
  have hA : Aconst ≠ 0 := ne_of_gt Aconst_pos
  field_simp
  ring

end Retention.EForm2
