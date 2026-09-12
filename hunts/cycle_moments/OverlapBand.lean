import Mathlib

/-!
# Weighted overlap identities and counting bounds

For multiplicities in `{1,2,3}`, the polynomial relation `H^2 = 4H - 3I`
and diagonal `H_ii=m_i` imply the exact identity `2S=6s+29N-33R`.
Here `S` is the explicitly defined weighted diagonal energy, `s` counts the
multiplicity-one locations, `N` is total multiplicity, and `R` is the number
of locations. The proof is valid in every finite dimension.

Replacing the polynomial relation by the explicit diagonal bounds proves the
corresponding inequality and a lower bound on `s`. The joint profile theorem
also proves the bound using the second moment and the overlap together.

The passage from a Hermitian spectral interval to the stated diagonal bounds
is not formalized here. All required bounds and multiplicity restrictions
remain visible hypotheses of the declarations.
-/
noncomputable section

open Matrix Finset
open scoped BigOperators

namespace CycleMoments.OverlapBand

def weightedEnergy {ι : Type*} [Fintype ι] (m : ι → ℕ) (q : ι → ℝ) : ℝ :=
  ∑ i, (q i)^2 / (m i : ℝ)

def simpleMultiplicityCount {ι : Type*} [Fintype ι] (m : ι → ℕ) : ℕ :=
  (Finset.univ.filter (fun i => m i = 1)).card

theorem scalar_profile (m : ℕ) (hm : m=1 ∨ m=2 ∨ m=3) :
    2 * (4*(m:ℝ)-3)^2 / (m:ℝ) =
      6 * (if m=1 then (1:ℝ) else 0) + 29*(m:ℝ)-33 := by
  rcases hm with rfl | rfl | rfl <;> norm_num

theorem scalar_profile_bound (m : ℕ) (hm : m=1 ∨ m=2 ∨ m=3)
    (q : ℝ) (h0 : 0 ≤ q) (hu : q ≤ 4*(m:ℝ)-3) :
    2*q^2/(m:ℝ) ≤ 6*(if m=1 then (1:ℝ) else 0)+29*(m:ℝ)-33 := by
  rcases hm with rfl | rfl | rfl <;> norm_num at hu ⊢ <;> nlinarith [abs_of_nonneg h0]

private theorem sum_profile {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    (∑ i, (6*(if m i=1 then (1:ℝ) else 0)+29*(m i:ℝ)-33)) =
      6*(simpleMultiplicityCount m : ℝ)+29*(∑ i, (m i:ℝ))-33*(Fintype.card ι:ℝ) := by
  have hi : (∑ i, (if m i=1 then (1:ℝ) else 0)) =
      (simpleMultiplicityCount m : ℝ) := by
    unfold simpleMultiplicityCount
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem weighted_profile_identity {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, m i=1 ∨ m i=2 ∨ m i=3) :
    2*weightedEnergy m (fun i => 4*(m i:ℝ)-3) =
      6*(simpleMultiplicityCount m : ℝ)+29*(∑ i, (m i:ℝ))-33*(Fintype.card ι:ℝ) := by
  unfold weightedEnergy
  rw [Finset.mul_sum]
  calc
    (∑ i, 2*((4*(m i:ℝ)-3)^2/(m i:ℝ))) =
        ∑ i, (6*(if m i=1 then (1:ℝ) else 0)+29*(m i:ℝ)-33) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [mul_div_assoc] using scalar_profile (m i) (hm i)
    _ = _ := sum_profile m

theorem weighted_profile_bound {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, m i=1 ∨ m i=2 ∨ m i=3)
    (q : ι → ℝ) (h0 : ∀ i, 0 ≤ q i) (hu : ∀ i, q i ≤ 4*(m i:ℝ)-3) :
    2*weightedEnergy m q ≤
      6*(simpleMultiplicityCount m : ℝ)+29*(∑ i, (m i:ℝ))-33*(Fintype.card ι:ℝ) := by
  unfold weightedEnergy
  rw [Finset.mul_sum]
  calc
    (∑ i, 2*((q i)^2/(m i:ℝ))) ≤
        ∑ i, (6*(if m i=1 then (1:ℝ) else 0)+29*(m i:ℝ)-33) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_div_assoc] using scalar_profile_bound (m i) (hm i) (q i) (h0 i) (hu i)
    _ = _ := sum_profile m

theorem matrix_overlap_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (m : ι → ℕ)
    (hm : ∀ i, m i=1 ∨ m i=2 ∨ m i=3)
    (hdiag : ∀ i, H i i = (m i:ℝ))
    (hpoly : H^2 = (4:ℝ) • H - (3:ℝ) • (1 : Matrix ι ι ℝ)) :
    2*weightedEnergy m (fun i => (H^2) i i) =
      6*(simpleMultiplicityCount m : ℝ)+29*(∑ i, (m i:ℝ))-33*(Fintype.card ι:ℝ) := by
  have hd (i : ι) : (H^2) i i = 4*(m i:ℝ)-3 := by
    have h := congrArg (fun A : Matrix ι ι ℝ => A i i) hpoly
    simpa [hdiag] using h
  simp_rw [hd]
  exact weighted_profile_identity m hm

theorem matrix_overlap_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (m : ι → ℕ)
    (hm : ∀ i, m i=1 ∨ m i=2 ∨ m i=3)
    (h0 : ∀ i, 0 ≤ (H^2) i i)
    (hu : ∀ i, (H^2) i i ≤ 4*(m i:ℝ)-3) :
    2*weightedEnergy m (fun i => (H^2) i i) ≤
      6*(simpleMultiplicityCount m : ℝ)+29*(∑ i, (m i:ℝ))-33*(Fintype.card ι:ℝ) :=
  weighted_profile_bound m hm (fun i => (H^2) i i) h0 hu

theorem simple_count_lower_bound {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, m i=1 ∨ m i=2 ∨ m i=3)
    (q : ι → ℝ) (h0 : ∀ i, 0 ≤ q i) (hu : ∀ i, q i ≤ 4*(m i:ℝ)-3) :
    (2*weightedEnergy m q - 29*(∑ i, (m i:ℝ))+33*(Fintype.card ι:ℝ))/6 ≤
      (simpleMultiplicityCount m : ℝ) := by
  have h := weighted_profile_bound m hm q h0 hu
  linarith


theorem joint_scalar_profile (m : ℕ) (hm : m=1 ∨ m=2 ∨ m=3)
    (r : ℝ) (hlo : (m:ℝ) ≤ r) (hhi : r ≤ 4-3/(m:ℝ)) :
    (m:ℝ)*r^2 ≤ (9/2:ℝ)*(m:ℝ)*r-(7/2:ℝ)*(m:ℝ)-3+
      3*(if m=1 then (1:ℝ) else 0) := by
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  rcases hm with rfl | rfl | rfl <;> norm_num at hlo hhi hp ⊢ <;> nlinarith

theorem joint_simple_count_lower_bound {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, m i=1 ∨ m i=2 ∨ m i=3)
    (r : ι → ℝ) (hlo : ∀ i, (m i:ℝ) ≤ r i)
    (hhi : ∀ i, r i ≤ 4-3/(m i:ℝ)) :
    (∑ i, (m i:ℝ)*(r i)^2)/3 - (3/2:ℝ)*(∑ i, (m i:ℝ)*r i)
      + (7/6:ℝ)*(∑ i, (m i:ℝ)) + (Fintype.card ι:ℝ) ≤
      (simpleMultiplicityCount m:ℝ) := by
  have hi : (∑ i, (if m i=1 then (1:ℝ) else 0)) =
      (simpleMultiplicityCount m : ℝ) := by
    unfold simpleMultiplicityCount
    rw [← Finset.sum_filter]
    simp
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i hi => joint_scalar_profile (m i) (hm i) (r i) (hlo i) (hhi i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  rw [hi] at hs
  linarith

/-- info: 'CycleMoments.OverlapBand.scalar_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalar_profile
/-- info: 'CycleMoments.OverlapBand.scalar_profile_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalar_profile_bound
/-- info: 'CycleMoments.OverlapBand.weighted_profile_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weighted_profile_identity
/-- info: 'CycleMoments.OverlapBand.weighted_profile_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weighted_profile_bound
/-- info: 'CycleMoments.OverlapBand.matrix_overlap_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matrix_overlap_identity
/-- info: 'CycleMoments.OverlapBand.matrix_overlap_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matrix_overlap_bound
/-- info: 'CycleMoments.OverlapBand.simple_count_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms simple_count_lower_bound
/-- info: 'CycleMoments.OverlapBand.joint_scalar_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joint_scalar_profile
/-- info: 'CycleMoments.OverlapBand.joint_simple_count_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joint_simple_count_lower_bound

end CycleMoments.OverlapBand
