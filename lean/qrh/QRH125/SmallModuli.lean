/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.IntervalExp

namespace QRH125

/-- The largest prime needed in each row of the q = 3,...,12 table. -/
def smallBound (q : ℕ) : ℕ :=
  match q with
  | 3 => 2 | 4 => 3 | 5 => 2 | 6 => 5 | 7 => 3
  | 8 => 5 | 9 => 2 | 10 => 3 | 11 => 2 | 12 => 7
  | _ => 0

/-- Every invertible residue is a power of a small prime times either one or
another small prime. This is a finite arithmetic certificate, not yet the
character theorem or the logarithmic comparison in Theorem 1(a). -/
def smallCover (q : ℕ) : Prop :=
  ∀ a ∈ Finset.range q, Nat.Coprime a q →
    ∃ e ∈ Finset.range 12, ∃ p ∈ ({2, 3, 5, 7} : Finset ℕ),
      ∃ r ∈ ({1, 5, 7} : Finset ℕ),
        p.Prime ∧ p ≤ smallBound q ∧
        (r = 1 ∨ r.Prime ∧ r ≤ smallBound q) ∧ (p ^ e * r) % q = a

instance (q : ℕ) : Decidable (smallCover q) := by
  unfold smallCover
  infer_instance

/-- Kernel reduction over a bounded list of natural numbers. -/
theorem small_moduli_cover :
    ∀ q ∈ Finset.Icc 3 12, smallCover q := by decide

/-- Multiplicativity turns the residue-cover data into a small prime on which
a nonprincipal character is neither zero nor one. -/
theorem exists_nonresidue_of_smallCover {q : ℕ} [NeZero q]
    (hcover : smallCover q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ≤ smallBound q ∧
      χ (p : ZMod q) ≠ 0 ∧ χ (p : ZMod q) ≠ 1 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hvalues (p : ℕ) (hp : p.Prime) (hle : p ≤ smallBound q) :
      χ (p : ZMod q) = 0 ∨ χ (p : ZMod q) = 1 := by
    by_cases hz : χ (p : ZMod q) = 0
    · exact Or.inl hz
    · exact Or.inr (hnone p hp hle hz)
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
  obtain ⟨e, _, p, _, r, _, hp, hple, hr, heq⟩ :=
    hcover (u : ZMod q).val (Finset.mem_range.mpr (ZMod.val_lt _))
      (ZMod.val_coe_unit_coprime u)
  have hcast : ((p ^ e * r : ℕ) : ZMod q) = u := by
    calc
      _ = (((p ^ e * r) % q : ℕ) : ZMod q) := (ZMod.natCast_mod _ _).symm
      _ = (((u : ZMod q).val : ℕ) : ZMod q) := congrArg (fun n : ℕ => (n : ZMod q)) heq
      _ = u := ZMod.natCast_zmod_val _
  have hrvalues : χ (r : ZMod q) = 0 ∨ χ (r : ZMod q) = 1 := by
    rcases hr with rfl | ⟨hrprime, hrle⟩
    · exact Or.inr (by simp)
    · exact hvalues r hrprime hrle
  have hpvalues : χ (p : ZMod q) ^ e = 0 ∨ χ (p : ZMod q) ^ e = 1 := by
    rcases hvalues p hp hple with hz | ho
    · by_cases he : e = 0
      · right; simp [he]
      · left; simp [hz, he]
    · right; simp [ho]
  have hproduct : χ (u : ZMod q) = 0 ∨ χ (u : ZMod q) = 1 := by
    rw [← hcast, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
    rcases hpvalues with h | h <;> rcases hrvalues with h' | h' <;> simp [h, h']
  exact hproduct.elim ((MulChar.apply_ne_zero_iff.mpr u.isUnit)) hu

/-- A deliberately coarse logarithm enclosure, sufficient for the binding
small modulus q = 3. The enclosure is evaluated by kernel arithmetic. -/
theorem log_three_gt : (1095 / 1000 : ℝ) < Real.log 3 := by
  obtain ⟨hlo, _⟩ := ZetaLean.Interval.contains_logQ
    (n := 12) (k := 1) (q := 3) (by norm_num) (by norm_num)
  refine lt_of_lt_of_le ?_ hlo
  norm_num [ZetaLean.Interval.logQ, ZetaLean.Interval.log2I,
    ZetaLean.Interval.log1, ZetaLean.Interval.exact, ZetaLean.Interval.neg,
    ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.logSum,
    ZetaLean.Interval.logRem, Finset.sum_range_succ]

theorem small_bound_le_log_pow {q : ℕ} (hq : q ∈ Finset.Icc 3 12) :
    (smallBound q : ℝ) ≤ (Real.log q) ^ 8 := by
  have hseven : ∀ q ∈ Finset.Icc 3 12, smallBound q ≤ 7 := by decide
  by_cases hthree : q = 3
  · subst q
    have hp : (1095 / 1000 : ℝ) ^ 8 ≤ (Real.log 3) ^ 8 := by
      gcongr <;> linarith [log_three_gt]
    change (2 : ℝ) ≤ (Real.log 3) ^ 8
    norm_num at hp
    linarith
  · have hfour : 4 ≤ q := by
      have := (Finset.mem_Icc.mp hq).1
      omega
    have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hlogq : (13 / 10 : ℝ) ≤ Real.log q := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ q by exact_mod_cast hfour)
      rw [hlogfour] at h
      linarith [ZetaLean.Interval.log_two_gt]
    have hp : (13 / 10 : ℝ) ^ 8 ≤ (Real.log q) ^ 8 := by
      gcongr <;> linarith [hlogq]
    have hbound : (smallBound q : ℝ) ≤ 7 := by exact_mod_cast hseven q hq
    norm_num at hp
    linarith

/-- The finite-modulus part of hunt 125, independent of OpenAI's theorem. -/
theorem small_moduli_nonresidue_bound {q : ℕ} [NeZero q]
    (hq : q ∈ Finset.Icc 3 12) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ (Real.log q) ^ 8 ∧
      χ (n : ZMod q) ≠ 0 ∧ χ (n : ZMod q) ≠ 1 := by
  obtain ⟨p, hp, hple, hpzero, hpone⟩ :=
    exists_nonresidue_of_smallCover (small_moduli_cover q hq) χ hχ
  have hple' : (p : ℝ) ≤ smallBound q := by exact_mod_cast hple
  exact ⟨p, hp.pos, hple'.trans (small_bound_le_log_pow hq), hpzero, hpone⟩

end QRH125
