/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib

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

end QRH125
