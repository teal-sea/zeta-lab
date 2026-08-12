/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.ClusterPrefix

/-!
# Exact labelled matching counts

This file isolates the finite counting identity used by the squarefree RAMS2
cluster majorant.  A matching with `a` edges on `r` labelled vertices is
obtained by choosing its `2a` covered vertices and pairing them.  The pairing
count is defined recursively, so the construction is division-free in `ℕ`.

The resulting `matchingCount r a` is shown to satisfy both the factorial
formula

`r! / (2^a * a! * (r - 2a)!)`

on its natural range and the vertex-removal recurrence.  No analytic estimate,
connected-component classification, or RAMS2 asymptotic is asserted here.
-/

namespace ZetaLean.HigherXi

/-- The number of pairings of `2a` labelled vertices. -/
def pairingCount : ℕ → ℕ
  | 0 => 1
  | a + 1 => (2 * a + 1) * pairingCount a

@[simp]
theorem pairingCount_zero : pairingCount 0 = 1 := rfl

@[simp]
theorem pairingCount_succ (a : ℕ) :
    pairingCount (a + 1) = (2 * a + 1) * pairingCount a := rfl

/-- The number of matchings with exactly `a` edges on `r` labelled vertices. -/
def matchingCount (r a : ℕ) : ℕ :=
  r.choose (2 * a) * pairingCount a

@[simp]
theorem matchingCount_zero_edges (r : ℕ) : matchingCount r 0 = 1 := by
  simp [matchingCount]

/-- There are no `a`-edge matchings when fewer than `2a` vertices are
available. -/
theorem matchingCount_eq_zero_of_lt {r a : ℕ} (h : r < 2 * a) :
    matchingCount r a = 0 := by
  simp [matchingCount, Nat.choose_eq_zero_of_lt h]

/-- The recursive pairing count clears the denominator in the standard
factorial expression `(2a)! / (2^a a!)`. -/
theorem pairingCount_mul_pow_two_mul_factorial (a : ℕ) :
    pairingCount a * (2 ^ a * a.factorial) = (2 * a).factorial := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pairingCount_succ, pow_succ, Nat.factorial_succ]
      calc
        (2 * a + 1) * pairingCount a *
              (2 ^ a * 2 * ((a + 1) * a.factorial)) =
            (2 * a + 2) * (2 * a + 1) *
              (pairingCount a * (2 ^ a * a.factorial)) := by ring
        _ = (2 * a + 2) * (2 * a + 1) * (2 * a).factorial := by rw [ih]
        _ = (2 * (a + 1)).factorial := by
          rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
            Nat.factorial_succ,
            show 2 * a + 1 = 2 * a + 1 by rfl, Nat.factorial_succ]
          ring

/-- Denominator-cleared form of the exact labelled matching count. -/
theorem matchingCount_mul_denominator_eq_factorial {r a : ℕ} (h : 2 * a ≤ r) :
    matchingCount r a *
        (2 ^ a * a.factorial * (r - 2 * a).factorial) = r.factorial := by
  rw [matchingCount]
  calc
    (r.choose (2 * a) * pairingCount a) *
          (2 ^ a * a.factorial * (r - 2 * a).factorial) =
        r.choose (2 * a) *
          (pairingCount a * (2 ^ a * a.factorial)) *
            (r - 2 * a).factorial := by ring
    _ = r.choose (2 * a) * (2 * a).factorial *
          (r - 2 * a).factorial := by
      rw [pairingCount_mul_pow_two_mul_factorial]
    _ = r.factorial := Nat.choose_mul_factorial_mul_factorial h

/-- The factorial formula used as `N(r,a)` in the RAMS2 squarefree cluster
majorant. -/
theorem matchingCount_eq_factorial_div {r a : ℕ} (h : 2 * a ≤ r) :
    matchingCount r a =
      r.factorial /
        (2 ^ a * a.factorial * (r - 2 * a).factorial) := by
  apply Nat.eq_div_of_mul_eq_right
  · positivity
  · rw [mul_comm]
    exact matchingCount_mul_denominator_eq_factorial h

/-- Removing one distinguished vertex either leaves it unmatched or pairs it
with one of the other vertices.  This recurrence characterizes the same exact
labelled count without division. -/
theorem matchingCount_add_two_succ (r a : ℕ) :
    matchingCount (r + 2) (a + 1) =
      matchingCount (r + 1) (a + 1) +
        (r + 1) * matchingCount r a := by
  unfold matchingCount
  rw [show r + 2 = (r + 1) + 1 by omega,
    show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
    Nat.choose_succ_succ', pairingCount_succ]
  have hchoose :
      (r + 1) * r.choose (2 * a) =
        (r + 1).choose (2 * a + 1) * (2 * a + 1) :=
    Nat.add_one_mul_choose_eq r (2 * a)
  rw [show (r + 1) * (r.choose (2 * a) * pairingCount a) =
      ((r + 1) * r.choose (2 * a)) * pairingCount a by ring, hchoose]
  ring

end ZetaLean.HigherXi
