import Mathlib

open Finset

namespace ShcBranch

/-- The removable branch `sinh t / t`, with its value at `0`. -/
noncomputable def shc (t : ℝ) : ℝ := if t = 0 then 1 else Real.sinh t / t

/-- **The branch is the divided series, for every `t` including `0`.**

This is the step that makes the truncation bound provable down to `t = 0`:
dividing the series termwise BEFORE bounding, rather than dividing the bound
for `sinh` afterwards (which blows up exactly at `0`). -/
theorem shc_eq_tsum (t : ℝ) :
    shc t = ∑' n : ℕ, t ^ (2 * n) / (Nat.factorial (2 * n + 1) : ℝ) := by
  unfold shc
  by_cases ht : t = 0
  · subst ht
    rw [if_pos rfl]
    rw [tsum_eq_single 0 ?_]
    · norm_num
    · intro n hn
      have : 0 < 2 * n := by omega
      simp [zero_pow this.ne']
  · rw [if_neg ht, Real.sinh_eq_tsum, ← tsum_div_const]
    refine tsum_congr fun n => ?_
    have h : t ^ (2 * n + 1) = t ^ (2 * n) * t := pow_succ t (2 * n)
    rw [h]
    field_simp

/-!
## What remains, and why this file stops here

The truncation bound is now a tail estimate on the series above: on `|t| ≤ 1`
each term is at most `1/(2n+1)!`, so the tail past `N` is at most
`∑_{n≥N} 1/(2n+1)! ≤ 2/(2N+1)!`. That is standard analysis, and it is out to
the theorem prover (`lean/ARISTOTLE-RUNS.md`, project `e7a77aa2`) with
`shc_eq_tsum` supplied as a given — which turns its problem from "find a route
that survives `t = 0`" into "do a tail estimate", a much narrower ask.

The identity is the part that could not be borrowed, and it is the part that is
done. Everything downstream of it is comparison against `1/n!`.
-/

end ShcBranch
#print axioms ShcBranch.shc_eq_tsum
