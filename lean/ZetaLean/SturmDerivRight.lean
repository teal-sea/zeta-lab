import Mathlib

open Polynomial Filter

/--
If `p` is a nonzero real polynomial with a root at `x`, then just to the right of `x`
the product `p * p'` is strictly positive.

Proof idea: write `p = (X - C x) ^ (k + 1) * q` with `q.eval x ≠ 0`, where `k + 1` is the
root multiplicity. Then `p * p' = (X - C x) ^ (2k+1) * g` with
`g = C (k+1) * q ^ 2 + (X - C x) * (q * q')`, and `g.eval x = (k+1) * (q.eval x) ^ 2 > 0`.
By continuity `g` stays positive near `x`, while `(y - x) ^ (2k+1) > 0` for `y > x`.
-/
theorem eval_mul_deriv_pos_right_of_root (p : Polynomial ℝ) (hp : p ≠ 0) (x : ℝ)
    (hx : p.IsRoot x) :
    ∃ ε > 0, ∀ y, x < y → y < x + ε → 0 < p.eval y * (Polynomial.derivative p).eval y := by
  have hpq : (X - C x) ^ p.rootMultiplicity x * (p /ₘ (X - C x) ^ p.rootMultiplicity x) = p :=
    pow_mul_divByMonic_rootMultiplicity_eq p x
  have hqx : (p /ₘ (X - C x) ^ p.rootMultiplicity x).eval x ≠ 0 :=
    eval_divByMonic_pow_rootMultiplicity_ne_zero x hp
  have hm1 : 1 ≤ p.rootMultiplicity x := (rootMultiplicity_pos hp).2 hx
  set q := p /ₘ (X - C x) ^ p.rootMultiplicity x with hqdef
  obtain ⟨k, hk⟩ : ∃ k, p.rootMultiplicity x = k + 1 := ⟨p.rootMultiplicity x - 1, by omega⟩
  rw [hk] at hpq
  set g : Polynomial ℝ := C ((k : ℝ) + 1) * q ^ 2 + (X - C x) * (q * derivative q) with hg
  have key : p * derivative p = (X - C x) ^ (2 * k + 1) * g := by
    rw [← hpq, hg, derivative_mul, derivative_pow, derivative_X_sub_C]
    simp
    ring
  have hgx : 0 < g.eval x := by
    have hval : g.eval x = ((k : ℝ) + 1) * (q.eval x) ^ 2 := by simp [hg]
    rw [hval]
    positivity
  have hcont : ContinuousAt (fun y => g.eval y) x := g.continuous_aeval.continuousAt
  have hev : ∀ᶠ y in nhds x, 0 < g.eval y := hcont.eventually (eventually_gt_nhds hgx)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε, hε, fun y hy1 hy2 => ?_⟩
  have hd : dist y x < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
  have hgy : 0 < g.eval y := hball hd
  have heval : p.eval y * (derivative p).eval y = (y - x) ^ (2 * k + 1) * g.eval y := by
    simpa using congrArg (Polynomial.eval y) key
  rw [heval]
  have hpow : 0 < (y - x) ^ (2 * k + 1) := pow_pos (by linarith) _
  positivity
