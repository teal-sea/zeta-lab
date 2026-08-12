import Mathlib

open Polynomial

/-- If `p` is coprime to its derivative, then no root of `p` is a root of `p'`.
Evaluating a Bézout combination `a * p + b * p' = 1` at the root `x` gives `0 = 1`. -/
theorem simple_roots_of_coprime_deriv (p : Polynomial ℝ)
    (h : IsCoprime p (Polynomial.derivative p)) (x : ℝ) (hx : p.IsRoot x) :
    ¬ (Polynomial.derivative p).IsRoot x := by
  intro hx'
  obtain ⟨a, b, hab⟩ := h
  have := congrArg (Polynomial.eval x) hab
  simp [Polynomial.IsRoot.def.mp hx, Polynomial.IsRoot.def.mp hx'] at this
