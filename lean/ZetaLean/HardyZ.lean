import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Complex

/--
Hardy's Z function.

Defined using the completed Riemann zeta function `Λ(s)` to avoid
needing a continuous branch of `log Γ` along the critical line.
Since `Λ(1/2 + it)` is real, we divide by the positive real factor
`π^(-1/4) * ‖Γ(1/4 + I*t/2)‖` to obtain `Z(t)`.

Note: The goal is to eventually type this as `ℝ → ℝ` if preferred by Mathlib,
but here we start with the definition over `ℂ` or returning `ℂ` for easier
algebra before extracting the real part or proving it's real.
-/
noncomputable def hardyZ (t : ℝ) : ℂ :=
  completedRiemannZeta (1/2 + t * I) /
    ( (Real.pi : ℂ) ^ (-(1/4 : ℝ) : ℂ) * ‖Gamma (1/4 + t / 2 * I)‖ )

-- The first PR should prove the following properties:

/-- `Z t` is strictly real. -/
-- lemma hardyZ_is_real (t : ℝ) : ∃ (r : ℝ), hardyZ t = r := by
--   -- Proof sketch: Use `riemannZeta_conj` and `completedRiemannZeta_one_sub`
--   -- to show that `conj (Λ(1/2 + it)) = Λ(1/2 - it) = Λ(1/2 + it)`.

/-- The absolute value of `Z t` is exactly the absolute value of `ζ(1/2 + it)`. -/
-- lemma abs_hardyZ_eq_abs_zeta (t : ℝ) : ‖hardyZ t‖ = ‖riemannZeta (1/2 + t * I)‖ := by
--   -- Needs `Γ ≠ 0` on the critical line.

/-- `Z t` is an even function. -/
-- lemma hardyZ_even (t : ℝ) : hardyZ (-t) = hardyZ t := by
--   -- Follows from properties of `Λ` and `Γ`.

/-- `Z t` is zero if and only if `ζ(1/2 + it)` is zero. -/
-- lemma hardyZ_zero_iff_zeta_zero (t : ℝ) : hardyZ t = 0 ↔ riemannZeta (1/2 + t * I) = 0 := by
--   -- Follows from the non-vanishing of the exponential/gamma factors on the critical line.

/-- `Z t` is continuous. -/
-- lemma continuous_hardyZ : Continuous hardyZ := by
--   -- Allows intermediate value theorem usage for finding sign changes.
