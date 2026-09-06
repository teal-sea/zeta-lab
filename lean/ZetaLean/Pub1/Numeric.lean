/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Pub 1 strong closure: the exact rational comparisons

Every numeric comparison the source-admissible strong-closure theorem leans on,
carried out in `ℚ` so that the Lean kernel decides it and nothing floating-point
enters the chain.  The informal source is
`hunts/wide_search/RESULTS-xiprime-admissible-closure.md`, section
"Exact strict-concavity bound".

The three load-bearing numbers are

* `uSecondDerivBound = 2 * c₁ = -410178/684401`, the exact bound on `u''`;
* `residualC2 = 0.006060899845`, the certified `‖w'' - u''‖_∞` bound;
* `concavityBound = -0.59326318`, the strict concavity constant for `w''`.

The whole point of this file is `concavity_margin`: the first two, added, still
clear the third.  The margin is genuinely tight, about `5.5 * 10^(-10)`, which
is why it is decided here in exact arithmetic rather than by decimal inspection.
-/

namespace ZetaLean.Pub1

/-! ### The exact-rational trial polynomial `u`

`u(s) = ∑_{j=0}^5 c_j s^(2j)` with the coefficients below.  They are transcribed
from the evidence document without rounding. -/

/-- Coefficient `c₀` of the exact-rational trial polynomial. -/
def c0 : ℚ := 427163 / 446844
/-- Coefficient `c₁`. -/
def c1 : ℚ := -205089 / 684401
/-- Coefficient `c₂`. -/
def c2 : ℚ := -2976898 / 824779
/-- Coefficient `c₃`. -/
def c3 : ℚ := -13369 / 15690
/-- Coefficient `c₄`. -/
def c4 : ℚ := -104561 / 672519
/-- Coefficient `c₅`. -/
def c5 : ℚ := -32375 / 630751

/-- The trial coefficients as a tuple, in the order displayed by the source. -/
def cCoeff : Fin 6 → ℚ := ![c0, c1, c2, c3, c4, c5]

/-- The constant coefficient is positive. -/
theorem c0_pos : 0 < c0 := by norm_num [c0]

/-- All five nonconstant coefficients of `u` are negative.  This is what makes
`u''(s) ≤ 2c₁` on the whole interval: every term past the first only subtracts. -/
theorem c1_neg : c1 < 0 := by norm_num [c1]
theorem c2_neg : c2 < 0 := by norm_num [c2]
theorem c3_neg : c3 < 0 := by norm_num [c3]
theorem c4_neg : c4 < 0 := by norm_num [c4]
theorem c5_neg : c5 < 0 := by norm_num [c5]

/-- Packaged form of the sign pattern: every nonconstant coefficient is `≤ 0`. -/
theorem cCoeff_nonpos (j : Fin 6) (hj : j ≠ 0) : cCoeff j ≤ 0 := by
  fin_cases j
  · exact absurd rfl hj
  · exact le_of_lt (by simpa [cCoeff] using c1_neg)
  · exact le_of_lt (by simpa [cCoeff] using c2_neg)
  · exact le_of_lt (by simpa [cCoeff] using c3_neg)
  · exact le_of_lt (by simpa [cCoeff] using c4_neg)
  · exact le_of_lt (by simpa [cCoeff] using c5_neg)

/-! ### The three certified constants -/

/-- The exact bound on `u''` over `I`: `u''(s) ≤ 2c₁ = -410178/684401`. -/
def uSecondDerivBound : ℚ := 2 * c1

/-- The certified residual-derived `C²` error bound,
`‖w'' - u''‖_∞ < 0.006060899845`. -/
def residualC2 : ℚ := 6060899845 / 10 ^ 12

/-- The strict concavity constant: `w''(s) < -0.59326318` on `I`. -/
def concavityBound : ℚ := -59326318 / 10 ^ 8

/-- The exact value of the `u''` bound. -/
theorem uSecondDerivBound_eq : uSecondDerivBound = -410178 / 684401 := by
  norm_num [uSecondDerivBound, c1]

/-- `2c₁ < -0.5993240804`, the decimal quoted by the evidence document.  The
inequality holds by about `1.2 * 10^(-10)` in relative terms, so it is decided
here rather than read off. -/
theorem uSecondDerivBound_lt : uSecondDerivBound < -5993240804 / 10 ^ 10 := by
  norm_num [uSecondDerivBound, c1]

/-- The certified `C²` bound is strictly below the rational witness `6061/10^6`
displayed in the source. -/
theorem residualC2_lt : residualC2 < 6061 / 10 ^ 6 := by
  norm_num [residualC2]

/-- **The margin closes.**  `u''`'s bound plus the certified `‖w'' - u''‖_∞`
still sits strictly below the strict-concavity constant, so `w'' = u'' + z''` is
bounded above by `-0.59326318`.  This single arithmetic fact is what strict
concavity of `w` reduces to. -/
theorem concavity_margin : uSecondDerivBound + residualC2 < concavityBound := by
  norm_num [uSecondDerivBound, residualC2, concavityBound, c1]

/-- The strict concavity constant is itself strictly below `-593/1000`, the
coarser rational bound quoted in the source, and in particular negative. -/
theorem concavityBound_lt : concavityBound < -593 / 1000 := by
  norm_num [concavityBound]

theorem concavityBound_neg : concavityBound < 0 := by
  norm_num [concavityBound]

/-! ### The ramp constants -/

/-- `‖η''‖₁ = 35/8` for the endpoint ramp. -/
def rampSecondDerivL1 : ℚ := 35 / 8

/-- `∫₀¹ η'(x)² dx = 700/429`. -/
def rampDerivSqIntegral : ℚ := 700 / 429

/-- The composite bound `‖(η²)''‖₁ ≤ 2∫η'² + 2‖η''‖₁ = 20615/1716`. -/
theorem ramp_sq_second_deriv_bound :
    2 * rampDerivSqIntegral + 2 * rampSecondDerivL1 = 20615 / 1716 := by
  norm_num [rampDerivSqIntegral, rampSecondDerivL1]

/-! ### The lesion test

The evidence document records a residual lesion: multiplying every
residual-derived bound by `101` must destroy the verdict.  Formalized, the
lesioned margin fails to clear the concavity constant, so any proof that routes
through `concavity_margin` becomes unusable under the lesion. -/

/-- **Residual lesion.**  With the residual bound inflated by `101`, the margin
no longer closes.  A proof of strict concavity that goes through
`concavity_margin` therefore cannot be replayed with a weakened residual bound. -/
theorem concavity_margin_lesioned :
    ¬ (uSecondDerivBound + 101 * residualC2 < concavityBound) := by
  norm_num [uSecondDerivBound, residualC2, concavityBound, c1]

/-- The lesioned margin lands on the wrong side of the concavity constant: the
verdict flips, exactly as the source's lesion record says. -/
theorem concavity_margin_lesioned_value :
    concavityBound < uSecondDerivBound + 101 * residualC2 := by
  norm_num [uSecondDerivBound, residualC2, concavityBound, c1]

end ZetaLean.Pub1
