import Mathlib

/-!
# Single-pair bandlimited retention: basic definitions

`gwin` is the window `g(u) = cos (√2 u)` on `|u| ≤ 1/2` (zero elsewhere), `c2` its
autocorrelation, `Aconst = √2 sin (1/√2) = ∫ g`, `Phi2` the Fourier transform of `g`
at a complex frequency, and `Ener G = (1/A²) ∫_{-1}^{1} c2 w ‖G w‖² dw`.
-/

open scoped BigOperators
open MeasureTheory

namespace Retention

/-- The window `g(u) = cos (√2 u)` for `|u| ≤ 1/2`, `0` otherwise. -/
noncomputable def gwin (u : ℝ) : ℝ := if |u| ≤ 1/2 then Real.cos (Real.sqrt 2 * u) else 0

/-- The autocorrelation `c2 w = ∫ g(u) g(u+w) du`. -/
noncomputable def c2 (w : ℝ) : ℝ := ∫ u : ℝ, gwin u * gwin (u + w)

/-- `A = √2 sin (1/√2) = ∫ g`. -/
noncomputable def Aconst : ℝ := Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)

/-- The Fourier transform of the window at a complex frequency. -/
noncomputable def Phi2 (z : ℂ) : ℂ := ∫ u : ℝ, (gwin u : ℂ) * Complex.exp (Complex.I * z * u)

/-- The energy functional `E[G] = (1/A²) ∫_{-1}^{1} c2 w ‖G w‖² dw`. -/
noncomputable def Ener (G : ℝ → ℂ) : ℝ :=
  (1 / Aconst ^ 2) * ∫ w in (-1:ℝ)..1, c2 w * ‖G w‖ ^ 2

/-- `Φ₂` restricted to real frequencies: `phiR r = ∫ g(u) cos (r u) du`. -/
noncomputable def phiR (r : ℝ) : ℝ :=
  ∫ u in (-(1/2 : ℝ))..(1/2), Real.cos (Real.sqrt 2 * u) * Real.cos (r * u)

/-- Real part of `Φ₂ (s + i y)`. -/
noncomputable def Pre (y s : ℝ) : ℝ :=
  ∫ u in (-(1/2 : ℝ))..(1/2), Real.cos (Real.sqrt 2 * u) * (Real.cos (s * u) * Real.cosh (y * u))

/-- Imaginary part of `Φ₂ (s + i y)`. -/
noncomputable def Qim (y s : ℝ) : ℝ :=
  -∫ u in (-(1/2 : ℝ))..(1/2), Real.cos (Real.sqrt 2 * u) * (Real.sin (s * u) * Real.sinh (y * u))

/-- The slack `σ`-quantity: `Shq y = ∫ g(u) sinh²(y u) du = (Φ₂(2iy) - A)/2`. -/
noncomputable def Shq (y : ℝ) : ℝ :=
  ∫ u in (-(1/2 : ℝ))..(1/2), Real.cos (Real.sqrt 2 * u) * (Real.sinh (y * u)) ^ 2

/-- The on-line sum `F(w) = ∑_{j<n} exp (i x_j w)`. -/
noncomputable def Fsum (n : ℕ) (x : ℕ → ℝ) : ℝ → ℂ :=
  fun w => ∑ j ∈ Finset.range n, Complex.exp (Complex.I * (x j : ℂ) * (w : ℂ))

/-- The single off-line pair `P(w) = 2 cosh (y w) exp (i t w)`. -/
noncomputable def Ppair (t y : ℝ) : ℝ → ℂ :=
  fun w => 2 * (Real.cosh (y * w) : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (w : ℂ))

end Retention
