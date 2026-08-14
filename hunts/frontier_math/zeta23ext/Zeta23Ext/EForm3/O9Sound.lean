import Zeta23Ext.EForm3.O9Field

/-!
# O9b: what `o9Field` is an enclosure *of*

`O9Check2.lean` runs `o9Field` in the kernel and gets `true` on every leaf.
By itself that says only that some integer arithmetic came out a certain way.
This file connects it to `Phi2`, in two steps.

**Step 1 — the real closed forms.** `ReNf`, `Ntilf`, `ReDf`, `D2f` below are
the real expressions `o9Field` evaluates, written as functions of `(y, s)`
rather than as intervals.  `Qref` and `Rf` are the two quantities it reports.

**Step 2 — the analytic identities**, which are the content:

    (Phi2 (s + y*I)).re = Qref y s
    (Phi2 (s + y*I)).im = y * Rf y s

The second is the one that matters.  It says `Im Phi2` carries an explicit
factor of `y`, so `Rf` is the honest `Qim / y` — finite at `y = 0`, where
`Qim / y` is literally `0 / 0`.  That is the whole reason the two-variable
table can be checked at all.

The bridge is `shfunR_mul : y * shfunR y = sinh (y/2)`, true at `y = 0` too
(`0 * (1/2) = 0 = sinh 0`), which is what lets `sinh (y/2)` be replaced by
`y * shq` and the `y` pulled out front.

Side condition: `Phi2_closed` needs `z^2 ≠ 2`.  The package supplies that from
`y ≠ 0`, which is exactly what is unavailable here; `sq_ne_two_of_re_gt`
supplies it from `√2 < s` instead, which holds on `[28/5, 60]`.
-/

namespace Retention

open BandDual Complex

/-! ### The real closed forms -/

/-- `Re N`, where `N = 2 (z sin(z/2) C - √2 S cos(z/2))` and `z = s + i y`. -/
noncomputable def ReNf (y s : ℝ) : ℝ :=
  2 * (Real.cos (Real.sqrt 2 / 2) *
        (s * Real.sin (s / 2) * Real.cosh (y / 2)
          - y * Real.cos (s / 2) * Real.sinh (y / 2))
      - Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * (Real.cos (s / 2) * Real.cosh (y / 2)))

/-- `Im N = 2 y * Ntilf`: the factor of `y` taken out. -/
noncomputable def Ntilf (y s : ℝ) : ℝ :=
  shfunR y * (Real.cos (Real.sqrt 2 / 2) * s * Real.cos (s / 2)
      + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.sin (s / 2))
    + Real.cos (Real.sqrt 2 / 2) * Real.sin (s / 2) * Real.cosh (y / 2)

/-- `Re D`, where `D = z^2 - 2`. -/
noncomputable def ReDf (y s : ℝ) : ℝ := s ^ 2 - y ^ 2 - 2

/-- `‖D‖²`. -/
noncomputable def D2f (y s : ℝ) : ℝ := ReDf y s ^ 2 + (2 * s * y) ^ 2

/-- `Re Phi2 (s + i y)`, in closed form. -/
noncomputable def Qref (y s : ℝ) : ℝ :=
  (ReNf y s * ReDf y s + 4 * s * y ^ 2 * Ntilf y s) / D2f y s

/-- `Im Phi2 (s + i y) / y`, in closed form and finite at `y = 0`. -/
noncomputable def Rf (y s : ℝ) : ℝ :=
  2 * (Ntilf y s * ReDf y s - s * ReNf y s) / D2f y s

/-! ### The bridge across `y = 0` -/

/-- `y * (sinh (y/2) / y) = sinh (y/2)`, including at `y = 0`. -/
theorem shfunR_mul (y : ℝ) : y * shfunR y = Real.sinh (y / 2) := by
  rcases eq_or_ne y 0 with rfl | h
  · simp [shfunR]
  · rw [shfunR, if_neg h]
    field_simp

/-! ### The side condition, from `s` rather than from `y` -/

/-- `(s + i y)^2 ≠ 2` whenever `√2 < s`, with no hypothesis on `y`.

`sq_ne_two_of_im_ne_zero` gets the same conclusion from `y ≠ 0`, which is
precisely the hypothesis this file cannot have. -/
theorem sq_ne_two_of_re_gt (s y : ℝ) (hs : Real.sqrt 2 < s) :
    ((s : ℂ) + (y : ℝ) * I) ^ 2 ≠ 2 := by
  have hs0 : 0 < s := lt_of_le_of_lt (Real.sqrt_nonneg 2) hs
  intro h
  have him : (((s : ℂ) + (y : ℝ) * I) ^ 2).im = (2 : ℂ).im := by rw [h]
  have hre : (((s : ℂ) + (y : ℝ) * I) ^ 2).re = (2 : ℂ).re := by rw [h]
  simp [pow_two, Complex.mul_im, Complex.mul_re] at him hre
  -- `im = 0` forces `y = 0` (since `s > 0`), and then `re = 2` forces `s = √2`
  have hy : y = 0 := by
    rcases mul_eq_zero.mp (by nlinarith : s * y = 0) with h1 | h1
    · exact absurd h1 (ne_of_gt hs0)
    · exact h1
  rw [hy] at hre
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-! ### `sin` and `cos` of `a + i b`, as four real identities

The same four `Phi.sinCosC_mem` establishes inline; hoisted here so the
numerator's real and imaginary parts can be computed directly. -/

theorem sin_addI_re (a b : ℝ) :
    (Complex.sin ((a : ℂ) + (b : ℝ) * I)).re = Real.sin a * Real.cosh b := by
  rw [Complex.sin_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

theorem sin_addI_im (a b : ℝ) :
    (Complex.sin ((a : ℂ) + (b : ℝ) * I)).im = Real.cos a * Real.sinh b := by
  rw [Complex.sin_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

theorem cos_addI_re (a b : ℝ) :
    (Complex.cos ((a : ℂ) + (b : ℝ) * I)).re = Real.cos a * Real.cosh b := by
  rw [Complex.cos_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

theorem cos_addI_im (a b : ℝ) :
    (Complex.cos ((a : ℂ) + (b : ℝ) * I)).im = -(Real.sin a * Real.sinh b) := by
  rw [Complex.cos_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

/-! ### The numerator and denominator, split into real and imaginary parts -/

/-- The numerator of `Phi2_closed` at `z = s + i y`. -/
noncomputable def Numc (y s : ℝ) : ℂ :=
  2 * (((s : ℂ) + (y : ℝ) * I) * Complex.sin (((s : ℂ) + (y : ℝ) * I) / 2)
        * ((Real.cos (Real.sqrt 2 / 2) : ℝ) : ℂ)
      - ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (((s : ℂ) + (y : ℝ) * I) / 2)
        * ((Real.sin (Real.sqrt 2 / 2) : ℝ) : ℂ))

theorem half_split (y s : ℝ) :
    ((s : ℂ) + (y : ℝ) * I) / 2 = ((s / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℝ) * I := by
  push_cast; ring

theorem Numc_re (y s : ℝ) : (Numc y s).re = ReNf y s := by
  simp only [Numc, half_split, ReNf]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, sin_addI_re, sin_addI_im, cos_addI_re, cos_addI_im]
  ring

/-- **The factor of `y` comes out.**  This is the identity the whole
two-variable route rests on. -/
theorem Numc_im (y s : ℝ) : (Numc y s).im = 2 * y * Ntilf y s := by
  simp only [Numc, half_split, Ntilf]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, sin_addI_re, sin_addI_im, cos_addI_re, cos_addI_im]
  rw [show Real.sinh (y / 2) = y * shfunR y from (shfunR_mul y).symm]
  ring

theorem den_re (y s : ℝ) : ((((s : ℂ) + (y : ℝ) * I) ^ 2 - 2)).re = ReDf y s := by
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, ReDf]
  ring

theorem den_im (y s : ℝ) : ((((s : ℂ) + (y : ℝ) * I) ^ 2 - 2)).im = 2 * s * y := by
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_im]
  ring

theorem den_normSq (y s : ℝ) :
    Complex.normSq (((s : ℂ) + (y : ℝ) * I) ^ 2 - 2) = D2f y s := by
  rw [Complex.normSq_apply, den_re, den_im, D2f]
  ring

/-! ### O9b, the two identities -/

/-- `Re Phi2 (s + i y)` is the closed form `o9Field` evaluates. -/
theorem phi2_re_eq (y s : ℝ) (hs : Real.sqrt 2 < s) :
    (Phi2 ((s : ℂ) + (y : ℝ) * I)).re = Qref y s := by
  have hne := sq_ne_two_of_re_gt s y hs
  rw [Phi2_closed _ hne]
  rw [show (2 * (((s : ℂ) + (y : ℝ) * I) * Complex.sin (((s : ℂ) + (y : ℝ) * I) / 2)
        * ((Real.cos (Real.sqrt 2 / 2) : ℝ) : ℂ)
      - ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (((s : ℂ) + (y : ℝ) * I) / 2)
        * ((Real.sin (Real.sqrt 2 / 2) : ℝ) : ℂ))) = Numc y s from rfl]
  rw [Complex.div_re, Numc_re, Numc_im, den_re, den_im, den_normSq, Qref]
  ring

/-- **`Im Phi2 (s + i y) = y * Rf y s`.**  The imaginary part carries an
explicit factor of `y`, so `Rf` is `Qim / y` with the removable zero taken
out — finite at `y = 0`, where `Qim / y` is `0 / 0`. -/
theorem phi2_im_eq (y s : ℝ) (hs : Real.sqrt 2 < s) :
    (Phi2 ((s : ℂ) + (y : ℝ) * I)).im = y * Rf y s := by
  have hne := sq_ne_two_of_re_gt s y hs
  rw [Phi2_closed _ hne]
  rw [show (2 * (((s : ℂ) + (y : ℝ) * I) * Complex.sin (((s : ℂ) + (y : ℝ) * I) / 2)
        * ((Real.cos (Real.sqrt 2 / 2) : ℝ) : ℂ)
      - ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (((s : ℂ) + (y : ℝ) * I) / 2)
        * ((Real.sin (Real.sqrt 2 / 2) : ℝ) : ℂ))) = Numc y s from rfl]
  rw [Complex.div_im, Numc_re, Numc_im, den_re, den_im, den_normSq, Rf]
  ring

end Retention
