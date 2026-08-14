import Zeta23Ext.EForm3.O9Bridge
import Zeta23Ext.EForm3.O9Assemble

/-!
# The numerator's parts, on the half-argument

`O9Assemble` shows `qreIv` encloses the componentwise quotient built from the
seven `boxParts` fields; `O9Bridge` shows `Re (Phi2 (s + i y)) = Qre y s`.
Between them: the field values must be the real and imaginary parts of
`Phi2_closed`'s numerator and denominator.

The denominator half is `O9Parts`. This file is the numerator half.

**Everything is stated on the half-argument `X = s/2`, `Y = y/2` as atomic
variables**, and that is not cosmetic. Written with the argument as `↑(s/2)`,
`simp` normalises the cast to `↑s * (1/2)` and the `ofReal` split lemmas stop
matching — the same Lean detail that forced `csin_re`/`csin_im` out of
`O9Bridge` as standalone helpers. Parametrising by the half-argument removes
the division before any tactic sees it.
-/

namespace Retention

open Complex BandDual

/-- `Re (cos (x + i b)) = cos x · cosh b`. -/
theorem ccos_re (x b : ℝ) :
    (Complex.cos ((x : ℂ) + (b : ℝ) * I)).re = Real.cos x * Real.cosh b := by
  rw [Complex.cos_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

/-- `Im (cos (x + i b)) = − sin x · sinh b`. -/
theorem ccos_im (x b : ℝ) :
    (Complex.cos ((x : ℂ) + (b : ℝ) * I)).im = -(Real.sin x * Real.sinh b) := by
  rw [Complex.cos_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

/-- **`Re` of `Phi2_closed`'s numerator**, on the half-argument.

With `X = s/2` and `Y = y/2`, the whole argument is `2X + 2Y i`. The result is
exactly the expression `reNum_mem` encloses — which is what makes the table's
real part a statement about `Phi2` rather than about an arbitrary composition. -/
theorem numC_re (X Y cc ss q : ℝ) :
    (2 * ((((2 * X : ℝ)) : ℂ) + ((2 * Y : ℝ)) * I) * Complex.sin ((X : ℂ) + (Y : ℝ) * I)
        * ((cc : ℝ) : ℂ)
      - 2 * ((q : ℝ) : ℂ) * Complex.cos ((X : ℂ) + (Y : ℝ) * I)
        * ((ss : ℝ) : ℂ)).re
      = 2 * ((2 * X * Real.sin X * Real.cosh Y
            - 2 * Y * Real.cos X * Real.sinh Y) * cc
          - Real.cos X * Real.cosh Y * ss * q) := by
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, csin_re, csin_im, ccos_re, ccos_im]
  ring

/-- **`Im` of `Phi2_closed`'s numerator**, on the half-argument.

Both terms carry a factor of `Y`: `Im(z sin(z/2))` through `z`'s own imaginary
part and through `sinh Y`, and `Im(cos(z/2))` through `sinh Y` alone. That is
the structural reason the quotient by `y` is taken termwise in `boxParts` and
`y = 0` never divides. -/
theorem numC_im (X Y cc ss q : ℝ) :
    (2 * ((((2 * X : ℝ)) : ℂ) + ((2 * Y : ℝ)) * I) * Complex.sin ((X : ℂ) + (Y : ℝ) * I)
        * ((cc : ℝ) : ℂ)
      - 2 * ((q : ℝ) : ℂ) * Complex.cos ((X : ℂ) + (Y : ℝ) * I)
        * ((ss : ℝ) : ℂ)).im
      = 2 * ((2 * X * Real.cos X * Real.sinh Y
            + 2 * Y * Real.sin X * Real.cosh Y) * cc
          + Real.sin X * Real.sinh Y * ss * q) := by
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, csin_re, csin_im, ccos_re, ccos_im]
  ring

end Retention

#print axioms Retention.ccos_re
#print axioms Retention.ccos_im
#print axioms Retention.numC_re
#print axioms Retention.numC_im
