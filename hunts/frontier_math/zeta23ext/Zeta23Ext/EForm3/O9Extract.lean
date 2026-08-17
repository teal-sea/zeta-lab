import Zeta23Ext.EForm3.O9Close
import Zeta23Ext.EForm3.O9Walk

/-!
# Reading real inequalities off a decided interval

`o9Box` is `Bool`-valued: it compares interval endpoints. The soundness
statement is about reals. This file is the conversion, and it is the only place
the two vocabularies meet.

`Iv.mem` is `(lo : ℝ) ≤ SO * x ∧ SO * x ≤ (hi : ℝ)`, so an endpoint comparison
divides through by the positive scale to give an inequality about the enclosed
value. Two directions are needed — an upper bound at or below zero, and one
enclosure's upper bound below another's lower bound — and both are one
`div`-free step from `SOR_pos`.

Stated on `Iv` rather than `EIv` on purpose: the `none` case of `o9Box` returns
`false`, so a decided box has already supplied the `some`.
-/

namespace Retention

open BandDual

/-- An enclosure whose upper endpoint is at or below zero encloses a
nonpositive value. -/
theorem nonpos_of_hi_nonpos {i : Iv} {x : ℝ} (h : i.mem x) (hhi : i.hi ≤ 0) :
    x ≤ 0 := by
  have hS := SOR_pos
  have h2 : (SO:ℝ) * x ≤ ((i.hi : ℤ) : ℝ) := h.2
  have h3 : ((i.hi : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hhi
  nlinarith [h2, h3, hS]

/-- If one enclosure's upper endpoint is at or below another's lower endpoint,
the enclosed values are ordered the same way. -/
theorem le_of_hi_le_lo {i j : Iv} {x z : ℝ}
    (hx : i.mem x) (hz : j.mem z) (h : i.hi ≤ j.lo) : x ≤ z := by
  have hS := SOR_pos
  have h1 : (SO:ℝ) * x ≤ ((i.hi : ℤ) : ℝ) := hx.2
  have h2 : ((j.lo : ℤ) : ℝ) ≤ (SO:ℝ) * z := hz.1
  have h3 : ((i.hi : ℤ) : ℝ) ≤ ((j.lo : ℤ) : ℝ) := by exact_mod_cast h
  nlinarith [h1, h2, h3, hS]

/-- The `mode = 1` test, read as a real inequality.

`excess` encloses `R² − cap`, so its upper endpoint being nonpositive says
`R² ≤ cap` — which is exactly `dam_le_of_mode1`'s hypothesis, and the branch
every box touching `y = 0` uses. -/
theorem mode1_bound {e : Iv} {R capR : ℝ}
    (hmem : e.mem (R * R - capR)) (hhi : e.hi ≤ 0) :
    R * R ≤ capR := by
  have := nonpos_of_hi_nonpos hmem hhi
  linarith

/-- The `mode = 2` test, read as a real inequality.

`l` encloses `y_hi² · (sup R² − cap)` and `q2` encloses `Qre²`, so the endpoint
comparison says the first is at most the second — `dam_le_of_mode2`'s
hypothesis. -/
theorem mode2_bound {l q2 : Iv} {lhs rhs : ℝ}
    (hl : l.mem lhs) (hq : q2.mem rhs) (h : l.hi ≤ q2.lo) :
    lhs ≤ rhs :=
  le_of_hi_le_lo hl hq h

end Retention

#print axioms Retention.nonpos_of_hi_nonpos
#print axioms Retention.le_of_hi_le_lo
#print axioms Retention.mode1_bound
#print axioms Retention.mode2_bound
