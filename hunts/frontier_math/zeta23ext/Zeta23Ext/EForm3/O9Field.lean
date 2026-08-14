import Zeta23Ext.BandCert.Phi

/-!
# The O9 field, factored so that `y = 0` is not a special point

`O9Damage.lean` encloses `Dam (1/2) s = -Re (Phi2 (s + I/2))^2` at the single
depth `y = 1/2`, and therefore needs

    D y s / y^2  ≤  4 * D (1/2) s        for all `y ∈ [0,1/2]`

to reach the other depths.  That reduction is measured, not proved.  This file
removes the need for it by making the table two-variable, which requires one
change of shape.

## Why the obvious two-variable table does not work

The obligation is `Qim^2 - Qre^2 ≤ c * y^2`.  On a box whose `y` range touches
`0`, interval arithmetic bounds the left side above and `c * y^2` below by
`c * 0 = 0`, so it demands `Qim^2 ≤ Qre^2` — false at the zeros of
`Qre (0, ·)`, and those zeros lie *inside* the windows (one per window, at
`s ≈ 6.6431, 12.7553, 18.9767, …`).  The two sides are both `O(y^2)` and the
enclosure has decorrelated them; bisecting in `y` refines forever.

## The factorisation

`Qim` is odd in `y`, so `Qim = y * R` with `R` analytic across `y = 0`.
Writing `C = cos (√2/2)`, `S = sin (√2/2)`, `sn = sin (s/2)`, `cs = cos (s/2)`,
`sh = sinh (y/2)`, `ch = cosh (y/2)`, and `shq = sinh (y/2) / y`:

    ReN  = 2 * (C * (s*sn*ch - y*cs*sh) - √2*S*cs*ch)
    Ntil = shq * (C*s*cs + √2*S*sn) + C*sn*ch          -- so `ImN = 2*y*Ntil`
    ReD  = s^2 - y^2 - 2 ,  ImD = 2*s*y ,  D2 = ReD^2 + ImD^2
    R    = 2 * (Ntil*ReD - s*ReN) / D2
    Qre  = (ReN*ReD + 4*s*y^2*Ntil) / D2

and the check becomes

    y^2 * (R^2 - c)  ≤  Qre^2                                          (*)

whose two sides are `O(1)` where the original pair was `O(y^2)`.  At `y = 0`
the left side is `0` and the right side is `Qre (0,s)^2 ≥ 0`, so the
degeneracy is gone.  With `c = 0`, `(*)` is exactly the complement claim ("no
damage between the windows"), so one shape serves the whole rectangle.

The only new leaf is `shq`, the removable branch of `sinh`.  It is the same
device `Leaves.lean` already carries for `sin (u/2) / u` (its `sfnL`), with
the alternating signs removed — `shfnL` below is `sinhL` halved, exactly as
`sfnL` is `sinL` halved.

## Soundness: what is proved here and what is not

Everything in this file is a **computable enclosure**, and `O9Check2.lean`
runs it in the kernel.  What that establishes is that the recorded rectangles
satisfy `(*)` *as evaluated by these definitions*.

The seam to the analysis is the membership lemma

    o9Field_mem :
      (some ⟨slo,shi⟩).mem s → (some ⟨ylo,yhi⟩).mem y → 0 ≤ y →
      ∃ f, o9Field slo shi ylo yhi = some f ∧
           f.Qre.mem (Phi2 (s + y*I)).re ∧
           f.R.mem   (if y = 0 then _ else (Phi2 (s + y*I)).im / y)

together with `shfnIv_mem` for the new leaf.  Neither is proved here, and **no
`sorry` stands in for either**: this package has been sorry-free throughout and
a placeholder would be the first.  They are recorded as obligations O9a/O9b in
`hunts/frontier_math/RETENTION-PROBLEM.md` §4.  Until they exist,
`O9Check2.lean` checks the table and proves nothing about `Dam`.

Generated companion data: `O9Data2.lean` (leaves), `O9Check2.lean` (the walk),
both from `hunts/frontier_math/o9_leaf2d.py`.
-/

namespace Retention

open BandDual

/-! ### The new leaf: `sinh (u/2) / u` -/

/-- The series of `sinh (u/2) / u` in `(u/2)^2`: `sinhL` halved, as `sfnL` is
`sinL` halved. -/
def shfnL : List (ℤ × ℤ) :=
  [(1, 2), (1, 12), (1, 240), (1, 10080), (1, 725760), (1, 79833600), (1, 12454041600),
   (1, 2615348736000), (1, 711374856192000), (1, 243290200817664000),
   (1, 102181884343418880000)]

theorem shfnL_pos : ∀ p ∈ shfnL, 0 < p.2 := by decide

/-- `sh(u) = sinh (u/2) / u`, extended by its removable value `1/2` at `0`. -/
noncomputable def shfunR (u : ℝ) : ℝ := if u = 0 then 1 / 2 else Real.sinh (u / 2) / u

theorem hornerR_shfnL (x : ℝ) : hornerR shfnL x = hornerR sinhL x / 2 := by
  simp only [hornerR, shfnL, sinhL]
  push_cast
  ring

/-- Interval enclosure of `sinh (u/2) / u`, series branch only.

`y ∈ [0,1/2]` throughout O9, so the far branch `sfnIv` needs is never reached
and is deliberately absent: outside `|u| ≤ 2` this returns `none`, which
`o9Cell2` reads as "undecided" rather than as a pass. -/
def shfnIv (u : EIv) : EIv :=
  match u with
  | none => none
  | some a =>
      if -(2 * SO) ≤ a.lo ∧ a.hi ≤ 2 * SO then
        EIv.widen (hornerI shfnL (EIv.sqr (EIv.divInt (some a) 2))) 1
      else none

/-! ### The field on a two-variable cell -/

/-- `R = Qim/y` and `Qre`, together with the cell's `y` range. -/
structure O9F where
  R : EIv
  Qre : EIv
  Y : EIv

/-- The field over `[slo,shi] × [ylo,yhi]`, all scaled by `2^64`.

Mirrors `hunts/frontier_math/o9_leaf2d.field_iv` operation for operation. -/
def o9Field (slo shi ylo yhi : ℤ) : Option O9F :=
  let X : EIv := some ⟨slo, shi⟩
  let Y : EIv := some ⟨ylo, yhi⟩
  let sc := sinCosIv (EIv.divInt X 2)
  let sn := sc.1
  let cs := sc.2
  let shch := sinhCoshSmall (EIv.divInt Y 2)
  let sh := shch.1
  let ch := shch.2
  let shq := shfnIv Y
  let rS := EIv.mul SQ2 SINC
  -- ReN = 2 (C (s sn ch - y cs sh) - r S cs ch)
  let ReN := EIv.mulInt
    (EIv.sub (EIv.mul COSC (EIv.sub (EIv.mul (EIv.mul X sn) ch) (EIv.mul (EIv.mul Y cs) sh)))
             (EIv.mul (EIv.mul rS cs) ch)) 2
  -- Ntil = shq (C s cs + r S sn) + C sn ch
  let Ntil := EIv.add
    (EIv.mul shq (EIv.add (EIv.mul (EIv.mul COSC X) cs) (EIv.mul rS sn)))
    (EIv.mul (EIv.mul COSC sn) ch)
  let ReD := EIv.sub (EIv.sub (EIv.sqr X) (EIv.sqr Y)) (EIv.ofInt 2)
  let ImD := EIv.mulInt (EIv.mul X Y) 2
  let D2 := EIv.add (EIv.sqr ReD) (EIv.sqr ImD)
  -- R = 2 (Ntil ReD - s ReN) / D2
  let R := EIv.div (EIv.mulInt (EIv.sub (EIv.mul Ntil ReD) (EIv.mul X ReN)) 2) D2
  -- Qre = (ReN ReD + 4 s y^2 Ntil) / D2
  let Qre := EIv.div
    (EIv.add (EIv.mul ReN ReD)
             (EIv.mulInt (EIv.mul (EIv.mul X (EIv.sqr Y)) Ntil) 4)) D2
  match R, Qre with
  | some r, some q => some ⟨some r, some q, Y⟩
  | _, _ => none

end Retention
