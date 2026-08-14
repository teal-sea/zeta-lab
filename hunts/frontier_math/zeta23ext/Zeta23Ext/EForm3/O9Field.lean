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

**O9a (`shfnIv_mem`, the new leaf) is proved below.  O9b is not**, and **no
`sorry` stands in for it**: this package has been sorry-free throughout and a
placeholder would be the first.  Both are recorded in
`hunts/frontier_math/RETENTION-PROBLEM.md` §4.  Until O9b exists,
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

/-! `Leaves.sinh_taylor` bounds the remainder by `RB` flat, having spent the
`|t|^22` that `Real.exp_bound` supplies on `|t|^22 ≤ 1`.  That is enough for
`sinhCoshSmall`, but not here: `shfunR` divides by `t`, so the remainder has
to keep a factor of `t` to survive.  `Leaves.sin_taylor` keeps its factor (it
comes through `exp_it_bound`), which is exactly why `sfunR_taylor` works and a
naive copy of it for `sinh` does not.  These two recover the factor. -/

theorem exp_bound_sharp (t : ℝ) (ht : |t| ≤ 1) :
    |Real.exp t - (∑ m ∈ Finset.range 22, t ^ m / (Nat.factorial m : ℝ))|
      ≤ |t| ^ 22 * RB := by
  have h := Real.exp_bound ht (n := 22) (by norm_num)
  refine le_trans h ?_
  have h2 : ((Nat.succ 22 : ℕ) : ℝ) / (((Nat.factorial 22 : ℕ) : ℝ) * (22 : ℕ)) ≤ RB := by
    norm_num [Nat.factorial, RB]
  have hp : (0 : ℝ) ≤ |t| ^ 22 := by positivity
  exact mul_le_mul_of_nonneg_left h2 hp

theorem sinh_taylor_sharp (t : ℝ) (ht : |t| ≤ 1) :
    |Real.sinh t - t * hornerR sinhL (t * t)| ≤ |t| ^ 22 * RB := by
  have h1 := exp_bound_sharp t ht
  rw [exp_partial_eq] at h1
  have h2 : |Real.exp (-t) - (hornerR coshL (t * t) - t * hornerR sinhL (t * t))|
      ≤ |t| ^ 22 * RB := by
    have h := exp_bound_sharp (-t) (by rwa [abs_neg])
    rw [exp_partial_eq'] at h
    simpa using h
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  rw [Real.sinh_eq, abs_le]
  constructor <;> linarith

/-- The Taylor bound for `shfunR`, from `sinh_taylor_sharp` exactly as
`sfunR_taylor` comes from `sin_taylor`. -/
theorem shfunR_taylor (u : ℝ) (hu : |u| ≤ 2) :
    |shfunR u - hornerR shfnL ((u / 2) * (u / 2))| ≤ RB := by
  have hRB := RB_nonneg
  rcases eq_or_ne u 0 with rfl | hne
  · simp only [shfunR, hornerR_shfnL]
    norm_num [hornerR, sinhL]
    exact hRB
  · set t : ℝ := u / 2 with hts
    have htne : t ≠ 0 := by simp [hts]; exact hne
    have hta : |t| ≤ 1 := by
      rw [hts, abs_div]
      rw [div_le_one (by norm_num)]
      simpa using hu
    have h := sinh_taylor_sharp t hta
    have hu2 : u = 2 * t := by rw [hts]; ring
    have hsf : shfunR u = Real.sinh t / (2 * t) := by
      simp only [shfunR, if_neg hne]
      rw [hu2]
      congr 1
      rw [hts]
      ring_nf
    have hpoly : hornerR shfnL (t * t) = hornerR sinhL (t * t) / 2 := hornerR_shfnL _
    rw [hsf, hpoly]
    have hkey : Real.sinh t / (2 * t) - hornerR sinhL (t * t) / 2
        = (Real.sinh t - t * hornerR sinhL (t * t)) / (2 * t) := by
      field_simp
    rw [hkey, abs_div]
    have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
    rw [habs]
    have htpos : 0 < |t| := abs_pos.mpr htne
    rw [div_le_iff₀ (by positivity)]
    have h21 : |t| ^ 22 = |t| ^ 21 * |t| := by ring
    have h21' : |t| ^ 21 ≤ 1 := pow_le_one₀ (abs_nonneg t) hta
    calc |Real.sinh t - t * hornerR sinhL (t * t)| ≤ |t| ^ 22 * RB := h
      _ = (|t| ^ 21 * RB) * |t| := by rw [h21]; ring
      _ ≤ (1 * RB) * (2 * |t|) := by
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h21') hRB) (le_of_lt htpos),
              mul_nonneg hRB (le_of_lt htpos)]
      _ = RB * (2 * |t|) := by ring

/-- **O9a.** `shfnIv` encloses `sinh (u/2) / u`. -/
theorem shfnIv_mem {u : EIv} {v : ℝ} (hu : u.mem v) : (shfnIv u).mem (shfunR v) := by
  cases u with
  | none => trivial
  | some a =>
      simp only [shfnIv]
      split_ifs with h1
      · have hv2 : |v| ≤ 2 := by
          obtain ⟨g1, g2⟩ := h1
          obtain ⟨hl, hh⟩ := hu
          have hS := SOR_pos
          have g1' : ((-(2 * SO) : ℤ) : ℝ) ≤ ((a.lo : ℤ) : ℝ) := by exact_mod_cast g1
          have g2' : ((a.hi : ℤ) : ℝ) ≤ ((2 * SO : ℤ) : ℝ) := by exact_mod_cast g2
          push_cast at g1' g2'
          rw [abs_le]
          constructor <;> nlinarith
        have hhalf : EIv.mem (EIv.divInt (some a) 2) (v / ((2 : ℤ) : ℝ)) :=
          EIv.divInt_mem (by norm_num) hu
        have hsq : EIv.mem (EIv.sqr (EIv.divInt (some a) 2))
            ((v / ((2 : ℤ) : ℝ)) * (v / ((2 : ℤ) : ℝ))) := EIv.sqr_mem hhalf
        have hh := hornerI_mem shfnL shfnL_pos hsq
        refine widen_of_abs hh ?_
        have := shfunR_taylor v hv2
        have heq : (v / ((2 : ℤ) : ℝ)) * (v / ((2 : ℤ) : ℝ)) = (v / 2) * (v / 2) := by
          push_cast; ring
        rw [heq]
        exact this
      · trivial

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
