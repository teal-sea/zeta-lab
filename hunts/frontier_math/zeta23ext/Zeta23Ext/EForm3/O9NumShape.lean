import Zeta23Ext.EForm3.O9Assemble
import Zeta23Ext.EForm3.O9Data2

/-!
# What the numerator fields actually enclose

`O9Num.reNum_mem` and `O9Num.imNumOverY_mem` conclude that two `boxParts`
fields enclose long trigonometric expressions. Those expressions are the
*shapes the interval arithmetic computes*: they are read off `boxParts`
operation for operation, and they leave the three constant leaves abstract
(`ss`, `cc`, `sc`, any reals the constant enclosures happen to contain). They
are not written as `Re num` and `Im num / y` for the numerator

    num z = 2 · (z · sin(z/2) · cos(√2/2) − √2 · cos(z/2) · sin(√2/2))

of `BandDual.Phi2_closed`. This file settles whether the two agree.

The answer is not the same on the two sides, and the difference is the whole
content:

* **`reNum` is an unconditional identification.** With the three constants
  instantiated at their true values (`SQ2_mem`, `SINC_mem`, `COSC_mem`) the
  computed shape *is* `Re num` at every `(s, y)`, `y = 0` included. No
  hypothesis is needed beyond the box memberships and the `|y/2| ≤ 1` the
  small-range leaves already carry.
* **`imNumOverY` is an identification only for `y ≠ 0`.** The field carries
  `shcSmall`, whose value at `0` is the removable limit `1` rather than a
  quotient, so what `imNumOverY` encloses is the *continuous extension* of
  `Im num / y`. For `y ≠ 0` the extension and the quotient agree and
  `imOverYShape_eq_im_div` proves it. At `y = 0` they do not: `Im num = 0`
  there, so `Im num / y` is `0` by Lean's division convention, while the
  enclosed real is the limit — and `imOverYShape_pi_zero_pos` exhibits a point
  where that limit is positive. `imOverYShape_ne_im_div_at_zero` is the
  mismatch, stated as a mismatch rather than hedged.

That asymmetry is a feature of the design and not a defect: the removable
branch exists precisely so that `y = 0` is an ordinary point, and it can only
be an ordinary point by enclosing something other than a quotient by `y`
there. What the file adds is that the "something other" is named and pinned,
rather than left as whatever the arithmetic happened to produce.

## Consequences for the dead-weight seam lemmas

`O9Seam.r_comp_mem` and `Retention.rIv_mem` were true, zero-sorry and vacuous
at every box in `o9boxes` (found by run 4df2ee65: they asked `denAbs2` to
enclose `c*c + dOverY*dOverY` where it encloses `c*c + d*d`, `d = dOverY·y`).
Nothing in this file rescued them, and nothing in this file needs them:
`rIv_mem_phi2` below reaches `Phi2` through `r_comp_mem'` and `rIv_mem_box`,
and `qreIv_mem_phi2` reaches it through `qre_comp_mem` and `qreIv_mem_box`.
They were dead weight in the strict sense — nothing downstream was stated in
terms of them — and both were **retired on 2026-08-18** at no reproof cost.

## Instantiability

A lemma that compiles is not thereby a lemma with content, which is exactly
the lesson the retired `r_comp_mem` taught. Every identification below is therefore also
instantiated at a *recorded* box: the first row of `Retention.o9boxes`
(`box0_in_table`), at a concrete interior point, with the memberships
discharged by `norm_num` rather than assumed.

Nothing here is evidence for or against the Riemann hypothesis.
-/

namespace Retention

open BandDual

/-! ## The mathematical numerator -/

/-- The numerator of `BandDual.Phi2_closed`, as a complex function. -/
noncomputable def numC (z : ℂ) : ℂ :=
  2 * (z * Complex.sin (z / 2) * ((Real.cos (Real.sqrt 2 / 2) : ℝ) : ℂ)
    - ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (z / 2)
      * ((Real.sin (Real.sqrt 2 / 2) : ℝ) : ℂ))

/-- `Phi2` is `numC` over `z² − 2`, which is what makes `numC` the right
object to identify the fields against. -/
theorem phi2_eq_numC_div (z : ℂ) (hz : z ^ 2 ≠ 2) :
    Phi2 z = numC z / (z ^ 2 - 2) := by
  rw [numC]
  exact Phi2_closed z hz

/-- The box point, in the form `Phi.lean` uses. -/
theorem half_pt (s y : ℝ) :
    ((s : ℂ) + (y : ℂ) * Complex.I) / 2
      = ((s / ((2:ℤ):ℝ) : ℝ) : ℂ) + ((y / ((2:ℤ):ℝ) : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- **`Re num`, componentwise** — and this is exactly the shape `reNum_mem`
encloses, once its three abstract constants are the true ones. -/
theorem numC_re_eq (s y : ℝ) :
    (numC ((s : ℂ) + (y : ℂ) * Complex.I)).re
      = ((s * Real.sin (s / ((2:ℤ):ℝ)) * Real.cosh (y / ((2:ℤ):ℝ))
            - y * Real.cos (s / ((2:ℤ):ℝ)) * Real.sinh (y / ((2:ℤ):ℝ)))
              * Real.cos (Real.sqrt 2 / 2)
          - Real.cos (s / ((2:ℤ):ℝ)) * Real.cosh (y / ((2:ℤ):ℝ))
              * Real.sin (Real.sqrt 2 / 2) * Real.sqrt 2)
        * ((2:ℤ):ℝ) := by
  rw [numC, half_pt, Complex.sin_add_mul_I, Complex.cos_add_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **`Im num`, componentwise.** -/
theorem numC_im_eq (s y : ℝ) :
    (numC ((s : ℂ) + (y : ℂ) * Complex.I)).im
      = ((s * Real.cos (s / ((2:ℤ):ℝ)) * Real.sinh (y / ((2:ℤ):ℝ))
            + y * Real.sin (s / ((2:ℤ):ℝ)) * Real.cosh (y / ((2:ℤ):ℝ)))
              * Real.cos (Real.sqrt 2 / 2)
          + Real.sin (s / ((2:ℤ):ℝ)) * Real.sinh (y / ((2:ℤ):ℝ))
              * Real.sin (Real.sqrt 2 / 2) * Real.sqrt 2)
        * ((2:ℤ):ℝ) := by
  rw [numC, half_pt, Complex.sin_add_mul_I, Complex.cos_add_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-! ## The real part: an unconditional identification -/

/-- **`reNum` encloses `Re num`.**

The hypotheses are the box memberships and the small-range bound the leaves
already require. There is no `y ≠ 0`: the real part never divides by `y` on
either side, so the identification holds at `y = 0` too. -/
theorem reNum_mem_numC {sLo sHi yLo yHi : ℤ} {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) :
    EIv.mem (boxParts sLo sHi yLo yHi).reNum
      ((numC ((s : ℂ) + (y : ℂ) * Complex.I)).re) := by
  rw [numC_re_eq]
  exact reNum_mem hs hy hy1 SINC_mem COSC_mem SQ2_mem

/-! ## The removable branch: an identification away from `y = 0` -/

/-- The real that `imNumOverY_mem` pins, named. This is the shape the interval
arithmetic computes: the `if` is `shcSmall`'s removable branch, whose value at
`0` is the limit `1` and not a quotient. -/
noncomputable def imOverYShape (s y : ℝ) : ℝ :=
  ((s * Real.cos (s / ((2:ℤ):ℝ))
      * ((if y / ((2:ℤ):ℝ) = 0 then 1
          else Real.sinh (y / ((2:ℤ):ℝ)) / (y / ((2:ℤ):ℝ))) / ((2:ℤ):ℝ))
    + Real.sin (s / ((2:ℤ):ℝ)) * Real.cosh (y / ((2:ℤ):ℝ)))
      * Real.cos (Real.sqrt 2 / 2)
  - -(Real.sin (s / ((2:ℤ):ℝ))
      * ((if y / ((2:ℤ):ℝ) = 0 then 1
          else Real.sinh (y / ((2:ℤ):ℝ)) / (y / ((2:ℤ):ℝ))) / ((2:ℤ):ℝ)))
      * Real.sin (Real.sqrt 2 / 2) * Real.sqrt 2)
    * ((2:ℤ):ℝ)

/-- **`imNumOverY` encloses `imOverYShape`** — the shape, unconditionally. -/
theorem imNumOverY_mem_shape {sLo sHi yLo yHi : ℤ} {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) :
    EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY (imOverYShape s y) := by
  rw [imOverYShape]
  exact imNumOverY_mem hs hy hy1 SINC_mem COSC_mem SQ2_mem

/-- **The shape is `Im num / y`, for `y ≠ 0`.**

The single step that needs the hypothesis is the `if`: away from zero the
removable branch is `sinh(y/2)/(y/2)`, and halving it gives `sinh(y/2)/y`,
which is what dividing `Im num` by `y` produces. -/
theorem imOverYShape_eq_im_div (s y : ℝ) (hy : y ≠ 0) :
    imOverYShape s y = (numC ((s : ℂ) + (y : ℂ) * Complex.I)).im / y := by
  have hy2 : y / ((2:ℤ):ℝ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff]
    push_neg
    exact ⟨hy, by norm_num⟩
  rw [numC_im_eq, imOverYShape, if_neg hy2]
  field_simp
  ring

/-- **`imNumOverY` encloses `Im num / y`, for `y ≠ 0`.** -/
theorem imNumOverY_mem_numC {sLo sHi yLo yHi : ℤ} {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hy0 : y ≠ 0) :
    EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY
      ((numC ((s : ℂ) + (y : ℂ) * Complex.I)).im / y) := by
  rw [← imOverYShape_eq_im_div s y hy0]
  exact imNumOverY_mem_shape hs hy hy1

/-! ## Why `y ≠ 0` cannot be dropped

Not "the proof needs it" — the statement is false without it, and the rest of
this section is the witness. -/

/-- `Im num` vanishes on the real axis. -/
theorem numC_im_zero (s : ℝ) :
    (numC ((s : ℂ) + ((0:ℝ) : ℂ) * Complex.I)).im = 0 := by
  rw [numC_im_eq]
  simp

/-- The shape at `y = 0` is the removable limit, written out. -/
theorem imOverYShape_zero (s : ℝ) :
    imOverYShape s 0
      = (s * Real.cos (s / ((2:ℤ):ℝ)) / ((2:ℤ):ℝ) + Real.sin (s / ((2:ℤ):ℝ)))
          * Real.cos (Real.sqrt 2 / 2) * ((2:ℤ):ℝ)
        + Real.sin (s / ((2:ℤ):ℝ)) * Real.sin (Real.sqrt 2 / 2) * Real.sqrt 2 := by
  rw [imOverYShape]
  norm_num
  ring

/-- `cos(√2/2) > 0`. -/
theorem cos_half_sqrt2_pos : 0 < Real.cos (Real.sqrt 2 / 2) := by
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · nlinarith [Real.pi_gt_three, sqrt_two_lt, Real.sqrt_nonneg 2]
  · nlinarith [Real.pi_gt_three, sqrt_two_lt, Real.sqrt_nonneg 2]

/-- `sin(√2/2) > 0`. -/
theorem sin_half_sqrt2_pos : 0 < Real.sin (Real.sqrt 2 / 2) := by
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · nlinarith [sqrt_two_gt]
  · nlinarith [Real.pi_gt_three, sqrt_two_lt]

/-- **The removable limit is not zero.** At `s = π` the shape at `y = 0` is
`2·cos(√2/2) + √2·sin(√2/2)`, which is positive. -/
theorem imOverYShape_pi_zero_pos : 0 < imOverYShape Real.pi 0 := by
  have hcos : Real.cos (Real.pi / ((2:ℤ):ℝ)) = 0 := by
    norm_num [Real.cos_pi_div_two]
  have hsin : Real.sin (Real.pi / ((2:ℤ):ℝ)) = 1 := by
    norm_num [Real.sin_pi_div_two]
  rw [imOverYShape_zero, hcos, hsin]
  have h1 := cos_half_sqrt2_pos
  have h2 := sin_half_sqrt2_pos
  have h3 : (0:ℝ) < Real.sqrt 2 := by nlinarith [sqrt_two_gt]
  norm_num
  nlinarith

/-- **The identification fails at `y = 0`**, and this is the witness.

`Im num / 0` is `0` — `Im num` vanishes on the real axis and Lean's division
sends `0/0` to `0` — while `imNumOverY` encloses the removable limit, which
`imOverYShape_pi_zero_pos` shows is not `0` at `s = π`. So `y ≠ 0` is not an
artefact of the proof of `imOverYShape_eq_im_div`; it is the exact hypothesis
the statement needs. -/
theorem imOverYShape_ne_im_div_at_zero :
    imOverYShape Real.pi 0
      ≠ (numC ((Real.pi : ℂ) + ((0:ℝ) : ℂ) * Complex.I)).im / 0 := by
  rw [numC_im_zero, zero_div]
  exact ne_of_gt imOverYShape_pi_zero_pos

/-! ## What the two compositions enclose

With both numerator components identified, the compositions can be read back
against `Phi2` itself rather than against abstract components. Both go through
the corrected seam lemmas, which is why the retirement cost nothing. -/

/-- The denominator's squared modulus is positive off the real axis. -/
theorem denAbs2_pos {s y : ℝ} (hy : y ≠ 0) :
    0 < (s * s - y * y - ((2:ℤ):ℝ)) ^ 2 + (s * ((2:ℤ):ℝ) * y) ^ 2 := by
  have sq_pos : ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2 := by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · nlinarith
    · nlinarith
  rcases eq_or_ne (s * s - y * y - ((2:ℤ):ℝ)) 0 with h | h
  · have hs : s ≠ 0 := by
      intro hs0
      rw [hs0] at h
      push_cast at h
      nlinarith [mul_self_nonneg y]
    have hd : s * ((2:ℤ):ℝ) * y ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨hs, by norm_num⟩, hy⟩
    have := sq_pos _ hd
    nlinarith [sq_nonneg (s * s - y * y - ((2:ℤ):ℝ))]
  · have := sq_pos _ h
    nlinarith [sq_nonneg (s * ((2:ℤ):ℝ) * y)]

/-- **`qreIv` encloses `Re Phi2 (s + i y)`.** -/
theorem qreIv_mem_phi2 {sLo sHi yLo yHi : ℤ} {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hy0 : y ≠ 0) :
    EIv.mem (qreIv sLo sHi yLo yHi)
      ((Phi2 ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)).re) := by
  have hpos := denAbs2_pos (s := s) hy0
  have hne : ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I) ^ 2 ≠ 2 :=
    sq_ne_two_of_im_ne_zero s y hy0
  have hbox := qreIv_mem_box (s := s) (y := y) hs hy
    (reNum_mem_numC hs hy hy1) (imNumOverY_mem_shape hs hy hy1)
  rw [phi2_eq_numC_div _ hne]
  have hz : ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I) ^ 2 - 2
      = (⟨s * s - y * y - ((2:ℤ):ℝ), s * ((2:ℤ):ℝ) * y⟩ : ℂ) := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  have hn : numC ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)
      = (⟨(numC ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)).re,
          (numC ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)).im⟩ : ℂ) := rfl
  rw [hn, hz, O9Real.re_div_eq _ _ _ _ hpos]
  have hsplit : (numC ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)).im
      = imOverYShape s y * y := by
    rw [imOverYShape_eq_im_div s y hy0]
    field_simp
  rw [hsplit]
  convert hbox using 2 <;> ring

/-- **`rIv` encloses `−Im Phi2 (s + i y) / y`** — the removable branch `R`. -/
theorem rIv_mem_phi2 {sLo sHi yLo yHi : ℤ} {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hy0 : y ≠ 0) :
    EIv.mem (rIv sLo sHi yLo yHi)
      (-((Phi2 ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)).im / y)) := by
  have hpos := denAbs2_pos (s := s) hy0
  have hne : ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I) ^ 2 ≠ 2 :=
    sq_ne_two_of_im_ne_zero s y hy0
  have hbox := rIv_mem_box (s := s) (y := y) hs hy
    (reNum_mem_numC hs hy hy1) (imNumOverY_mem_shape hs hy hy1)
  rw [phi2_eq_numC_div _ hne]
  have hz : ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I) ^ 2 - 2
      = (⟨s * s - y * y - ((2:ℤ):ℝ), s * ((2:ℤ):ℝ) * y⟩ : ℂ) := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  have hsplit : (numC ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)).im
      = imOverYShape s y * y := by
    rw [imOverYShape_eq_im_div s y hy0]
    field_simp
  have hn : numC ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)
      = (⟨(numC ((s : ℂ) + ((y:ℝ) : ℂ) * Complex.I)).re, imOverYShape s y * y⟩ : ℂ) := by
    rw [← hsplit]
  have hpos' : 0 < (s * s - y * y - ((2:ℤ):ℝ)) ^ 2 + (s * ((2:ℤ):ℝ) * y) ^ 2 := hpos
  rw [hn, hz]
  rw [O9Real.im_div_over_y _ _ _ _ _ hy0 hpos']
  convert hbox using 3 <;> ring

/-! ## Instantiation at a recorded box

The first row of `o9boxes` is `s ∈ [5.5999…, 5.8300…]`, `y ∈ [0, 1/4]`, and it
is a `mode = 2` box. The point `(23/4, 1/8)` is interior to it. -/

/-- The box below is the first row of the recorded table, not an invented one. -/
theorem box0_in_table :
    (⟨103301766812773489049, 107547284961337742355, 0, 4611686018427387904, 0, 2⟩ :
      O9Box) ∈ o9boxes := by
  unfold o9boxes
  exact List.Mem.head _

theorem s_in_box0 :
    EIv.mem (some ⟨103301766812773489049, 107547284961337742355⟩) (23/4 : ℝ) := by
  constructor <;> norm_num [Iv.mem, SO]

theorem y_in_box0 :
    EIv.mem (some ⟨(0:ℤ), 4611686018427387904⟩) (1/8 : ℝ) := by
  constructor <;> norm_num [Iv.mem, SO]

theorem y_small_box0 : |(1/8 : ℝ) / ((2:ℤ):ℝ)| ≤ 1 := by
  rw [abs_le]
  constructor <;> norm_num

/-- **`reNum` encloses `Re num` at a recorded box**, every hypothesis
discharged. -/
theorem reNum_mem_numC_box0 :
    EIv.mem (boxParts 103301766812773489049 107547284961337742355
        0 4611686018427387904).reNum
      ((numC (((23/4 : ℝ) : ℂ) + (((1/8 : ℝ)) : ℂ) * Complex.I)).re) :=
  reNum_mem_numC s_in_box0 y_in_box0 y_small_box0

/-- **`imNumOverY` encloses `Im num / y` at a recorded box**, every hypothesis
discharged. -/
theorem imNumOverY_mem_numC_box0 :
    EIv.mem (boxParts 103301766812773489049 107547284961337742355
        0 4611686018427387904).imNumOverY
      ((numC (((23/4 : ℝ) : ℂ) + (((1/8 : ℝ)) : ℂ) * Complex.I)).im / (1/8 : ℝ)) :=
  imNumOverY_mem_numC s_in_box0 y_in_box0 y_small_box0 (by norm_num)

/-- **`rIv` encloses the removable branch of `Phi2` at a recorded box.** -/
theorem rIv_mem_phi2_box0 :
    EIv.mem (rIv 103301766812773489049 107547284961337742355
        0 4611686018427387904)
      (-((Phi2 (((23/4 : ℝ) : ℂ) + (((1/8 : ℝ)) : ℂ) * Complex.I)).im / (1/8 : ℝ))) :=
  rIv_mem_phi2 s_in_box0 y_in_box0 y_small_box0 (by norm_num)

/-- **`qreIv` encloses `Re Phi2` at a recorded box.** -/
theorem qreIv_mem_phi2_box0 :
    EIv.mem (qreIv 103301766812773489049 107547284961337742355
        0 4611686018427387904)
      ((Phi2 (((23/4 : ℝ) : ℂ) + (((1/8 : ℝ)) : ℂ) * Complex.I)).re) :=
  qreIv_mem_phi2 s_in_box0 y_in_box0 y_small_box0 (by norm_num)

end Retention

#print axioms Retention.phi2_eq_numC_div
#print axioms Retention.numC_re_eq
#print axioms Retention.numC_im_eq
#print axioms Retention.reNum_mem_numC
#print axioms Retention.imNumOverY_mem_shape
#print axioms Retention.imOverYShape_eq_im_div
#print axioms Retention.imNumOverY_mem_numC
#print axioms Retention.numC_im_zero
#print axioms Retention.imOverYShape_pi_zero_pos
#print axioms Retention.imOverYShape_ne_im_div_at_zero
#print axioms Retention.qreIv_mem_phi2
#print axioms Retention.rIv_mem_phi2
#print axioms Retention.box0_in_table
#print axioms Retention.reNum_mem_numC_box0
#print axioms Retention.imNumOverY_mem_numC_box0
#print axioms Retention.rIv_mem_phi2_box0
#print axioms Retention.qreIv_mem_phi2_box0
