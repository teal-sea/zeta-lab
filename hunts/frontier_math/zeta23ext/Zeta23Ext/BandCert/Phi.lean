import RequestProject.Leaves

/-!
# The paper field `Phi2`, its closed form, and the interval evaluators
-/

namespace BandDual

open Complex

/-! ### Complex intervals -/

/-- A complex interval: an enclosure of the real and of the imaginary part. -/
abbrev CIv := EIv × EIv

namespace CIv

def mem (a : CIv) (z : ℂ) : Prop := a.1.mem z.re ∧ a.2.mem z.im

def add (a b : CIv) : CIv := (EIv.add a.1 b.1, EIv.add a.2 b.2)
def sub (a b : CIv) : CIv := (EIv.sub a.1 b.1, EIv.sub a.2 b.2)
def mul (a b : CIv) : CIv :=
  (EIv.sub (EIv.mul a.1 b.1) (EIv.mul a.2 b.2), EIv.add (EIv.mul a.1 b.2) (EIv.mul a.2 b.1))
def mulInt (a : CIv) (k : ℤ) : CIv := (EIv.mulInt a.1 k, EIv.mulInt a.2 k)
/-- Multiplication by a real interval. -/
def mulR (a : CIv) (r : EIv) : CIv := (EIv.mul a.1 r, EIv.mul a.2 r)
def div (a b : CIv) : CIv :=
  let n2 := EIv.add (EIv.sqr b.1) (EIv.sqr b.2)
  (EIv.div (EIv.add (EIv.mul a.1 b.1) (EIv.mul a.2 b.2)) n2,
   EIv.div (EIv.sub (EIv.mul a.2 b.1) (EIv.mul a.1 b.2)) n2)
/-- A real interval seen as a complex one. -/
def ofR (a : EIv) : CIv := (a, EIv.pt 0)

theorem add_mem {a b : CIv} {z w : ℂ} (ha : a.mem z) (hb : b.mem w) : (add a b).mem (z + w) :=
  ⟨by simpa [Complex.add_re] using EIv.add_mem ha.1 hb.1,
   by simpa [Complex.add_im] using EIv.add_mem ha.2 hb.2⟩

theorem sub_mem {a b : CIv} {z w : ℂ} (ha : a.mem z) (hb : b.mem w) : (sub a b).mem (z - w) :=
  ⟨by simpa [Complex.sub_re] using EIv.sub_mem ha.1 hb.1,
   by simpa [Complex.sub_im] using EIv.sub_mem ha.2 hb.2⟩

theorem mul_mem {a b : CIv} {z w : ℂ} (ha : a.mem z) (hb : b.mem w) : (mul a b).mem (z * w) :=
  ⟨by simpa [Complex.mul_re] using EIv.sub_mem (EIv.mul_mem ha.1 hb.1) (EIv.mul_mem ha.2 hb.2),
   by simpa [Complex.mul_im] using EIv.add_mem (EIv.mul_mem ha.1 hb.2) (EIv.mul_mem ha.2 hb.1)⟩

theorem mulInt_mem {a : CIv} {z : ℂ} {k : ℤ} (ha : a.mem z) : (mulInt a k).mem (z * (k:ℂ)) := by
  constructor
  · have := EIv.mulInt_mem (k := k) ha.1
    simpa [Complex.mul_re] using this
  · have := EIv.mulInt_mem (k := k) ha.2
    simpa [Complex.mul_im] using this

theorem mulR_mem {a : CIv} {r : EIv} {z : ℂ} {x : ℝ} (ha : a.mem z) (hr : r.mem x) :
    (mulR a r).mem (z * (x:ℂ)) := by
  constructor
  · have := EIv.mul_mem ha.1 hr
    simpa [Complex.mul_re] using this
  · have := EIv.mul_mem ha.2 hr
    simpa [Complex.mul_im] using this

theorem div_mem {a b : CIv} {z w : ℂ} (ha : a.mem z) (hb : b.mem w) : (div a b).mem (z / w) := by
  have hn2 : (EIv.add (EIv.sqr b.1) (EIv.sqr b.2)).mem (w.re * w.re + w.im * w.im) :=
    EIv.add_mem (EIv.sqr_mem hb.1) (EIv.sqr_mem hb.2)
  constructor
  · have h := EIv.div_mem (EIv.add_mem (EIv.mul_mem ha.1 hb.1) (EIv.mul_mem ha.2 hb.2)) hn2
    have heq : (z.re * w.re + z.im * w.im) / (w.re * w.re + w.im * w.im) = (z / w).re := by
      rw [Complex.div_re, Complex.normSq_apply, ← add_div]
    rwa [heq] at h
  · have h := EIv.div_mem (EIv.sub_mem (EIv.mul_mem ha.2 hb.1) (EIv.mul_mem ha.1 hb.2)) hn2
    have heq : (z.im * w.re - z.re * w.im) / (w.re * w.re + w.im * w.im) = (z / w).im := by
      rw [Complex.div_im, Complex.normSq_apply, div_sub_div_same]
    rwa [heq] at h

theorem ofR_mem {a : EIv} {x : ℝ} (ha : a.mem x) : (ofR a).mem ((x : ℂ)) := by
  refine ⟨by simpa using ha, ?_⟩
  have := EIv.pt_mem 0
  simpa using this

end CIv

/-! ### The constants -/

theorem sqrt_two_lt : Real.sqrt 2 < 1.5 := by
  nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]

theorem sqrt_two_gt : 1.4 < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]

/-- `√2 / 2`. -/
def HSQ2 : EIv := EIv.divInt SQ2 2

theorem HSQ2_mem : HSQ2.mem (Real.sqrt 2 / 2) := by
  have h := EIv.divInt_mem (d := 2) (by norm_num) SQ2_mem
  have : Real.sqrt 2 / ((2:ℤ):ℝ) = Real.sqrt 2 / 2 := by norm_num
  rwa [this] at h

theorem half_sqrt2_le_one : |Real.sqrt 2 / 2| ≤ 1 := by
  rw [abs_le]
  constructor <;> nlinarith [sqrt_two_lt, Real.sqrt_nonneg 2]

/-- `sin (√2/2)`. -/
def SINC : EIv := (sinCosSmall HSQ2).1
/-- `cos (√2/2)`. -/
def COSC : EIv := (sinCosSmall HSQ2).2

theorem SINC_mem : SINC.mem (Real.sin (Real.sqrt 2 / 2)) :=
  (sinCosSmall_mem HSQ2_mem half_sqrt2_le_one).1

theorem COSC_mem : COSC.mem (Real.cos (Real.sqrt 2 / 2)) :=
  (sinCosSmall_mem HSQ2_mem half_sqrt2_le_one).2

/-! ### The paper field -/

/-- `s(u) = sin(u/2)/u`, with its removable value `1/2` at `u = 0`. -/
noncomputable def sfunC (u : ℂ) : ℂ := if u = 0 then 1/2 else Complex.sin (u/2) / u

/-- `Phi2 z = s(z + √2) + s(z - √2)`. -/
noncomputable def Phi2 (z : ℂ) : ℂ := sfunC (z + (Real.sqrt 2 : ℝ)) + sfunC (z - (Real.sqrt 2 : ℝ))

/-- `A = Phi2 0`. -/
noncomputable def Acst : ℝ := (Phi2 0).re

/-- `f = 4 (Im² - Re²) Phi2(g + iy) / A²`, the quantity whose positivity marks a band. -/
noncomputable def fBig (y g : ℝ) : ℝ :=
  4 * (((Phi2 ((g : ℂ) + (y : ℝ) * I)).im) ^ 2 - ((Phi2 ((g : ℂ) + (y : ℝ) * I)).re) ^ 2)
    / Acst ^ 2

/-- `ω(r) = Re Phi2(r) / A` for real `r`. -/
noncomputable def omg (r : ℝ) : ℝ := (Phi2 (r : ℂ)).re / Acst

/-- `σ₂(y) = (Phi2(2iy) - A)/(2A)`. -/
noncomputable def sigma2 (y : ℝ) : ℝ := ((Phi2 (2 * (y:ℝ) * I)).re - Acst) / (2 * Acst)

/-- `slack(y) = 8 σ₂ + 8 σ₂²`. -/
noncomputable def slackF (y : ℝ) : ℝ := 8 * sigma2 y + 8 * (sigma2 y) ^ 2

/-! ### The closed form -/

theorem Phi2_closed (z : ℂ) (hz : z ^ 2 ≠ 2) :
    Phi2 z = 2 * (z * Complex.sin (z / 2) * ((Real.cos (Real.sqrt 2 / 2) : ℝ) : ℂ)
      - ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (z / 2)
        * ((Real.sin (Real.sqrt 2 / 2) : ℝ) : ℂ)) / (z ^ 2 - 2) := by
  set w : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hw
  have hw2 : w ^ 2 = 2 := by
    rw [hw, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hprod : (z + w) * (z - w) = z ^ 2 - 2 := by
    have : (z + w) * (z - w) = z ^ 2 - w ^ 2 := by ring
    rw [this, hw2]
  have hne : z ^ 2 - 2 ≠ 0 := sub_ne_zero.mpr hz
  have hp : z + w ≠ 0 := by
    intro h
    apply hne
    rw [← hprod, h, zero_mul]
  have hm : z - w ≠ 0 := by
    intro h
    apply hne
    rw [← hprod, h, mul_zero]
  have hhalf : ((Real.cos (Real.sqrt 2 / 2) : ℝ) : ℂ) = Complex.cos (w / 2) := by
    rw [hw, Complex.ofReal_cos]
    congr 1
    push_cast
    ring
  have hhalf' : ((Real.sin (Real.sqrt 2 / 2) : ℝ) : ℂ) = Complex.sin (w / 2) := by
    rw [hw, Complex.ofReal_sin]
    congr 1
    push_cast
    ring
  rw [Phi2, sfunC, sfunC, if_neg hp, if_neg hm, hhalf, hhalf']
  rw [show (z + w) / 2 = z / 2 + w / 2 by ring, show (z - w) / 2 = z / 2 - w / 2 by ring]
  rw [Complex.sin_add, Complex.sin_sub]
  rw [div_add_div _ _ hp hm, hprod]
  congr 1
  ring

theorem sq_ne_two_of_im_ne_zero (g y : ℝ) (hy : y ≠ 0) : ((g : ℂ) + (y : ℝ) * I) ^ 2 ≠ 2 := by
  intro h
  have him : (((g : ℂ) + (y : ℝ) * I) ^ 2).im = (2:ℂ).im := by rw [h]
  have hre : (((g : ℂ) + (y : ℝ) * I) ^ 2).re = (2:ℂ).re := by rw [h]
  simp [pow_two, Complex.mul_im, Complex.mul_re] at him hre
  rcases mul_eq_zero.mp (by nlinarith : g * y = 0) with h1 | h1
  · rw [h1] at hre; nlinarith
  · exact hy h1

/-! ### The evaluators -/

/-- `sin` and `cos` of `x + i b` where `SH, CH` enclose `sinh b`, `cosh b`. -/
def sinCosC (X SH CH : EIv) : CIv × CIv :=
  let sc := sinCosIv X
  ((EIv.mul sc.1 CH, EIv.mul sc.2 SH), (EIv.mul sc.2 CH, EIv.neg (EIv.mul sc.1 SH)))

theorem sinCosC_mem {X SH CH : EIv} {a b : ℝ} (hX : X.mem a) (hSH : SH.mem (Real.sinh b))
    (hCH : CH.mem (Real.cosh b)) :
    (sinCosC X SH CH).1.mem (Complex.sin ((a : ℂ) + (b : ℝ) * I)) ∧
    (sinCosC X SH CH).2.mem (Complex.cos ((a : ℂ) + (b : ℝ) * I)) := by
  have hs := (sinCosIv_mem hX).1
  have hc := (sinCosIv_mem hX).2
  have hre1 : (Complex.sin ((a : ℂ) + (b : ℝ) * I)).re = Real.sin a * Real.cosh b := by
    rw [Complex.sin_add_mul_I]
    simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
      Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]
  have him1 : (Complex.sin ((a : ℂ) + (b : ℝ) * I)).im = Real.cos a * Real.sinh b := by
    rw [Complex.sin_add_mul_I]
    simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
      Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]
  have hre2 : (Complex.cos ((a : ℂ) + (b : ℝ) * I)).re = Real.cos a * Real.cosh b := by
    rw [Complex.cos_add_mul_I]
    simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
      Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]
  have him2 : (Complex.cos ((a : ℂ) + (b : ℝ) * I)).im = -(Real.sin a * Real.sinh b) := by
    rw [Complex.cos_add_mul_I]
    simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
      Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hre1]; exact EIv.mul_mem hs hCH
  · rw [him1]; exact EIv.mul_mem hc hSH
  · rw [hre2]; exact EIv.mul_mem hc hCH
  · rw [him2]; exact EIv.neg_mem (EIv.mul_mem hs hSH)

/-- Enclosure of `Phi2 (g + i y)` from enclosures `X ∋ g`, `Y ∋ y`,
`SH ∋ sinh (y/2)`, `CH ∋ cosh (y/2)`. -/
def phiC (X Y SH CH : EIv) : CIv :=
  let z : CIv := (X, Y)
  let sc := sinCosC (EIv.divInt X 2) SH CH
  let num := CIv.mulInt (CIv.sub (CIv.mulR (CIv.mul z sc.1) COSC)
      (CIv.mulR (CIv.mulR sc.2 SINC) SQ2)) 2
  let den := CIv.sub (CIv.mul z z) (CIv.ofR (EIv.ofInt 2))
  CIv.div num den

theorem phiC_mem {X Y SH CH : EIv} {g y : ℝ} (hX : X.mem g) (hY : Y.mem y) (hy : y ≠ 0)
    (hSH : SH.mem (Real.sinh (y/2))) (hCH : CH.mem (Real.cosh (y/2))) :
    (phiC X Y SH CH).mem (Phi2 ((g : ℂ) + (y : ℝ) * I)) := by
  set z : ℂ := (g : ℂ) + (y : ℝ) * I with hz
  have hzmem : CIv.mem (X, Y) z := by
    constructor
    · simpa [hz] using hX
    · simpa [hz] using hY
  have hhalf : (EIv.divInt X 2).mem (g / ((2:ℤ):ℝ)) := EIv.divInt_mem (by norm_num) hX
  have hzh : z / 2 = ((g / ((2:ℤ):ℝ) : ℝ) : ℂ) + ((y/2 : ℝ) : ℝ) * I := by
    rw [hz]; push_cast; ring
  have hsc := sinCosC_mem hhalf hSH hCH
  rw [← hzh] at hsc
  have hnum : CIv.mem (CIv.mulInt (CIv.sub (CIv.mulR (CIv.mul (X, Y) (sinCosC (EIv.divInt X 2) SH CH).1) COSC)
      (CIv.mulR (CIv.mulR (sinCosC (EIv.divInt X 2) SH CH).2 SINC) SQ2)) 2)
      ((z * Complex.sin (z/2) * ((Real.cos (Real.sqrt 2/2) : ℝ) : ℂ)
        - ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (z/2) * ((Real.sin (Real.sqrt 2/2):ℝ):ℂ))
        * ((2:ℤ):ℂ)) := by
    refine CIv.mulInt_mem (CIv.sub_mem ?_ ?_)
    · exact CIv.mulR_mem (CIv.mul_mem hzmem hsc.1) COSC_mem
    · have h1 := CIv.mulR_mem (CIv.mulR_mem hsc.2 SINC_mem) SQ2_mem
      have heq : Complex.cos (z/2) * ((Real.sin (Real.sqrt 2/2):ℝ):ℂ) * ((Real.sqrt 2:ℝ):ℂ)
          = ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (z/2) * ((Real.sin (Real.sqrt 2/2):ℝ):ℂ) := by
        ring
      rwa [heq] at h1
  have hden : CIv.mem (CIv.sub (CIv.mul (X, Y) (X, Y)) (CIv.ofR (EIv.ofInt 2))) (z * z - ((2:ℝ):ℂ)) :=
    CIv.sub_mem (CIv.mul_mem hzmem hzmem) (CIv.ofR_mem (EIv.ofInt_mem 2))
  have hdiv := CIv.div_mem hnum hden
  have hclosed : Phi2 z = ((z * Complex.sin (z/2) * ((Real.cos (Real.sqrt 2/2) : ℝ) : ℂ)
        - ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (z/2) * ((Real.sin (Real.sqrt 2/2):ℝ):ℂ))
        * ((2:ℤ):ℂ)) / (z * z - ((2:ℝ):ℂ)) := by
    rw [Phi2_closed z (sq_ne_two_of_im_ne_zero g y hy)]
    push_cast
    rw [pow_two]
    ring
  rw [hclosed]
  exact hdiv

/-- Enclosure of `Re Phi2 r` for real `r`, via the two `s`-branches. -/
def phiR (X : EIv) : EIv := EIv.add (sfnIv (EIv.add X SQ2)) (sfnIv (EIv.sub X SQ2))

theorem sfunC_ofReal (u : ℝ) : sfunC ((u : ℝ) : ℂ) = ((sfunR u : ℝ) : ℂ) := by
  rcases eq_or_ne u 0 with rfl | hne
  · simp [sfunC, sfunR]
  · have hne' : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    rw [sfunC, if_neg hne', sfunR, if_neg hne]
    push_cast
    ring

theorem Phi2_ofReal_re (r : ℝ) :
    (Phi2 ((r : ℝ) : ℂ)).re = sfunR (r + Real.sqrt 2) + sfunR (r - Real.sqrt 2) := by
  rw [Phi2]
  have h1 : ((r : ℝ) : ℂ) + ((Real.sqrt 2 : ℝ) : ℂ) = ((r + Real.sqrt 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((r : ℝ) : ℂ) - ((Real.sqrt 2 : ℝ) : ℂ) = ((r - Real.sqrt 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, sfunC_ofReal, sfunC_ofReal]
  simp

theorem phiR_mem {X : EIv} {r : ℝ} (hX : X.mem r) : (phiR X).mem ((Phi2 ((r : ℝ) : ℂ)).re) := by
  rw [Phi2_ofReal_re]
  exact EIv.add_mem (sfnIv_mem (EIv.add_mem hX SQ2_mem)) (sfnIv_mem (EIv.sub_mem hX SQ2_mem))

/-- Enclosure of `A`. -/
def AIV : EIv := phiR (EIv.pt 0)

theorem AIV_mem : AIV.mem Acst := by
  have h := phiR_mem (X := EIv.pt 0) (r := 0) (by simpa using EIv.pt_mem 0)
  simpa [Acst] using h

/-- Enclosure of `A²`. -/
def A2IV : EIv := EIv.sqr AIV

theorem A2IV_mem : A2IV.mem (Acst ^ 2) := by
  have := EIv.sqr_mem AIV_mem
  rwa [← pow_two] at this

/-- Enclosure of `ω(r) = Re Phi2(r)/A`. -/
def omgIv (X : EIv) : EIv := EIv.div (phiR X) AIV

theorem omgIv_mem {X : EIv} {r : ℝ} (hX : X.mem r) : (omgIv X).mem (omg r) :=
  EIv.div_mem (phiR_mem hX) AIV_mem

/-- Enclosure of `f(y, g)` on the cell `X`. -/
def fIv (X Y SH CH : EIv) : EIv :=
  let p := phiC X Y SH CH
  EIv.div (EIv.mulInt (EIv.sub (EIv.sqr p.2) (EIv.sqr p.1)) 4) A2IV

theorem fIv_mem {X Y SH CH : EIv} {g y : ℝ} (hX : X.mem g) (hY : Y.mem y) (hy : y ≠ 0)
    (hSH : SH.mem (Real.sinh (y/2))) (hCH : CH.mem (Real.cosh (y/2))) :
    (fIv X Y SH CH).mem (fBig y g) := by
  have hp := phiC_mem hX hY hy hSH hCH
  set P := Phi2 ((g : ℂ) + (y : ℝ) * I) with hP
  have h1 : EIv.mem (EIv.sub (EIv.sqr (phiC X Y SH CH).2) (EIv.sqr (phiC X Y SH CH).1))
      (P.im * P.im - P.re * P.re) := EIv.sub_mem (EIv.sqr_mem hp.2) (EIv.sqr_mem hp.1)
  have h2 := EIv.mulInt_mem (k := 4) h1
  have h3 := EIv.div_mem h2 A2IV_mem
  have heq : (P.im * P.im - P.re * P.re) * ((4:ℤ):ℝ) / Acst ^ 2 = fBig y g := by
    rw [fBig]
    push_cast
    ring
  rwa [heq] at h3

end BandDual
