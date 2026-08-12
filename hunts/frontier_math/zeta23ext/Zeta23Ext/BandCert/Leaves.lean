import Zeta23Ext.BandCert.Iv

set_option maxRecDepth 40000

/-!
# The analytic leaves

* `L1` Taylor enclosures of `sin`, `cos` at `|t| ≤ 1` (22 terms, Lagrange-free:
  the bound comes from `Complex.exp_bound` applied at `t * I`).
* `L2` interval widening is built into the fixed point operations.
* `L3` argument reduction, with a `2^-64`-accurate enclosure of `π`.
* `L4` `sinh`, `cosh` on `[-1,1]`.
* `L5` `√2` from `Nat.sqrt`.
* `L6` the series branch of `s(u) = sin(u/2)/u`.
-/

namespace BandDual

open Complex in
/-! ### Horner evaluation -/

/-- Real Horner evaluation of a polynomial with rational coefficients. -/
noncomputable def hornerR : List (ℤ × ℤ) → ℝ → ℝ
  | [], _ => 0
  | (n, d) :: cs, x => (n : ℝ) / (d : ℝ) + hornerR cs x * x

/-- Interval Horner evaluation. -/
def hornerI : List (ℤ × ℤ) → EIv → EIv
  | [], _ => EIv.ofInt 0
  | (n, d) :: cs, x => EIv.add (EIv.ofQ n d) (EIv.mul (hornerI cs x) x)

theorem hornerI_mem : ∀ (cs : List (ℤ × ℤ)) (_ : ∀ p ∈ cs, 0 < p.2) {a : EIv} {v : ℝ},
    a.mem v → (hornerI cs a).mem (hornerR cs v)
  | [], _, _, _, _ => by
      simpa [hornerI, hornerR] using EIv.ofInt_mem 0
  | (n, d) :: cs, hd, a, v, ha => by
      have hd0 : 0 < d := hd (n, d) (List.mem_cons_self ..)
      have hrest : ∀ p ∈ cs, 0 < p.2 := fun p hp => hd p (List.mem_cons_of_mem _ hp)
      have := EIv.add_mem (EIv.ofQ_mem (n := n) hd0) (EIv.mul_mem (hornerI_mem cs hrest ha) ha)
      simpa [hornerI, hornerR] using this

/-! ### Coefficient lists -/

def sinL : List (ℤ × ℤ) :=
  [(1, 1), (-1, 6), (1, 120), (-1, 5040), (1, 362880), (-1, 39916800), (1, 6227020800),
   (-1, 1307674368000), (1, 355687428096000), (-1, 121645100408832000),
   (1, 51090942171709440000)]

def cosL : List (ℤ × ℤ) :=
  [(1, 1), (-1, 2), (1, 24), (-1, 720), (1, 40320), (-1, 3628800), (1, 479001600),
   (-1, 87178291200), (1, 20922789888000), (-1, 6402373705728000), (1, 2432902008176640000)]

def sfnL : List (ℤ × ℤ) :=
  [(1, 2), (-1, 12), (1, 240), (-1, 10080), (1, 725760), (-1, 79833600), (1, 12454041600),
   (-1, 2615348736000), (1, 711374856192000), (-1, 243290200817664000),
   (1, 102181884343418880000)]

def sinhL : List (ℤ × ℤ) :=
  [(1, 1), (1, 6), (1, 120), (1, 5040), (1, 362880), (1, 39916800), (1, 6227020800),
   (1, 1307674368000), (1, 355687428096000), (1, 121645100408832000),
   (1, 51090942171709440000)]

def coshL : List (ℤ × ℤ) :=
  [(1, 1), (1, 2), (1, 24), (1, 720), (1, 40320), (1, 3628800), (1, 479001600),
   (1, 87178291200), (1, 20922789888000), (1, 6402373705728000), (1, 2432902008176640000)]

theorem sinL_pos : ∀ p ∈ sinL, 0 < p.2 := by decide
theorem cosL_pos : ∀ p ∈ cosL, 0 < p.2 := by decide
theorem sfnL_pos : ∀ p ∈ sfnL, 0 < p.2 := by decide
theorem sinhL_pos : ∀ p ∈ sinhL, 0 < p.2 := by decide
theorem coshL_pos : ∀ p ∈ coshL, 0 < p.2 := by decide

/-- The 22-term remainder bound `23 / (22! * 22)`, rounded up. -/
noncomputable def RB : ℝ := 1 / 10 ^ 21

/-! ### L1 : `sin` and `cos` on `[-1,1]` -/

open Complex in
theorem partial_sum_eq (t : ℝ) :
    (∑ m ∈ Finset.range 22, ((t : ℂ) * I) ^ m / (Nat.factorial m : ℂ))
      = ((hornerR cosL (t * t) : ℝ) : ℂ) + ((t * hornerR sinL (t * t) : ℝ) : ℂ) * I := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sinL, cosL, hornerR]
  norm_num [Nat.factorial]
  rw [Complex.ext_iff]
  constructor <;>
    · simp [pow_succ]
      ring

open Complex in
theorem exp_it_bound (t : ℝ) (ht : |t| ≤ 1) :
    ‖Complex.exp ((t : ℂ) * I) - (((hornerR cosL (t * t) : ℝ) : ℂ)
        + ((t * hornerR sinL (t * t) : ℝ) : ℂ) * I)‖ ≤ |t| ^ 22 * RB := by
  have hnorm : ‖(t : ℂ) * I‖ ≤ 1 := by simpa using ht
  have h := Complex.exp_bound hnorm (n := 22) (by norm_num)
  rw [partial_sum_eq] at h
  refine le_trans h ?_
  have h1 : ‖(t : ℂ) * I‖ = |t| := by simp
  rw [h1]
  have h2 : ((Nat.succ 22 : ℕ) : ℝ) * (((Nat.factorial 22 : ℕ) : ℝ) * (22 : ℕ))⁻¹ ≤ RB := by
    norm_num [Nat.factorial, RB]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem cos_taylor (t : ℝ) (ht : |t| ≤ 1) :
    |Real.cos t - hornerR cosL (t * t)| ≤ |t| ^ 22 * RB := by
  have h := exp_it_bound t ht
  rw [Complex.exp_mul_I] at h
  have hre : (Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I
      - (((hornerR cosL (t * t) : ℝ) : ℂ) + ((t * hornerR sinL (t * t) : ℝ) : ℂ)
        * Complex.I)).re = Real.cos t - hornerR cosL (t * t) := by
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  calc |Real.cos t - hornerR cosL (t * t)|
      = |(Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I
          - (((hornerR cosL (t * t) : ℝ) : ℂ)
            + ((t * hornerR sinL (t * t) : ℝ) : ℂ) * Complex.I)).re| := by rw [hre]
    _ ≤ _ := le_trans (Complex.abs_re_le_norm _) h

theorem sin_taylor (t : ℝ) (ht : |t| ≤ 1) :
    |Real.sin t - t * hornerR sinL (t * t)| ≤ |t| ^ 22 * RB := by
  have h := exp_it_bound t ht
  rw [Complex.exp_mul_I] at h
  have him : (Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I
      - (((hornerR cosL (t * t) : ℝ) : ℂ) + ((t * hornerR sinL (t * t) : ℝ) : ℂ)
        * Complex.I)).im = Real.sin t - t * hornerR sinL (t * t) := by
    simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  calc |Real.sin t - t * hornerR sinL (t * t)|
      = |(Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I
          - (((hornerR cosL (t * t) : ℝ) : ℂ)
            + ((t * hornerR sinL (t * t) : ℝ) : ℂ) * Complex.I)).im| := by rw [him]
    _ ≤ _ := le_trans (Complex.abs_im_le_norm _) h

/-! ### L4 : `sinh` and `cosh` on `[-1,1]` -/

theorem exp_partial_eq (t : ℝ) :
    (∑ m ∈ Finset.range 22, t ^ m / (Nat.factorial m : ℝ))
      = hornerR coshL (t * t) + t * hornerR sinhL (t * t) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sinhL, coshL, hornerR]
  norm_num [Nat.factorial]
  ring

theorem exp_partial_eq' (t : ℝ) :
    (∑ m ∈ Finset.range 22, (-t) ^ m / (Nat.factorial m : ℝ))
      = hornerR coshL (t * t) - t * hornerR sinhL (t * t) := by
  have h := exp_partial_eq (-t)
  have hn : (-t) * (-t) = t * t := by ring
  rw [hn] at h
  rw [h]
  ring

theorem exp_bound' (t : ℝ) (ht : |t| ≤ 1) :
    |Real.exp t - (∑ m ∈ Finset.range 22, t ^ m / (Nat.factorial m : ℝ))| ≤ RB := by
  have h := Real.exp_bound ht (n := 22) (by norm_num)
  refine le_trans h ?_
  have h1 : |t| ^ 22 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  have h2 : ((Nat.succ 22 : ℕ) : ℝ) / (((Nat.factorial 22 : ℕ) : ℝ) * (22 : ℕ)) ≤ RB := by
    norm_num [Nat.factorial, RB]
  calc |t| ^ 22 * (((Nat.succ 22 : ℕ) : ℝ) / (((Nat.factorial 22 : ℕ) : ℝ) * (22 : ℕ)))
      ≤ 1 * RB := by
        refine mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ = RB := one_mul _

theorem cosh_taylor (t : ℝ) (ht : |t| ≤ 1) :
    |Real.cosh t - hornerR coshL (t * t)| ≤ RB := by
  have h1 := exp_bound' t ht
  rw [exp_partial_eq] at h1
  have h2 : |Real.exp (-t) - (hornerR coshL (t * t) - t * hornerR sinhL (t * t))| ≤ RB := by
    have h := exp_bound' (-t) (by rwa [abs_neg])
    rwa [exp_partial_eq'] at h
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  rw [Real.cosh_eq, abs_le]
  constructor <;> linarith

theorem sinh_taylor (t : ℝ) (ht : |t| ≤ 1) :
    |Real.sinh t - t * hornerR sinhL (t * t)| ≤ RB := by
  have h1 := exp_bound' t ht
  rw [exp_partial_eq] at h1
  have h2 : |Real.exp (-t) - (hornerR coshL (t * t) - t * hornerR sinhL (t * t))| ≤ RB := by
    have h := exp_bound' (-t) (by rwa [abs_neg])
    rwa [exp_partial_eq'] at h
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  rw [Real.sinh_eq, abs_le]
  constructor <;> linarith


/-! ### Interval level enclosures -/

/-- The trivial enclosure `[-1,1]`. -/
def topI : EIv := some ⟨-SO, SO⟩

theorem topI_sin (v : ℝ) : topI.mem (Real.sin v) := by
  have h1 := Real.neg_one_le_sin v
  have h2 := Real.sin_le_one v
  have hS := SOR_pos
  constructor <;> · push_cast; nlinarith

theorem topI_cos (v : ℝ) : topI.mem (Real.cos v) := by
  have h1 := Real.neg_one_le_cos v
  have h2 := Real.cos_le_one v
  have hS := SOR_pos
  constructor <;> · push_cast; nlinarith

theorem RB_SO : RB * (SO:ℝ) ≤ 1 := by
  simp only [RB, SO]
  norm_num

theorem RB_nonneg : (0:ℝ) ≤ RB := by simp [RB]

/-- Widening by one ulp absorbs a remainder bounded by `RB`. -/
theorem widen_of_abs {a : EIv} {x u : ℝ} (ha : a.mem x) (h : |u - x| ≤ RB) :
    (EIv.widen a 1).mem u := by
  refine EIv.widen_mem ha ?_
  have hS := SOR_pos
  have h2 := RB_SO
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h (le_of_lt hS)]

/-- `(sin, cos)` enclosure valid for arguments in `[-1,1]`. -/
def sinCosSmall (a : EIv) : EIv × EIv :=
  let x2 := EIv.sqr a
  (EIv.widen (EIv.mul (hornerI sinL x2) a) 1, EIv.widen (hornerI cosL x2) 1)

theorem sinCosSmall_mem {a : EIv} {v : ℝ} (ha : a.mem v) (hv : |v| ≤ 1) :
    (sinCosSmall a).1.mem (Real.sin v) ∧ (sinCosSmall a).2.mem (Real.cos v) := by
  have hx2 : (EIv.sqr a).mem (v * v) := EIv.sqr_mem ha
  have hsin := EIv.mul_mem (hornerI_mem sinL sinL_pos hx2) ha
  have hcos := hornerI_mem cosL cosL_pos hx2
  have hpow : |v| ^ 22 ≤ 1 := pow_le_one₀ (abs_nonneg v) hv
  have hRB := RB_nonneg
  refine ⟨widen_of_abs hsin ?_, widen_of_abs hcos ?_⟩
  · have h := sin_taylor v hv
    rw [mul_comm (hornerR sinL (v*v)) v]
    calc |Real.sin v - v * hornerR sinL (v * v)| ≤ |v| ^ 22 * RB := h
      _ ≤ 1 * RB := by nlinarith
      _ = RB := one_mul _
  · have h := cos_taylor v hv
    calc |Real.cos v - hornerR cosL (v * v)| ≤ |v| ^ 22 * RB := h
      _ ≤ 1 * RB := by nlinarith
      _ = RB := one_mul _

/-- `(sinh, cosh)` enclosure valid for arguments in `[-1,1]`. -/
def sinhCoshSmall (a : EIv) : EIv × EIv :=
  let x2 := EIv.sqr a
  (EIv.widen (EIv.mul (hornerI sinhL x2) a) 1, EIv.widen (hornerI coshL x2) 1)

theorem sinhCoshSmall_mem {a : EIv} {v : ℝ} (ha : a.mem v) (hv : |v| ≤ 1) :
    (sinhCoshSmall a).1.mem (Real.sinh v) ∧ (sinhCoshSmall a).2.mem (Real.cosh v) := by
  have hx2 : (EIv.sqr a).mem (v * v) := EIv.sqr_mem ha
  have hsin := EIv.mul_mem (hornerI_mem sinhL sinhL_pos hx2) ha
  have hcos := hornerI_mem coshL coshL_pos hx2
  refine ⟨widen_of_abs hsin ?_, widen_of_abs hcos ?_⟩
  · rw [mul_comm (hornerR sinhL (v*v)) v]
    exact sinh_taylor v hv
  · exact cosh_taylor v hv

/-! ### L5 : `√2` -/

def sq2n : ℤ := 26087635650665564424

def SQ2 : EIv := some ⟨sq2n, sq2n + 1⟩

theorem SQ2_mem : SQ2.mem (Real.sqrt 2) := by
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hSO : ((SO:ℤ):ℝ) = 18446744073709551616 := by simp [SO]
  constructor
  · simp only [sq2n, hSO]
    push_cast
    nlinarith [hr, hnn, sq_nonneg ((18446744073709551616:ℝ) * Real.sqrt 2 - 26087635650665564424)]
  · simp only [sq2n, hSO]
    push_cast
    nlinarith [hr, hnn, sq_nonneg ((18446744073709551616:ℝ) * Real.sqrt 2 - 26087635650665564425)]

/-! ### L3 : `π` -/

/-- Bool test `m < 2 * lo`. -/
def loGt (o : EIv) (m : ℤ) : Bool :=
  match o with
  | some a => decide (m < 2 * a.lo)
  | none => false

/-- Bool test `2 * hi < m`. -/
def hiLt (o : EIv) (m : ℤ) : Bool :=
  match o with
  | some a => decide (2 * a.hi < m)
  | none => false

theorem loGt_sound {o : EIv} {x : ℝ} {m : ℤ} (h : loGt o m = true) (hm : o.mem x) :
    (m:ℝ) < 2 * ((SO:ℝ) * x) := by
  cases o with
  | none => simp [loGt] at h
  | some a =>
      simp only [loGt, decide_eq_true_eq] at h
      have h1 : ((m:ℤ):ℝ) < ((2 * a.lo : ℤ):ℝ) := by exact_mod_cast h
      have h2 := hm.1
      push_cast at h1
      linarith

theorem hiLt_sound {o : EIv} {x : ℝ} {m : ℤ} (h : hiLt o m = true) (hm : o.mem x) :
    2 * ((SO:ℝ) * x) < (m:ℝ) := by
  cases o with
  | none => simp [hiLt] at h
  | some a =>
      simp only [hiLt, decide_eq_true_eq] at h
      have h1 : ((2 * a.hi : ℤ):ℝ) < ((m:ℤ):ℝ) := by exact_mod_cast h
      have h2 := hm.2
      push_cast at h1
      linarith

def piqa : ℤ := 14488038916154245652
def piqb : ℤ := 14488038916154245716

theorem piqa_lt : (piqa:ℝ)/(SO:ℝ) < Real.pi / 4 := by
  set xa : ℝ := (piqa:ℝ)/(SO:ℝ) with hxa
  have hSO : ((SO:ℤ):ℝ) = 18446744073709551616 := by simp [SO]
  have hxa_bounds : |xa| ≤ 1 := by
    rw [hxa, hSO, abs_le]
    norm_num [piqa]
  have hmem : (EIv.pt piqa).mem xa := EIv.pt_mem piqa
  have hcos := (sinCosSmall_mem hmem hxa_bounds).2
  have hchk : loGt (sinCosSmall (EIv.pt piqa)).2 (sq2n + 1) = true := by decide +kernel
  have hlt := loGt_sound hchk hcos
  -- cos xa > √2 / 2
  have hsq := SQ2_mem
  have hs2 : Real.sqrt 2 * (SO:ℝ) ≤ ((sq2n + 1 : ℤ):ℝ) := by
    have := hsq.2
    push_cast at this ⊢
    linarith [this]
  have hS := SOR_pos
  have hgt : Real.sqrt 2 / 2 < Real.cos xa := by
    push_cast at hlt hs2
    have h9 : Real.sqrt 2 * (SO:ℝ) < (2 * Real.cos xa) * (SO:ℝ) := by nlinarith
    have h10 := lt_of_mul_lt_mul_right h9 (le_of_lt hS)
    linarith
  have hxle : xa ≤ 3 := by
    rw [hxa, hSO]
    norm_num [piqa]
  have hxpi : xa ≤ Real.pi := le_trans hxle (le_of_lt Real.pi_gt_three)
  by_contra hcon
  push_neg at hcon
  have hle : Real.cos xa ≤ Real.cos (Real.pi / 4) := by
    rcases eq_or_lt_of_le hcon with heq | hlt'
    · rw [heq]
    · exact le_of_lt (Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) hxpi hlt')
  rw [Real.cos_pi_div_four] at hle
  linarith

theorem piqb_gt : Real.pi / 4 < (piqb:ℝ)/(SO:ℝ) := by
  set xb : ℝ := (piqb:ℝ)/(SO:ℝ) with hxb
  have hSO : ((SO:ℤ):ℝ) = 18446744073709551616 := by simp [SO]
  have hxb_bounds : |xb| ≤ 1 := by
    rw [hxb, hSO, abs_le]
    norm_num [piqb]
  have hmem : (EIv.pt piqb).mem xb := EIv.pt_mem piqb
  have hcos := (sinCosSmall_mem hmem hxb_bounds).2
  have hchk : hiLt (sinCosSmall (EIv.pt piqb)).2 sq2n = true := by decide +kernel
  have hlt := hiLt_sound hchk hcos
  have hsq := SQ2_mem
  have hs2 : ((sq2n : ℤ):ℝ) ≤ Real.sqrt 2 * (SO:ℝ) := by
    have := hsq.1
    push_cast at this ⊢
    linarith [this]
  have hS := SOR_pos
  have hgt : Real.cos xb < Real.sqrt 2 / 2 := by
    push_cast at hlt hs2
    have h9 : (2 * Real.cos xb) * (SO:ℝ) < Real.sqrt 2 * (SO:ℝ) := by nlinarith
    have h10 := lt_of_mul_lt_mul_right h9 (le_of_lt hS)
    linarith
  have hxnn : 0 ≤ xb := by
    rw [hxb, hSO]
    norm_num [piqb]
  by_contra hcon
  push_neg at hcon
  have hle : Real.cos (Real.pi/4) ≤ Real.cos xb := by
    rcases eq_or_lt_of_le hcon with heq | hlt'
    · rw [heq]
    · refine le_of_lt (Real.cos_lt_cos_of_nonneg_of_le_pi hxnn ?_ hlt')
      linarith [Real.pi_pos]
  rw [Real.cos_pi_div_four] at hle
  linarith

/-- Enclosure of `2π`. -/
def PI2iv : EIv := some ⟨8 * piqa, 8 * piqb⟩

theorem PI2iv_mem : PI2iv.mem (2 * Real.pi) := by
  have h1 := piqa_lt
  have h2 := piqb_gt
  have hS := SOR_pos
  constructor
  · push_cast
    rw [div_lt_iff₀ hS] at h1
    nlinarith
  · push_cast
    rw [lt_div_iff₀ hS] at h2
    nlinarith

/-! ### General `sin`/`cos` enclosure -/

theorem cos_two_mul_sin (t : ℝ) : Real.cos (2 * t) = 1 - Real.sin t * Real.sin t * 2 := by
  rw [Real.cos_two_mul']
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- One doubling step. -/
def dbl (sc : EIv × EIv) : EIv × EIv :=
  (EIv.mulInt (EIv.mul sc.1 sc.2) 2, EIv.sub (EIv.ofInt 1) (EIv.mulInt (EIv.sqr sc.1) 2))

theorem dbl_mem {sc : EIv × EIv} {t : ℝ} (hs : sc.1.mem (Real.sin t)) (hc : sc.2.mem (Real.cos t)) :
    (dbl sc).1.mem (Real.sin (2*t)) ∧ (dbl sc).2.mem (Real.cos (2*t)) := by
  constructor
  · have h := EIv.mulInt_mem (k := 2) (EIv.mul_mem hs hc)
    have he : Real.sin t * Real.cos t * ((2:ℤ):ℝ) = Real.sin (2*t) := by
      rw [Real.sin_two_mul]; push_cast; ring
    rwa [he] at h
  · have h := EIv.sub_mem (EIv.ofInt_mem 1) (EIv.mulInt_mem (k := 2) (EIv.sqr_mem hs))
    have he : ((1:ℤ):ℝ) - Real.sin t * Real.sin t * ((2:ℤ):ℝ) = Real.cos (2*t) := by
      rw [cos_two_mul_sin]; push_cast; ring
    rwa [he] at h

/-- `(sin, cos)` enclosure for an arbitrary argument: reduce mod `2π`, quarter,
evaluate, then double twice. -/
def sinCosIv (a : EIv) : EIv × EIv :=
  match a, PI2iv with
  | some i, some p =>
      let m := i.lo + i.hi
      let ps := p.lo + p.hi
      let k := (m + ps / 2) / ps
      let r := i.sub (p.mulInt k)
      let t := r.divInt 4
      if -SO ≤ t.lo ∧ t.hi ≤ SO then
        dbl (dbl (sinCosSmall (some t)))
      else (topI, topI)
  | _, _ => (topI, topI)

theorem sinCosIv_mem {a : EIv} {v : ℝ} (ha : a.mem v) :
    (sinCosIv a).1.mem (Real.sin v) ∧ (sinCosIv a).2.mem (Real.cos v) := by
  unfold sinCosIv
  cases a with
  | none => exact ⟨topI_sin v, topI_cos v⟩
  | some i =>
    simp only [PI2iv]
    split_ifs with hg
    · set p : Iv := ⟨8 * piqa, 8 * piqb⟩ with hp
      set k : ℤ := (i.lo + i.hi + (p.lo + p.hi) / 2) / (p.lo + p.hi) with hk
      set r : Iv := i.sub (p.mulInt k) with hr
      set t : Iv := r.divInt 4 with ht
      have hpm : Iv.mem p (2 * Real.pi) := PI2iv_mem
      have hrm : Iv.mem r (v - 2 * Real.pi * (k:ℝ)) :=
        Iv.sub_mem (a := i) ha (Iv.mulInt_mem (k := k) hpm)
      have htm : EIv.mem (some t) ((v - 2 * Real.pi * (k:ℝ)) / ((4:ℤ):ℝ)) :=
        Iv.divInt_mem (by norm_num) hrm
      set w : ℝ := (v - 2 * Real.pi * (k:ℝ)) / ((4:ℤ):ℝ) with hw
      have hwb : |w| ≤ 1 := by
        obtain ⟨hl, hh⟩ := htm
        have hS := SOR_pos
        obtain ⟨g1, g2⟩ := hg
        have g1' : ((-SO : ℤ):ℝ) ≤ ((t.lo:ℤ):ℝ) := by exact_mod_cast g1
        have g2' : ((t.hi:ℤ):ℝ) ≤ ((SO:ℤ):ℝ) := by exact_mod_cast g2
        rw [abs_le]
        push_cast at g1' g2' hl hh
        constructor <;> nlinarith
      have hsc := sinCosSmall_mem htm hwb
      have hd1 := dbl_mem hsc.1 hsc.2
      have hd2 := dbl_mem hd1.1 hd1.2
      have hv4 : 2 * (2 * w) = v - 2 * Real.pi * (k:ℝ) := by
        rw [hw]; push_cast; ring
      rw [hv4] at hd2
      have hsv : Real.sin (v - 2 * Real.pi * (k:ℝ)) = Real.sin v := by
        have := Real.sin_add_int_mul_two_pi (v - 2 * Real.pi * (k:ℝ)) k
        rw [show v - 2 * Real.pi * (k:ℝ) + (k:ℝ) * (2 * Real.pi) = v by ring] at this
        exact this.symm
      have hcv : Real.cos (v - 2 * Real.pi * (k:ℝ)) = Real.cos v := by
        have := Real.cos_add_int_mul_two_pi (v - 2 * Real.pi * (k:ℝ)) k
        rw [show v - 2 * Real.pi * (k:ℝ) + (k:ℝ) * (2 * Real.pi) = v by ring] at this
        exact this.symm
      rw [hsv] at hd2
      rw [hcv] at hd2
      exact hd2
    · exact ⟨topI_sin v, topI_cos v⟩


/-! ### L6 : the series branch of `s(u) = sin(u/2)/u` -/

/-- `s(u) = sin(u/2)/u`, extended by its removable value `1/2` at `0`. -/
noncomputable def sfunR (u : ℝ) : ℝ := if u = 0 then 1/2 else Real.sin (u/2) / u

theorem hornerR_sfnL (x : ℝ) : hornerR sfnL x = hornerR sinL x / 2 := by
  simp only [hornerR, sfnL, sinL]
  push_cast
  ring

theorem sfunR_taylor (u : ℝ) (hu : |u| ≤ 2) :
    |sfunR u - hornerR sfnL ((u/2) * (u/2))| ≤ RB := by
  have hRB := RB_nonneg
  rcases eq_or_ne u 0 with rfl | hne
  · simp only [sfunR, hornerR_sfnL]
    norm_num [hornerR, sinL]
    exact hRB
  · set t : ℝ := u / 2 with hts
    have htne : t ≠ 0 := by simp [hts]; exact hne
    have hta : |t| ≤ 1 := by
      rw [hts, abs_div]
      rw [div_le_one (by norm_num)]
      simpa using hu
    have h := sin_taylor t hta
    have hu2 : u = 2 * t := by rw [hts]; ring
    have hsf : sfunR u = Real.sin t / (2 * t) := by
      simp only [sfunR, if_neg hne]
      rw [hu2]
      congr 1
      rw [hts]
      ring_nf
    have hpoly : hornerR sfnL (t * t) = hornerR sinL (t * t) / 2 := hornerR_sfnL _
    rw [hsf, hpoly]
    have hkey : Real.sin t / (2 * t) - hornerR sinL (t * t) / 2
        = (Real.sin t - t * hornerR sinL (t * t)) / (2 * t) := by
      field_simp
    rw [hkey, abs_div]
    have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
    rw [habs]
    have htpos : 0 < |t| := abs_pos.mpr htne
    rw [div_le_iff₀ (by positivity)]
    have h21 : |t| ^ 22 = |t| ^ 21 * |t| := by ring
    have h21' : |t| ^ 21 ≤ 1 := pow_le_one₀ (abs_nonneg t) hta
    calc |Real.sin t - t * hornerR sinL (t * t)| ≤ |t| ^ 22 * RB := h
      _ = (|t| ^ 21 * RB) * |t| := by rw [h21]; ring
      _ ≤ (1 * RB) * (2 * |t|) := by
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h21') hRB) (le_of_lt htpos),
              mul_nonneg hRB (le_of_lt htpos)]
      _ = RB * (2 * |t|) := by ring

/-- Interval enclosure of `s(u) = sin(u/2)/u` for real `u`. -/
def sfnIv (u : EIv) : EIv :=
  match u with
  | none => none
  | some a =>
      if -(2*SO) ≤ a.lo ∧ a.hi ≤ 2*SO then
        EIv.widen (hornerI sfnL (EIv.sqr (EIv.divInt (some a) 2))) 1
      else if 0 < a.lo then
        EIv.div (sinCosIv (EIv.divInt (some a) 2)).1 (some a)
      else none

theorem sfnIv_mem {u : EIv} {v : ℝ} (hu : u.mem v) : (sfnIv u).mem (sfunR v) := by
  cases u with
  | none => trivial
  | some a =>
      simp only [sfnIv]
      split_ifs with h1 h2
      · have hv2 : |v| ≤ 2 := by
          obtain ⟨g1, g2⟩ := h1
          obtain ⟨hl, hh⟩ := hu
          have hS := SOR_pos
          have g1' : ((-(2*SO) : ℤ):ℝ) ≤ ((a.lo:ℤ):ℝ) := by exact_mod_cast g1
          have g2' : ((a.hi:ℤ):ℝ) ≤ ((2*SO:ℤ):ℝ) := by exact_mod_cast g2
          push_cast at g1' g2'
          rw [abs_le]
          constructor <;> nlinarith
        have hhalf : EIv.mem (EIv.divInt (some a) 2) (v / ((2:ℤ):ℝ)) :=
          EIv.divInt_mem (by norm_num) hu
        have hsq : EIv.mem (EIv.sqr (EIv.divInt (some a) 2))
            ((v / ((2:ℤ):ℝ)) * (v / ((2:ℤ):ℝ))) := EIv.sqr_mem hhalf
        have hh := hornerI_mem sfnL sfnL_pos hsq
        refine widen_of_abs hh ?_
        have := sfunR_taylor v hv2
        have heq : (v / ((2:ℤ):ℝ)) * (v / ((2:ℤ):ℝ)) = (v/2) * (v/2) := by push_cast; ring
        rw [heq]
        exact this
      · have hvpos : 0 < v := by
          obtain ⟨hl, _⟩ := hu
          have hS := SOR_pos
          have h2' : (0:ℝ) < ((a.lo:ℤ):ℝ) := by exact_mod_cast h2
          nlinarith
        have hne : v ≠ 0 := ne_of_gt hvpos
        have hhalf : EIv.mem (EIv.divInt (some a) 2) (v / ((2:ℤ):ℝ)) :=
          EIv.divInt_mem (by norm_num) hu
        have hsin := (sinCosIv_mem hhalf).1
        have hdiv := EIv.div_mem hsin hu
        have heq : Real.sin (v / ((2:ℤ):ℝ)) / v = sfunR v := by
          simp only [sfunR, if_neg hne]
          norm_num
        rwa [heq] at hdiv
      · trivial


end BandDual
