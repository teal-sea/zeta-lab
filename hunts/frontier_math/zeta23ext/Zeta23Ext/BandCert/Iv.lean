import Mathlib

/-!
# Fixed-point interval arithmetic at scale `2^64`

An `Iv` is a pair of integers `⟨lo, hi⟩` denoting the real interval
`[lo / 2^64, hi / 2^64]`.  `EIv = Option Iv` adds a top element (`none`,
"no information"), which is what division returns when it cannot certify
that its denominator is bounded away from zero.

Every operation comes with a soundness lemma: if the inputs enclose the
reals `x`, `y`, then the output encloses `x ⋆ y`.
-/

namespace BandDual

/-- The fixed-point scale, `2^64`. -/
def SO : ℤ := 18446744073709551616

theorem SO_eq : SO = 2 ^ 64 := by decide +kernel

theorem SO_pos : (0:ℤ) < SO := by decide +kernel

theorem SOR_pos : (0:ℝ) < (SO:ℝ) := by
  exact_mod_cast SO_pos

/-- A fixed-point interval `[lo/2^64, hi/2^64]`. -/
structure Iv where
  lo : ℤ
  hi : ℤ
deriving DecidableEq, Repr

/-- An interval, or `none` for "no information". -/
abbrev EIv := Option Iv

namespace Iv

/-- `x` lies in the interval. -/
def mem (a : Iv) (x : ℝ) : Prop := (a.lo : ℝ) ≤ (SO:ℝ) * x ∧ (SO:ℝ) * x ≤ (a.hi : ℝ)

end Iv

/-- `x` lies in the extended interval (`none` carries no information). -/
def EIv.mem : EIv → ℝ → Prop
  | none, _ => True
  | some a, x => a.mem x

@[simp] theorem EIv.mem_none (x : ℝ) : EIv.mem none x := trivial

@[simp] theorem EIv.mem_some (a : Iv) (x : ℝ) : EIv.mem (some a) x ↔ a.mem x := Iff.rfl

/-! ### Directed rounding -/

/-- Floor of `p / 2^64`. -/
def flo (p : ℤ) : ℤ := p / SO

/-- Ceiling of `p / 2^64`. -/
def fhi (p : ℤ) : ℤ := -((-p) / SO)

theorem ediv_mul_le (p : ℤ) {d : ℤ} (hd : 0 < d) : (p / d) * d ≤ p := by
  have h := Int.mul_ediv_add_emod p d
  have h2 : 0 ≤ p % d := Int.emod_nonneg p (ne_of_gt hd)
  nlinarith [h, h2]

theorem le_ediv_mul (p : ℤ) {d : ℤ} (hd : 0 < d) : p ≤ (-((-p) / d)) * d := by
  have h := ediv_mul_le (-p) hd
  nlinarith [h]

theorem flo_le (p : ℤ) : ((flo p : ℤ) : ℝ) * (SO:ℝ) ≤ (p : ℝ) := by
  have := ediv_mul_le p SO_pos
  exact_mod_cast this

theorem le_fhi (p : ℤ) : (p : ℝ) ≤ ((fhi p : ℤ) : ℝ) * (SO:ℝ) := by
  have := le_ediv_mul p SO_pos
  exact_mod_cast this

theorem ediv_le_of (p : ℤ) {d : ℤ} (hd : 0 < d) : ((p / d : ℤ) : ℝ) ≤ (p:ℝ) / (d:ℝ) := by
  have h := ediv_mul_le p hd
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast h

theorem le_cdiv_of (p : ℤ) {d : ℤ} (hd : 0 < d) : (p:ℝ) / (d:ℝ) ≤ ((-((-p) / d) : ℤ) : ℝ) := by
  have h := le_ediv_mul p hd
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  exact_mod_cast h

/-! ### The linear/box bounds -/

theorem lin_le {a1 a2 X c : ℝ} (h1 : a1 ≤ X) (h2 : X ≤ a2) :
    X * c ≤ max (a1 * c) (a2 * c) := by
  rcases le_total 0 c with hc | hc
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

theorem le_lin {a1 a2 X c : ℝ} (h1 : a1 ≤ X) (h2 : X ≤ a2) :
    min (a1 * c) (a2 * c) ≤ X * c := by
  rcases le_total 0 c with hc | hc
  · exact le_trans (min_le_left _ _) (by nlinarith)
  · exact le_trans (min_le_right _ _) (by nlinarith)

theorem mul_box_le {a1 a2 b1 b2 X Y : ℝ} (h1 : a1 ≤ X) (h2 : X ≤ a2)
    (h3 : b1 ≤ Y) (h4 : Y ≤ b2) :
    X * Y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  have h5 : X * Y ≤ max (a1 * Y) (a2 * Y) := lin_le h1 h2
  have h6 : a1 * Y ≤ max (a1 * b1) (a1 * b2) := by
    have := lin_le (a1 := b1) (a2 := b2) (X := Y) (c := a1) h3 h4
    calc a1 * Y = Y * a1 := by ring
      _ ≤ max (b1 * a1) (b2 * a1) := this
      _ = max (a1 * b1) (a1 * b2) := by rw [mul_comm b1 a1, mul_comm b2 a1]
  have h7 : a2 * Y ≤ max (a2 * b1) (a2 * b2) := by
    have := lin_le (a1 := b1) (a2 := b2) (X := Y) (c := a2) h3 h4
    calc a2 * Y = Y * a2 := by ring
      _ ≤ max (b1 * a2) (b2 * a2) := this
      _ = max (a2 * b1) (a2 * b2) := by rw [mul_comm b1 a2, mul_comm b2 a2]
  exact le_trans h5 (max_le (le_max_of_le_left h6) (le_max_of_le_right h7))

theorem le_mul_box {a1 a2 b1 b2 X Y : ℝ} (h1 : a1 ≤ X) (h2 : X ≤ a2)
    (h3 : b1 ≤ Y) (h4 : Y ≤ b2) :
    min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ X * Y := by
  have h5 : min (a1 * Y) (a2 * Y) ≤ X * Y := le_lin h1 h2
  have h6 : min (a1 * b1) (a1 * b2) ≤ a1 * Y := by
    have := le_lin (a1 := b1) (a2 := b2) (X := Y) (c := a1) h3 h4
    calc min (a1 * b1) (a1 * b2) = min (b1 * a1) (b2 * a1) := by
          rw [mul_comm b1 a1, mul_comm b2 a1]
      _ ≤ Y * a1 := this
      _ = a1 * Y := by ring
  have h7 : min (a2 * b1) (a2 * b2) ≤ a2 * Y := by
    have := le_lin (a1 := b1) (a2 := b2) (X := Y) (c := a2) h3 h4
    calc min (a2 * b1) (a2 * b2) = min (b1 * a2) (b2 * a2) := by
          rw [mul_comm b1 a2, mul_comm b2 a2]
      _ ≤ Y * a2 := this
      _ = a2 * Y := by ring
  exact le_trans (le_min (le_trans (min_le_left _ _) h6) (le_trans (min_le_right _ _) h7)) h5

/-! ### Operations -/

namespace Iv

def add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : Iv) : Iv := ⟨a.lo - b.hi, a.hi - b.lo⟩
def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩

def mul (a b : Iv) : Iv :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨flo (min (min p1 p2) (min p3 p4)), fhi (max (max p1 p2) (max p3 p4))⟩

def sqr (a : Iv) : Iv :=
  if 0 ≤ a.lo then ⟨flo (a.lo * a.lo), fhi (a.hi * a.hi)⟩
  else if a.hi ≤ 0 then ⟨flo (a.hi * a.hi), fhi (a.lo * a.lo)⟩
  else ⟨0, fhi (max (a.lo * a.lo) (a.hi * a.hi))⟩

/-- Multiply by an exact integer. -/
def mulInt (a : Iv) (k : ℤ) : Iv :=
  if 0 ≤ k then ⟨a.lo * k, a.hi * k⟩ else ⟨a.hi * k, a.lo * k⟩

/-- Divide by an exact positive integer. -/
def divInt (a : Iv) (d : ℤ) : Iv := ⟨a.lo / d, -((-a.hi) / d)⟩

/-- Widen by `r / 2^64` on each side. -/
def widen (a : Iv) (r : ℤ) : Iv := ⟨a.lo - r, a.hi + r⟩

/-- The exact rational `n / d` (`d > 0`). -/
def ofQ (n d : ℤ) : Iv := ⟨(n * SO) / d, -((-(n * SO)) / d)⟩

/-- The exact integer `n`. -/
def ofInt (n : ℤ) : Iv := ⟨n * SO, n * SO⟩

/-- Interval division; `none` unless the denominator is enclosed away from zero. -/
def div (a b : Iv) : EIv :=
  if 0 < b.lo then
    let q1 := a.lo * SO
    let q2 := a.hi * SO
    some ⟨min (min (q1 / b.hi) (q1 / b.lo)) (min (q2 / b.hi) (q2 / b.lo)),
          max (max (-((-q1) / b.hi)) (-((-q1) / b.lo)))
              (max (-((-q2) / b.hi)) (-((-q2) / b.lo)))⟩
  else none

end Iv

/-! ### Soundness -/

namespace Iv

theorem add_mem {a b : Iv} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) : (a.add b).mem (x + y) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  constructor <;> · simp only [add] at *; push_cast; nlinarith

theorem sub_mem {a b : Iv} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) : (a.sub b).mem (x - y) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  constructor <;> · simp only [sub] at *; push_cast; nlinarith

theorem neg_mem {a : Iv} {x : ℝ} (ha : a.mem x) : (a.neg).mem (-x) := by
  obtain ⟨h1, h2⟩ := ha
  constructor <;> · simp only [neg] at *; push_cast; nlinarith

theorem mul_mem {a b : Iv} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) : (a.mul b).mem (x * y) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  have hS := SOR_pos
  set X : ℝ := (SO:ℝ) * x with hX
  set Y : ℝ := (SO:ℝ) * y with hY
  have key : (SO:ℝ) * (x * y) * (SO:ℝ) = X * Y := by rw [hX, hY]; ring
  constructor
  · have hlo := le_mul_box (a1 := (a.lo:ℝ)) (a2 := (a.hi:ℝ)) (b1 := (b.lo:ℝ)) (b2 := (b.hi:ℝ))
      h1 h2 h3 h4
    have hmin : ((min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)) : ℤ) : ℝ)
        ≤ X * Y := by
      refine le_trans ?_ hlo
      push_cast [Int.cast_min]
      rfl
    have hf := flo_le (min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)))
    simp only [mul]
    have : ((flo (min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))) : ℤ) : ℝ)
        * (SO:ℝ) ≤ X * Y := le_trans hf hmin
    rw [← key] at this
    nlinarith
  · have hhi := mul_box_le (a1 := (a.lo:ℝ)) (a2 := (a.hi:ℝ)) (b1 := (b.lo:ℝ)) (b2 := (b.hi:ℝ))
      h1 h2 h3 h4
    have hmax : X * Y ≤
        ((max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)) : ℤ) : ℝ) := by
      refine le_trans hhi ?_
      push_cast [Int.cast_max]
      rfl
    have hf := le_fhi (max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)))
    simp only [mul]
    have : X * Y ≤
        ((fhi (max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))) : ℤ) : ℝ)
          * (SO:ℝ) := le_trans hmax hf
    rw [← key] at this
    nlinarith

theorem sqr_mem {a : Iv} {x : ℝ} (ha : a.mem x) : (a.sqr).mem (x * x) := by
  obtain ⟨h1, h2⟩ := ha
  have hS := SOR_pos
  set X : ℝ := (SO:ℝ) * x with hX
  have key : (SO:ℝ) * (x * x) * (SO:ℝ) = X * X := by rw [hX]; ring
  unfold sqr
  split_ifs with hlo hhi
  · have hlo' : (0:ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast hlo
    constructor
    · have hf := flo_le (a.lo * a.lo)
      have : ((a.lo * a.lo : ℤ):ℝ) ≤ X * X := by push_cast; nlinarith
      have h3 : ((flo (a.lo * a.lo) : ℤ):ℝ) * (SO:ℝ) ≤ X * X := le_trans hf this
      rw [← key] at h3; nlinarith
    · have hf := le_fhi (a.hi * a.hi)
      have : X * X ≤ ((a.hi * a.hi : ℤ):ℝ) := by push_cast; nlinarith
      have h3 : X * X ≤ ((fhi (a.hi * a.hi) : ℤ):ℝ) * (SO:ℝ) := le_trans this hf
      rw [← key] at h3; nlinarith
  · have hhi' : ((a.hi:ℤ):ℝ) ≤ 0 := by exact_mod_cast hhi
    constructor
    · have hf := flo_le (a.hi * a.hi)
      have : ((a.hi * a.hi : ℤ):ℝ) ≤ X * X := by push_cast; nlinarith
      have h3 : ((flo (a.hi * a.hi) : ℤ):ℝ) * (SO:ℝ) ≤ X * X := le_trans hf this
      rw [← key] at h3; nlinarith
    · have hf := le_fhi (a.lo * a.lo)
      have : X * X ≤ ((a.lo * a.lo : ℤ):ℝ) := by push_cast; nlinarith
      have h3 : X * X ≤ ((fhi (a.lo * a.lo) : ℤ):ℝ) * (SO:ℝ) := le_trans this hf
      rw [← key] at h3; nlinarith
  · constructor
    · have : (0:ℝ) ≤ X * X := mul_self_nonneg X
      rw [← key] at this
      push_cast
      nlinarith
    · have hf := le_fhi (max (a.lo * a.lo) (a.hi * a.hi))
      have hmax : X * X ≤ ((max (a.lo * a.lo) (a.hi * a.hi) : ℤ):ℝ) := by
        rcases le_total 0 X with h | h
        · have : X * X ≤ (a.hi:ℝ) * (a.hi:ℝ) := by nlinarith
          refine le_trans this ?_
          push_cast [Int.cast_max]
          exact le_max_right _ _
        · have : X * X ≤ (a.lo:ℝ) * (a.lo:ℝ) := by nlinarith
          refine le_trans this ?_
          push_cast [Int.cast_max]
          exact le_max_left _ _
      have h3 : X * X ≤ ((fhi (max (a.lo * a.lo) (a.hi * a.hi)) : ℤ):ℝ) * (SO:ℝ) :=
        le_trans hmax hf
      rw [← key] at h3; nlinarith

theorem mulInt_mem {a : Iv} {x : ℝ} {k : ℤ} (ha : a.mem x) : (a.mulInt k).mem (x * (k:ℝ)) := by
  obtain ⟨h1, h2⟩ := ha
  unfold mulInt
  split_ifs with hk
  · have hk' : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    constructor <;> · push_cast; nlinarith
  · have hk0 : k ≤ 0 := le_of_lt (not_le.mp hk)
    have hk' : ((k:ℤ):ℝ) ≤ 0 := by exact_mod_cast hk0
    constructor <;> · push_cast; nlinarith

theorem divInt_mem {a : Iv} {x : ℝ} {d : ℤ} (hd : 0 < d) (ha : a.mem x) :
    (a.divInt d).mem (x / (d:ℝ)) := by
  obtain ⟨h1, h2⟩ := ha
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  constructor
  · have h3 := ediv_le_of a.lo hd
    simp only [divInt]
    rw [le_div_iff₀ hd'] at h3
    have : (SO:ℝ) * (x / (d:ℝ)) * (d:ℝ) = (SO:ℝ) * x := by field_simp
    nlinarith
  · have h3 := le_cdiv_of a.hi hd
    simp only [divInt]
    rw [div_le_iff₀ hd'] at h3
    have : (SO:ℝ) * (x / (d:ℝ)) * (d:ℝ) = (SO:ℝ) * x := by field_simp
    nlinarith

theorem widen_mem {a : Iv} {x u : ℝ} {r : ℤ} (ha : a.mem x) (hr : |u - x| * (SO:ℝ) ≤ (r:ℝ)) :
    (a.widen r).mem u := by
  obtain ⟨h1, h2⟩ := ha
  have h3 : |u - x| * (SO:ℝ) ≤ (r:ℝ) := hr
  have hS := SOR_pos
  have h4 : -(r:ℝ) ≤ (u - x) * (SO:ℝ) ∧ (u - x) * (SO:ℝ) ≤ (r:ℝ) := by
    constructor
    · nlinarith [neg_abs_le (u - x), abs_nonneg (u - x), mul_le_mul_of_nonneg_right
        (neg_abs_le (u-x)) (le_of_lt hS)]
    · nlinarith [le_abs_self (u - x), mul_le_mul_of_nonneg_right (le_abs_self (u-x))
        (le_of_lt hS)]
  constructor <;> · simp only [widen]; push_cast; nlinarith [h4.1, h4.2]

theorem ofQ_mem {n d : ℤ} (hd : 0 < d) : (ofQ n d).mem ((n:ℝ) / (d:ℝ)) := by
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hS := SOR_pos
  constructor
  · have h3 := ediv_le_of (n * SO) hd
    simp only [ofQ]
    rw [le_div_iff₀ hd'] at h3
    push_cast at h3 ⊢
    have : (SO:ℝ) * ((n:ℝ) / (d:ℝ)) * (d:ℝ) = (n:ℝ) * (SO:ℝ) := by field_simp
    nlinarith
  · have h3 := le_cdiv_of (n * SO) hd
    simp only [ofQ]
    rw [div_le_iff₀ hd'] at h3
    push_cast at h3 ⊢
    have : (SO:ℝ) * ((n:ℝ) / (d:ℝ)) * (d:ℝ) = (n:ℝ) * (SO:ℝ) := by field_simp
    nlinarith

theorem ofInt_mem (n : ℤ) : (ofInt n).mem (n:ℝ) := by
  constructor <;> · simp only [ofInt]; refine le_of_eq ?_; push_cast; ring

theorem corner_lo {n d : ℤ} (hd : 0 < d) :
    (((n * SO) / d : ℤ) : ℝ) ≤ (n:ℝ) * ((SO:ℝ)/(d:ℝ)) := by
  have h := ediv_le_of (n * SO) hd
  refine le_trans h (le_of_eq ?_)
  push_cast
  ring

theorem corner_hi {n d : ℤ} (hd : 0 < d) :
    (n:ℝ) * ((SO:ℝ)/(d:ℝ)) ≤ -((((-(n * SO)) / d) : ℤ) : ℝ) := by
  have h := le_cdiv_of (n * SO) hd
  have h2 : (((-((-(n * SO)) / d)) : ℤ) : ℝ) = -((((-(n * SO)) / d) : ℤ) : ℝ) := by push_cast; ring
  rw [h2] at h
  refine le_trans (le_of_eq ?_) h
  push_cast
  ring

theorem div_mem {a b : Iv} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) :
    (a.div b).mem (x / y) := by
  unfold div
  split_ifs with hpos
  · obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
    have hS := SOR_pos
    have hblo : (0:ℝ) < (b.lo:ℝ) := by exact_mod_cast hpos
    have hbhi : (0:ℝ) < (b.hi:ℝ) := lt_of_lt_of_le hblo (le_trans h3 h4)
    have hbhiZ : (0:ℤ) < b.hi := by exact_mod_cast hbhi
    have hy : (0:ℝ) < y := by nlinarith
    have hu1 : (SO:ℝ)/(b.hi:ℝ) ≤ 1/y := by
      rw [div_le_div_iff₀ hbhi hy]
      nlinarith
    have hu2 : 1/y ≤ (SO:ℝ)/(b.lo:ℝ) := by
      rw [div_le_div_iff₀ hy hblo]
      nlinarith
    have hkey : (SO:ℝ) * (x / y) = ((SO:ℝ)*x) * (1/y) := by field_simp
    have hbox_le := mul_box_le (a1 := (a.lo:ℝ)) (a2 := (a.hi:ℝ))
      (b1 := (SO:ℝ)/(b.hi:ℝ)) (b2 := (SO:ℝ)/(b.lo:ℝ)) h1 h2 hu1 hu2
    have hbox_ge := le_mul_box (a1 := (a.lo:ℝ)) (a2 := (a.hi:ℝ))
      (b1 := (SO:ℝ)/(b.hi:ℝ)) (b2 := (SO:ℝ)/(b.lo:ℝ)) h1 h2 hu1 hu2
    simp only [EIv.mem_some, mem]
    rw [hkey]
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ hbox_ge
      push_cast [Int.cast_min]
      refine min_le_min (min_le_min (corner_lo hbhiZ) (corner_lo hpos))
        (min_le_min (corner_lo hbhiZ) (corner_lo hpos))
    · refine le_trans hbox_le ?_
      push_cast [Int.cast_max]
      refine max_le_max (max_le_max (corner_hi hbhiZ) (corner_hi hpos))
        (max_le_max (corner_hi hbhiZ) (corner_hi hpos))
  · trivial

end Iv

/-! ### The lifted (`Option`) layer -/

namespace EIv

def add (a b : EIv) : EIv :=
  match a, b with
  | some x, some y => some (x.add y)
  | _, _ => none

def sub (a b : EIv) : EIv :=
  match a, b with
  | some x, some y => some (x.sub y)
  | _, _ => none

def neg (a : EIv) : EIv :=
  match a with
  | some x => some x.neg
  | _ => none

def mul (a b : EIv) : EIv :=
  match a, b with
  | some x, some y => some (x.mul y)
  | _, _ => none

def sqr (a : EIv) : EIv :=
  match a with
  | some x => some x.sqr
  | _ => none

def mulInt (a : EIv) (k : ℤ) : EIv :=
  match a with
  | some x => some (x.mulInt k)
  | _ => none

def divInt (a : EIv) (d : ℤ) : EIv :=
  match a with
  | some x => some (x.divInt d)
  | _ => none

def widen (a : EIv) (r : ℤ) : EIv :=
  match a with
  | some x => some (x.widen r)
  | _ => none

def div (a b : EIv) : EIv :=
  match a, b with
  | some x, some y => x.div y
  | _, _ => none

theorem add_mem {a b : EIv} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) : (add a b).mem (x + y) := by
  cases a <;> cases b <;> simp_all [add, Iv.add_mem]

theorem sub_mem {a b : EIv} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) : (sub a b).mem (x - y) := by
  cases a <;> cases b <;> simp_all [sub, Iv.sub_mem]

theorem neg_mem {a : EIv} {x : ℝ} (ha : a.mem x) : (neg a).mem (-x) := by
  cases a <;> simp_all [neg, Iv.neg_mem]

theorem mul_mem {a b : EIv} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) : (mul a b).mem (x * y) := by
  cases a <;> cases b <;> simp_all [mul, Iv.mul_mem]

theorem sqr_mem {a : EIv} {x : ℝ} (ha : a.mem x) : (sqr a).mem (x * x) := by
  cases a <;> simp_all [sqr, Iv.sqr_mem]

theorem mulInt_mem {a : EIv} {x : ℝ} {k : ℤ} (ha : a.mem x) : (mulInt a k).mem (x * (k:ℝ)) := by
  cases a <;> simp_all [mulInt, Iv.mulInt_mem]

theorem divInt_mem {a : EIv} {x : ℝ} {d : ℤ} (hd : 0 < d) (ha : a.mem x) :
    (divInt a d).mem (x / (d:ℝ)) := by
  cases a <;> simp_all [divInt, Iv.divInt_mem hd]

theorem widen_mem {a : EIv} {x u : ℝ} {r : ℤ} (ha : a.mem x) (hr : |u - x| * (SO:ℝ) ≤ (r:ℝ)) :
    (widen a r).mem u := by
  cases a
  · trivial
  · exact Iv.widen_mem (by simpa using ha) hr

theorem div_mem {a b : EIv} {x y : ℝ} (ha : a.mem x) (hb : b.mem y) : (div a b).mem (x / y) := by
  cases a <;> cases b <;> simp_all [div, Iv.div_mem]

/-- The exact rational `n / d`. -/
def ofQ (n d : ℤ) : EIv := some (Iv.ofQ n d)

/-- The exact integer `n`. -/
def ofInt (n : ℤ) : EIv := some (Iv.ofInt n)

/-- The exact dyadic `n / 2^64`. -/
def pt (n : ℤ) : EIv := some ⟨n, n⟩

theorem ofQ_mem {n d : ℤ} (hd : 0 < d) : (ofQ n d).mem ((n:ℝ)/(d:ℝ)) := Iv.ofQ_mem hd

theorem ofInt_mem (n : ℤ) : (ofInt n).mem (n:ℝ) := Iv.ofInt_mem n

theorem pt_mem (n : ℤ) : (pt n).mem ((n:ℝ)/(SO:ℝ)) := by
  have hS := SOR_pos
  constructor <;> · rw [mul_div_assoc']; rw [mul_comm]
                    rw [mul_div_assoc, div_self (ne_of_gt hS), mul_one]

end EIv

end BandDual
