import Mathlib

/-!
# Frobenius traces of a Weierstrass family over `ZMod p`, certified

The one setting where the Riemann Hypothesis is a *theorem* is the function
field / finite field one, and `zeta/finitefield.py` is the laboratory's
computational face of it: curves over `F_p`, point counts, Frobenius
eigenvalues, Sato–Tate.  This file is the kernel-checked counterpart of two
exact statements about that family: the **first and second moments** of the
Frobenius trace over the whole Weierstrass family.

For an odd prime `p` and the affine equation `y² = x³ + a x + b`, the number of
affine points is `∑_x (1 + χ(x³ + a x + b))` with `χ` the quadratic character,
so the trace of Frobenius is

    a(a, b) = -∑_{x ∈ ZMod p} χ(x³ + a x + b).

Here `frobTrace p a b` is exactly that sum, and the two theorems prove

    ∑_{a} ∑_{b} a(a, b)  = 0,        ∑_{a} ∑_{b} a(a, b)² = p³ - p².

Both right-hand sides were checked numerically first, with exact integer
arithmetic, for p = 5, 7, 11, 13, 17, 19, 23, 29 before any Lean was written.

## What is proved

* `frobTrace_sum_b`: for fixed `a` and `x`, the inner sum over `b` of
  `χ(x³ + a x + b)` vanishes.  This is the whole content: `b ↦ x³ + a x + b`
  is a bijection of `ZMod p`, and a nontrivial multiplicative character sums to
  zero over the field (`quadraticChar_sum_zero`).
* `sum_frobTrace_eq_zero`: the first moment of the trace over the family is
  `0`.
* `sum_frobTrace_sq`: the **second** moment is `p³ - p²`, i.e. `p²(p - 1)`.
  The supporting shifted-character sum is `sum_quadraticChar_mul_shift`.

## What is NOT proved

* Nothing here is about the Riemann Hypothesis for `ζ`.  This is a statement
  about a family of Weierstrass *equations* over a finite field.  The repo's
  honest-scope rule applies in full: no computation and no formalization in
  this tree bears on RH.
* The sum runs over **all** pairs `(a, b) ∈ (ZMod p)²`, including the singular
  ones (`4a³ + 27b² = 0`), where `y² = x³ + a x + b` is not an elliptic curve
  and `frobTrace` is a character sum rather than a trace of Frobenius on a
  curve.  That is deliberate: summing over all pairs is *why* the proof is
  short.  The restriction to the nonsingular family is a different statement
  with a different right-hand side (an independent measurement of the second
  moment over nonsingular pairs gives `(p-1)²(p+1)`, not `p³ - p²`) and is not
  claimed here.
* `frobTrace` is *defined* by the character sum.  That it equals the trace of
  Frobenius acting on the ℓ-adic Tate module of the corresponding elliptic
  curve, the identification that makes the name honest, is standard but is
  not formalized here; no Hasse bound is claimed either.

House rule carried over: nothing counts until it compiles with zero `sorry`s.
Checked: `#print axioms` on both theorems reports only `propext`,
`Classical.choice`, `Quot.sound`: no `sorryAx`.
-/

open Finset

namespace ZetaLean.FiniteFieldTrace

variable (p : ℕ) [Fact p.Prime]

/-- The Frobenius trace attached to the Weierstrass equation
`y² = x³ + a x + b` over `ZMod p`, defined by the character sum
`-∑_x χ(x³ + a x + b)`.

For nonsingular `(a, b)` and odd `p` this is the trace of Frobenius, since the
affine point count is `∑_x (1 + χ(x³ + a x + b)) = p - a(a,b)`.  For singular
`(a, b)` it is just the character sum; see the module docstring. -/
def frobTrace (a b : ZMod p) : ℤ :=
  -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b)

/-- For an odd prime `p`, the ring characteristic of `ZMod p` is not `2`. -/
theorem ringChar_ne_two (hp : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact_mod_cast hp

/-- The inner sum vanishes: for fixed `a` and `x`, translating by the constant
`x³ + a x` permutes `ZMod p`, so `∑_b χ(x³ + a x + b) = ∑_u χ(u) = 0`. -/
theorem frobTrace_sum_b (hp : p ≠ 2) (a x : ZMod p) :
    ∑ b : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) = 0 := by
  have h : ∑ b : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b)
      = ∑ u : ZMod p, quadraticChar (ZMod p) u :=
    Fintype.sum_equiv (Equiv.addLeft (x ^ 3 + a * x)) _ _ (fun _ => rfl)
  rw [h, quadraticChar_sum_zero (ringChar_ne_two p hp)]

/-- **First moment.**  Summed over the whole family of Weierstrass equations
`y² = x³ + a x + b` with `(a, b) ∈ (ZMod p)²`, `p` an odd prime, the Frobenius
traces cancel exactly:

    ∑_{a} ∑_{b} a(a, b) = 0.

Scope: all pairs, singular ones included; this is a statement about a family of
equations over a finite field, not about the Riemann Hypothesis. -/
theorem sum_frobTrace_eq_zero (hp : p ≠ 2) :
    ∑ a : ZMod p, ∑ b : ZMod p, frobTrace p a b = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  simp only [frobTrace, Finset.sum_neg_distrib, neg_eq_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun x _ => frobTrace_sum_b p hp a x

/-! ### The second moment -/

/-- The shifted quadratic-character sum: for `d ≠ 0`,
`∑_u χ(u) χ(u + d) = -1`.

Reindexing `u = -d x` turns the sum into `χ(-d) χ(d) · J(χ, χ)`, and
`J(χ, χ) = J(χ, χ⁻¹) = -χ(-1)` since the quadratic character is its own
inverse. -/
theorem sum_quadraticChar_mul_shift (hp : p ≠ 2) {d : ZMod p} (hd : d ≠ 0) :
    ∑ u : ZMod p, quadraticChar (ZMod p) u * quadraticChar (ZMod p) (u + d) = -1 := by
  have hχ : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one (ringChar_ne_two p hp)
  have hj : jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p))
      = -quadraticChar (ZMod p) (-1) := by
    have h := jacobiSum_nontrivial_inv (R := ℤ) hχ
    rwa [(quadraticChar_isQuadratic (ZMod p)).inv] at h
  have hne : (-d) ≠ 0 := neg_ne_zero.mpr hd
  have hreindex :
      ∑ x : ZMod p, quadraticChar (ZMod p) (-d * x) * quadraticChar (ZMod p) (-d * x + d)
        = ∑ u : ZMod p, quadraticChar (ZMod p) u * quadraticChar (ZMod p) (u + d) :=
    Fintype.sum_equiv (Equiv.mulLeft₀ (-d) hne) _ _ (fun _ => rfl)
  rw [← hreindex]
  have hterm : ∀ x : ZMod p,
      quadraticChar (ZMod p) (-d * x) * quadraticChar (ZMod p) (-d * x + d)
        = (quadraticChar (ZMod p) (-d) * quadraticChar (ZMod p) d) *
          (quadraticChar (ZMod p) x * quadraticChar (ZMod p) (1 - x)) := by
    intro x
    have hx : -d * x + d = d * (1 - x) := by ring
    rw [hx, map_mul, map_mul]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum, ← jacobiSum, hj]
  have hdd : quadraticChar (ZMod p) (-d) * quadraticChar (ZMod p) d
      = quadraticChar (ZMod p) (-1) := by
    rw [← map_mul]
    have : (-d) * d = -1 * d ^ 2 := by ring
    rw [this, map_mul, quadraticChar_sq_one' hd, mul_one]
  rw [hdd]
  have hone : ((-1 : ZMod p)) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have := quadraticChar_sq_one (F := ZMod p) hone
  nlinarith [this]

/-- The unshifted case: `∑_u χ(u)² = p - 1`, since `χ(u)² = 1` off zero. -/
theorem sum_quadraticChar_sq :
    ∑ u : ZMod p, quadraticChar (ZMod p) u * quadraticChar (ZMod p) u = (p : ℤ) - 1 := by
  have hterm : ∀ u : ZMod p, quadraticChar (ZMod p) u * quadraticChar (ZMod p) u
      = (1 : ℤ) - (if u = 0 then 1 else 0) := by
    intro u
    by_cases h : u = 0
    · simp [h]
    · rw [if_neg h, sub_zero, ← pow_two, quadraticChar_sq_one h]
  simp only [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (0 : ZMod p) (fun _ => (1 : ℤ))]
  simp [ZMod.card]

/-- The inner sum over `b`, for fixed `a`, `x`, `y`.  Translating `b` so that
`x³ + a x + b` becomes the summation variable turns it into a shifted
quadratic-character sum whose shift is `(y - x)(x² + xy + y² + a)`. -/
theorem sum_b_pair (hp : p ≠ 2) (a x y : ZMod p) :
    ∑ b : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) *
        quadraticChar (ZMod p) (y ^ 3 + a * y + b)
      = if (y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0 then (p : ℤ) - 1 else -1 := by
  set d : ZMod p := (y - x) * (x ^ 2 + x * y + y ^ 2 + a) with hd
  have hre : ∑ b : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) *
        quadraticChar (ZMod p) (y ^ 3 + a * y + b)
      = ∑ u : ZMod p, quadraticChar (ZMod p) u * quadraticChar (ZMod p) (u + d) := by
    refine Fintype.sum_equiv (Equiv.addLeft (x ^ 3 + a * x)) _ _ (fun b => ?_)
    have hb : y ^ 3 + a * y + b = (x ^ 3 + a * x + b) + d := by rw [hd]; ring
    rw [hb]
    rfl
  rw [hre]
  by_cases h : d = 0
  · rw [if_pos h, h]
    simpa using sum_quadraticChar_sq p
  · rw [if_neg h]
    exact sum_quadraticChar_mul_shift p hp h

/-- For `x ≠ y` the `a`-sum of the inner values cancels: exactly one `a` makes
the shift vanish (contributing `p - 1`), and the other `p - 1` values of `a`
each contribute `-1`. -/
theorem sum_a_off_diag {x y : ZMod p} (hxy : y ≠ x) :
    ∑ a : ZMod p, (if (y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0 then (p : ℤ) - 1 else -1)
      = 0 := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy
  have hcond : ∀ a : ZMod p,
      ((y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0) ↔ (a = -(x ^ 2 + x * y + y ^ 2)) := by
    intro a
    rw [mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hyx
      · linear_combination h
    · intro h
      right
      rw [h]; ring
  have hterm : ∀ a : ZMod p,
      (if (y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0 then (p : ℤ) - 1 else -1)
        = -1 + (if a = -(x ^ 2 + x * y + y ^ 2) then (p : ℤ) else 0) := by
    intro a
    rw [if_congr (hcond a) rfl rfl]
    by_cases h : a = -(x ^ 2 + x * y + y ^ 2)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  simp only [hterm]
  rw [Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (-(x ^ 2 + x * y + y ^ 2)) (fun _ => (p : ℤ))]
  simp [ZMod.card]

/-- **Second moment.**  Over the whole family of Weierstrass equations
`y² = x³ + a x + b` with `(a, b) ∈ (ZMod p)²`, `p` an odd prime,

    ∑_{a} ∑_{b} a(a, b)² = p³ - p²  (= p²(p - 1)).

Only the diagonal `x = y` of the doubled character sum survives: it contributes
`p·(p-1)` for each of the `p` values of `x`, and every off-diagonal pair
contributes exactly `0`.

Scope, again: all pairs `(a, b)`, singular ones included.  The nonsingular
subfamily obeys a *different* identity (`(p-1)²(p+1)`), which is not proved
here.  Nothing in this file bears on the Riemann Hypothesis for `ζ`. -/
theorem sum_frobTrace_sq (hp : p ≠ 2) :
    ∑ a : ZMod p, ∑ b : ZMod p, (frobTrace p a b) ^ 2 = (p : ℤ) ^ 3 - (p : ℤ) ^ 2 := by
  have hsq : ∀ a b : ZMod p, (frobTrace p a b) ^ 2
      = ∑ x : ZMod p, ∑ y : ZMod p,
          quadraticChar (ZMod p) (x ^ 3 + a * x + b) *
            quadraticChar (ZMod p) (y ^ 3 + a * y + b) := by
    intro a b
    rw [frobTrace, neg_sq, pow_two, Fintype.sum_mul_sum]
  -- for fixed `a`, sum over `b` and reduce to the `x`, `y` grid
  have inner : ∀ a : ZMod p, ∑ b : ZMod p, (frobTrace p a b) ^ 2
      = ∑ x : ZMod p, ∑ y : ZMod p,
          (if (y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0 then (p : ℤ) - 1 else -1) := by
    intro a
    calc ∑ b : ZMod p, (frobTrace p a b) ^ 2
        = ∑ b : ZMod p, ∑ x : ZMod p, ∑ y : ZMod p,
            quadraticChar (ZMod p) (x ^ 3 + a * x + b) *
              quadraticChar (ZMod p) (y ^ 3 + a * y + b) := by simp only [hsq]
      _ = ∑ x : ZMod p, ∑ b : ZMod p, ∑ y : ZMod p,
            quadraticChar (ZMod p) (x ^ 3 + a * x + b) *
              quadraticChar (ZMod p) (y ^ 3 + a * y + b) := Finset.sum_comm
      _ = ∑ x : ZMod p, ∑ y : ZMod p, ∑ b : ZMod p,
            quadraticChar (ZMod p) (x ^ 3 + a * x + b) *
              quadraticChar (ZMod p) (y ^ 3 + a * y + b) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ x : ZMod p, ∑ y : ZMod p,
            (if (y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0 then (p : ℤ) - 1 else -1) :=
            Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => sum_b_pair p hp a x y
  simp only [inner]
  -- reorder to put the `a`-sum innermost
  have reorder : ∑ a : ZMod p, ∑ x : ZMod p, ∑ y : ZMod p,
        (if (y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0 then (p : ℤ) - 1 else -1)
      = ∑ x : ZMod p, ∑ y : ZMod p, ∑ a : ZMod p,
        (if (y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0 then (p : ℤ) - 1 else -1) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [reorder]
  have diag : ∀ x : ZMod p, ∑ y : ZMod p, ∑ a : ZMod p,
      (if (y - x) * (x ^ 2 + x * y + y ^ 2 + a) = 0 then (p : ℤ) - 1 else -1)
        = (p : ℤ) * ((p : ℤ) - 1) := by
    intro x
    rw [Finset.sum_eq_single x (fun y _ hy => sum_a_off_diag p hy)
      (fun h => absurd (Finset.mem_univ x) h)]
    simp [ZMod.card]
    ring
  rw [Finset.sum_congr rfl fun x _ => diag x]
  simp [ZMod.card]
  ring

end ZetaLean.FiniteFieldTrace
