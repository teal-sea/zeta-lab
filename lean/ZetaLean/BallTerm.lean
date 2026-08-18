/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.Ball
import ZetaLean.DHCertSupport

/-!
# Dirichlet terms through the ball layer

`ZetaLean.Ball` builds the arithmetic — centre-plus-radius, its soundness, and
the exponential tower.  This file points it at the thing the rung-3 certificate
actually evaluates: `m^{-s}` for a natural `m` and an `s` ranging over a ball.

It is the ball counterpart of `IntervalCExp.dirichletTermBox2` and
`DHCertSupport.contains_cpow_mul_coarsen`, and it deliberately reuses the
*rectangle* layer's `Interval.logQ` unchanged.  There is no rotation in a real
logarithm, so a ball buys nothing there; `ofRealInterval` converts once, exactly,
and every subsequent operation — where the value does rotate — is a ball.

Measured consequence of that split, over all 215 sites of
`lean/cert/rung3_plan2.json` (`scripts/65_rung3_full_validation.py`):
110/110 big boxes, 104/104 grid sites and the centre all clear their own
thresholds, where the rectangle layer cleared none of the big boxes and the
centre could not clear its own at any parameters.
-/

open Complex

namespace ZetaLean

namespace ComplexBall

/-! ### A real interval as a ball

Exact: the minimal ball around a segment of the real axis has radius half its
length, so nothing is lost converting `logQ`'s output. -/

/-- A real `Interval` as a ball centred on the real axis. -/
def ofRealInterval (iv : Interval) : ComplexBall :=
  ⟨(iv.lo + iv.hi) / 2, 0, (iv.hi - iv.lo) / 2⟩

theorem contains_ofRealInterval {iv : Interval} {r : ℝ} (h : iv.contains r) :
    (ofRealInterval iv).contains ((r : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := h
  have hdiff : ((r : ℝ) : ℂ) - (ofRealInterval iv).centre
      = (((r - ((iv.lo + iv.hi) / 2 : ℚ) : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [ofRealInterval, centre]
  have hrad : ((ofRealInterval iv).rad : ℝ) = ((iv.hi : ℝ) - (iv.lo : ℝ)) / 2 := by
    simp [ofRealInterval] <;> push_cast <;> ring
  rw [contains, hdiff, Complex.norm_real, Real.norm_eq_abs, hrad, abs_le]
  constructor <;> push_cast <;> linarith

/-! ### The term `m^{-s}` -/

/-- The ball enclosing `m^{-s}`: `logQ` for `log m` (a real interval, converted
once), the complex product with `-s`, then the ball exponential tower. -/
def dirichletTermBallB (nLog nExp p kL kE : ℕ) (m : ℕ) (S : ComplexBall) :
    ComplexBall :=
  expCrB nExp p kE (mulA p S.neg (ofRealInterval (Interval.logQ nLog kL (m : ℚ))))

theorem contains_dirichletTermBallB {nLog nExp p kL kE : ℕ} (hnE : 0 < nExp)
    {m : ℕ} (hm : 0 < m) {S : ComplexBall} {s : ℂ} (hS : S.contains s)
    (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBoundB p (smulQ (1 / 2 ^ kE)
      (mulA p S.neg (ofRealInterval (Interval.logQ nLog kL (m : ℚ))))) ≤ 1) :
    (dirichletTermBallB nLog nExp p kL kE m S).contains ((m : ℂ) ^ (-s)) := by
  have hlogQ := Interval.contains_logQ (n := nLog) (k := kL) (q := (m : ℚ)) h0 h2
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlogQ
  have hL : (ofRealInterval (Interval.logQ nLog kL (m : ℚ))).contains
      ((Real.log m : ℝ) : ℂ) := contains_ofRealInterval hlogQ
  have hprod := contains_mulA p (contains_neg hS) hL
  have hexp := contains_expCrB hnE p kE hprod hb
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show ((m : ℂ) ^ (-s)) = Complex.exp (-s * ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hm0,
      show Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    , mul_comm]]
  exact hexp

/-! ### Composites cost one product, not a tower

`cpow` of a natural is multiplicative with no side condition, so only the primes
below `5K` need an exponential tower.  Rounding after the product is the same
discipline the tower already applies after every squaring, and for the same
reason: `mulA`'s radius is `ux·r₂ + uy·r₁ + r₁r₂`, which compounds denominators
if left unrounded. -/

theorem contains_cpow_mulB (p : ℕ) {a b : ℕ} {A B : ComplexBall} {s : ℂ}
    (hA : A.contains ((a : ℂ) ^ (-s))) (hB : B.contains ((b : ℂ) ^ (-s))) :
    (mulA p A B).contains (((a * b : ℕ) : ℂ) ^ (-s)) := by
  have h := contains_mulA p hA hB
  rwa [show (((a * b : ℕ) : ℂ) ^ (-s)) = ((a : ℂ) ^ (-s)) * ((b : ℂ) ^ (-s)) by
    rw [Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow a b (-s)]

/-- The composite step a generated certificate emits: multiply, then round. -/
theorem contains_cpow_mulB_coarsen (p : ℕ) {a b : ℕ} {A B : ComplexBall} {s : ℂ}
    (hA : A.contains ((a : ℂ) ^ (-s))) (hB : B.contains ((b : ℂ) ^ (-s))) :
    (coarsenB p (mulA p A B)).contains (((a * b : ℕ) : ℂ) ^ (-s)) :=
  contains_coarsenB p (contains_cpow_mulB p hA hB)

/-! ### The DH coefficient, as a ball

`kappaI` is the kernel-checked rational enclosure of `κ` in `DHAssembly`; the
DH coefficients are `1, κ, -κ, -1, 0` by residue mod 5. -/

/-- `κ` as a ball on the real axis, from the rectangle layer's enclosure. -/
def kappaBall : ComplexBall := ofRealInterval DH.kappaI

theorem contains_kappaBall : kappaBall.contains ((dh_kappa : ℝ) : ℂ) :=
  contains_ofRealInterval DH.contains_kappaI

end ComplexBall

end ZetaLean
