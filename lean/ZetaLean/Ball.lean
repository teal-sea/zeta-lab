/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.IntervalCExp

/-!
# Complex ball enclosures

The second enclosure primitive, alongside `ComplexInterval`.  A ball is an exact
Gaussian-rational centre plus a rational radius, denoting `{z : ‖z - c‖ ≤ r}`.

**Why a second one.**  `docs/25` §4.3 measured the boxed-`s` width constant of
the rung-3 certificate at `ρ_W ≈ 5.9` against a planned `2.6`, and isolated the
cause: a rectangle is not rotation-invariant, so each of `expCr`'s `kE`
squarings pays for wrapping a rotating value in an axis-aligned box.  A ball is
rotation-invariant and does not.  Measured in the Python mirror over the same 15
big boxes (`scripts/62_rung3_rho_w.py --arith ball`), `ρ_W` falls to `0.37`, a
13.7× reduction, and every site of the certificate — 15 of 15 big boxes, 8 of 8
grid sites, and the centre — passes at plan v2's existing geometry.

Two structural gains, not just a tighter constant:

* `normBound` is `‖c‖ + r`, where the rectangle's is the L1
  `max|re| + max|im| + 2r`.  The rectangle form charges an inflation radius
  **twice**, which is why the centre could not pass at any parameters
  (`docs/25` §4.3 defect 1): `2·r_c = 7.47e-4` already exceeds `ε' = 5e-4`.
* Products no longer wrap, so widths stop compounding through the tower.

**No invariant field.**  `ComplexInterval` carries `lo ≤ hi` as a proof field;
this structure deliberately carries nothing.  A negative radius makes `contains`
unsatisfiable rather than unsound (norms are non-negative), so the invariant buys
no safety, and a proof field in *data* is paid on every kernel evaluation.  The
non-negativity each soundness theorem needs is a hypothesis there instead.

**Moduli are arguments, not computations.**  `‖c‖` is irrational in general, so
every operation whose radius needs it (`mul`, `normBound`, `normLower`) takes a
rational bound as an explicit argument and the soundness theorem takes the
inequality as a hypothesis.  `norm_centre_le` / `le_norm_centre` reduce those to
one rational inequality apiece, which `norm_num` discharges at a generated call
site — the same shape as the rest of the certificate, where "every hypothesis
beyond two structural containments is a rational inequality".
-/

open Complex

namespace ZetaLean

/-- A complex ball: exact Gaussian-rational centre, rational radius.  Carries no
invariant — see the module docstring. -/
structure ComplexBall where
  cre : ℚ
  cim : ℚ
  rad : ℚ
  deriving Repr, DecidableEq

namespace ComplexBall

/-- The centre, as a complex number. -/
def centre (x : ComplexBall) : ℂ := ⟨(x.cre : ℝ), (x.cim : ℝ)⟩

/-- The set of complex numbers the ball encloses. -/
def contains (x : ComplexBall) (z : ℂ) : Prop := ‖z - x.centre‖ ≤ (x.rad : ℝ)

theorem rad_nonneg_of_contains {x : ComplexBall} {z : ℂ} (h : x.contains z) :
    0 ≤ (x.rad : ℝ) :=
  le_trans (norm_nonneg _) h

/-! ### Moduli of the centre, as rational inequalities -/

theorem norm_centre_sq (x : ComplexBall) :
    ‖x.centre‖ ^ 2 = ((x.cre ^ 2 + x.cim ^ 2 : ℚ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [centre]
  push_cast
  ring

/-- An upper bound on `‖c‖` from one rational inequality: `cre² + cim² ≤ u²`. -/
theorem norm_centre_le {x : ComplexBall} {u : ℚ} (hu : 0 ≤ u)
    (h : x.cre ^ 2 + x.cim ^ 2 ≤ u ^ 2) : ‖x.centre‖ ≤ (u : ℝ) := by
  have hu' : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hsq : ‖x.centre‖ ^ 2 ≤ ((u : ℝ)) ^ 2 := by
    rw [norm_centre_sq]; exact_mod_cast h
  nlinarith [norm_nonneg x.centre]

/-- A lower bound on `‖c‖` from one rational inequality: `l² ≤ cre² + cim²`. -/
theorem le_norm_centre {x : ComplexBall} {l : ℚ} (hl : 0 ≤ l)
    (h : l ^ 2 ≤ x.cre ^ 2 + x.cim ^ 2) : (l : ℝ) ≤ ‖x.centre‖ := by
  have hl' : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hsq : ((l : ℝ)) ^ 2 ≤ ‖x.centre‖ ^ 2 := by
    rw [norm_centre_sq]; exact_mod_cast h
  nlinarith [norm_nonneg x.centre]

/-! ### The exact operations: addition, negation, scaling -/

/-- The degenerate ball `{q + ri}`. -/
def exact (q r : ℚ) : ComplexBall := ⟨q, r, 0⟩

theorem contains_exact (q r : ℚ) :
    (exact q r).contains ⟨(q : ℝ), (r : ℝ)⟩ := by
  simp [contains, exact, centre]

def add (x y : ComplexBall) : ComplexBall :=
  ⟨x.cre + y.cre, x.cim + y.cim, x.rad + y.rad⟩

theorem contains_add {x y : ComplexBall} {a b : ℂ}
    (hx : x.contains a) (hy : y.contains b) : (x.add y).contains (a + b) := by
  have h : a + b - (x.add y).centre = (a - x.centre) + (b - y.centre) := by
    apply Complex.ext <;> simp [add, centre] <;> push_cast <;> ring
  rw [contains, h]
  refine le_trans (norm_add_le _ _) ?_
  push_cast [add]
  exact add_le_add hx hy

def neg (x : ComplexBall) : ComplexBall := ⟨-x.cre, -x.cim, x.rad⟩

theorem contains_neg {x : ComplexBall} {a : ℂ} (hx : x.contains a) :
    x.neg.contains (-a) := by
  have h : -a - x.neg.centre = -(a - x.centre) := by
    apply Complex.ext <;> simp [neg, centre] <;> push_cast <;> ring
  rw [contains, h, norm_neg]
  exact hx

def sub (x y : ComplexBall) : ComplexBall := x.add y.neg

theorem contains_sub {x y : ComplexBall} {a b : ℂ}
    (hx : x.contains a) (hy : y.contains b) : (x.sub y).contains (a - b) :=
  sub_eq_add_neg a b ▸ contains_add hx (contains_neg hy)

/-- Scaling by an exact rational: the radius scales by `|q|`. -/
def smulQ (q : ℚ) (x : ComplexBall) : ComplexBall :=
  ⟨q * x.cre, q * x.cim, |q| * x.rad⟩

theorem contains_smulQ {q : ℚ} {x : ComplexBall} {a : ℂ} (hx : x.contains a) :
    (smulQ q x).contains ((q : ℂ) * a) := by
  have h : (q : ℂ) * a - (smulQ q x).centre = (q : ℂ) * (a - x.centre) := by
    apply Complex.ext <;> simp [smulQ, centre] <;> push_cast <;> ring
  rw [contains, h, norm_mul]
  have hq : ‖(q : ℂ)‖ = ((|q| : ℚ) : ℝ) := by
    rw [show ((q : ℂ)) = (((q : ℝ) : ℂ)) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    push_cast
    rfl
  rw [hq]
  push_cast [smulQ]
  exact mul_le_mul_of_nonneg_left hx (by positivity)

def halve (x : ComplexBall) : ComplexBall := smulQ (1 / 2) x

/-- Widening by an explicit radius — the tail-bound step. -/
def inflate (x : ComplexBall) (r : ℚ) : ComplexBall := ⟨x.cre, x.cim, x.rad + |r|⟩

theorem contains_inflate {x : ComplexBall} {z : ℂ} (r : ℚ) (hx : x.contains z) :
    (x.inflate r).contains z := by
  have hc : (x.inflate r).centre = x.centre := rfl
  have hx' : ‖z - x.centre‖ ≤ (x.rad : ℝ) := hx
  rw [contains, hc]
  push_cast [inflate]
  have : (0 : ℝ) ≤ |(r : ℝ)| := abs_nonneg _
  linarith

/-! ### The product — where the rotation waste goes away

`(c₁+d₁)(c₂+d₂) - c₁c₂ = c₁d₂ + c₂d₁ + d₁d₂`, so the radius grows at the true
first-order rate `‖c₁‖r₂ + ‖c₂‖r₁ + r₁r₂` with no term for orientation.  The
rectangle product has no such form: it takes the min/max of four corner
products componentwise, and a rotated rectangle needs a strictly larger
axis-aligned box, which is the `ρ_W` penalty compounding over `kE` squarings. -/

/-- Ball product.  `ux`, `uy` are rational upper bounds for `‖x.centre‖` and
`‖y.centre‖`; supply them with `norm_centre_le`. -/
def mul (x y : ComplexBall) (ux uy : ℚ) : ComplexBall :=
  ⟨x.cre * y.cre - x.cim * y.cim,
   x.cre * y.cim + x.cim * y.cre,
   ux * y.rad + uy * x.rad + x.rad * y.rad⟩

theorem contains_mul {x y : ComplexBall} {a b : ℂ} {ux uy : ℚ}
    (hux : ‖x.centre‖ ≤ (ux : ℝ)) (huy : ‖y.centre‖ ≤ (uy : ℝ))
    (hx : x.contains a) (hy : y.contains b) :
    (x.mul y ux uy).contains (a * b) := by
  have hxr : (0 : ℝ) ≤ (x.rad : ℝ) := rad_nonneg_of_contains hx
  have hyr : (0 : ℝ) ≤ (y.rad : ℝ) := rad_nonneg_of_contains hy
  have hkey : a * b - (x.mul y ux uy).centre
      = x.centre * (b - y.centre) + y.centre * (a - x.centre)
        + (a - x.centre) * (b - y.centre) := by
    apply Complex.ext <;> simp [mul, centre] <;> push_cast <;> ring
  rw [contains, hkey]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) (le_refl _)) ?_
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖x.centre‖ * ‖b - y.centre‖ ≤ (ux : ℝ) * (y.rad : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hux hyr)
  have h2 : ‖y.centre‖ * ‖a - x.centre‖ ≤ (uy : ℝ) * (x.rad : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
      (mul_le_mul_of_nonneg_right huy hxr)
  have h3 : ‖a - x.centre‖ * ‖b - y.centre‖ ≤ (x.rad : ℝ) * (y.rad : ℝ) :=
    mul_le_mul hx hy (norm_nonneg _) hxr
  push_cast [mul]
  linarith

/-! ### Outward rounding

`Interval.coarsen` rounds endpoints outward; the ball analogue rounds the
*centre* and moves the displacement into the radius.  The displacement is
bounded by `|Δre| + |Δim|`, so no square root is needed: it costs at most a
factor `√2` on a quantity of size `2^{-p}`, and buys a sqrt-free lemma. -/

/-- Round the centre to a multiple of `2^{-p}`, paying the displacement in the
radius.  `nre`/`nim` are the rounded centre, supplied by the caller (the
generator computes them; the kernel only checks the inequality). -/
def recentre (x : ComplexBall) (nre nim : ℚ) : ComplexBall :=
  ⟨nre, nim, x.rad + (|x.cre - nre| + |x.cim - nim|)⟩

theorem contains_recentre {x : ComplexBall} {z : ℂ} (nre nim : ℚ)
    (hx : x.contains z) : (x.recentre nre nim).contains z := by
  have hsplit : z - (x.recentre nre nim).centre
      = (z - x.centre) + (x.centre - (x.recentre nre nim).centre) := by ring
  rw [contains, hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hd : ‖x.centre - (x.recentre nre nim).centre‖
      ≤ ((|x.cre - nre| + |x.cim - nim| : ℚ) : ℝ) := by
    have : x.centre - (x.recentre nre nim).centre
        = ⟨((x.cre - nre : ℚ) : ℝ), ((x.cim - nim : ℚ) : ℝ)⟩ := by
      apply Complex.ext <;> simp [recentre, centre] <;> push_cast <;> ring
    rw [this]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    push_cast
    simp
  have hx' : ‖z - x.centre‖ ≤ (x.rad : ℝ) := hx
  push_cast [recentre] at hd ⊢
  linarith

/-! ### Reading bounds off a ball

Both are strictly tighter than the rectangle forms, and `normBound` charges an
inflation radius once rather than twice. -/

/-- `‖z‖ ≤ u + r` for `z` in the ball, given `‖c‖ ≤ u`. -/
theorem norm_le_normBound {x : ComplexBall} {z : ℂ} {u : ℚ}
    (hu : ‖x.centre‖ ≤ (u : ℝ)) (hx : x.contains z) :
    ‖z‖ ≤ ((u + x.rad : ℚ) : ℝ) := by
  have : z = x.centre + (z - x.centre) := by ring
  rw [this]
  refine le_trans (norm_add_le _ _) ?_
  push_cast
  exact add_le_add hu hx

/-- `l - r ≤ ‖z‖` for `z` in the ball, given `l ≤ ‖c‖`.  This is the lower bound
the frontier certificate reads, and it is where the ball wins outright: the
rectangle's `normLower` is the larger of two componentwise distances to zero and
ignores the other component entirely. -/
theorem normLower_le_norm {x : ComplexBall} {z : ℂ} {l : ℚ}
    (hl : (l : ℝ) ≤ ‖x.centre‖) (hx : x.contains z) :
    ((l - x.rad : ℚ) : ℝ) ≤ ‖z‖ := by
  have hrev : ‖x.centre‖ - ‖z‖ ≤ ‖x.centre - z‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev] at hrev
  have hx' : ‖z - x.centre‖ ≤ (x.rad : ℝ) := hx
  push_cast
  linarith

/-- The `q ≤ ‖z‖` form a generated site states, matching
`DHCertSupport`'s reading for rectangles. -/
theorem le_norm_of_normLower {x : ComplexBall} {z : ℂ} {l q : ℚ}
    (hl : (l : ℝ) ≤ ‖x.centre‖) (hx : x.contains z) (h : q ≤ l - x.rad) :
    (q : ℝ) ≤ ‖z‖ :=
  le_trans (by exact_mod_cast h) (normLower_le_norm hl hx)

/-! ### From a rectangle to a ball

Every site of the rung-3 certificate is a *segment* of a square's frontier, i.e.
a rectangle degenerate in one direction, and the minimal enclosing ball of a
segment has radius exactly half its length.  So the conversion at the input of
the evaluation costs no enclosure at all — the whole gain is downstream, in the
product chain. -/

/-- The ball around a rectangle, given a rational bound `hw` on the half-diagonal.
For a segment, `hw` is exactly half the length and the conversion is lossless. -/
def ofInterval (B : ComplexInterval) (hw : ℚ) : ComplexBall :=
  ⟨(B.re.lo + B.re.hi) / 2, (B.im.lo + B.im.hi) / 2, hw⟩

theorem contains_ofInterval {B : ComplexInterval} {z : ℂ} {hw : ℚ}
    (hb : B.contains z)
    (h : ((B.re.hi - B.re.lo) / 2) ^ 2 + ((B.im.hi - B.im.lo) / 2) ^ 2 ≤ hw ^ 2)
    (hw0 : 0 ≤ hw) : (ofInterval B hw).contains z := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hb
  have hre : |z.re - (((B.re.lo + B.re.hi) / 2 : ℚ) : ℝ)|
      ≤ (((B.re.hi - B.re.lo) / 2 : ℚ) : ℝ) := by
    rw [abs_le]; push_cast; constructor <;> linarith
  have him : |z.im - (((B.im.lo + B.im.hi) / 2 : ℚ) : ℝ)|
      ≤ (((B.im.hi - B.im.lo) / 2 : ℚ) : ℝ) := by
    rw [abs_le]; push_cast; constructor <;> linarith
  obtain ⟨hre1, hre2⟩ := abs_le.mp hre
  obtain ⟨him1, him2⟩ := abs_le.mp him
  have hsqre := sq_le_sq' hre1 hre2
  have hsqim := sq_le_sq' him1 him2
  have hcast : (((B.re.hi - B.re.lo) / 2 : ℚ) : ℝ) ^ 2
      + (((B.im.hi - B.im.lo) / 2 : ℚ) : ℝ) ^ 2 ≤ ((hw : ℝ)) ^ 2 := by
    exact_mod_cast h
  have hn : ‖z - (ofInterval B hw).centre‖ ^ 2 ≤ ((hw : ℝ)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have e1 : (z - (ofInterval B hw).centre).re
        = z.re - (((B.re.lo + B.re.hi) / 2 : ℚ) : ℝ) := rfl
    have e2 : (z - (ofInterval B hw).centre).im
        = z.im - (((B.im.lo + B.im.hi) / 2 : ℚ) : ℝ) := rfl
    rw [e1, e2]
    nlinarith [hsqre, hsqim, hcast]
  have hw' : (0 : ℝ) ≤ (hw : ℝ) := by exact_mod_cast hw0
  have hrad : ((ofInterval B hw).rad : ℝ) = (hw : ℝ) := rfl
  show ‖z - (ofInterval B hw).centre‖ ≤ ((ofInterval B hw).rad : ℝ)
  rw [hrad]
  nlinarith [norm_nonneg (z - (ofInterval B hw).centre)]

end ComplexBall

end ZetaLean
