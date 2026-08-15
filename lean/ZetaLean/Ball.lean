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


/-! ### A computable rational upper bound for `‖c‖`

The product needs `‖c‖` bounded above by a rational.  Two routes were measured
in the Python mirror before either was formalized
(`scripts/62_rung3_rho_w.py --arith ball --absmode {sqrt,l1}`):

* `|cre| + |cim|` needs no square root and proves in one line from
  `Complex.norm_le_abs_re_add_abs_im`, but it is loose by up to `√2` per
  product, and **that looseness compounds through the `kE` squarings**: `ρ_W`
  goes back to `5.6-6.8` and 13 of 15 big boxes fail again.  The shortcut
  destroys the entire gain.
* The tight rational square root keeps `ρ_W` at `0.37` and all 15 pass.

So tightness here is load-bearing, not a refinement, and `Nat.sqrt` earns its
place.  `sqrtUpperQ q p` is the smallest `k / 2^p` whose square is at least `q`,
computed by one `Nat.sqrt` — which the kernel evaluates on GMP-backed naturals. -/

/-- Smallest `k / 2^p` with `k : ℕ` whose square is at least `q`. -/
def sqrtUpperQ (q : ℚ) (p : ℕ) : ℚ :=
  ((Nat.sqrt ((q.num.toNat * 4 ^ p) / q.den) + 1 : ℕ) : ℚ) / ((2 ^ p : ℕ) : ℚ)

theorem sqrtUpperQ_nonneg (q : ℚ) (p : ℕ) : 0 ≤ sqrtUpperQ q p := by
  unfold sqrtUpperQ
  positivity

theorem le_sq_sqrtUpperQ {q : ℚ} (hq : 0 ≤ q) (p : ℕ) :
    q ≤ (sqrtUpperQ q p) ^ 2 := by
  have hb0 : 0 < q.den := q.pos
  have hb0' : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast hb0
  -- `M < k*k` for `k = sqrt M + 1`, then clear the floor division.
  have h1 : q.num.toNat * 4 ^ p / q.den
      < (Nat.sqrt (q.num.toNat * 4 ^ p / q.den) + 1)
        * (Nat.sqrt (q.num.toNat * 4 ^ p / q.den) + 1) := by
    have h := Nat.lt_succ_sqrt' (q.num.toNat * 4 ^ p / q.den)
    simpa [pow_two] using h
  have hlt : q.num.toNat * 4 ^ p
      < ((Nat.sqrt (q.num.toNat * 4 ^ p / q.den) + 1)
        * (Nat.sqrt (q.num.toNat * 4 ^ p / q.den) + 1)) * q.den :=
    (Nat.div_lt_iff_lt_mul hb0).mp h1
  have hltQ : ((q.num.toNat : ℚ)) * (4 : ℚ) ^ p
      ≤ (((Nat.sqrt (q.num.toNat * 4 ^ p / q.den) + 1 : ℕ) : ℚ)
        * ((Nat.sqrt (q.num.toNat * 4 ^ p / q.den) + 1 : ℕ) : ℚ)) * (q.den : ℚ) := by
    exact_mod_cast hlt.le
  -- `q = num / den` with `num = toNat num` because `q` is non-negative.
  have hnum : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    have := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
  have hqv : q = ((q.num.toNat : ℕ) : ℚ) / (q.den : ℚ) := by
    rw [hnum]; exact (Rat.num_div_den q).symm
  have hexp : sqrtUpperQ q p
      = ((Nat.sqrt (q.num.toNat * 4 ^ p / q.den) + 1 : ℕ) : ℚ) / (2 : ℚ) ^ p := by
    unfold sqrtUpperQ; push_cast; ring
  have h4 : ((2 : ℚ) ^ p) ^ 2 = (4 : ℚ) ^ p := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  -- Rewrite `sqrtUpperQ` away FIRST.  Rewriting `q = num/den` before this point
  -- also fires inside `sqrtUpperQ`'s own body, leaving `(num/den).num.toNat`.
  rw [hexp, div_pow, h4, le_div_iff₀ (by positivity : (0:ℚ) < (4:ℚ) ^ p)]
  have hqd : q * (q.den : ℚ) = ((q.num.toNat : ℕ) : ℚ) := by
    rw [hnum]; exact_mod_cast q.mul_den_eq_num
  push_cast at hltQ ⊢
  nlinarith [hltQ, hqd, hb0']

/-- A rational upper bound on `‖c‖`, computed. -/
def absUpper (p : ℕ) (x : ComplexBall) : ℚ := sqrtUpperQ (x.cre ^ 2 + x.cim ^ 2) p

theorem norm_centre_le_absUpper (p : ℕ) (x : ComplexBall) :
    ‖x.centre‖ ≤ ((absUpper p x : ℚ) : ℝ) :=
  norm_centre_le (sqrtUpperQ_nonneg _ _)
    (le_sq_sqrtUpperQ (by positivity) p)

/-- The self-contained product: no modulus arguments, so a tower can recurse. -/
def mulA (p : ℕ) (x y : ComplexBall) : ComplexBall :=
  mul x y (absUpper p x) (absUpper p y)

theorem contains_mulA (p : ℕ) {x y : ComplexBall} {a b : ℂ}
    (hx : x.contains a) (hy : y.contains b) : (mulA p x y).contains (a * b) :=
  contains_mul (norm_centre_le_absUpper p x) (norm_centre_le_absUpper p y) hx hy

/-- Widening the radius alone. -/
def widenRad (x : ComplexBall) (r' : ℚ) : ComplexBall := ⟨x.cre, x.cim, r'⟩

theorem contains_widenRad {x : ComplexBall} {z : ℂ} {r' : ℚ}
    (hx : x.contains z) (h : x.rad ≤ r') : (widenRad x r').contains z := by
  have hx' : ‖z - x.centre‖ ≤ (x.rad : ℝ) := hx
  have hc : (widenRad x r').centre = x.centre := rfl
  have h' : (x.rad : ℝ) ≤ (r' : ℝ) := by exact_mod_cast h
  rw [contains, hc]
  exact le_trans hx' h'

/-- Round a rational UP to a multiple of `2^{-p}`. -/
def ceilP (p : ℕ) (q : ℚ) : ℚ := ((⌈q * 2 ^ p⌉ : ℤ) : ℚ) / 2 ^ p

theorem le_ceilP (p : ℕ) (q : ℚ) : q ≤ ceilP p q := by
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  rw [ceilP, le_div_iff₀ hp]
  exact_mod_cast Int.le_ceil (q * 2 ^ p)

/-- Outward rounding of BOTH centre and radius to multiples of `2^{-p}`.

Rounding the radius is not cosmetic.  `mulA`'s radius is
`ux·r₂ + uy·r₁ + r₁r₂`, so leaving it unrounded lets denominators compound
through the tower exactly as the rectangle layer's endpoints did: measured by
`#eval`, an unrounded `expCrB 20 64 10` produces a radius with a denominator of
tens of thousands of bits.  The Python mirror rounded both from the start; this
definition did not, until the `#eval` said so. -/
def coarsenB (p : ℕ) (x : ComplexBall) : ComplexBall :=
  let y := x.recentre ((round (x.cre * 2 ^ p) : ℚ) / 2 ^ p)
                      ((round (x.cim * 2 ^ p) : ℚ) / 2 ^ p)
  widenRad y (ceilP p y.rad)

theorem contains_coarsenB (p : ℕ) {x : ComplexBall} {z : ℂ} (hx : x.contains z) :
    (coarsenB p x).contains z :=
  contains_widenRad (contains_recentre _ _ hx) (le_ceilP p _)

/-- The rational bound on `‖z‖` valid for every `z` the ball encloses. -/
def normBoundB (p : ℕ) (x : ComplexBall) : ℚ := absUpper p x + x.rad

theorem norm_le_normBoundB (p : ℕ) {x : ComplexBall} {z : ℂ} (hx : x.contains z) :
    ‖z‖ ≤ ((normBoundB p x : ℚ) : ℝ) :=
  norm_le_normBound (norm_centre_le_absUpper p x) hx

/-! ### The exponential tower, in balls -/

def powIB (p : ℕ) (x : ComplexBall) : ℕ → ComplexBall
  | 0 => exact 1 0
  | m + 1 => mulA p (powIB p x m) x

theorem contains_powIB (p : ℕ) {x : ComplexBall} {z : ℂ} (hx : x.contains z) :
    ∀ m, (powIB p x m).contains (z ^ m)
  | 0 => by
    rw [pow_zero]
    have h := contains_exact (1 : ℚ) (0 : ℚ)
    rw [show ((⟨((1 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ)) = (1 : ℂ) by
      apply Complex.ext <;> simp] at h
    simpa [powIB] using h
  | m + 1 => by
    rw [pow_succ]
    exact contains_mulA p (contains_powIB p hx m) hx

def expSumCB (p : ℕ) (x : ComplexBall) : ℕ → ComplexBall
  | 0 => exact 0 0
  | m + 1 => (expSumCB p x m).add (smulQ (1 / m.factorial) (powIB p x m))

theorem contains_expSumCB (p : ℕ) {x : ComplexBall} {z : ℂ} (hx : x.contains z) :
    ∀ m, (expSumCB p x m).contains (∑ i ∈ Finset.range m, z ^ i / i.factorial)
  | 0 => by
    have h := contains_exact (0 : ℚ) (0 : ℚ)
    rw [show ((⟨((0 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ)) = (0 : ℂ) by
      apply Complex.ext <;> simp] at h
    simpa [expSumCB] using h
  | m + 1 => by
    rw [Finset.sum_range_succ]
    have h := contains_smulQ (q := 1 / m.factorial) (contains_powIB p hx m)
    rw [show ((((1 / m.factorial : ℚ)) : ℂ)) * z ^ m = z ^ m / m.factorial by
      push_cast; ring] at h
    exact contains_add (contains_expSumCB p hx m) h

/-- Widening to cover a value at a bounded distance from an enclosed one — the
Taylor-remainder step. -/
theorem contains_inflate_of_dist {x : ComplexBall} {z w : ℂ} (r : ℚ)
    (hx : x.contains z) (h : ‖w - z‖ ≤ (r : ℝ)) : (x.inflate r).contains w := by
  have hx' : ‖z - x.centre‖ ≤ (x.rad : ℝ) := hx
  have hc : (x.inflate r).centre = x.centre := rfl
  have htri : ‖w - x.centre‖ ≤ ‖w - z‖ + ‖z - x.centre‖ := by
    have he : w - x.centre = (w - z) + (z - x.centre) := by ring
    rw [he]; exact norm_add_le _ _
  have hr : (r : ℝ) ≤ |(r : ℝ)| := le_abs_self _
  rw [contains, hc]
  push_cast [inflate]
  linarith

/-- `exp` on a ball of norm at most 1, by Taylor sum plus Mathlib's remainder. -/
def expSmallB (n p : ℕ) (x : ComplexBall) : ComplexBall :=
  (expSumCB p x n).inflate (normBoundB p x ^ n * ((n + 1) / (n.factorial * n)))

theorem contains_expSmallB {n : ℕ} (hn : 0 < n) (p : ℕ) {x : ComplexBall} {z : ℂ}
    (hx : x.contains z) (hb : normBoundB p x ≤ 1) :
    (expSmallB n p x).contains (Complex.exp z) := by
  have hzb : ‖z‖ ≤ ((normBoundB p x : ℚ) : ℝ) := norm_le_normBoundB p hx
  have hz1 : ‖z‖ ≤ 1 := hzb.trans (by exact_mod_cast hb)
  have h := Complex.exp_bound hz1 hn
  refine contains_inflate_of_dist _ (contains_expSumCB p hx n) (h.trans ?_)
  have h1 : ‖z‖ ^ n ≤ ((normBoundB p x : ℚ) : ℝ) ^ n :=
    pow_le_pow_left₀ (norm_nonneg z) hzb n
  have h2 : (0 : ℝ) ≤ (n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹ := by positivity
  calc ‖z‖ ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹)
      ≤ ((normBoundB p x : ℚ) : ℝ) ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = ((normBoundB p x ^ n * ((n + 1) / (n.factorial * n)) : ℚ) : ℝ) := by
        push_cast [Nat.succ_eq_add_one]
        ring

/-! ### The squaring tower

The rectangle tower halves its argument *recursively*, which makes the side
condition `normBound x ≤ 2^k` and needs `normBound (halve x) = normBound x / 2`.
That identity is unavailable here: `absUpper` rounds to the `2^{-p}` grid, so
halving is only exact up to `2^{-p}`.  Scaling down once by the exact rational
`1/2^k` and then squaring `k` times avoids the issue entirely and leaves a
*single* side condition, decidable by `norm_num` at a generated call site. -/

def sqIter (p : ℕ) : ℕ → ComplexBall → ComplexBall
  | 0, y => y
  | k + 1, y => let z := sqIter p k y; coarsenB p (mulA p z z)

theorem contains_sqIter (p : ℕ) :
    ∀ (k : ℕ) {y : ComplexBall} {w : ℂ}, y.contains w →
      (sqIter p k y).contains (w ^ (2 ^ k))
  | 0, y, w, hy => by simpa [sqIter] using hy
  | k + 1, y, w, hy => by
    have h := contains_sqIter p k hy
    have h2 := contains_mulA p h h
    rw [show w ^ (2 ^ k) * w ^ (2 ^ k) = w ^ (2 ^ (k + 1)) by
      rw [← pow_add]; congr 1; ring] at h2
    exact contains_coarsenB p h2

/-- `exp` by scale-down-and-square, with outward rounding after each squaring. -/
def expCrB (n p k : ℕ) (x : ComplexBall) : ComplexBall :=
  sqIter p k (expSmallB n p (smulQ (1 / 2 ^ k) x))

theorem contains_expCrB {n : ℕ} (hn : 0 < n) (p k : ℕ) {x : ComplexBall} {z : ℂ}
    (hx : x.contains z) (hb : normBoundB p (smulQ (1 / 2 ^ k) x) ≤ 1) :
    (expCrB n p k x).contains (Complex.exp z) := by
  have hs : (smulQ (1 / 2 ^ k) x).contains (((1 / 2 ^ k : ℚ) : ℂ) * z) :=
    contains_smulQ hx
  have he := contains_expSmallB hn p hs hb
  have h := contains_sqIter p k he
  rw [show (Complex.exp (((1 / 2 ^ k : ℚ) : ℂ) * z)) ^ (2 ^ k) = Complex.exp z by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp] at h
  exact h

end ComplexBall

end ZetaLean
