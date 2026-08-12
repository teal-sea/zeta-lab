import Mathlib

/-!
# A rational weak-duality certificate for a 6-variable LP, plus four trig inequalities

This file is a complete, self-contained formalisation of the statement in `PROBLEM.md`:

* `MTKernel.theoremA` — the linear-programming lower bound obtained from the explicit
  rational dual certificate `(y, u₁, u₂)` (pure rational arithmetic);
* `MTKernel.B1`, `MTKernel.B2`, `MTKernel.B3`, `MTKernel.B4` — the four lower bounds on the
  Montgomery-Taylor kernel `g` at the explicit rational points/intervals of the problem;
* `MTKernel.corollary` — the combination of the two.

All constants are the exact rationals of §1 of `PROBLEM.md`, coerced to `ℝ`.

The analytic input is developed from scratch: explicit truncation error bounds for the
Taylor series of `sin` and `cos` (`abs_sin_sub_taylor`, `abs_cos_sub_taylor`), Mathlib's
20-digit bounds on `π`, a rational enclosure of `√2`, and a small amount of interval
arithmetic.  `B3` and `B4` are proved by covering the interval with finitely many
sub-intervals on each of which a Lipschitz estimate plus one enclosure-carrying point evaluation
of `sin` and `cos` suffices; the sub-division is coarse (4 resp. 6 pieces) because it is
refined only near the endpoint at which the bound is tight.
-/

/-! ## Rigorous rational bounds for `sin` and `cos` -/

open Real Finset

namespace MTKernel

open scoped Nat

/-- `M! * ((M+1)(M+2))^i ≤ (M+2i)!`. -/
theorem factorial_pow_le (M i : ℕ) : M ! * ((M + 1) * (M + 2)) ^ i ≤ (M + 2 * i)! := by
  induction i with
  | zero => simp
  | succ n ih =>
      have h1 : M + 2 * (n + 1) = M + 2 * n + 1 + 1 := by ring
      rw [h1, Nat.factorial_succ, Nat.factorial_succ]
      have h2 : M ! * ((M + 1) * (M + 2)) ^ (n + 1)
          = (M + 1) * (M + 2) * (M ! * ((M + 1) * (M + 2)) ^ n) := by ring
      rw [h2]
      have h3 : (M + 1) * (M + 2) ≤ (M + 2 * n + 1 + 1) * (M + 2 * n + 1) := by
        calc (M + 1) * (M + 2) ≤ (M + 2 * n + 1) * (M + 2 * n + 1 + 1) :=
              Nat.mul_le_mul (by lia) (by lia)
          _ = (M + 2 * n + 1 + 1) * (M + 2 * n + 1) := by ring
      calc (M + 1) * (M + 2) * (M ! * ((M + 1) * (M + 2)) ^ n)
          ≤ (M + 2 * n + 1 + 1) * (M + 2 * n + 1) * (M + 2 * n)! := Nat.mul_le_mul h3 ih
        _ = (M + 2 * n + 1 + 1) * ((M + 2 * n + 1) * (M + 2 * n)!) := by ring

/-- Termwise geometric comparison for the tails of the sine and cosine series. -/
theorem term_le (r : ℝ) (M : ℕ) (hq : 2 * r ^ 2 ≤ (M + 1) * (M + 2)) (i : ℕ) :
    |r| ^ (M + 2 * i) / (M + 2 * i)! ≤ |r| ^ M / M ! * (1 / 2) ^ i := by
  have hG : (0 : ℝ) < (M ! : ℝ) := by exact_mod_cast Nat.factorial_pos M
  have hF : (0 : ℝ) < ((M + 2 * i)! : ℝ) := by exact_mod_cast Nat.factorial_pos (M + 2 * i)
  have hX : (0 : ℝ) ≤ |r| ^ M := by positivity
  have hfac : (M ! : ℝ) * ((((M + 1) * (M + 2)) : ℕ) : ℝ) ^ i ≤ (((M + 2 * i)! : ℕ) : ℝ) := by
    exact_mod_cast factorial_pow_le M i
  have h2r : (2 * r ^ 2) ^ i ≤ ((((M + 1) * (M + 2)) : ℕ) : ℝ) ^ i := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  have he : (r ^ 2) ^ i * 2 ^ i = (2 * r ^ 2) ^ i := by rw [← mul_pow]; ring_nf
  have hYG : (r ^ 2) ^ i * (M ! : ℝ) * 2 ^ i ≤ (((M + 2 * i)! : ℕ) : ℝ) := by
    calc (r ^ 2) ^ i * (M ! : ℝ) * 2 ^ i = (M ! : ℝ) * ((r ^ 2) ^ i * 2 ^ i) := by ring
      _ = (M ! : ℝ) * (2 * r ^ 2) ^ i := by rw [he]
      _ ≤ (M ! : ℝ) * ((((M + 1) * (M + 2)) : ℕ) : ℝ) ^ i := mul_le_mul_of_nonneg_left h2r hG.le
      _ ≤ _ := hfac
  have habs : |r| ^ (M + 2 * i) = |r| ^ M * (r ^ 2) ^ i := by
    simp [pow_add, pow_mul, sq_abs]
  rw [habs, show (1 / 2 : ℝ) ^ i = 1 / 2 ^ i by rw [div_pow, one_pow]]
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hF (by positivity)]
  calc |r| ^ M * (r ^ 2) ^ i * ((M ! : ℝ) * 2 ^ i)
      = |r| ^ M * ((r ^ 2) ^ i * (M ! : ℝ) * 2 ^ i) := by ring
    _ ≤ |r| ^ M * (((M + 2 * i)! : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hYG hX

private theorem geom_hasSum (C : ℝ) : HasSum (fun i : ℕ => C * (1 / 2 : ℝ) ^ i) (2 * C) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).mul_left C
  norm_num at h
  convert h using 1
  ring

/-- Explicit truncation error for the Taylor series of `cos`. -/
theorem abs_cos_sub_taylor (r : ℝ) (N : ℕ) (hq : 2 * r ^ 2 ≤ (2 * N + 1) * (2 * N + 2)) :
    |Real.cos r - ∑ n ∈ range N, (-1 : ℝ) ^ n * r ^ (2 * n) / (2 * n)!|
      ≤ 2 * (|r| ^ (2 * N) / (2 * N)!) := by
  set f : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * r ^ (2 * n) / (2 * n)! with hf
  have hs : HasSum f (Real.cos r) := Real.hasSum_cos r
  have htail : HasSum (fun i => f (i + N)) (Real.cos r - ∑ n ∈ range N, f n) := by
    rw [hasSum_nat_add_iff]
    simpa using hs
  have hb : ∀ i, ‖f (i + N)‖ ≤ |r| ^ (2 * N) / (2 * N)! * (1 / 2) ^ i := by
    intro i
    have hidx : 2 * (i + N) = 2 * N + 2 * i := by ring
    have : ‖f (i + N)‖ = |r| ^ (2 * N + 2 * i) / (2 * N + 2 * i)! := by
      simp only [hf, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, hidx, Nat.abs_cast]
    rw [this]
    have := term_le r (2 * N) (by push_cast; linarith) i
    simpa using this
  have := htail.norm_le_of_bounded (geom_hasSum (|r| ^ (2 * N) / (2 * N)!)) hb
  simpa using this

/-- Explicit truncation error for the Taylor series of `sin`. -/
theorem abs_sin_sub_taylor (r : ℝ) (N : ℕ) (hq : 2 * r ^ 2 ≤ (2 * N + 2) * (2 * N + 3)) :
    |Real.sin r - ∑ n ∈ range N, (-1 : ℝ) ^ n * r ^ (2 * n + 1) / (2 * n + 1)!|
      ≤ 2 * (|r| ^ (2 * N + 1) / (2 * N + 1)!) := by
  set f : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * r ^ (2 * n + 1) / (2 * n + 1)! with hf
  have hs : HasSum f (Real.sin r) := Real.hasSum_sin r
  have htail : HasSum (fun i => f (i + N)) (Real.sin r - ∑ n ∈ range N, f n) := by
    rw [hasSum_nat_add_iff]
    simpa using hs
  have hb : ∀ i, ‖f (i + N)‖ ≤ |r| ^ (2 * N + 1) / (2 * N + 1)! * (1 / 2) ^ i := by
    intro i
    have hidx : 2 * (i + N) + 1 = 2 * N + 1 + 2 * i := by ring
    have : ‖f (i + N)‖ = |r| ^ (2 * N + 1 + 2 * i) / (2 * N + 1 + 2 * i)! := by
      simp only [hf, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, hidx, Nat.abs_cast]
    rw [this]
    have := term_le r (2 * N + 1) (by push_cast; linarith) i
    simpa using this
  have := htail.norm_le_of_bounded (geom_hasSum (|r| ^ (2 * N + 1) / (2 * N + 1)!)) hb
  simpa using this

/-- Convenience form: explicit rational enclosure for `cos r`. -/
theorem cos_mem (r : ℝ) (N : ℕ) (lo hi : ℝ) (hq : 2 * r ^ 2 ≤ (2 * N + 1) * (2 * N + 2))
    (h1 : lo ≤ (∑ n ∈ range N, (-1 : ℝ) ^ n * r ^ (2 * n) / (2 * n)!)
      - 2 * (|r| ^ (2 * N) / (2 * N)!))
    (h2 : (∑ n ∈ range N, (-1 : ℝ) ^ n * r ^ (2 * n) / (2 * n)!)
      + 2 * (|r| ^ (2 * N) / (2 * N)!) ≤ hi) :
    lo ≤ Real.cos r ∧ Real.cos r ≤ hi := by
  have h := abs_le.1 (abs_cos_sub_taylor r N hq)
  constructor <;> linarith [h.1, h.2]

/-- Convenience form: explicit rational enclosure for `sin r`. -/
theorem sin_mem (r : ℝ) (N : ℕ) (lo hi : ℝ) (hq : 2 * r ^ 2 ≤ (2 * N + 2) * (2 * N + 3))
    (h1 : lo ≤ (∑ n ∈ range N, (-1 : ℝ) ^ n * r ^ (2 * n + 1) / (2 * n + 1)!)
      - 2 * (|r| ^ (2 * N + 1) / (2 * N + 1)!))
    (h2 : (∑ n ∈ range N, (-1 : ℝ) ^ n * r ^ (2 * n + 1) / (2 * n + 1)!)
      + 2 * (|r| ^ (2 * N + 1) / (2 * N + 1)!) ≤ hi) :
    lo ≤ Real.sin r ∧ Real.sin r ≤ hi := by
  have h := abs_le.1 (abs_sin_sub_taylor r N hq)
  constructor <;> linarith [h.1, h.2]

end MTKernel

/-! ## The Montgomery-Taylor kernel and the tools used to bound it -/

open Real Finset

namespace MTKernel

/-! ### `√2` and `K = √2/2` -/

/-- `K = √2 / 2`, so that `d₁ u = 2 (K - πu)` and `d₂ u = 2 (K + πu)`. -/
noncomputable def K : ℝ := Real.sqrt 2 / 2

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt2_lo : (141421356237309504880168 / 10 ^ 23 : ℝ) ≤ Real.sqrt 2 := by
  nlinarith [sqrt2_sq, Real.sqrt_nonneg 2]

theorem sqrt2_hi : Real.sqrt 2 ≤ 141421356237309504880169 / 10 ^ 23 := by
  nlinarith [sqrt2_sq, Real.sqrt_nonneg 2]

theorem K_sq : K ^ 2 = 1 / 2 := by
  rw [K, div_pow, sqrt2_sq]; norm_num

theorem K_lo : (70710678118654752440084 / 10 ^ 23 : ℝ) ≤ K := by
  rw [K]; linarith [sqrt2_lo]

theorem K_hi : K ≤ 70710678118654752440085 / 10 ^ 23 := by
  rw [K]; linarith [sqrt2_hi]

theorem K_pos : 0 < K := by linarith [K_lo]

theorem sinK_pos : 0 < Real.sin K :=
  Real.sin_pos_of_pos_of_lt_pi K_pos (by linarith [K_hi, Real.pi_gt_three])

/-! ### The kernel -/

/-- `d₁ u = √2 - 2πu`. -/
noncomputable def dd1 (u : ℝ) : ℝ := Real.sqrt 2 - 2 * π * u
/-- `d₂ u = √2 + 2πu`. -/
noncomputable def dd2 (u : ℝ) : ℝ := Real.sqrt 2 + 2 * π * u
/-- `A u = sin (d₁ u / 2) / d₁ u`. -/
noncomputable def kA (u : ℝ) : ℝ := Real.sin (dd1 u / 2) / dd1 u
/-- `B u = sin (d₂ u / 2) / d₂ u`. -/
noncomputable def kB (u : ℝ) : ℝ := Real.sin (dd2 u / 2) / dd2 u
/-- The Montgomery-Taylor kernel `g u = (A u + B u)² / (1 - cos √2)`. -/
noncomputable def gk (u : ℝ) : ℝ := (kA u + kB u) ^ 2 / (1 - Real.cos (Real.sqrt 2))

/-- The numerator `P u = πu cos K sin (πu) - K sin K cos (πu)` of `A + B`. -/
noncomputable def Pk (u : ℝ) : ℝ :=
  π * u * Real.cos K * Real.sin (π * u) - K * Real.sin K * Real.cos (π * u)

theorem one_sub_cos_sqrt2 : 1 - Real.cos (Real.sqrt 2) = 2 * Real.sin K ^ 2 := by
  have h : Real.sqrt 2 = 2 * K := by rw [K]; ring
  rw [h, Real.cos_two_mul, Real.cos_sq']
  ring

/-- Closed form for the kernel in terms of `P`. -/
theorem gk_eq (u : ℝ) (h : (π * u) ^ 2 ≠ K ^ 2) :
    gk u = Pk u ^ 2 / (2 * Real.sin K ^ 2 * ((π * u) ^ 2 - K ^ 2) ^ 2) := by
  have hs : Real.sqrt 2 = 2 * K := by rw [K]; ring
  have h1 : dd1 u = 2 * (K - π * u) := by rw [dd1, hs]; ring
  have h2 : dd2 u = 2 * (K + π * u) := by rw [dd2, hs]; ring
  have hne1 : K - π * u ≠ 0 := by
    intro hc; apply h
    have : π * u = K := by linarith
    rw [this]
  have hne2 : K + π * u ≠ 0 := by
    intro hc; apply h
    have : π * u = -K := by linarith
    rw [this]; ring
  have e1 : dd1 u / 2 = K - π * u := by rw [h1]; ring
  have e2 : dd2 u / 2 = K + π * u := by rw [h2]; ring
  have hd : ((π * u) ^ 2 - K ^ 2) ≠ 0 := sub_ne_zero.2 h
  have hAB : kA u + kB u = Pk u / ((π * u) ^ 2 - K ^ 2) := by
    rw [kA, kB, Pk, e1, e2, h1, h2, Real.sin_sub, Real.sin_add]
    rw [div_add_div _ _ (by simpa using hne1) (by simpa using hne2), div_eq_div_iff (by
      simpa using mul_ne_zero (mul_ne_zero two_ne_zero hne1) (mul_ne_zero two_ne_zero hne2)) hd]
    ring
  rw [gk, hAB, one_sub_cos_sqrt2, div_pow, div_div]
  congr 1
  ring

/-- Master lower bound for the kernel: it suffices to bound `|P|` from below and the
denominator from above. -/
theorem gk_ge_of {u r Plo Dhi SK : ℝ} (hPlo : 0 < Plo) (hP : Plo ≤ |Pk u|)
    (hD0 : 0 < (π * u) ^ 2 - K ^ 2) (hD : (π * u) ^ 2 - K ^ 2 ≤ Dhi)
    (hSK : Real.sin K ≤ SK) (hfin : r * (2 * SK ^ 2 * Dhi ^ 2) ≤ Plo ^ 2) :
    r ≤ gk u := by
  have hne : (π * u) ^ 2 ≠ K ^ 2 := by intro hc; rw [hc] at hD0; simp at hD0
  have hsk := sinK_pos
  have hSK0 : 0 < SK := lt_of_lt_of_le hsk hSK
  have hDhi : 0 < Dhi := lt_of_lt_of_le hD0 hD
  have hnum : Plo ^ 2 ≤ Pk u ^ 2 := by
    have := sq_abs (Pk u)
    nlinarith [abs_nonneg (Pk u)]
  have hden : (0 : ℝ) < 2 * Real.sin K ^ 2 * ((π * u) ^ 2 - K ^ 2) ^ 2 := by positivity
  have hden2 : 2 * Real.sin K ^ 2 * ((π * u) ^ 2 - K ^ 2) ^ 2 ≤ 2 * SK ^ 2 * Dhi ^ 2 := by
    have h1 : Real.sin K ^ 2 ≤ SK ^ 2 := by nlinarith
    have h2 : ((π * u) ^ 2 - K ^ 2) ^ 2 ≤ Dhi ^ 2 := by nlinarith
    nlinarith [sq_nonneg (Real.sin K), sq_nonneg ((π * u) ^ 2 - K ^ 2)]
  rw [gk_eq u hne]
  rcases le_total r 0 with hr | hr
  · exact le_trans hr (by positivity)
  rw [le_div_iff₀ hden]
  calc r * (2 * Real.sin K ^ 2 * ((π * u) ^ 2 - K ^ 2) ^ 2)
      ≤ r * (2 * SK ^ 2 * Dhi ^ 2) := mul_le_mul_of_nonneg_left hden2 hr
    _ ≤ Plo ^ 2 := hfin
    _ ≤ Pk u ^ 2 := hnum

/-! ### Elementary interval arithmetic -/

theorem min_mul_le {x xl xh y : ℝ} (hxl : xl ≤ x) (hxh : x ≤ xh) :
    min (xl * y) (xh * y) ≤ x * y := by
  rcases le_total 0 y with h | h
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hxl h)
  · exact le_trans (min_le_right _ _) (by nlinarith)

theorem le_max_mul {x xl xh y : ℝ} (hxl : xl ≤ x) (hxh : x ≤ xh) :
    x * y ≤ max (xl * y) (xh * y) := by
  rcases le_total 0 y with h | h
  · exact le_trans (mul_le_mul_of_nonneg_right hxh h) (le_max_right _ _)
  · exact le_trans (by nlinarith) (le_max_left _ _)

/-- Lower bound for a product of two intervals, via the four corners. -/
theorem le_mul_of_corners {x y xl xh yl yh L : ℝ} (hxl : xl ≤ x) (hxh : x ≤ xh)
    (hyl : yl ≤ y) (hyh : y ≤ yh) (h1 : L ≤ xl * yl) (h2 : L ≤ xl * yh) (h3 : L ≤ xh * yl)
    (h4 : L ≤ xh * yh) : L ≤ x * y := by
  have k1 : L ≤ x * yl := le_trans (le_min h1 h3) (min_mul_le hxl hxh)
  have k2 : L ≤ x * yh := le_trans (le_min h2 h4) (min_mul_le hxl hxh)
  have := min_mul_le (x := y) (xl := yl) (xh := yh) (y := x) hyl hyh
  calc L ≤ min (yl * x) (yh * x) := by
        rw [le_min_iff]; constructor <;>
          [linarith [k1, mul_comm x yl]; linarith [k2, mul_comm x yh]]
    _ ≤ y * x := this
    _ = x * y := mul_comm _ _

/-- Upper bound for a product of two intervals, via the four corners. -/
theorem mul_le_of_corners {x y xl xh yl yh U : ℝ} (hxl : xl ≤ x) (hxh : x ≤ xh)
    (hyl : yl ≤ y) (hyh : y ≤ yh) (h1 : xl * yl ≤ U) (h2 : xl * yh ≤ U) (h3 : xh * yl ≤ U)
    (h4 : xh * yh ≤ U) : x * y ≤ U := by
  have k1 : x * yl ≤ U := le_trans (le_max_mul hxl hxh) (max_le h1 h3)
  have k2 : x * yh ≤ U := le_trans (le_max_mul hxl hxh) (max_le h2 h4)
  have := le_max_mul (x := y) (xl := yl) (xh := yh) (y := x) hyl hyh
  calc x * y = y * x := mul_comm _ _
    _ ≤ max (yl * x) (yh * x) := this
    _ ≤ U := by
        rw [max_le_iff]; constructor <;>
          [linarith [k1, mul_comm x yl]; linarith [k2, mul_comm x yh]]

/-! ### From `u` to `sin (πu)`, `cos (πu)` -/

theorem pi_mul_lb {u ulo tlo : ℝ} (h : ulo ≤ u) (h0 : 0 ≤ ulo)
    (hnum : tlo ≤ 3.14159265358979323846 * ulo) : tlo ≤ π * u := by
  nlinarith [Real.pi_gt_d20]

theorem pi_mul_ub {u uhi thi : ℝ} (h : u ≤ uhi) (h0 : 0 ≤ uhi)
    (hnum : 3.14159265358979323847 * uhi ≤ thi) : π * u ≤ thi := by
  nlinarith [Real.pi_lt_d20, Real.pi_pos]

theorem sin_shift {x T0 W S1 S2 : ℝ} (h : |x - T0| ≤ W) (hs1 : S1 ≤ Real.sin T0)
    (hs2 : Real.sin T0 ≤ S2) : S1 - W ≤ Real.sin x ∧ Real.sin x ≤ S2 + W := by
  have h2 := abs_le.1 (Real.abs_sin_sub_sin_le x T0)
  have h3 := abs_le.1 h
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]

theorem cos_shift {x T0 W C1 C2 : ℝ} (h : |x - T0| ≤ W) (hc1 : C1 ≤ Real.cos T0)
    (hc2 : Real.cos T0 ≤ C2) : C1 - W ≤ Real.cos x ∧ Real.cos x ≤ C2 + W := by
  have h2 := abs_le.1 (Real.abs_cos_sub_cos_le x T0)
  have h3 := abs_le.1 h
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]

theorem D_pos {u tlo : ℝ} (ht1 : tlo ≤ π * u) (h0 : 0 ≤ tlo) (h : 1 / 2 < tlo ^ 2) :
    0 < (π * u) ^ 2 - K ^ 2 := by
  rw [K_sq]; nlinarith

theorem D_le {u thi Dhi : ℝ} (ht2 : π * u ≤ thi) (ht0 : 0 ≤ π * u)
    (h : thi ^ 2 - 1 / 2 ≤ Dhi) : (π * u) ^ 2 - K ^ 2 ≤ Dhi := by
  rw [K_sq]; nlinarith

/-! ### Bounds for `P` -/

/-- Lower bound for `P u` from interval data. -/
theorem Pk_lower {u tlo thi S1 S2 C1 C2 L1 U2 ck1 ck2 m1 m2 : ℝ}
    (hck1 : ck1 ≤ Real.cos K) (hck2 : Real.cos K ≤ ck2) (hck0 : 0 ≤ ck1)
    (hm1 : m1 ≤ K * Real.sin K) (hm2 : K * Real.sin K ≤ m2)
    (ht1 : tlo ≤ π * u) (ht2 : π * u ≤ thi) (ht0 : 0 ≤ tlo)
    (hs1 : S1 ≤ Real.sin (π * u)) (hs2 : Real.sin (π * u) ≤ S2)
    (hc1 : C1 ≤ Real.cos (π * u)) (hc2 : Real.cos (π * u) ≤ C2)
    (a1 : L1 ≤ tlo * ck1 * S1) (a2 : L1 ≤ tlo * ck1 * S2)
    (a3 : L1 ≤ thi * ck2 * S1) (a4 : L1 ≤ thi * ck2 * S2)
    (b1 : m1 * C1 ≤ U2) (b2 : m1 * C2 ≤ U2) (b3 : m2 * C1 ≤ U2) (b4 : m2 * C2 ≤ U2) :
    L1 - U2 ≤ Pk u := by
  have hck : 0 ≤ Real.cos K := le_trans hck0 hck1
  have hx1 : tlo * ck1 ≤ π * u * Real.cos K :=
    mul_le_mul ht1 hck1 hck0 (le_trans ht0 ht1)
  have hx2 : π * u * Real.cos K ≤ thi * ck2 :=
    mul_le_mul ht2 hck2 hck (le_trans (le_trans ht0 ht1) ht2)
  have hA : L1 ≤ π * u * Real.cos K * Real.sin (π * u) :=
    le_mul_of_corners hx1 hx2 hs1 hs2 a1 a2 a3 a4
  have hB : K * Real.sin K * Real.cos (π * u) ≤ U2 :=
    mul_le_of_corners hm1 hm2 hc1 hc2 b1 b2 b3 b4
  rw [Pk]
  linarith

/-- Upper bound for `P u` from interval data. -/
theorem Pk_upper {u tlo thi S1 S2 C1 C2 U1 L2 ck1 ck2 m1 m2 : ℝ}
    (hck1 : ck1 ≤ Real.cos K) (hck2 : Real.cos K ≤ ck2) (hck0 : 0 ≤ ck1)
    (hm1 : m1 ≤ K * Real.sin K) (hm2 : K * Real.sin K ≤ m2)
    (ht1 : tlo ≤ π * u) (ht2 : π * u ≤ thi) (ht0 : 0 ≤ tlo)
    (hs1 : S1 ≤ Real.sin (π * u)) (hs2 : Real.sin (π * u) ≤ S2)
    (hc1 : C1 ≤ Real.cos (π * u)) (hc2 : Real.cos (π * u) ≤ C2)
    (a1 : tlo * ck1 * S1 ≤ U1) (a2 : tlo * ck1 * S2 ≤ U1)
    (a3 : thi * ck2 * S1 ≤ U1) (a4 : thi * ck2 * S2 ≤ U1)
    (b1 : L2 ≤ m1 * C1) (b2 : L2 ≤ m1 * C2) (b3 : L2 ≤ m2 * C1) (b4 : L2 ≤ m2 * C2) :
    Pk u ≤ U1 - L2 := by
  have hck : 0 ≤ Real.cos K := le_trans hck0 hck1
  have hx1 : tlo * ck1 ≤ π * u * Real.cos K :=
    mul_le_mul ht1 hck1 hck0 (le_trans ht0 ht1)
  have hx2 : π * u * Real.cos K ≤ thi * ck2 :=
    mul_le_mul ht2 hck2 hck (le_trans (le_trans ht0 ht1) ht2)
  have hA : π * u * Real.cos K * Real.sin (π * u) ≤ U1 :=
    mul_le_of_corners hx1 hx2 hs1 hs2 a1 a2 a3 a4
  have hB : L2 ≤ K * Real.sin K * Real.cos (π * u) :=
    le_mul_of_corners hm1 hm2 hc1 hc2 b1 b2 b3 b4
  rw [Pk]
  linarith

end MTKernel

open Real Finset

namespace MTKernel

/-! ## §1 Exact rational data -/

/-- `ν = 6725007037 / 10^10`. -/
noncomputable def nu : ℝ := 6725007037 / 10 ^ 10

/-- `a = 8417946722491071 / 9007199254740992`. -/
noncomputable def ea : ℝ := 8417946722491071 / 9007199254740992

/-- `b = 1170477432362207 / 1125899906842624`. -/
noncomputable def eb : ℝ := 1170477432362207 / 1125899906842624

/-- `c = 3048825866473933 / 2251799813685248`. -/
noncomputable def ec : ℝ := 3048825866473933 / 2251799813685248

/-- `d = 8997362478613249 / 4503599627370496`. -/
noncomputable def ed : ℝ := 8997362478613249 / 4503599627370496

/-- `r_a = 147223 / 10^7`. -/
noncomputable def ra : ℝ := 147223 / 10 ^ 7

/-- `r_b = 250294 / 10^9`. -/
noncomputable def rb : ℝ := 250294 / 10 ^ 9

/-- `r_h = 185 / 10^6`. -/
noncomputable def rh : ℝ := 185 / 10 ^ 6

/-- `r_j = 398 / 10^6`. -/
noncomputable def rj : ℝ := 398 / 10 ^ 6

/-- `y = 2351506773321 / (5 * 10^15)`. -/
noncomputable def dualY : ℝ := 2351506773321 / (5 * 10 ^ 15)

/-- `u₁ = -212 / 900565`. -/
noncomputable def dualU1 : ℝ := -212 / 900565

/-- `u₂ = -79 / 700438`. -/
noncomputable def dualU2 : ℝ := -79 / 700438

/-- `F = 15836524170563975879104102066119 / 3153949737350000000000000000000000000`. -/
noncomputable def Fbound : ℝ :=
  15836524170563975879104102066119 / 3153949737350000000000000000000000000

/-! ## §2 Theorem A -/

/-- **Theorem A** (the LP bound, by explicit weak duality).  For every `x ∈ ℝ⁶` satisfying the
primal constraints (P1)–(P4) and every cost vector `c' ∈ ℝ⁶` dominating `(r_a, r_b, 0, r_h, 0,
r_j)` componentwise (C), the objective is at least `F`. -/
theorem theoremA (x1 x2 x3 x4 x5 x6 c1 c2 c3 c4 c5 c6 : ℝ)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3) (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5) (hx6 : 0 ≤ x6)
    (hP2 : x1 + x2 + x3 + x4 + x5 = nu)
    (hP3 : ea * x2 + eb * x3 + ec * x4 + ed * x5 ≤ 1)
    (hP4 : 2 * x3 - x6 ≤ nu)
    (hc1 : ra ≤ c1) (hc2 : rb ≤ c2) (hc3 : 0 ≤ c3) (hc4 : rh ≤ c4) (hc5 : 0 ≤ c5)
    (hc6 : rj ≤ c6) :
    Fbound ≤ c1 * x1 + c2 * x2 + c3 * x3 + c4 * x4 + c5 * x5 + c6 * x6 := by
  -- (C) together with `x ≥ 0`
  have k1 : ra * x1 ≤ c1 * x1 := mul_le_mul_of_nonneg_right hc1 hx1
  have k2 : rb * x2 ≤ c2 * x2 := mul_le_mul_of_nonneg_right hc2 hx2
  have k3 : (0 : ℝ) * x3 ≤ c3 * x3 := mul_le_mul_of_nonneg_right hc3 hx3
  have k4 : rh * x4 ≤ c4 * x4 := mul_le_mul_of_nonneg_right hc4 hx4
  have k5 : (0 : ℝ) * x5 ≤ c5 * x5 := mul_le_mul_of_nonneg_right hc5 hx5
  have k6 : rj * x6 ≤ c6 * x6 := mul_le_mul_of_nonneg_right hc6 hx6
  -- the six column inequalities (D1)–(D6), each multiplied by `x_i ≥ 0`
  have d1 : dualY * x1 ≤ ra * x1 :=
    mul_le_mul_of_nonneg_right (by norm_num [dualY, ra]) hx1
  have d2 : (dualY + ea * dualU1) * x2 ≤ rb * x2 :=
    mul_le_mul_of_nonneg_right (by norm_num [dualY, rb, ea, dualU1]) hx2
  have d3 : (dualY + eb * dualU1 + 2 * dualU2) * x3 ≤ 0 * x3 :=
    mul_le_mul_of_nonneg_right (by norm_num [dualY, eb, dualU1, dualU2]) hx3
  have d4 : (dualY + ec * dualU1) * x4 ≤ rh * x4 :=
    mul_le_mul_of_nonneg_right (by norm_num [dualY, rh, ec, dualU1]) hx4
  have d5 : (dualY + ed * dualU1) * x5 ≤ 0 * x5 :=
    mul_le_mul_of_nonneg_right (by norm_num [dualY, ed, dualU1]) hx5
  have d6 : (-dualU2) * x6 ≤ rj * x6 :=
    mul_le_mul_of_nonneg_right (by norm_num [dualU2, rj]) hx6
  -- the two dual sign conditions against (P3) and (P4)
  have e1 : dualU1 * 1 ≤ dualU1 * (ea * x2 + eb * x3 + ec * x4 + ed * x5) :=
    mul_le_mul_of_nonpos_left hP3 (by norm_num [dualU1])
  have e2 : dualU2 * nu ≤ dualU2 * (2 * x3 - x6) :=
    mul_le_mul_of_nonpos_left hP4 (by norm_num [dualU2])
  -- the value identity `y·ν + u₁ + u₂·ν = F`
  have hval : dualY * nu + dualU1 + dualU2 * nu = Fbound := by
    norm_num [dualY, dualU1, dualU2, nu, Fbound]
  have hP2' : dualY * (x1 + x2 + x3 + x4 + x5) = dualY * nu := by rw [hP2]
  simp only [nu, dualY, dualU1, dualU2, ra, rb, rh, rj, ea, eb, ec, ed, Fbound] at *
  linarith


/-! ## §3 The kernel: numerical constants -/

-- K constants (generated)

theorem sinK_lo : (64963693908006244412939/100000000000000000000000 : ℝ) ≤ Real.sin K := by
  have hW : |K - (14142135623730950488017/20000000000000000000000 : ℝ)| ≤
    (1/100000000000000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [K_lo, K_hi]
  obtain ⟨h1, h2⟩ := sin_mem (14142135623730950488017/20000000000000000000000 : ℝ) 12
    (3248184695400312220647/5000000000000000000000 : ℝ)
    (1299273878160124888259/2000000000000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  linarith [(sin_shift hW h1 h2).1]

theorem sinK_hi : Real.sin K ≤ (64963693908006244412951/100000000000000000000000 : ℝ) := by
  have hW : |K - (14142135623730950488017/20000000000000000000000 : ℝ)| ≤
    (1/100000000000000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [K_lo, K_hi]
  obtain ⟨h1, h2⟩ := sin_mem (14142135623730950488017/20000000000000000000000 : ℝ) 12
    (3248184695400312220647/5000000000000000000000 : ℝ)
    (1299273878160124888259/2000000000000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  linarith [(sin_shift hW h1 h2).2]

theorem cosK_lo : (76024459707563015125349/100000000000000000000000 : ℝ) ≤ Real.cos K := by
  have hW : |K - (14142135623730950488017/20000000000000000000000 : ℝ)| ≤
    (1/100000000000000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [K_lo, K_hi]
  obtain ⟨h1, h2⟩ := cos_mem (14142135623730950488017/20000000000000000000000 : ℝ) 12
    (1520489194151260302507/2000000000000000000000 : ℝ)
    (950305746344537689067/1250000000000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  linarith [(cos_shift hW h1 h2).1]

theorem cosK_hi : Real.cos K ≤ (76024459707563015125361/100000000000000000000000 : ℝ) := by
  have hW : |K - (14142135623730950488017/20000000000000000000000 : ℝ)| ≤
    (1/100000000000000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [K_lo, K_hi]
  obtain ⟨h1, h2⟩ := cos_mem (14142135623730950488017/20000000000000000000000 : ℝ) 12
    (1520489194151260302507/2000000000000000000000 : ℝ)
    (950305746344537689067/1250000000000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  linarith [(cos_shift hW h1 h2).2]

theorem m_lo : (114840671233196054723/250000000000000000000 : ℝ) ≤ K * Real.sin K := by
  nlinarith [K_lo, K_hi, sinK_lo, sinK_hi, sinK_pos, K_pos]

theorem m_hi : K * Real.sin K ≤ (2296813424663921094461/5000000000000000000000 : ℝ) := by
  nlinarith [K_lo, K_hi, sinK_lo, sinK_hi, sinK_pos, K_pos]

theorem B1_piece (u : ℝ) (hu1 : (8417946722491071/9007199254740992 : ℝ) ≤ u)
  (hu2 : u ≤ (8417946722491071/9007199254740992 : ℝ)) : ra ≤ gk u := by
  have ht1 : (2936069119129/1000000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (293606911913/100000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (2936069119129/1000000000000 : ℝ)| ≤ (1/1000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (2936069119129/1000000000000 : ℝ) 14 (51019926037/250000000000 : ℝ)
    (204079704149/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (2936069119129/1000000000000 : ℝ) 14
    (-978954275927/1000000000000 : ℝ) (-489477137963/500000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_lower (L1 := (455532569701/1000000000000 : ℝ))
    (U2 := (-89939012923/200000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (226306908579/250000000000 : ℝ) ≤ |Pk u| := le_trans (by norm_num)
    (le_trans hP (le_abs_self _))
  exact gk_ge_of (Plo := (226306908579/250000000000 : ℝ)) (Dhi := (8120501872309/1000000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [ra])

theorem B2_piece (u : ℝ) (hu1 : (1170477432362207/1125899906842624 : ℝ) ≤ u)
  (hu2 : u ≤ (1170477432362207/1125899906842624 : ℝ)) : rb ≤ gk u := by
  have ht1 : (32659770911729367/10000000000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num)
    (by norm_num)
  have ht2 : π * u ≤ (4082471363966171/1250000000000000 : ℝ) := pi_mul_ub hu2 (by norm_num)
    (by norm_num)
  have hW : |π * u - (32659770911729367/10000000000000000 : ℝ)| ≤ (1/10000000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (32659770911729367/10000000000000000 : ℝ) 16
    (-1240639502090671/10000000000000000 : ℝ) (-124063950209067/1000000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (32659770911729367/10000000000000000 : ℝ) 16
    (-496137112162183/500000000000000 : ℝ) (-9922742243243659/10000000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_lower (L1 := (-3080435229034339/10000000000000000 : ℝ))
    (U2 := (-1139534379688091/2500000000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (59108091588721/400000000000000 : ℝ) ≤ |Pk u| := le_trans (by norm_num)
    (le_trans hP (le_abs_self _))
  exact gk_ge_of (Plo := (59108091588721/400000000000000 : ℝ))
    (Dhi := (12708257950083047/1250000000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rb])

theorem B3_piece1 (u : ℝ) (hu1 : (3048825866473933/2251799813685248 : ℝ) ≤ u)
  (hu2 : u ≤ (1666039/1000000 : ℝ)) : rh ≤ gk u := by
  have ht1 : (850712295647/200000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (1046803176599/200000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (948757736123/200000000000 : ℝ)| ≤ (24511360119/50000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (948757736123/200000000000 : ℝ) 14
    (-999507069929/1000000000000 : ℝ) (-99950706991/100000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (948757736123/200000000000 : ℝ) 14 (31394540691/1000000000000 : ℝ)
    (7848635201/250000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_upper (U1 := (-164688231109/100000000000 : ℝ))
    (L2 := (-210770603409/1000000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (1436111707681/1000000000000 : ℝ) ≤ |Pk u| := by
    have h : (1436111707681/1000000000000 : ℝ) ≤ -Pk u := by linarith
    exact le_trans h (neg_le_abs _)
  exact gk_ge_of (Plo := (1436111707681/1000000000000 : ℝ))
    (Dhi := (6723730565861/250000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rh])

theorem B3_piece2 (u : ℝ) (hu1 : (1666039/1000000 : ℝ) ≤ u) (hu2 : u ≤ (1928183/1000000 : ℝ)) : rh ≤
  gk u := by
  have ht1 : (2617007941497/500000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (6057565547577/1000000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (1129158143057/200000000000 : ℝ)| ≤ (102943708073/250000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (1129158143057/200000000000 : ℝ) 14 (-59510363213/100000000000 : ℝ)
    (-23804145171/40000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (1129158143057/200000000000 : ℝ) 14 (100456120091/125000000000 : ℝ)
    (25114030481/31250000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_upper (U1 := (-729489536871/1000000000000 : ℝ))
    (L2 := (90006175897/500000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (181900377733/200000000000 : ℝ) ≤ |Pk u| := by
    have h : (181900377733/200000000000 : ℝ) ≤ -Pk u := by linarith
    exact le_trans h (neg_le_abs _)
  exact gk_ge_of (Plo := (181900377733/200000000000 : ℝ)) (Dhi := (4524262545399/125000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rh])

theorem B3_piece3 (u : ℝ) (hu1 : (1928183/1000000 : ℝ) ≤ u) (hu2 : u ≤ (1993719/1000000 : ℝ)) : rh ≤
  gk u := by
  have ht1 : (757195693447/125000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (6263452963723/1000000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (6160509255649/1000000000000 : ℝ)| ≤ (51471854037/500000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (6160509255649/1000000000000 : ℝ) 14
    (-122368609073/1000000000000 : ℝ) (-122368573229/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (6160509255649/1000000000000 : ℝ) 14
    (992484600553/1000000000000 : ℝ) (992484769281/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_upper (U1 := (-44728000243/500000000000 : ℝ))
    (L2 := (204310946363/500000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (124519473303/250000000000 : ℝ) ≤ |Pk u| := by
    have h : (124519473303/250000000000 : ℝ) ≤ -Pk u := by linarith
    exact le_trans h (neg_le_abs _)
  exact gk_ge_of (Plo := (124519473303/250000000000 : ℝ))
    (Dhi := (38730843028771/1000000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rh])

theorem B3_piece4 (u : ℝ) (hu1 : (1993719/1000000 : ℝ) ≤ u)
  (hu2 : u ≤ (8997362478613249/4503599627370496 : ℝ)) : rh ≤ gk u := by
  have ht1 : (3131726481861/500000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (1255264686173/200000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (6269888197293/1000000000000 : ℝ)| ≤ (1608808393/250000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (6269888197293/1000000000000 : ℝ) 14 (-2659352443/200000000000 : ℝ)
    (-13296702503/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (6269888197293/1000000000000 : ℝ) 14
    (999911390601/1000000000000 : ℝ) (999911666783/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_upper (U1 := (-6534528547/200000000000 : ℝ))
    (L2 := (456365874909/1000000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (122259629411/250000000000 : ℝ) ≤ |Pk u| := by
    have h : (122259629411/250000000000 : ℝ) ≤ -Pk u := by linarith
    exact le_trans h (neg_le_abs _)
  exact gk_ge_of (Plo := (122259629411/250000000000 : ℝ)) (Dhi := (19446117904413/500000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rh])

theorem B4_piece1 (u : ℝ) (hu1 : (1170477432362207/562949953421312 : ℝ) ≤ u)
  (hu2 : u ≤ (1039721/500000 : ℝ)) : rj ≤ gk u := by
  have ht1 : (1306390836469/200000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (6532759710767/1000000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (1633089236639/250000000000 : ℝ)| ≤ (402764211/1000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (1633089236639/250000000000 : ℝ) 14
    (246601120629/1000000000000 : ℝ) (123300658381/500000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (1633089236639/250000000000 : ℝ) 14
    (969116386157/1000000000000 : ℝ) (484558628437/500000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_lower (L1 := (244518440421/200000000000 : ℝ))
    (U2 := (222680659991/500000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (777230882123/1000000000000 : ℝ) ≤ |Pk u| := le_trans (by norm_num)
    (le_trans hP (le_abs_self _))
  exact gk_ge_of (Plo := (777230882123/1000000000000 : ℝ))
    (Dhi := (42176949438621/1000000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rj])

theorem B4_piece2 (u : ℝ) (hu1 : (1039721/500000 : ℝ) ≤ u) (hu2 : u ≤ (208149/100000 : ℝ)) : rj ≤ gk
  u := by
  have ht1 : (3266379855383/500000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (6539193692521/1000000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (6535976701643/1000000000000 : ℝ)| ≤ (1608495439/500000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (6535976701643/1000000000000 : ℝ) 14
    (250107461359/1000000000000 : ℝ) (62526915167/250000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (6535976701643/1000000000000 : ℝ) 14
    (968217392901/1000000000000 : ℝ) (968218277229/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_lower (L1 := (245236070973/200000000000 : ℝ))
    (U2 := (446241112997/1000000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (194984810467/250000000000 : ℝ) ≤ |Pk u| := le_trans (by norm_num)
    (le_trans hP (le_abs_self _))
  exact gk_ge_of (Plo := (194984810467/250000000000 : ℝ))
    (Dhi := (42261054148307/1000000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rj])

theorem B4_piece3 (u : ℝ) (hu1 : (208149/100000 : ℝ) ≤ u) (hu2 : u ≤ (1048937/500000 : ℝ)) : rj ≤ gk
  u := by
  have ht1 : (163479842313/25000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (3295332773279/500000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (6564929619539/1000000000000 : ℝ)| ≤ (25735927019/1000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (6564929619539/1000000000000 : ℝ) 14
    (278031440767/1000000000000 : ℝ) (278031667333/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (6564929619539/1000000000000 : ℝ) 14 (30017849599/31250000000 : ℝ)
    (960572188001/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_lower (L1 := (1254258554949/1000000000000 : ℝ))
    (U2 := (453073143887/1000000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (400592705531/500000000000 : ℝ) ≤ |Pk u| := le_trans (by norm_num)
    (le_trans hP (le_abs_self _))
  exact gk_ge_of (Plo := (400592705531/500000000000 : ℝ))
    (Dhi := (42936872346587/1000000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rj])

theorem B4_piece4 (u : ℝ) (hu1 : (1048937/500000 : ℝ) ≤ u) (hu2 : u ≤ (1114473/500000 : ℝ)) : rj ≤
  gk u := by
  have ht1 : (6590665546557/1000000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (7002440378849/1000000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (6796552962703/1000000000000 : ℝ)| ≤ (102943708073/500000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (6796552962703/1000000000000 : ℝ) 14 (61389139857/125000000000 : ℝ)
    (245556869073/500000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (6796552962703/1000000000000 : ℝ) 14
    (871093600699/1000000000000 : ℝ) (871096243127/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_lower (L1 := (1429128481239/1000000000000 : ℝ))
    (U2 := (494726105353/1000000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (467201187943/500000000000 : ℝ) ≤ |Pk u| := le_trans (by norm_num)
    (le_trans hP (le_abs_self _))
  exact gk_ge_of (Plo := (467201187943/500000000000 : ℝ)) (Dhi := (9706834251867/200000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rj])

theorem B4_piece5 (u : ℝ) (hu1 : (1114473/500000 : ℝ) ≤ u) (hu2 : u ≤ (249109/100000 : ℝ)) : rj ≤ gk
  u := by
  have ht1 : (218826261839/31250000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (7825990043431/1000000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (7414215211139/1000000000000 : ℝ)| ≤ (102943708073/250000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (7414215211139/1000000000000 : ℝ) 14
    (226211362341/250000000000 : ℝ) (90485316571/100000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (7414215211139/1000000000000 : ℝ) 14
    (425705939383/1000000000000 : ℝ) (85147224227/200000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_lower (L1 := (1312447347339/500000000000 : ℝ))
    (U2 := (384721280227/1000000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (2240173414451/1000000000000 : ℝ) ≤ |Pk u| := le_trans (by norm_num)
    (le_trans hP (le_abs_self _))
  exact gk_ge_of (Plo := (2240173414451/1000000000000 : ℝ))
    (Dhi := (30373060079941/500000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rj])

theorem B4_piece6 (u : ℝ) (hu1 : (249109/100000 : ℝ) ≤ u)
  (hu2 : u ≤ (3048825866473933/1125899906842624 : ℝ)) : rj ≤ gk u := by
  have ht1 : (782599004343/100000000000 : ℝ) ≤ π * u := pi_mul_lb hu1 (by norm_num) (by norm_num)
  have ht2 : π * u ≤ (8507122956471/1000000000000 : ℝ) := pi_mul_ub hu2 (by norm_num) (by norm_num)
  have hW : |π * u - (163331129999/20000000000 : ℝ)| ≤ (340566456521/1000000000000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hsT1, hsT2⟩ := sin_mem (163331129999/20000000000 : ℝ) 14 (475725818773/500000000000 : ℝ)
    (475789442827/500000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hcT1, hcT2⟩ := cos_mem (163331129999/20000000000 : ℝ) 14 (-153920271673/500000000000 : ℝ)
    (-307388676623/1000000000000 : ℝ) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  obtain ⟨hs1, hs2⟩ := sin_shift hW hsT1 hsT2
  obtain ⟨hc1, hc2⟩ := cos_shift hW hcT1 hcT2
  have hP := Pk_lower (L1 := (726912637373/200000000000 : ℝ)) (U2 := (3048126811/200000000000 : ℝ))
    (ck1 := (76024459707563015125349/100000000000000000000000 : ℝ))
    (ck2 := (76024459707563015125361/100000000000000000000000 : ℝ))
    (m1 := (114840671233196054723/250000000000000000000 : ℝ))
      (m2 := (2296813424663921094461/5000000000000000000000 : ℝ)) cosK_lo cosK_hi (by norm_num) m_lo
      m_hi ht1 ht2
    (by norm_num) hs1 hs2 hc1 hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have habs : (361932255281/100000000000 : ℝ) ≤ |Pk u| := le_trans (by norm_num)
    (le_trans hP (le_abs_self _))
  exact gk_ge_of (Plo := (361932255281/100000000000 : ℝ)) (Dhi := (17967785249129/250000000000 : ℝ))
    (SK := (64963693908006244412951/100000000000000000000000 : ℝ)) (by norm_num) habs
    (D_pos ht1 (by norm_num) (by norm_num)) (D_le ht2 (by linarith) (by norm_num))
    sinK_hi (by norm_num [rj])

/-- **Theorem B1.** `g a ≥ r_a`. -/
theorem B1 : ra ≤ gk ea := B1_piece ea (by norm_num [ea]) (by norm_num [ea])

/-- **Theorem B2.** `g b ≥ r_b`. -/
theorem B2 : rb ≤ gk eb := B2_piece eb (by norm_num [eb]) (by norm_num [eb])

/-- **Theorem B3.** `g u ≥ r_h` for all `u ∈ [c, d]`. -/
theorem B3 (u : ℝ) (hu1 : ec ≤ u) (hu2 : u ≤ ed) : rh ≤ gk u := by
  simp only [ec] at hu1
  simp only [ed] at hu2
  rcases le_total u (1666039/1000000 : ℝ) with h0 | h0
  · exact B3_piece1 u (by linarith) (by linarith)
  rcases le_total u (1928183/1000000 : ℝ) with h1 | h1
  · exact B3_piece2 u (by linarith) (by linarith)
  rcases le_total u (1993719/1000000 : ℝ) with h2 | h2
  · exact B3_piece3 u (by linarith) (by linarith)
  exact B3_piece4 u (by linarith) (by linarith)

/-- **Theorem B4.** `g u ≥ r_j` for all `u ∈ [2b, 2c]`. -/
theorem B4 (u : ℝ) (hu1 : 2 * eb ≤ u) (hu2 : u ≤ 2 * ec) : rj ≤ gk u := by
  simp only [eb] at hu1
  simp only [ec] at hu2
  rcases le_total u (1039721/500000 : ℝ) with h0 | h0
  · exact B4_piece1 u (by linarith) (by linarith)
  rcases le_total u (208149/100000 : ℝ) with h1 | h1
  · exact B4_piece2 u (by linarith) (by linarith)
  rcases le_total u (1048937/500000 : ℝ) with h2 | h2
  · exact B4_piece3 u (by linarith) (by linarith)
  rcases le_total u (1114473/500000 : ℝ) with h3 | h3
  · exact B4_piece4 u (by linarith) (by linarith)
  rcases le_total u (249109/100000 : ℝ) with h4 | h4
  · exact B4_piece5 u (by linarith) (by linarith)
  exact B4_piece6 u (by linarith) (by linarith)

/-! ## §4 The combined statement -/

/-- `h* = inf_{[c,d]} g`. -/
noncomputable def hstar : ℝ := sInf (gk '' Set.Icc ec ed)

/-- `j* = inf_{[2b,2c]} g`. -/
noncomputable def jstar : ℝ := sInf (gk '' Set.Icc (2 * eb) (2 * ec))

theorem rh_le_hstar : rh ≤ hstar := by
  apply le_csInf
  · exact ⟨gk ec, ⟨ec, ⟨le_refl _, by norm_num [ec, ed]⟩, rfl⟩⟩
  · rintro x ⟨u, ⟨h1, h2⟩, rfl⟩
    exact B3 u h1 h2

theorem rj_le_jstar : rj ≤ jstar := by
  apply le_csInf
  · exact ⟨gk (2 * eb), ⟨2 * eb, ⟨le_refl _, by norm_num [eb, ec]⟩, rfl⟩⟩
  · rintro x ⟨u, ⟨h1, h2⟩, rfl⟩
    exact B4 u h1 h2

/-- **Corollary.**  With `h* = inf_{[c,d]} g` and `j* = inf_{[2b,2c]} g`, for every `x ∈ ℝ⁶`
satisfying (P1)-(P4) one has `g(a)·x₁ + g(b)·x₂ + h*·x₄ + j*·x₆ ≥ F`. -/
theorem corollary (x1 x2 x3 x4 x5 x6 : ℝ)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3) (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5) (hx6 : 0 ≤ x6)
    (hP2 : x1 + x2 + x3 + x4 + x5 = nu)
    (hP3 : ea * x2 + eb * x3 + ec * x4 + ed * x5 ≤ 1)
    (hP4 : 2 * x3 - x6 ≤ nu) :
    Fbound ≤ gk ea * x1 + gk eb * x2 + hstar * x4 + jstar * x6 := by
  have h := theoremA x1 x2 x3 x4 x5 x6 (gk ea) (gk eb) 0 hstar 0 jstar
    hx1 hx2 hx3 hx4 hx5 hx6 hP2 hP3 hP4 B1 B2 le_rfl rh_le_hstar le_rfl rj_le_jstar
  linarith

end MTKernel
