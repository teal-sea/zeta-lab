import Zeta23Ext.EForm.Sharp

open scoped BigOperators
open scoped Real
open MeasureTheory

namespace Retention.EForm

/-!
# A single-pair bandlimited retention inequality

`gker u = cos (√2 u)` on `|u| ≤ 1/2` and `0` elsewhere, `c2` is its autocorrelation,
`Aconst = √2 sin (1/√2) = ∫ gker`, and

  `En G = (1/Aconst²) ∫_{-1}^{1} c2 w ‖G w‖² dw`.

For on-line points `x₁ < ⋯ < xₙ`, `F w = ∑_j exp (I xⱼ w)` and `P w = 2 cosh (y w) exp (I t w)`
the target inequality is

  `En (F + P) ≥ θ En F + (1 - θ) n + 4`,  `θ = 199/200`.

`retention_gap` below is the exact reduction of the problem: the difference of the two sides is

  `(1/Aconst²) ((1/200) (∑_{j,k} Icos (xⱼ - x_k) - n Aconst²)
      + (∑_j 4 Icross y (xⱼ - t) + 2 Ichy (2y)))`,

where `Icos s = ∫ c2 w cos (s w) dw = Φ₂(s)² ≥ 0` is the on-line interaction kernel,
`Icross y s = ∫ c2 w cosh (y w) cos (s w) dw` is (minus) the damage a single on-line point at
offset `s` does to the pair, and `2 Ichy (2y) = 2 ∫ c2 w (cosh (2 y w) - 1) dw` is the pair's own
slack.  The ingredients proved are:

* `Icos_nonneg` and `diag_bound` : `∑_{j,k} Icos (xⱼ - x_k) ≥ n Aconst²`, i.e. `En F ≥ n`;
* `Icross_lower_sharp` : `Icross y s ≥ - Shq y (Aconst + 1/4)/2` for every `s`, where
  `Shq y = ∫ gker u sinh (y u)² du`.  This is Cauchy-Schwarz for the weight `gker`,
  `(∫ gker sinh (y u) sin (s u))² ≤ Shq y · ∫ gker sin (s u)²`, combined with the uniform
  bound `Φ₂ ≥ -1/4` on the Fourier transform of the window (`Wcos_lower`);
* `Ichy_two_eq` : `Ichy (2y) = 4 Aconst · Shq y + 4 (Shq y)²`, the pair's slack, exactly;
* `Aconst_ge` : `Aconst ≥ 3/4`.

Together these give the inequality as soon as `2 n (Aconst + 1/4) ≤ 8 Aconst`, which holds for
`n ≤ 3`; that is `retention_le_three`, proved for the exact constants of the problem and
uniformly in the shift `t` and in the depth `y`.  For `n ≥ 4` no bound of the form
`Icross y s ≥ -κ · Shq y` with `κ` uniform in `s` can suffice (the numerically optimal `κ` is
about `0.245`, giving at best `n ≤ 7`); the finer, oscillation-sensitive behaviour of
`s ↦ Icross y s` (damage localized in narrow bands around the zeros of `Φ₂`, decaying like
`1/s²`) together with a cluster/repulsion argument is needed.  See `README.md`.
-/

/-- **Exact reduction of the retention inequality.**  The gap between the two sides of
`En (F + P) ≥ (199/200) En F + (1/200) n + 4` equals

`(1/A²) ((1/200) (∑_{j,k} Icos (xⱼ - x_k) - n A²) + (∑_j 4 Icross y (xⱼ - t) + 2 Ichy (2y)))`. -/
theorem retention_gap {n : ℕ} (x : Fin n → ℝ) (t y : ℝ) :
    En (fun w => (∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + 2 * (Real.cosh (y * w) : ℂ) * Complex.exp (Complex.I * ((t * w : ℝ) : ℂ)))
      - ((199/200) * En (fun w => ∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + (1/200) * n + 4)
      = (1 / Aconst ^ 2) * ((1 / 200) * ((∑ j, ∑ k, Icos (x j - x k)) - (n : ℝ) * Aconst ^ 2)
          + ((∑ j, 4 * Icross y (x j - t)) + 2 * Ichy (2 * y))) := by
  have hEFP : En (fun w => (∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + 2 * (Real.cosh (y * w) : ℂ) * Complex.exp (Complex.I * ((t * w : ℝ) : ℂ)))
      = En (fun w => Fsum x w + Pterm t y w) := rfl
  have hEF : En (fun w => ∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ))) = En (Fsum x) := rfl
  have hAne : Aconst ≠ 0 := ne_of_gt Aconst_pos
  rw [hEFP, hEF, En_FP, En_F]
  field_simp
  ring

/-- An offset `s` is *damaging* at depth `y` when the localization criterion of
`Icross_nonneg_of_Wcos_large` fails, i.e. when `|Φ₂(s)|` is small compared with `Shq y`.
Only such offsets can erode the pair term. -/
def IsNear (y s : ℝ) : Prop :=
  ¬ (Shq y / 2 ≤ |Wcos s| ∧ Shq y * ((Aconst + 1/4) / 2) ≤ (|Wcos s| - Shq y / 2) ^ 2)

open Classical in
/-- **Retention inequality whenever at most three on-line points are damaging**, at the exact
constants `θ = 199/200`, for an arbitrary number `n` of on-line points: it suffices that at
most three of the offsets `xⱼ - t` are damaging in the sense of `IsNear`, i.e. that all but at
most three of the on-line points sit at a place where `|Φ₂(xⱼ - t)|` is not small.

Quantitatively, `IsNear y s` fails as soon as `|Φ₂(s)| ≥ Shq y / 2 + √(Shq y (A + 1/4)/2)`,
a threshold of order `y` (about `0.11` at `y = 1/2`).  The criterion therefore covers a
configuration with arbitrarily many on-line points, provided all but three of them avoid both
the neighbourhoods of the zeros of `Φ₂` and the far region `|xⱼ - t| ≳ 1/y`, where `Φ₂` itself
is small.  (Points in the far region do in fact almost no damage — the damage decays like
`1/s²` — but that decay is not proved here, see `README.md`.)

The hypotheses `hx`, `hy0` and `hy1` are part of the problem statement; the proof does not use
them. -/
theorem retention_of_few_near {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) (t y : ℝ)
    (hy0 : 0 < y) (hy1 : y ≤ 1/2)
    (hcard : (Finset.univ.filter (fun j : Fin n => IsNear y (x j - t))).card ≤ 3) :
    En (fun w => (∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + 2 * (Real.cosh (y * w) : ℂ) * Complex.exp (Complex.I * ((t * w : ℝ) : ℂ)))
      ≥ (199/200) * En (fun w => ∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + (1/200) * n + 4 := by
  rw [ge_iff_le, ← sub_nonneg, retention_gap x t y]
  set S : ℝ := ∑ j, ∑ k, Icos (x j - x k) with hS
  set C : ℝ := ∑ j, 4 * Icross y (x j - t) with hC
  set N : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => IsNear y (x j - t)) with hN
  set m : ℕ := N.card with hm
  -- the on-line interaction energy is at least its diagonal
  have hdiag : (n : ℝ) * Aconst ^ 2 ≤ S := diag_bound x
  have hShq : 0 ≤ Shq y := Shq_nonneg y
  have hA : (3:ℝ)/4 ≤ Aconst := Aconst_ge
  -- split the damage into the damaging and the harmless offsets
  have hsplit : C = (∑ j ∈ N, 4 * Icross y (x j - t))
      + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ IsNear y (x j - t)), 4 * Icross y (x j - t) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hfar : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ IsNear y (x j - t)),
      4 * Icross y (x j - t) := by
    refine Finset.sum_nonneg (fun j hj => ?_)
    have hj' : ¬ IsNear y (x j - t) := (Finset.mem_filter.1 hj).2
    rw [IsNear, not_not] at hj'
    have := Icross_nonneg_of_Wcos_large y (x j - t) hj'.1 hj'.2
    linarith
  have hnear : -(4 * (m : ℝ) * (Shq y * ((Aconst + 1/4) / 2)))
      ≤ ∑ j ∈ N, 4 * Icross y (x j - t) := by
    have hterm : ∀ j ∈ N, -(4 * (Shq y * ((Aconst + 1/4) / 2))) ≤ 4 * Icross y (x j - t) := by
      intro j _
      have := Icross_lower_sharp y (x j - t)
      linarith
    calc -(4 * (m : ℝ) * (Shq y * ((Aconst + 1/4) / 2)))
        = ∑ _j ∈ N, -(4 * (Shq y * ((Aconst + 1/4) / 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← hm]; ring
      _ ≤ ∑ j ∈ N, 4 * Icross y (x j - t) := Finset.sum_le_sum hterm
  have hcross : -(4 * (m : ℝ) * (Shq y * ((Aconst + 1/4) / 2))) ≤ C := by
    rw [hsplit]; linarith
  -- the pair's own slack
  have hslack : Ichy (2 * y) = 4 * Aconst * Shq y + 4 * (Shq y) ^ 2 := Ichy_two_eq y
  have hm' : (m : ℝ) ≤ 3 := by exact_mod_cast hcard
  have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine mul_nonneg (by positivity) ?_
  have h1 : 0 ≤ (1 / 200) * (S - (n : ℝ) * Aconst ^ 2) := by linarith
  have e1 : 0 ≤ (3 - (m : ℝ)) * (Shq y * (Aconst + 1/4)) :=
    mul_nonneg (by linarith) (by nlinarith)
  have e2 : 0 ≤ Shq y * (2 * Aconst - 3/2) := mul_nonneg hShq (by linarith)
  have e3 : 0 ≤ Shq y ^ 2 := sq_nonneg _
  have h2 : 0 ≤ C + 2 * Ichy (2 * y) := by
    rw [hslack]; nlinarith [e1, e2, e3, hcross]
  linarith

/-- **Retention inequality for at most three on-line points**, at the exact constants
`θ = 199/200`: for every `t` and every depth `y ∈ (0, 1/2]`,
`E[F + P] ≥ (199/200) E[F] + (1/200) n + 4` whenever `n ≤ 3`.

The hypotheses `hx` (the on-line points are strictly increasing), `hy0` and `hy1` are part of
the problem statement; the proof does not use them (in particular the statement holds for
every real `y`). -/
theorem retention_le_three {n : ℕ} (hn : n ≤ 3) (x : Fin n → ℝ) (hx : StrictMono x) (t y : ℝ)
    (hy0 : 0 < y) (hy1 : y ≤ 1/2) :
    En (fun w => (∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + 2 * (Real.cosh (y * w) : ℂ) * Complex.exp (Complex.I * ((t * w : ℝ) : ℂ)))
      ≥ (199/200) * En (fun w => ∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + (1/200) * n + 4 := by
  classical
  refine retention_of_few_near x hx t y hy0 hy1 ?_
  calc (Finset.univ.filter (fun j : Fin n => IsNear y (x j - t))).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp
    _ ≤ 3 := hn

/-- **Retention inequality for at most two on-line points**, a special case of
`retention_le_three`. -/
theorem retention_le_two {n : ℕ} (hn : n ≤ 2) (x : Fin n → ℝ) (hx : StrictMono x) (t y : ℝ)
    (hy0 : 0 < y) (hy1 : y ≤ 1/2) :
    En (fun w => (∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + 2 * (Real.cosh (y * w) : ℂ) * Complex.exp (Complex.I * ((t * w : ℝ) : ℂ)))
      ≥ (199/200) * En (fun w => ∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ)))
        + (1/200) * n + 4 :=
  retention_le_three (by omega) x hx t y hy0 hy1

/-! ## Axiom audit -/

#print axioms retention_gap
#print axioms retention_of_few_near
#print axioms retention_le_three
#print axioms retention_le_two
#print axioms Icross_localized
#print axioms Icross_lower_sharp
#print axioms Ichy_two_eq
#print axioms Wcos_lower
#print axioms Icos_eq_sq
#print axioms Aconst_ge

end Retention.EForm
