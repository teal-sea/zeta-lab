import Mathlib

/-!
# Pair-energy positivity for a cosh-weighted exponential sum

This file establishes the statement of `PROBLEM.md`.

Let `g u = cos (√2 * u)` for `|u| ≤ 1/2` and `0` otherwise, let

  `c₂ w = ∫ u, g u * g (u - w)`,  `A = √2 * sin (1/√2) = ∫ u, g u`,

and, for `t, y : Fin k → ℝ`, let `S w = ∑ i, 2 * cosh (y i * w) * exp (I * t i * w)`.

We prove
  `4 * k ≤ (1 / A ^ 2) * ∫ w in (-1)..1, c₂ w * ‖S w‖ ^ 2`.

The proof has two parts.

*Analytic part.*  Since `g ≥ 0` and `g` is even, `c₂ = g ⋆ g` and for every `z : ℂ`
`∫ w, c₂ w * exp (z * w) = Ψ z ^ 2` where `Ψ z = ∫ u, g u * exp (z * u)`.  Writing
`S w = ∑ a : Fin k × Bool, exp (ζ a * w)` with `ζ (i, e) = ± y i + I * t i`, the energy becomes
`A ^ 2 * ∑ a, ∑ b, Q a b ^ 2` where `Q a b = Ψ (ζ a + conj (ζ b)) / A` is a Gram matrix of the
functions `u ↦ exp (ζ a * u)` for the probability measure `g u du / A`.  Consequently `Q` is
positive semidefinite, `Q a (σ a) = 1` for the fixed-point-free involution `σ (i, e) = (i, !e)`,
and `Q (σ a) (σ b) = Q b a`.

*Algebraic part.*  If `Q` is a positive semidefinite `2k × 2k` matrix with `Q a (σ a) = 1` and
`Q (σ a) (σ b) = Q b a`, then `∑ a, ∑ b, Q a b ^ 2 ≥ 4 k`.  Writing `P` for (twice) the
permutation matrix of `σ`, one has `∑ a, ∑ b, Q a b ^ 2 = tr ((QP)²)/4` and `tr (QP) = 4k`, while
`P/2 = V Vᴴ - W Wᴴ` with `V`, `W` having only `k` columns.  Writing `Q = Bᴴ B` and
`C = B P Bᴴ = Z Zᴴ - Y` (`Z = B V`, `Y = (BW)(BW)ᴴ`), the matrix `T = Z (ZᴴZ + ε)⁻¹ Zᴴ`
satisfies `0 ≤ T ≤ 1`, `tr (T²) ≤ k` and `tr (CT) ≥ tr C - ε k`; Cauchy–Schwarz for the trace
form then gives `(tr C)² ≤ k * tr (C²)` in the limit `ε → 0`, which is the claim.  This is the
usual inertia argument (`QP` has at most `k` positive eigenvalues), carried out without
spectral theory.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace PairEnergy

/-! ## Part I: trace inequalities for matrices -/

section MatrixPart

open Matrix ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
/-- The square of a Hermitian matrix is Hermitian. -/
lemma isHermitian_mul_self {C : Matrix ι ι ℂ} (hC : C.IsHermitian) : (C * C).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, hC.eq]

omit [Fintype ι] [DecidableEq ι] in
/-- `C - x • T` is Hermitian for real `x` and Hermitian `C`, `T`. -/
lemma isHermitian_sub_smul {C T : Matrix ι ι ℂ} (hC : C.IsHermitian) (hT : T.IsHermitian)
    (x : ℝ) : (C - (x : ℂ) • T).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hC.eq, hT.eq]
  simp [Complex.conj_ofReal]

omit [DecidableEq ι] in
/-- The trace of a Hermitian matrix is real. -/
lemma ofReal_trace_re {K : Matrix ι ι ℂ} (hK : K.IsHermitian) :
    ((K.trace.re : ℝ) : ℂ) = K.trace := by
  have h : star K.trace = K.trace := by rw [← Matrix.trace_conjTranspose, hK.eq]
  exact Complex.conj_eq_iff_re.mp h

omit [DecidableEq ι] in
/-- The trace of the square of a Hermitian matrix is nonnegative. -/
lemma trace_mul_self_nonneg {K : Matrix ι ι ℂ} (hK : K.IsHermitian) : 0 ≤ (K * K).trace := by
  have h : (K * K).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self K
    rwa [hK.eq] at this
  exact h.trace_nonneg

omit [DecidableEq ι] in
/-- The trace of a product of positive semidefinite matrices is nonnegative. -/
lemma trace_mul_nonneg {A K : Matrix ι ι ℂ} (hA : A.PosSemidef) (hK : K.PosSemidef) :
    0 ≤ (A * K).trace := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
    classical
    open scoped MatrixOrder in
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    exact ⟨B, by rw [hB, Matrix.star_eq_conjTranspose]⟩
  rw [hB, Matrix.mul_assoc, Matrix.trace_mul_comm Bᴴ (B * K)]
  have h2 : (B * K * Bᴴ).PosSemidef := by
    have := hK.conjTranspose_mul_mul_same (Bᴴ)
    simpa [Matrix.mul_assoc] using this
  exact h2.trace_nonneg

omit [DecidableEq ι] in
/-- Cauchy–Schwarz for the trace inner product on Hermitian matrices. -/
lemma trace_cauchy_schwarz {C T : Matrix ι ι ℂ} (hC : C.IsHermitian) (hT : T.IsHermitian) :
    ((C * T).trace.re) ^ 2 ≤ (C * C).trace.re * (T * T).trace.re := by
  set m := (C * C).trace.re with hm
  set p := (C * T).trace.re with hp
  set q := (T * T).trace.re with hq
  have hpre : ((p : ℝ) : ℂ) = (C * T).trace := by
    have h : star (C * T).trace = (C * T).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hC.eq, hT.eq,
        Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.mp h
  have hmre : ((m : ℝ) : ℂ) = (C * C).trace := ofReal_trace_re (isHermitian_mul_self hC)
  have hqre : ((q : ℝ) : ℂ) = (T * T).trace := ofReal_trace_re (isHermitian_mul_self hT)
  have key : ∀ x : ℝ, 0 ≤ q * (x * x) + (-2 * p) * x + m := by
    intro x
    have h0 := trace_mul_self_nonneg (isHermitian_sub_smul hC hT x)
    have hexp : ((C - (x : ℂ) • T) * (C - (x : ℂ) • T)).trace
        = ((q * (x * x) + (-2 * p) * x + m : ℝ) : ℂ) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
        Matrix.trace_sub]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [Matrix.trace_mul_comm T C, ← hpre, ← hmre, ← hqre]
      push_cast
      ring
    rw [hexp] at h0
    exact Complex.zero_le_real.mp h0
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- The regularised approximate projection onto the range of `Z`: for every `ε > 0` there is a
Hermitian `T` with `tr (T²) ≤ card κ` and `tr ((ZZᴴ - Y) T) ≥ tr (ZZᴴ - Y) - ε card κ`. -/
lemma exists_test_matrix (Z : Matrix ι κ ℂ) (Y : Matrix ι ι ℂ) (hY : Y.PosSemidef) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ T : Matrix ι ι ℂ, T.IsHermitian ∧ (T * T).trace.re ≤ (Fintype.card κ : ℝ) ∧
      (Z * Zᴴ - Y).trace.re - ε * (Fintype.card κ : ℝ) ≤ ((Z * Zᴴ - Y) * T).trace.re := by
  set S := Zᴴ * Z with hSdef
  have hS : S.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Z
  set Sε := S + (ε : ℂ) • (1 : Matrix κ κ ℂ) with hSε_def
  have hSε : Sε.PosDef := by
    have h1 : ((ε : ℂ) • (1 : Matrix κ κ ℂ)).PosDef :=
      Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hε)
    rw [hSε_def, add_comm]; exact h1.add_posSemidef hS
  set G := Sε⁻¹ with hGdef
  have hG : G.PosDef := hSε.inv
  have hGh : Gᴴ = G := hG.isHermitian
  have hu : IsUnit Sε.det := (Matrix.isUnit_iff_isUnit_det Sε).mp hSε.isUnit
  have hinv1 : Sε * G = 1 := Matrix.mul_nonsing_inv _ hu
  have hinv2 : G * Sε = 1 := Matrix.nonsing_inv_mul _ hu
  have hSsub : S = Sε - (ε : ℂ) • (1 : Matrix κ κ ℂ) := by rw [hSε_def]; abel
  have hGS : G * S = 1 - (ε : ℂ) • G := by
    rw [hSsub, Matrix.mul_sub, hinv2, Matrix.mul_smul, Matrix.mul_one]
  have hSG : S * G = 1 - (ε : ℂ) • G := by
    rw [hSsub, Matrix.sub_mul, hinv1, Matrix.smul_mul, Matrix.one_mul]
  set T := Z * G * Zᴴ with hTdef
  have hTh : T.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hTdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hGh, Matrix.mul_assoc]
  have hTT : T - T * T = (ε : ℂ) • ((Z * G) * (Z * G)ᴴ) := by
    have h1 : T * T = Z * (G * S * G) * Zᴴ := by
      rw [hTdef, hSdef]; simp only [Matrix.mul_assoc]
    have h2 : G * S * G = G - (ε : ℂ) • (G * G) := by
      rw [hGS, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [h1, h2, Matrix.conjTranspose_mul, hGh, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hTdef]
    simp only [Matrix.mul_assoc]
    abel
  have hPos1 : (T - T * T).PosSemidef := by
    rw [hTT]
    exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_lt_real.mpr hε).le
  have hPos2 : ((1 : Matrix ι ι ℂ) - T).PosSemidef := by
    have h1 : ((1 : Matrix ι ι ℂ) - T)ᴴ = 1 - T := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hTh.eq]
    have hid : ((1 : Matrix ι ι ℂ) - T) = ((1 : Matrix ι ι ℂ) - T)ᴴ * (1 - T) + (T - T * T) := by
      rw [h1]; noncomm_ring
    rw [hid]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).add hPos1
  have htrG : 0 ≤ G.trace := hG.posSemidef.trace_nonneg
  have htrT : T.trace = (Fintype.card κ : ℂ) - (ε : ℂ) * G.trace := by
    rw [hTdef, Matrix.trace_mul_comm (Z * G) Zᴴ, ← Matrix.mul_assoc, ← hSdef, hSG]
    rw [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul, smul_eq_mul]
  have htrTT : (T * T).trace ≤ (Fintype.card κ : ℂ) := by
    have h0 : 0 ≤ (T - T * T).trace := hPos1.trace_nonneg
    rw [Matrix.trace_sub] at h0
    calc (T * T).trace ≤ T.trace := sub_nonneg.mp h0
      _ ≤ (Fintype.card κ : ℂ) := by
          rw [htrT]
          exact sub_le_self _ (mul_nonneg (Complex.zero_le_real.mpr hε.le) htrG)
  refine ⟨T, hTh, ?_, ?_⟩
  · have := (Complex.le_def.mp htrTT).1
    simpa using this
  · have hCT : ((Z * Zᴴ - Y) - (Z * Zᴴ - Y) * T).trace
        ≤ ((ε * (Fintype.card κ : ℝ) : ℝ) : ℂ) := by
      have hsplit : ((Z * Zᴴ - Y) - (Z * Zᴴ - Y) * T)
          = ((Z * Zᴴ) * (1 - T)) - (Y * (1 - T)) := by noncomm_ring
      rw [hsplit, Matrix.trace_sub]
      have h1 : ((Z * Zᴴ) * (1 - T)).trace
          = (ε : ℂ) * ((Fintype.card κ : ℂ) - (ε : ℂ) * G.trace) := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
        have ha : (Z * Zᴴ).trace = S.trace := by rw [Matrix.trace_mul_comm Z Zᴴ, hSdef]
        have hb : (Z * Zᴴ * T).trace = (S * S * G).trace := by
          rw [hTdef]
          rw [show Z * Zᴴ * (Z * G * Zᴴ) = (Z * Zᴴ * Z * G) * Zᴴ by simp only [Matrix.mul_assoc]]
          rw [Matrix.trace_mul_comm (Z * Zᴴ * Z * G) Zᴴ, hSdef]
          simp only [Matrix.mul_assoc]
        rw [ha, hb]
        have hc : S * S * G = S - (ε : ℂ) • (1 - (ε : ℂ) • G) := by
          rw [Matrix.mul_assoc, hSG, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hSG]
        rw [hc, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one,
          Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
        ring
      have h2 : 0 ≤ (Y * (1 - T)).trace := trace_mul_nonneg hY hPos2
      have h3 : 0 ≤ (ε : ℂ) * ((ε : ℂ) * G.trace) :=
        mul_nonneg (Complex.zero_le_real.mpr hε.le)
          (mul_nonneg (Complex.zero_le_real.mpr hε.le) htrG)
      have heq : (ε : ℂ) * ((Fintype.card κ : ℂ) - (ε : ℂ) * G.trace)
          = ((ε * (Fintype.card κ : ℝ) : ℝ) : ℂ) - (ε : ℂ) * ((ε : ℂ) * G.trace) := by
        push_cast; ring
      rw [h1, heq]
      calc ((ε * (Fintype.card κ : ℝ) : ℝ) : ℂ) - (ε : ℂ) * ((ε : ℂ) * G.trace)
            - (Y * (1 - T)).trace
          ≤ ((ε * (Fintype.card κ : ℝ) : ℝ) : ℂ) - (ε : ℂ) * ((ε : ℂ) * G.trace) :=
            sub_le_self _ h2
        _ ≤ ((ε * (Fintype.card κ : ℝ) : ℝ) : ℂ) := sub_le_self _ h3
    have h4 := (Complex.le_def.mp hCT).1
    rw [Matrix.trace_sub] at h4
    simp only [Complex.sub_re, Complex.ofReal_re] at h4
    linarith

/-- The inertia bound: if `Q` is positive semidefinite and `P = V Vᴴ - W Wᴴ` where `V` and `W`
have `card κ` columns, then `(tr (Q P))² ≤ card κ * tr ((Q P)²)`. -/
theorem trace_sq_ge (Q : Matrix ι ι ℂ) (hQ : Q.PosSemidef) (V W : Matrix ι κ ℂ)
    (P : Matrix ι ι ℂ) (hP : P = V * Vᴴ - W * Wᴴ) (hpos : 0 ≤ (Q * P).trace.re) :
    ((Q * P).trace.re) ^ 2 ≤ (Fintype.card κ : ℝ) * ((Q * P * (Q * P)).trace.re) := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix ι ι ℂ, Q = Bᴴ * B := by
    open scoped MatrixOrder in
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
    exact ⟨B, by rw [hB, Matrix.star_eq_conjTranspose]⟩
  set Z := B * V with hZ
  set Y := (B * W) * (B * W)ᴴ with hY
  have hYpsd : Y.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  set C := Z * Zᴴ - Y with hC
  have hCeq : C = B * P * Bᴴ := by
    rw [hC, hZ, hY, hP, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_sub,
      Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hCh : C.IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose Z).1.sub hYpsd.1
  have htr1 : C.trace = (Q * P).trace := by
    rw [hCeq, Matrix.trace_mul_comm (B * P) Bᴴ, hB, ← Matrix.mul_assoc]
  have htr2 : (C * C).trace = (Q * P * (Q * P)).trace := by
    rw [hCeq]
    rw [show (B * P * Bᴴ) * (B * P * Bᴴ) = (B * (P * (Bᴴ * B) * P)) * Bᴴ by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm (B * (P * (Bᴴ * B) * P)) Bᴴ, hB]
    simp only [Matrix.mul_assoc]
  set a := (Q * P).trace.re with ha
  set X := (Q * P * (Q * P)).trace.re with hX
  set k := (Fintype.card κ : ℝ) with hk
  have hk0 : 0 ≤ k := by positivity
  have hX0 : 0 ≤ X := by
    have h := trace_mul_self_nonneg hCh
    rw [htr2] at h
    exact (Complex.le_def.mp h).1
  have main : ∀ ε : ℝ, 0 < ε → a - ε * k ≥ 0 → (a - ε * k) ^ 2 ≤ X * k := by
    intro ε hε hge
    obtain ⟨T, hTh, hTT, hCT⟩ := exists_test_matrix Z Y hYpsd ε hε
    rw [← hC, htr1] at hCT
    have hcs := trace_cauchy_schwarz hCh hTh
    rw [htr2] at hcs
    have hq0 : 0 ≤ (T * T).trace.re := (Complex.le_def.mp (trace_mul_self_nonneg hTh)).1
    nlinarith [hcs, hCT, hTT, hq0, hX0, hge]
  rcases eq_or_lt_of_le hpos with h0 | h0
  · nlinarith [hX0, hk0]
  · have hfin : a ^ 2 ≤ X * k := by
      refine le_of_forall_pos_le_add ?_
      intro d hd
      have hk1 : (0 : ℝ) < k + 1 := by linarith
      have hden : (0 : ℝ) < 2 * a * k + 1 := by nlinarith
      set ε := min (a / (k + 1)) (d / (2 * a * k + 1)) with hεdef
      have hε : 0 < ε := lt_min (by positivity) (by positivity)
      have hεk : ε * k ≤ a := by
        have h1 : ε ≤ a / (k + 1) := min_le_left _ _
        have h2 : ε * k ≤ (a / (k + 1)) * k := mul_le_mul_of_nonneg_right h1 hk0
        have h3 : (a / (k + 1)) * k ≤ a := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hk1]; nlinarith
        linarith
      have hm := main ε hε (by linarith)
      have h3 : ε ≤ d / (2 * a * k + 1) := min_le_right _ _
      have hak : (0 : ℝ) ≤ 2 * a * k := by nlinarith
      have h5 := mul_le_mul_of_nonneg_left h3 hak
      have h6 : 2 * a * k * (d / (2 * a * k + 1)) ≤ d := by
        rw [mul_div_assoc', div_le_iff₀ hden]; nlinarith
      nlinarith [hm, h5, h6, hε, hk0]
    linarith [hfin]

/-- The flip involution `(i, e) ↦ (i, !e)` on `Fin n × Bool`. -/
def flipEquiv (n : ℕ) : (Fin n × Bool) ≃ (Fin n × Bool) :=
  ⟨fun a => (a.1, !a.2), fun a => (a.1, !a.2), fun a => by simp, fun a => by simp⟩

/-- **Key algebraic inequality.**  If `Q` is a positive semidefinite matrix indexed by
`Fin n × Bool` with `Q a (a.1, !a.2) = 1` and `Q (a.1, !a.2) (b.1, !b.2) = Q b a`, then
`∑ a, ∑ b, (Q a b)² ≥ 4 n`. -/
theorem four_n_le_sum_sq (n : ℕ) (Q : Matrix (Fin n × Bool) (Fin n × Bool) ℂ) (hQ : Q.PosSemidef)
    (hdiag : ∀ a : Fin n × Bool, Q a (a.1, !a.2) = 1)
    (hsym : ∀ a b : Fin n × Bool, Q (a.1, !a.2) (b.1, !b.2) = Q b a) :
    (4 * n : ℝ) ≤ (∑ a, ∑ b, Q a b ^ 2).re := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  set P : Matrix (Fin n × Bool) (Fin n × Bool) ℂ := fun a b => if a = (b.1, !b.2) then 2 else 0
    with hPdef
  set V : Matrix (Fin n × Bool) (Fin n) ℂ := fun a j => if a.1 = j then 1 else 0 with hVdef
  set W : Matrix (Fin n × Bool) (Fin n) ℂ :=
    fun a j => if a.1 = j then (if a.2 then 1 else -1) else 0 with hWdef
  have hP : P = V * Vᴴ - W * Wᴴ := by
    have hPap : ∀ c d : Fin n × Bool, P c d = if c = (d.1, !d.2) then (2 : ℂ) else 0 := by
      intro c d; rw [hPdef]
    have hVap : ∀ (c : Fin n × Bool) (j : Fin n), V c j = if c.1 = j then (1 : ℂ) else 0 := by
      intro c j; rw [hVdef]
    have hWap : ∀ (c : Fin n × Bool) (j : Fin n),
        W c j = if c.1 = j then (if c.2 then (1 : ℂ) else -1) else 0 := by
      intro c j; rw [hWdef]
    ext a b
    have hVV : (V * Vᴴ) a b = if a.1 = b.1 then (1 : ℂ) else 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a.1]
      · rw [Matrix.conjTranspose_apply, hVap, hVap, if_pos rfl]
        by_cases h : a.1 = b.1
        · rw [if_pos h.symm, if_pos h]
          simp
        · have h' : ¬ (b.1 = a.1) := fun hh => h hh.symm
          rw [if_neg h', if_neg h]
          simp
      · intro l _ hl
        rw [hVap, if_neg (Ne.symm hl), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ a.1) h
    have hWW : (W * Wᴴ) a b = if a.1 = b.1 then
        ((if a.2 then (1 : ℂ) else -1) * (if b.2 then (1 : ℂ) else -1)) else 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a.1]
      · rw [Matrix.conjTranspose_apply, hWap, hWap, if_pos rfl]
        by_cases h : a.1 = b.1
        · rw [if_pos h.symm, if_pos h]
          cases hb : b.2 <;> simp
        · have h' : ¬ (b.1 = a.1) := fun hh => h hh.symm
          rw [if_neg h', if_neg h]
          simp
      · intro l _ hl
        rw [hWap, if_neg (Ne.symm hl), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ a.1) h
    rw [Matrix.sub_apply, hVV, hWW, hPap]
    by_cases h1 : a.1 = b.1
    · rw [if_pos h1, if_pos h1]
      rcases Bool.eq_false_or_eq_true a.2 with hab | hab <;>
        rcases Bool.eq_false_or_eq_true b.2 with hb | hb
      · have hne : a ≠ (b.1, !b.2) := by
          intro h; rw [h] at hab; simp [hb] at hab
        rw [if_neg hne, hab, hb]; norm_num
      · have heq : a = (b.1, !b.2) := by
          rw [Prod.ext_iff]; exact ⟨h1, by simp [hab, hb]⟩
        rw [if_pos heq, hab, hb]; norm_num
      · have heq : a = (b.1, !b.2) := by
          rw [Prod.ext_iff]; exact ⟨h1, by simp [hab, hb]⟩
        rw [if_pos heq, hab, hb]; norm_num
      · have hne : a ≠ (b.1, !b.2) := by
          intro h; rw [h] at hab; simp [hb] at hab
        rw [if_neg hne, hab, hb]; norm_num
    · have hne : a ≠ (b.1, !b.2) := by
        intro h
        exact h1 (by rw [h])
      rw [if_neg hne, if_neg h1, if_neg h1]
      ring
  have hQP : ∀ a b, (Q * P) a b = 2 * Q a (b.1, !b.2) := by
    intro a b
    rw [Matrix.mul_apply]
    simp only [hPdef, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have htr1 : (Q * P).trace = (4 * n : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, hQP, hdiag]
    simp [Finset.card_univ, mul_comm]
    ring
  have htr2 : (Q * P * (Q * P)).trace = 4 * ∑ a, ∑ b, Q a b ^ 2 := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, hQP]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (flipEquiv n) (fun b => (2 * Q a (b.1, !b.2)) * (2 * Q b (a.1, !a.2)))]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [flipEquiv, Equiv.coe_fn_mk, Bool.not_not]
    rw [hsym b a]
    ring
  have hpos : 0 ≤ (Q * P).trace.re := by rw [htr1]; simp
  have hkey := trace_sq_ge Q hQ V W P hP hpos
  rw [htr1, htr2] at hkey
  have e1 : ((4 : ℂ) * (n : ℂ)).re = 4 * (n : ℝ) := by simp
  have e2 : ((4 : ℂ) * ∑ a, ∑ b, Q a b ^ 2).re = 4 * (∑ a, ∑ b, Q a b ^ 2).re := by simp
  rw [Fintype.card_fin, e1, e2] at hkey
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith [hkey, hn']

end MatrixPart

/-! ## Part II: the kernel `g`, its autocorrelation `c₂` and the exponential moments -/

section Analysis

open MeasureTheory Matrix ComplexOrder

/-- The bandlimited kernel `g u = cos (√2 u)` on `[-1/2, 1/2]`, zero elsewhere. -/
noncomputable def gker (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * u) else 0

/-- The normalising constant `A = √2 sin (1/√2)`. -/
noncomputable def Aconst : ℝ := Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)

/-- The autocorrelation `c₂ w = ∫ g u * g (u - w) du`. -/
noncomputable def c2 (w : ℝ) : ℝ := ∫ u : ℝ, gker u * gker (u - w)

/-- The (two-sided) Laplace transform `Ψ z = ∫ g u * exp (z u) du` of `g`. -/
noncomputable def Psi (z : ℂ) : ℂ := ∫ u : ℝ, (gker u : ℂ) * Complex.exp (z * u)

lemma gker_eq_indicator :
    gker = Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun u => Real.cos (Real.sqrt 2 * u)) := by
  funext u
  rw [gker, Set.indicator_apply]
  congr 1
  simp [abs_le, Set.mem_Icc]

lemma gker_even (u : ℝ) : gker (-u) = gker u := by
  rw [gker, gker, abs_neg, mul_neg, Real.cos_neg]

lemma sqrt_two_lt_pi : Real.sqrt 2 < π := by
  have h1 : Real.sqrt 2 < 1.5 := by
    rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    apply Real.sqrt_lt_sqrt <;> norm_num
  linarith [Real.pi_gt_three]

/-- `g` is nonnegative: this is what makes `c₂` a nonnegative kernel. -/
lemma gker_nonneg (u : ℝ) : 0 ≤ gker u := by
  rw [gker]
  split_ifs with h
  · have habs : |Real.sqrt 2 * u| ≤ Real.sqrt 2 * (1 / 2) := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
      exact mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg 2)
    have h2 := abs_le.mp habs
    have h3 : Real.sqrt 2 * (1 / 2) ≤ π / 2 := by linarith [sqrt_two_lt_pi]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · exact le_refl 0

lemma integral_gker : ∫ u : ℝ, gker u = Aconst := by
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  rw [gker_eq_indicator, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hs2, integral_cos]
  have h2 : Real.sqrt 2 * (1 / 2) = 1 / Real.sqrt 2 := by
    rw [eq_div_iff hs2, mul_assoc, mul_comm (1 / 2 : ℝ), ← mul_assoc,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [show Real.sqrt 2 * (-(1 / 2)) = -(Real.sqrt 2 * (1 / 2)) by ring, h2, Real.sin_neg, Aconst,
    smul_eq_mul]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma Aconst_pos : 0 < Aconst := by
  rw [Aconst]
  apply mul_pos (Real.sqrt_pos.mpr (by norm_num))
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have h1 : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num)), show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith [Real.pi_gt_three]

lemma integrable_gker_mul {F : ℝ → ℂ} (hF : Continuous F) :
    Integrable (fun u => (gker u : ℂ) * F u) := by
  have heq : (fun u => (gker u : ℂ) * F u)
      = Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2))
        (fun u => (Real.cos (Real.sqrt 2 * u) : ℂ) * F u) := by
    funext u
    rw [gker_eq_indicator, Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp
  rw [heq]
  exact MeasureTheory.IntegrableOn.integrable_indicator
    (Continuous.integrableOn_Icc (by fun_prop)) measurableSet_Icc

lemma Psi_even (z : ℂ) : Psi (-z) = Psi z := by
  rw [Psi, Psi, ← integral_neg_eq_self (fun u : ℝ => (gker u : ℂ) * Complex.exp (z * u)) volume]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [gker_even]
  push_cast
  ring_nf

lemma Psi_zero : Psi 0 = (Aconst : ℂ) := by
  rw [Psi]
  simp only [zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, integral_gker]

/-- `c₂ w * exp (z w)` is the convolution of `u ↦ g u * exp (z u)` with itself. -/
lemma c2_exp_eq_conv (z : ℂ) (w : ℝ) :
    ((c2 w : ℝ) : ℂ) * Complex.exp (z * w)
      = convolution (fun u : ℝ => (gker u : ℂ) * Complex.exp (z * u))
          (fun u : ℝ => (gker u : ℂ) * Complex.exp (z * u))
          (ContinuousLinearMap.mul ℂ ℂ) volume w := by
  rw [convolution]
  simp only [ContinuousLinearMap.mul_apply']
  have key : ∀ u : ℝ, ((gker u : ℂ) * Complex.exp (z * (u : ℂ))) *
      ((gker (w - u) : ℂ) * Complex.exp (z * ((w - u : ℝ) : ℂ)))
      = ((gker u * gker (w - u) : ℝ) : ℂ) * Complex.exp (z * w) := by
    intro u
    rw [show ((gker u : ℂ) * Complex.exp (z * (u : ℂ))) *
        ((gker (w - u) : ℂ) * Complex.exp (z * ((w - u : ℝ) : ℂ)))
        = ((gker u : ℂ) * (gker (w - u) : ℂ)) *
          (Complex.exp (z * (u : ℂ)) * Complex.exp (z * ((w - u : ℝ) : ℂ))) by ring]
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  simp_rw [key]
  rw [MeasureTheory.integral_mul_const]
  congr 1
  rw [integral_complex_ofReal]
  congr 1
  rw [c2]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show gker u * gker (u - w) = gker u * gker (w - u)
  rw [show u - w = -(w - u) by ring, gker_even]

lemma integrable_c2_exp (z : ℂ) :
    Integrable (fun w : ℝ => ((c2 w : ℝ) : ℂ) * Complex.exp (z * w)) := by
  have hI : Integrable (fun u : ℝ => (gker u : ℂ) * Complex.exp (z * u)) :=
    integrable_gker_mul (by fun_prop)
  refine (hI.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hI).congr ?_
  filter_upwards with w
  exact (c2_exp_eq_conv z w).symm

/-- The exponential moments of `c₂`: `∫ c₂ w * exp (z w) dw = Ψ z ^ 2`. -/
lemma integral_c2_exp (z : ℂ) : ∫ w : ℝ, ((c2 w : ℝ) : ℂ) * Complex.exp (z * w) = Psi z ^ 2 := by
  have hI : Integrable (fun u : ℝ => (gker u : ℂ) * Complex.exp (z * u)) :=
    integrable_gker_mul (by fun_prop)
  have h := MeasureTheory.integral_convolution (μ := volume) (ν := volume)
    (ContinuousLinearMap.mul ℂ ℂ) hI hI
  calc ∫ w : ℝ, ((c2 w : ℝ) : ℂ) * Complex.exp (z * w)
      = ∫ w : ℝ, convolution (fun u : ℝ => (gker u : ℂ) * Complex.exp (z * u))
          (fun u : ℝ => (gker u : ℂ) * Complex.exp (z * u))
          (ContinuousLinearMap.mul ℂ ℂ) volume w :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => c2_exp_eq_conv z w)
    _ = Psi z ^ 2 := by rw [h]; simp [Psi, sq]

/-- `c₂` vanishes outside `(-1, 1)`. -/
lemma c2_eq_zero_of_one_le_abs {w : ℝ} (hw : 1 ≤ |w|) : c2 w = 0 := by
  rw [c2]
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  have hnull : volume ({w / 2} : Set ℝ) = 0 := measure_singleton _
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with u hu
  by_contra hne
  have h1 : gker u ≠ 0 := fun h => hne (by simp [h])
  have h2 : gker (u - w) ≠ 0 := fun h => hne (by simp [h])
  have hu1 : |u| ≤ 1 / 2 := by
    by_contra hcon
    exact h1 (by rw [gker, if_neg hcon])
  have hu2 : |u - w| ≤ 1 / 2 := by
    by_contra hcon
    exact h2 (by rw [gker, if_neg hcon])
  have ha1 := abs_le.mp hu1
  have ha2 := abs_le.mp hu2
  have : u = w / 2 := by
    rcases abs_cases w with ⟨he, _⟩ | ⟨he, _⟩
    · have hw1 : 1 ≤ w := by rw [he] at hw; linarith
      linarith [ha1.1, ha1.2, ha2.1, ha2.2]
    · have hw1 : w ≤ -1 := by rw [he] at hw; linarith
      linarith [ha1.1, ha1.2, ha2.1, ha2.2]
  exact hu (by simp [this])

/-- Gram matrices for the nonnegative weight `g` are positive semidefinite. -/
lemma gram_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℝ → ℂ)
    (he : ∀ a, Continuous (e a)) :
    (Matrix.of fun a b => ∫ u : ℝ, (gker u : ℂ) * (e a u * (starRingEnd ℂ) (e b u))).PosSemidef := by
  set M : Matrix ι ι ℂ :=
    Matrix.of fun a b => ∫ u : ℝ, (gker u : ℂ) * (e a u * (starRingEnd ℂ) (e b u)) with hM
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, hM, Matrix.of_apply, RCLike.star_def]
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [mul_comm]
  · intro x
    set A : ι → ℝ → ℂ := fun a u => (starRingEnd ℂ) (x a) * e a u with hA
    have expand : star x ⬝ᵥ (M *ᵥ x) = ∑ a, ∑ b, (starRingEnd ℂ) (x a) * (M a b * x b) := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    have hterm : ∀ a b : ι, (starRingEnd ℂ) (x a) * (M a b * x b)
        = ∫ u : ℝ, (gker u : ℂ) * (A a u * (starRingEnd ℂ) (A b u)) := by
      intro a b
      simp only [hM, Matrix.of_apply, hA]
      rw [show (starRingEnd ℂ) (x a) *
          ((∫ u : ℝ, (gker u : ℂ) * (e a u * (starRingEnd ℂ) (e b u))) * x b)
          = ((starRingEnd ℂ) (x a) * x b) *
            ∫ u : ℝ, (gker u : ℂ) * (e a u * (starRingEnd ℂ) (e b u)) by ring,
        ← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [map_mul, Complex.conj_conj]
      ring
    have hint : ∀ a b : ι, Integrable
        (fun u : ℝ => (gker u : ℂ) * (A a u * (starRingEnd ℂ) (A b u))) := by
      intro a b
      refine integrable_gker_mul (Continuous.mul ?_ ?_)
      · rw [hA]; exact continuous_const.mul (he a)
      · rw [hA]; exact Complex.continuous_conj.comp (continuous_const.mul (he b))
    have hswap : (∑ a, ∑ b, ∫ u : ℝ, (gker u : ℂ) * (A a u * (starRingEnd ℂ) (A b u)))
        = ∫ u : ℝ, ∑ a, ∑ b, (gker u : ℂ) * (A a u * (starRingEnd ℂ) (A b u)) := by
      rw [MeasureTheory.integral_finsetSum _
        (fun a _ => integrable_finsetSum _ fun b _ => hint a b)]
      exact Finset.sum_congr rfl fun a _ =>
        (MeasureTheory.integral_finsetSum _ fun b _ => hint a b).symm
    have hpt : ∀ u : ℝ, (∑ a, ∑ b, (gker u : ℂ) * (A a u * (starRingEnd ℂ) (A b u)))
        = ((gker u * Complex.normSq (∑ a, A a u) : ℝ) : ℂ) := by
      intro u
      have h1 : ∑ a, ∑ b, (gker u : ℂ) * (A a u * (starRingEnd ℂ) (A b u))
          = (gker u : ℂ) * ((∑ a, A a u) * (starRingEnd ℂ) (∑ b, A b u)) := by
        rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
      rw [h1, Complex.mul_conj]
      push_cast
      ring
    rw [expand]
    simp only [hterm]
    rw [hswap]
    simp only [hpt]
    rw [integral_complex_ofReal]
    refine Complex.zero_le_real.mpr (integral_nonneg fun u => ?_)
    exact mul_nonneg (gker_nonneg u) (Complex.normSq_nonneg _)

/-! ## Part III: the pair energy -/

variable {k : ℕ}

/-- The exponents `ζ (i, e) = ± y i + I * t i` of the `2k` complex exponentials making up `S`. -/
noncomputable def zeta (y t : Fin k → ℝ) (a : Fin k × Bool) : ℂ :=
  ((if a.2 then y a.1 else -y a.1 : ℝ) : ℂ) + Complex.I * (t a.1 : ℂ)

/-- The cosh-weighted exponential sum `S w = ∑ i, 2 cosh (y i w) exp (I t i w)`. -/
noncomputable def Ssum (y t : Fin k → ℝ) (w : ℝ) : ℂ :=
  ∑ i, 2 * (Real.cosh (y i * w) : ℂ) * Complex.exp (Complex.I * (t i : ℂ) * (w : ℂ))

lemma two_mul_cosh (z : ℂ) : 2 * Complex.cosh z = Complex.exp z + Complex.exp (-z) := by
  have h1 := Complex.cosh_add_sinh z
  have h2 := Complex.cosh_sub_sinh z
  linear_combination h1 + h2

lemma Ssum_eq_sum_exp (y t : Fin k → ℝ) (w : ℝ) :
    Ssum y t w = ∑ a : Fin k × Bool, Complex.exp (zeta y t a * w) := by
  rw [Ssum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  have hc : ((Real.cosh (y i * w) : ℝ) : ℂ) = Complex.cosh ((y i : ℂ) * (w : ℂ)) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
  have e1 : zeta y t (i, true) = (y i : ℂ) + Complex.I * (t i : ℂ) := by simp [zeta]
  have e2 : zeta y t (i, false) = -(y i : ℂ) + Complex.I * (t i : ℂ) := by simp [zeta]
  rw [e1, e2, hc,
    show ((y i : ℂ) + Complex.I * (t i : ℂ)) * (w : ℂ)
      = (y i : ℂ) * (w : ℂ) + Complex.I * (t i : ℂ) * (w : ℂ) by ring,
    show (-(y i : ℂ) + Complex.I * (t i : ℂ)) * (w : ℂ)
      = -((y i : ℂ) * (w : ℂ)) + Complex.I * (t i : ℂ) * (w : ℂ) by ring,
    Complex.exp_add, Complex.exp_add, ← add_mul, ← two_mul_cosh]

/-- The (normalised) Gram matrix of the exponentials `u ↦ exp (ζ a u)`. -/
noncomputable def Qmat (y t : Fin k → ℝ) : Matrix (Fin k × Bool) (Fin k × Bool) ℂ :=
  Matrix.of fun a b => Psi (zeta y t a + (starRingEnd ℂ) (zeta y t b)) / (Aconst : ℂ)

lemma Psi_zeta_eq (y t : Fin k → ℝ) (a b : Fin k × Bool) :
    Psi (zeta y t a + (starRingEnd ℂ) (zeta y t b))
      = ∫ u : ℝ, (gker u : ℂ) *
          (Complex.exp (zeta y t a * u) * (starRingEnd ℂ) (Complex.exp (zeta y t b * u))) := by
  rw [Psi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hconj : (starRingEnd ℂ) (Complex.exp (zeta y t b * u))
      = Complex.exp ((starRingEnd ℂ) (zeta y t b) * u) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  show (gker u : ℂ) * Complex.exp ((zeta y t a + (starRingEnd ℂ) (zeta y t b)) * u)
      = (gker u : ℂ) *
        (Complex.exp (zeta y t a * u) * (starRingEnd ℂ) (Complex.exp (zeta y t b * u)))
  rw [hconj, ← Complex.exp_add, add_mul]

lemma Qmat_posSemidef (y t : Fin k → ℝ) : (Qmat y t).PosSemidef := by
  have hgram := gram_posSemidef (fun a : Fin k × Bool => fun u : ℝ => Complex.exp (zeta y t a * u))
    (fun a => by fun_prop)
  have hnn : (0 : ℂ) ≤ ((Aconst : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (le_of_lt (inv_pos.mpr Aconst_pos))
  have heq : Qmat y t
      = ((Aconst : ℂ))⁻¹ • (Matrix.of fun a b : Fin k × Bool => ∫ u : ℝ, (gker u : ℂ) *
          (Complex.exp (zeta y t a * u) * (starRingEnd ℂ) (Complex.exp (zeta y t b * u)))) := by
    ext a b
    rw [Qmat, Matrix.of_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      Psi_zeta_eq, div_eq_inv_mul]
  rw [heq]
  exact hgram.smul hnn

lemma Qmat_diag (y t : Fin k → ℝ) (a : Fin k × Bool) : Qmat y t a (a.1, !a.2) = 1 := by
  have hz : zeta y t a + (starRingEnd ℂ) (zeta y t (a.1, !a.2)) = 0 := by
    obtain ⟨i, e⟩ := a
    cases e <;> simp [zeta, Complex.ext_iff]
  have hA : (Aconst : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Aconst_pos)
  rw [Qmat, Matrix.of_apply, hz, Psi_zero, div_self hA]

lemma Qmat_sym (y t : Fin k → ℝ) (a b : Fin k × Bool) :
    Qmat y t (a.1, !a.2) (b.1, !b.2) = Qmat y t b a := by
  have hz : zeta y t (a.1, !a.2) + (starRingEnd ℂ) (zeta y t (b.1, !b.2))
      = -(zeta y t b + (starRingEnd ℂ) (zeta y t a)) := by
    obtain ⟨i, e⟩ := a
    obtain ⟨j, f⟩ := b
    cases e <;> cases f <;> simp [zeta, Complex.ext_iff]
  rw [Qmat, Matrix.of_apply, Matrix.of_apply, hz, Psi_even]

/-- Pointwise expansion of `|S w| ^ 2` as a double sum of exponentials. -/
lemma Ssum_normSq (y t : Fin k → ℝ) (w : ℝ) :
    ((‖Ssum y t w‖ ^ 2 : ℝ) : ℂ)
      = ∑ a : Fin k × Bool, ∑ b : Fin k × Bool,
          Complex.exp ((zeta y t a + (starRingEnd ℂ) (zeta y t b)) * w) := by
  have h1 : ((‖Ssum y t w‖ ^ 2 : ℝ) : ℂ) = Ssum y t w * (starRingEnd ℂ) (Ssum y t w) := by
    rw [Complex.mul_conj]; norm_cast; exact (Complex.normSq_eq_norm_sq _).symm
  rw [h1, Ssum_eq_sum_exp, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, add_mul]

/-- The pair energy over the whole line, expanded via the exponential moments of `c₂`. -/
lemma energy_eq_sum_Psi (y t : Fin k → ℝ) :
    ((∫ w : ℝ, c2 w * ‖Ssum y t w‖ ^ 2 : ℝ) : ℂ)
      = ∑ a : Fin k × Bool, ∑ b : Fin k × Bool,
          Psi (zeta y t a + (starRingEnd ℂ) (zeta y t b)) ^ 2 := by
  rw [← integral_complex_ofReal]
  have hpt : ∀ w : ℝ, ((c2 w * ‖Ssum y t w‖ ^ 2 : ℝ) : ℂ)
      = ∑ a : Fin k × Bool, ∑ b : Fin k × Bool,
          ((c2 w : ℝ) : ℂ) * Complex.exp ((zeta y t a + (starRingEnd ℂ) (zeta y t b)) * w) := by
    intro w
    rw [Complex.ofReal_mul, Ssum_normSq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  simp_rw [hpt]
  rw [MeasureTheory.integral_finsetSum _
    (fun a _ => integrable_finsetSum _ fun b _ => integrable_c2_exp _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun b _ => integrable_c2_exp _)]
  exact Finset.sum_congr rfl fun b _ => integral_c2_exp _

/-- The energy integral over `[-1, 1]` agrees with the integral over the whole line. -/
lemma interval_energy_eq (y t : Fin k → ℝ) :
    (∫ w in (-1 : ℝ)..1, c2 w * ‖Ssum y t w‖ ^ 2)
      = ∫ w : ℝ, c2 w * ‖Ssum y t w‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have hx1 : 1 ≤ |x| := by
    rw [Set.mem_Ioc] at hx
    push Not at hx
    rcases le_or_gt x (-1) with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · have := hx h
      rw [abs_of_nonneg (by linarith)]; linarith
  rw [c2_eq_zero_of_one_le_abs hx1, zero_mul]

lemma Psi_eq_Aconst_mul_Qmat (y t : Fin k → ℝ) (a b : Fin k × Bool) :
    Psi (zeta y t a + (starRingEnd ℂ) (zeta y t b)) = (Aconst : ℂ) * Qmat y t a b := by
  have hA : (Aconst : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Aconst_pos)
  rw [Qmat, Matrix.of_apply]
  field_simp

/-- The energy in terms of the normalised Gram matrix `Q`. -/
lemma energy_eq_Aconst_sq_mul (y t : Fin k → ℝ) :
    (∫ w : ℝ, c2 w * ‖Ssum y t w‖ ^ 2)
      = Aconst ^ 2 * (∑ a : Fin k × Bool, ∑ b : Fin k × Bool, Qmat y t a b ^ 2).re := by
  have h := energy_eq_sum_Psi y t
  simp_rw [Psi_eq_Aconst_mul_Qmat, mul_pow] at h
  have h2 : (∑ a : Fin k × Bool, ∑ b : Fin k × Bool, (Aconst : ℂ) ^ 2 * Qmat y t a b ^ 2)
      = ((Aconst ^ 2 : ℝ) : ℂ) * ∑ a : Fin k × Bool, ∑ b : Fin k × Bool, Qmat y t a b ^ 2 := by
    simp [Complex.ofReal_pow, Finset.mul_sum]
  rw [h2] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre
  exact hre

/-- **Main theorem** (general form): for all real `y i` and `t i`, the `c₂`-weighted energy of
`S w = ∑ i, 2 cosh (y i w) exp (I t i w)`, normalised by `A ^ 2`, is at least `4 k`. -/
theorem four_k_le_energy (y t : Fin k → ℝ) :
    (4 * k : ℝ) ≤ (1 / Aconst ^ 2) * ∫ w in (-1 : ℝ)..1, c2 w * ‖Ssum y t w‖ ^ 2 := by
  have hA2 : (Aconst : ℝ) ^ 2 ≠ 0 := ne_of_gt (pow_pos Aconst_pos 2)
  have hQ := four_n_le_sum_sq k (Qmat y t) (Qmat_posSemidef y t) (Qmat_diag y t) (Qmat_sym y t)
  rw [interval_energy_eq, energy_eq_Aconst_sq_mul, ← mul_assoc, one_div,
    inv_mul_cancel₀ hA2, one_mul]
  exact hQ

/-- **Main theorem**, in the exact form of `PROBLEM.md`.  The hypotheses `1 ≤ k` and
`y i ∈ [0, 1/2]` are stated as requested but are in fact not needed: the bound holds for every
`k` and all real `y i`, `t i` (see `four_k_le_energy`). -/
theorem pair_energy_ge (k : ℕ) (y t : Fin k → ℝ) (_hk : 1 ≤ k)
    (_hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (4 * k : ℝ) ≤ (1 / Aconst ^ 2) *
      ∫ w in (-1 : ℝ)..1, c2 w * ‖∑ i, 2 * (Real.cosh (y i * w) : ℂ) *
        Complex.exp (Complex.I * (t i : ℂ) * (w : ℂ))‖ ^ 2 :=
  four_k_le_energy y t

end Analysis

end PairEnergy

/-! ## Axiom audit: every theorem of this file depends only on
`propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms PairEnergy.isHermitian_mul_self
#print axioms PairEnergy.isHermitian_sub_smul
#print axioms PairEnergy.ofReal_trace_re
#print axioms PairEnergy.trace_mul_self_nonneg
#print axioms PairEnergy.trace_mul_nonneg
#print axioms PairEnergy.trace_cauchy_schwarz
#print axioms PairEnergy.exists_test_matrix
#print axioms PairEnergy.trace_sq_ge
#print axioms PairEnergy.four_n_le_sum_sq
#print axioms PairEnergy.gker_eq_indicator
#print axioms PairEnergy.gker_even
#print axioms PairEnergy.sqrt_two_lt_pi
#print axioms PairEnergy.gker_nonneg
#print axioms PairEnergy.integral_gker
#print axioms PairEnergy.Aconst_pos
#print axioms PairEnergy.integrable_gker_mul
#print axioms PairEnergy.Psi_even
#print axioms PairEnergy.Psi_zero
#print axioms PairEnergy.c2_exp_eq_conv
#print axioms PairEnergy.integrable_c2_exp
#print axioms PairEnergy.integral_c2_exp
#print axioms PairEnergy.c2_eq_zero_of_one_le_abs
#print axioms PairEnergy.gram_posSemidef
#print axioms PairEnergy.two_mul_cosh
#print axioms PairEnergy.Ssum_eq_sum_exp
#print axioms PairEnergy.Psi_zeta_eq
#print axioms PairEnergy.Qmat_posSemidef
#print axioms PairEnergy.Qmat_diag
#print axioms PairEnergy.Qmat_sym
#print axioms PairEnergy.Ssum_normSq
#print axioms PairEnergy.energy_eq_sum_Psi
#print axioms PairEnergy.interval_energy_eq
#print axioms PairEnergy.Psi_eq_Aconst_mul_Qmat
#print axioms PairEnergy.energy_eq_Aconst_sq_mul
#print axioms PairEnergy.four_k_le_energy
#print axioms PairEnergy.pair_energy_ge
