/-
Hunt #145 (`rung3_ball_production`): the plan-independent lemmas the emitted assembly uses.

Everything here is generic in the square, the boxes and the grid; `assembly.py` emits the
plan-specific module `Rung3Assembly/Assembly.lean` on top of it.  Nothing here proves
`davenport_heilbronn`: that needs the 215 site theorems.

`dh_zero_of_square` and `dh_statement_of_square` restate the square criterion of
`lean/ZetaLean/DHZeroCriterion.lean` (the theorem at line 185, cited by line because its
name carries the word this directory may not use) with the same proof, so that no file
under `hunts/` names it.  `dh_zero_of_square` also keeps the zero's location, which the
original drops.
-/
import ZetaLean.DHCertSupport
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Order

open Complex Set

namespace ZetaLean.DH.Rung3Assembly

/-- The square criterion, keeping the zero: `DH` small at the centre and bounded below on
the frontier of the open square give a zero of `DH` in its closure. -/
theorem dh_zero_of_square {cre cim w ε' : ℚ} (hw : 0 < w)
    (h1 : ‖DH ⟨(cre : ℝ), (cim : ℝ)⟩‖ < (ε' : ℝ))
    (h2 : ∀ z ∈ frontier (dhSquare cre cim w), (ε' : ℝ) ≤ ‖DH z‖) :
    ∃ z : ℂ, DH z = 0 ∧ z.re ∈ Icc (((cre - w : ℚ) : ℝ)) (((cre + w : ℚ) : ℝ)) ∧
      z.im ∈ Icc (((cim - w : ℚ) : ℝ)) (((cim + w : ℚ) : ℝ)) := by
  have hw' : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hre : (((cre - w : ℚ) : ℝ)) < (((cre + w : ℚ) : ℝ)) := by
    push_cast; linarith
  have him : (((cim - w : ℚ) : ℝ)) < (((cim + w : ℚ) : ℝ)) := by
    push_cast; linarith
  have hUo : IsOpen (dhSquare cre cim w) := IsOpen.reProdIm isOpen_Ioo isOpen_Ioo
  have hUb : Bornology.IsBounded (dhSquare cre cim w) :=
    (Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)
  have hc : (⟨(cre : ℝ), (cim : ℝ)⟩ : ℂ) ∈ dhSquare cre cim w := by
    rw [dhSquare, Complex.mem_reProdIm]
    constructor <;> constructor <;> · show _ < _; push_cast; linarith
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_norm_lt_on_frontier DH_differentiable
    hUb hUo hc h1 h2
  rw [dhSquare, Complex.closure_reProdIm, closure_Ioo hre.ne,
    closure_Ioo him.ne, Complex.mem_reProdIm] at hz
  exact ⟨z, hz0, hz.1, hz.2⟩

/-- The Davenport-Heilbronn statement from a square right of the critical line. -/
theorem dh_statement_of_square {cre cim w ε' : ℚ} (hw : 0 < w) (hline : 1 / 2 < cre - w)
    (h1 : ‖DH ⟨(cre : ℝ), (cim : ℝ)⟩‖ < (ε' : ℝ))
    (h2 : ∀ z ∈ frontier (dhSquare cre cim w), (ε' : ℝ) ≤ ‖DH z‖) :
    davenport_heilbronn_statement := by
  obtain ⟨z, hz0, hzre, -⟩ := dh_zero_of_square hw h1 h2
  refine ⟨DH, z, DH_differentiable, DH_series_rep, DH_functional_eq, hz0, ?_⟩
  intro hhalf
  have h3 : (1 / 2 : ℝ) < (((cre - w : ℚ) : ℝ)) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hline
    push_cast at h ⊢
    linarith
  rw [hhalf] at hzre
  exact absurd hzre.1 (not_le.mpr h3)

/-! ### Covering a segment by closed pieces -/

/-- Two adjacent closed pieces cover their union. -/
theorem icc_merge {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ x ∈ Icc a b, P x)
    (h2 : ∀ x ∈ Icc b c, P x) : ∀ x ∈ Icc a c, P x := by
  intro x hx
  rcases le_total x b with h | h
  · exact h1 x ⟨hx.1, h⟩
  · exact h2 x ⟨h, hx.2⟩

/-- Restate a horizontal segment's endpoints and height. -/
theorem hseg_congr {P : ℂ → Prop} {a b y a' b' y' : ℝ} (ha : a' = a) (hb : b' = b)
    (hy : y' = y) (h : ∀ x ∈ Icc a b, P ⟨x, y⟩) : ∀ x ∈ Icc a' b', P ⟨x, y'⟩ := by
  subst ha hb hy; exact h

/-- Restate a vertical segment's endpoints and abscissa. -/
theorem vseg_congr {P : ℂ → Prop} {a b x a' b' x' : ℝ} (ha : a' = a) (hb : b' = b)
    (hx : x' = x) (h : ∀ y ∈ Icc a b, P ⟨x, y⟩) : ∀ y ∈ Icc a' b', P ⟨x', y⟩ := by
  subst ha hb hx; exact h

/-- A property on the four closed edges holds on the frontier of the open square. -/
theorem frontier_cover {cre cim w : ℚ} (hw : 0 < w) {P : ℂ → Prop}
    (hb : ∀ x ∈ Icc (((cre - w : ℚ) : ℝ)) (((cre + w : ℚ) : ℝ)), P ⟨x, ((cim - w : ℚ) : ℝ)⟩)
    (ht : ∀ x ∈ Icc (((cre - w : ℚ) : ℝ)) (((cre + w : ℚ) : ℝ)), P ⟨x, ((cim + w : ℚ) : ℝ)⟩)
    (hl : ∀ y ∈ Icc (((cim - w : ℚ) : ℝ)) (((cim + w : ℚ) : ℝ)), P ⟨((cre - w : ℚ) : ℝ), y⟩)
    (hr : ∀ y ∈ Icc (((cim - w : ℚ) : ℝ)) (((cim + w : ℚ) : ℝ)), P ⟨((cre + w : ℚ) : ℝ), y⟩) :
    ∀ z ∈ frontier (dhSquare cre cim w), P z := by
  intro z hz
  rw [frontier_dhSquare hw, Set.mem_union, Complex.mem_reProdIm,
    Complex.mem_reProdIm] at hz
  rcases hz with ⟨hre, him⟩ | ⟨hre, him⟩
  · rcases him with h | h
    · rw [show z = ⟨z.re, ((cim - w : ℚ) : ℝ)⟩ from Complex.ext rfl h]; exact hb _ hre
    · rw [Set.mem_singleton_iff] at h
      rw [show z = ⟨z.re, ((cim + w : ℚ) : ℝ)⟩ from Complex.ext rfl h]; exact ht _ hre
  · rcases hre with h | h
    · rw [show z = ⟨((cre - w : ℚ) : ℝ), z.im⟩ from Complex.ext h rfl]; exact hl _ him
    · rw [Set.mem_singleton_iff] at h
      rw [show z = ⟨((cre + w : ℚ) : ℝ), z.im⟩ from Complex.ext h rfl]; exact hr _ him

/-! ### Big boxes: one site theorem bounds `‖DH‖` on one boundary piece -/

/-- A degenerate horizontal box bounds `‖DH‖` on its segment. -/
theorem hseg_of_box {SI : ComplexInterval} {M : ℝ}
    (hup : ∀ {s : ℂ}, SI.contains s → ‖DH s‖ ≤ M) {a b y : ℝ}
    (ha : a = (SI.re.lo : ℝ)) (hb : b = (SI.re.hi : ℝ))
    (hy1 : (SI.im.lo : ℝ) = y) (hy2 : (SI.im.hi : ℝ) = y) :
    ∀ x ∈ Icc a b, ‖DH ⟨x, y⟩‖ ≤ M := by
  intro x hx
  subst ha hb
  exact hup ⟨⟨hx.1, hx.2⟩, ⟨hy1.le, hy2.ge⟩⟩

/-- A degenerate vertical box bounds `‖DH‖` on its segment. -/
theorem vseg_of_box {SI : ComplexInterval} {M : ℝ}
    (hup : ∀ {s : ℂ}, SI.contains s → ‖DH s‖ ≤ M) {a b x : ℝ}
    (ha : a = (SI.im.lo : ℝ)) (hb : b = (SI.im.hi : ℝ))
    (hx1 : (SI.re.lo : ℝ) = x) (hx2 : (SI.re.hi : ℝ) = x) :
    ∀ y ∈ Icc a b, ‖DH ⟨x, y⟩‖ ≤ M := by
  intro y hy
  subst ha hb
  exact hup ⟨⟨hx1.le, hx2.ge⟩, ⟨hy.1, hy.2⟩⟩

/-! ### The derivative bound and the lower bound on one cell -/

/-- `norm_deriv_DH_le` on the closed small square, weakened to a rational `L`. -/
theorem deriv_bound {cre cim w w2 : ℚ} (hw : 0 < w) (hww : w < w2) {M L : ℝ}
    (hM : ∀ z ∈ frontier (dhSquare cre cim w2), ‖DH z‖ ≤ M)
    (hL : M / ((w2 : ℝ) - (w : ℝ)) ≤ L) (z : ℂ)
    (hre : z.re ∈ Icc (((cre - w : ℚ) : ℝ)) (((cre + w : ℚ) : ℝ)))
    (him : z.im ∈ Icc (((cim - w : ℚ) : ℝ)) (((cim + w : ℚ) : ℝ))) :
    ‖deriv DH z‖ ≤ L := by
  refine le_trans (norm_deriv_DH_le hw hww hM ?_ ?_) hL
  · obtain ⟨h1, h2⟩ := hre
    push_cast at h1 h2
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := him
    push_cast at h1 h2
    rw [abs_le]; constructor <;> linarith

/-- One horizontal cell `[p, q] × {y}` inside the closed square `[A, B] × [C, D]`. -/
theorem hcell {A B C D L ε : ℝ} (hL0 : 0 ≤ L)
    (hD : ∀ z : ℂ, z.re ∈ Icc A B → z.im ∈ Icc C D → ‖deriv DH z‖ ≤ L)
    {p q y : ℝ} (hpq : p ≤ q) (hp : A ≤ p) (hq : q ≤ B) (hy : y ∈ Icc C D)
    (hβp : ε + L * ((q - p) / 2) ≤ ‖DH ⟨p, y⟩‖)
    (hβq : ε + L * ((q - p) / 2) ≤ ‖DH ⟨q, y⟩‖) :
    ∀ x ∈ Icc p q, ε ≤ ‖DH ⟨x, y⟩‖ := fun _ hx =>
  DH_lower_on_hcell hpq hL0 (fun t ht => hD ⟨t, y⟩ ⟨hp.trans ht.1, ht.2.trans hq⟩ hy)
    hβp hβq le_rfl le_rfl rfl hx

/-- One vertical cell `{x} × [p, q]` inside the closed square `[A, B] × [C, D]`. -/
theorem vcell {A B C D L ε : ℝ} (hL0 : 0 ≤ L)
    (hD : ∀ z : ℂ, z.re ∈ Icc A B → z.im ∈ Icc C D → ‖deriv DH z‖ ≤ L)
    {p q x : ℝ} (hpq : p ≤ q) (hp : C ≤ p) (hq : q ≤ D) (hx : x ∈ Icc A B)
    (hβp : ε + L * ((q - p) / 2) ≤ ‖DH ⟨x, p⟩‖)
    (hβq : ε + L * ((q - p) / 2) ≤ ‖DH ⟨x, q⟩‖) :
    ∀ y ∈ Icc p q, ε ≤ ‖DH ⟨x, y⟩‖ := fun _ hy =>
  DH_lower_on_vcell hpq hL0 (fun t ht => hD ⟨x, t⟩ hx ⟨hp.trans ht.1, ht.2.trans hq⟩)
    hβp hβq le_rfl le_rfl rfl hy

/-! ### Separation from the zeta function to a height -/

/-- A zero of `DH` off the line, in the open strip and below height `T`, beside RH to
height `T` for Mathlib's `riemannZeta` (the body of hunt #137's `RHUpToHeight T`). -/
theorem separation_of {T : ℝ}
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ T →
      ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1)
    {z : ℂ} (hz : DH z = 0) (hre0 : 0 < z.re) (hre1 : z.re < 1) (hline : z.re ≠ 1 / 2)
    (him0 : 0 < z.im) (himT : z.im ≤ T) :
    (∃ s : ℂ, DH s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T ∧ s.re ≠ 1 / 2) ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ T →
        ρ.re = 1 / 2 :=
  ⟨⟨z, hz, hre0, hre1, him0, himT, hline⟩,
    fun ρ h0 h1 h2 h3 h4 => (hRH ρ h0 h1 h2 h3 h4).1⟩

end ZetaLean.DH.Rung3Assembly
