/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.DavenportHeilbronn
import ZetaLean.DHAnalytic
import ZetaLean.OracleDH

/-!
# The zero criterion: rung 3 reduced to two interval inequalities

The analytic half of the Davenport-Heilbronn theorem is kernel-checked in
`ZetaLean/DHAnalytic.lean`.  What separates it from the full
`davenport_heilbronn_statement` is the *existence of the off-line zero* —
and existence of an exact zero of an entire function cannot be certified by
evaluating the function at a point, however precisely.  This file supplies
the topological bridge that turns finite computation into existence:

* `exists_zero_of_norm_lt_on_sphere` — the **minimum-modulus criterion**:
  if `f` is entire and `‖f‖` is smaller at the centre of a disk than
  everywhere on its boundary sphere, `f` has a zero inside.  (Proof: apply
  Mathlib's maximum-modulus principle to `1/f`; no argument principle, no
  winding numbers.)

* `davenport_heilbronn_of_ball_bounds` — the criterion specialised to `DH`,
  with a disk kept strictly to the right of the critical line, concluding
  `davenport_heilbronn_statement` itself.

* `davenport_heilbronn_of_certified_disk` — the concrete instantiation at
  the oracle point `0.808517 + 85.699348i` (`ZetaLean/OracleDH.lean`) with
  radius `1/10` and threshold `1/100`.  **Rung 3 is now exactly these two
  hypotheses**:

  1. `‖DH dhZeroCenter‖ < 1/100`, and
  2. `1/100 ≤ ‖DH z‖ for every z on the radius-1/10 sphere`,

  both statements about certified evaluation of `DH` — no more topology, no
  more analysis, only the (open) computational mountain of interval-arithmetic
  L-function evaluation inside the kernel.  The lab's `mpmath` cross-check
  (30 digits, 720 boundary samples) puts `‖DH‖ ≈ 6.5e-7` at the centre and
  `min ≈ 0.121` on the sphere, so both hypotheses hold with more than a
  tenfold margin — but per the honest-scope rule those numbers are an
  oracle's, not the kernel's, and nothing here claims otherwise.
-/

open Complex

namespace ZetaLean.DH

/-- **Minimum-modulus criterion.**  If an entire `f` has smaller norm at the
centre of a disk than anywhere on the boundary sphere, it has a zero in the
closed disk.  Mathlib's maximum-modulus principle applied to `1/f`. -/
theorem exists_zero_of_norm_lt_on_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {r ε : ℝ} (hr : 0 < r)
    (h1 : ‖f c‖ < ε) (h2 : ∀ z ∈ Metric.sphere c r, ε ≤ ‖f z‖) :
    ∃ z ∈ Metric.closedBall c r, f z = 0 := by
  by_contra hno
  push Not at hno
  have hε : 0 < ε := lt_of_le_of_lt (norm_nonneg _) h1
  have hcl : closure (Metric.ball c r) = Metric.closedBall c r := closure_ball c hr.ne'
  have hd : DiffContOnCl ℂ (fun z => (f z)⁻¹) (Metric.ball c r) := by
    refine ⟨hf.differentiableOn.inv fun z hz => hno z (Metric.ball_subset_closedBall hz), ?_⟩
    rw [hcl]
    exact hf.continuous.continuousOn.inv₀ fun z hz => hno z hz
  have hfr : ∀ z ∈ frontier (Metric.ball c r), ‖(f z)⁻¹‖ ≤ ε⁻¹ := by
    intro z hz
    rw [frontier_ball c hr.ne'] at hz
    rw [norm_inv]
    exact inv_anti₀ hε (h2 z hz)
  have hcm : c ∈ closure (Metric.ball c r) := by
    rw [hcl]
    exact Metric.mem_closedBall_self hr.le
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    Metric.isBounded_ball hd hfr hcm
  rw [norm_inv] at hmax
  have h0 : 0 < ‖f c‖ :=
    norm_pos_iff.mpr (hno c (Metric.mem_closedBall_self hr.le))
  exact absurd h1 (not_lt.mpr ((inv_le_inv₀ h0 hε).mp hmax))

/-- The minimum-modulus criterion specialised to `DH`, on a disk kept
strictly to the right of the critical line: two norm bounds on `DH` imply
the full Davenport-Heilbronn statement. -/
theorem davenport_heilbronn_of_ball_bounds {c : ℂ} {r ε : ℝ} (hr : 0 < r)
    (hline : r < |c.re - 1 / 2|)
    (h1 : ‖DH c‖ < ε) (h2 : ∀ z ∈ Metric.sphere c r, ε ≤ ‖DH z‖) :
    davenport_heilbronn_statement := by
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_norm_lt_on_sphere DH_differentiable hr h1 h2
  refine ⟨DH, z, DH_differentiable, DH_series_rep, DH_functional_eq, hz0, ?_⟩
  intro hz2
  have h3 : |z.re - c.re| ≤ r :=
    calc |z.re - c.re| = |(z - c).re| := by rw [Complex.sub_re]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      _ = dist z c := (dist_eq_norm z c).symm
      _ ≤ r := Metric.mem_closedBall.mp hz
  rw [hz2, abs_sub_comm] at h3
  linarith

/-- The centre of the certification disk: the oracle's off-line zero
(`ZetaLean/OracleDH.lean`), `0.808517 + 85.699348i`. -/
noncomputable def dhZeroCenter : ℂ :=
  ⟨(offline_zero_re : ℝ), (offline_zero_im : ℝ)⟩

/-- **Rung 3, reduced to computation.**  The Davenport-Heilbronn theorem
follows from two interval inequalities about `DH` on the disk of radius
`1/10` around the oracle point: small at the centre, bounded below on the
boundary.  Discharging these two hypotheses by certified evaluation is all
that remains of rung 3. -/
theorem davenport_heilbronn_of_certified_disk
    (h1 : ‖DH dhZeroCenter‖ < 1 / 100)
    (h2 : ∀ z ∈ Metric.sphere dhZeroCenter (1 / 10), 1 / 100 ≤ ‖DH z‖) :
    davenport_heilbronn_statement := by
  refine davenport_heilbronn_of_ball_bounds (by norm_num) ?_ h1 h2
  have hcre : dhZeroCenter.re = 808517 / 1000000 := by
    simp [dhZeroCenter, offline_zero_re]
  rw [hcre, show (808517 / 1000000 : ℝ) - 1 / 2 = 308517 / 1000000 by norm_num,
    abs_of_pos (by norm_num : (0:ℝ) < 308517 / 1000000)]
  norm_num

/-! ### The square-contour variant

The sphere of `davenport_heilbronn_of_certified_disk` is the natural
statement, but a circle is an awkward object for rectangle arithmetic to
cover.  The same minimum-modulus argument works verbatim for **any** bounded
open set, and for an axis-aligned open square the frontier is four segments —
exactly the sets that boxed-`s` interval evaluation covers without slack.
Assembly should discharge `davenport_heilbronn_of_certified_square`, not the
disk version. -/

/-- **Minimum-modulus criterion, general boundary version.**  If entire `f`
has smaller norm at a point of a bounded open `U` than anywhere on
`frontier U`, it has a zero in `closure U`.  The proof is the ball version's
proof; the ball was never needed. -/
theorem exists_zero_of_norm_lt_on_frontier {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U : Set ℂ} (hUb : Bornology.IsBounded U) (hUo : IsOpen U)
    {c : ℂ} (hc : c ∈ U) {ε : ℝ}
    (h1 : ‖f c‖ < ε) (h2 : ∀ z ∈ frontier U, ε ≤ ‖f z‖) :
    ∃ z ∈ closure U, f z = 0 := by
  by_contra hno
  push_neg at hno
  have hε : 0 < ε := lt_of_le_of_lt (norm_nonneg _) h1
  have hd : DiffContOnCl ℂ (fun z => (f z)⁻¹) U := by
    refine ⟨hf.differentiableOn.inv fun z hz => hno z (subset_closure hz), ?_⟩
    exact hf.continuous.continuousOn.inv₀ fun z hz => hno z hz
  have hfr : ∀ z ∈ frontier U, ‖(f z)⁻¹‖ ≤ ε⁻¹ := by
    intro z hz
    rw [norm_inv]
    exact inv_anti₀ hε (h2 z hz)
  have hcm : c ∈ closure U := subset_closure hc
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hUb hd hfr hcm
  rw [norm_inv] at hmax
  have h0 : 0 < ‖f c‖ := norm_pos_iff.mpr (hno c hcm)
  exact absurd h1 (not_lt.mpr ((inv_le_inv₀ h0 hε).mp hmax))

/-- The open axis-aligned square with rational centre `cre + i·cim` and
half-width `w`. -/
def dhSquare (cre cim w : ℚ) : Set ℂ :=
  Set.Ioo (((cre - w : ℚ) : ℝ)) (((cre + w : ℚ) : ℝ)) ×ℂ
    Set.Ioo (((cim - w : ℚ) : ℝ)) (((cim + w : ℚ) : ℝ))

/-- The square's frontier is its four boundary segments — the sets that
boxed-`s` interval evaluation covers without slack. -/
lemma frontier_dhSquare {cre cim w : ℚ} (hw : 0 < w) :
    frontier (dhSquare cre cim w) =
      Set.Icc (((cre - w : ℚ) : ℝ)) (((cre + w : ℚ) : ℝ)) ×ℂ
          ({((cim - w : ℚ) : ℝ), ((cim + w : ℚ) : ℝ)} : Set ℝ)
        ∪ ({((cre - w : ℚ) : ℝ), ((cre + w : ℚ) : ℝ)} : Set ℝ) ×ℂ
          Set.Icc (((cim - w : ℚ) : ℝ)) (((cim + w : ℚ) : ℝ)) := by
  have hw' : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hre : (((cre - w : ℚ) : ℝ)) < (((cre + w : ℚ) : ℝ)) := by
    push_cast; linarith
  have him : (((cim - w : ℚ) : ℝ)) < (((cim + w : ℚ) : ℝ)) := by
    push_cast; linarith
  rw [dhSquare, Complex.frontier_reProdIm, closure_Ioo hre.ne, closure_Ioo him.ne,
    frontier_Ioo hre, frontier_Ioo him]

/-- The square criterion for `DH`: a square kept strictly right of the
critical line, `DH` small at the centre and bounded below on the four
boundary segments, imply the full Davenport-Heilbronn statement. -/
theorem davenport_heilbronn_of_certified_square {cre cim w ε' : ℚ}
    (hw : 0 < w) (hline : 1 / 2 < cre - w)
    (h1 : ‖DH ⟨(cre : ℝ), (cim : ℝ)⟩‖ < (ε' : ℝ))
    (h2 : ∀ z ∈ frontier (dhSquare cre cim w), (ε' : ℝ) ≤ ‖DH z‖) :
    davenport_heilbronn_statement := by
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
  refine ⟨DH, z, DH_differentiable, DH_series_rep, DH_functional_eq, hz0, ?_⟩
  have hzre : z.re ∈ Set.Icc (((cre - w : ℚ) : ℝ)) (((cre + w : ℚ) : ℝ)) := by
    rw [dhSquare, Complex.closure_reProdIm, closure_Ioo hre.ne,
      closure_Ioo him.ne, Complex.mem_reProdIm] at hz
    exact hz.1
  intro hhalf
  have h3 : (1 / 2 : ℝ) < (((cre - w : ℚ) : ℝ)) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hline
    push_cast at h ⊢
    linarith
  rw [hhalf] at hzre
  exact absurd hzre.1 (not_le.mpr h3)

end ZetaLean.DH
