import Zeta23Ext.EForm3.O9Comp
import Zeta23Ext.EForm3.ClosedForm

/-!
# O9 soundness: the seams between the table and the damage

`O9Check2.lean` decides a table of boxes. Deciding it says the recorded
inequalities hold *in the kernel's interval arithmetic*; it says nothing about
`Dam` until the enclosures are connected to the quantities they enclose. This
file is where that connection is built.

The damage is `Dam y s = Qim y s ^ 2 - Qre y s ^ 2`, and the obligation is
`Dam y s ≤ c * y ^ 2` on each window. Written through the removable branch
`R = Qim y s / y` it becomes

    y ^ 2 * (R ^ 2 - c) ≤ Qre y s ^ 2

which is what the two modes of `o9Box` test:

* **mode 1**: `R ^ 2 - c ≤ 0`, so the left side is `≤ 0 ≤ Qre ^ 2` whatever
  `Qre` does. This is the branch that carries every box touching `y = 0`.
* **mode 2**: `y_hi ^ 2 * (sup R ^ 2 - c) ≤ inf Qre ^ 2`.

## Why the `y = 0` split comes first

`BandDual.phiC_mem` carries the hypothesis `y ≠ 0`, and the two-dimensional
boxes reach `y = 0` by construction. `O9-2D-STATUS.md` §4 is explicit that the
right response is a case split and **not** weakening that side condition, so
the split is written here before anything that might tempt one.

At `y = 0` the whole obligation collapses: `Qim 0 s = 0` (`Qim_zero_left`), so
`Dam 0 s = -Qre 0 s ^ 2 ≤ 0 = c * 0 ^ 2` for any `c`, with no interval
arithmetic involved at all.
-/

namespace Retention

open BandDual

/-- The damage, in the form the O9 table bounds. -/
noncomputable def Dam (y s : ℝ) : ℝ := Qim y s ^ 2 - Qre y s ^ 2

/-- **The `y = 0` split.**

At zero depth the damage is a negated square, so it is bounded by `c * y ^ 2`
for every nonnegative `c` with nothing to compute. This is the case
`phiC_mem` cannot reach, and it is discharged without touching that lemma's
`y ≠ 0` hypothesis. -/
theorem dam_zero_le (s c : ℝ) (hc : 0 ≤ c) : Dam 0 s ≤ c * (0:ℝ) ^ 2 := by
  have h : Dam 0 s = -Qre 0 s ^ 2 := by
    simp [Dam, Qim_zero_left]
  rw [h]
  have : (0:ℝ) ≤ Qre 0 s ^ 2 := sq_nonneg _
  simpa using by nlinarith [this]

/-- The obligation, restated through the removable branch.

For `y ≠ 0`, `Dam y s ≤ c * y ^ 2` is equivalent to
`y ^ 2 * ((Qim y s / y) ^ 2 - c) ≤ Qre y s ^ 2`. Both modes of `o9Box` are
sufficient conditions for the right-hand form, which is why the table can be
built on `R` and still bound `Dam`. -/
theorem dam_le_of_branch {y s c : ℝ} (hy : y ≠ 0)
    (h : y ^ 2 * ((Qim y s / y) ^ 2 - c) ≤ Qre y s ^ 2) :
    Dam y s ≤ c * y ^ 2 := by
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have hsq : y ^ 2 * (Qim y s / y) ^ 2 = Qim y s ^ 2 := by
    field_simp
  rw [Dam]
  nlinarith [h, hsq]

/-- **Mode 1 is sound.**

If the branch is under the cap outright, the obligation holds at every depth,
including `y = 0`, where it is `dam_zero_le`. This is the only mode a box
touching `y = 0` may use, and it needs no enclosure of `Qre` at all. -/
theorem dam_le_of_mode1 {y s c : ℝ} (hy0 : 0 ≤ y) (hc : 0 ≤ c)
    (h : (if y = 0 then (0:ℝ) else (Qim y s / y) ^ 2) ≤ c) :
    Dam y s ≤ c * y ^ 2 := by
  by_cases hy : y = 0
  · subst hy; simpa using dam_zero_le s c hc
  · rw [if_neg hy] at h
    refine dam_le_of_branch hy ?_
    have hy2 : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
    have hle : (Qim y s / y) ^ 2 - c ≤ 0 := by linarith
    have : y ^ 2 * ((Qim y s / y) ^ 2 - c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy2 hle
    exact this.trans (sq_nonneg _)

/-- **Mode 2 is sound.**

The test the table records is `y_hi² · (sup R² − c) ≤ inf Qre²`: one inequality
at the box's *largest* depth, standing in for every depth in it. This lemma is
why that suffices.

The case split is the content. When `sup R² ≤ c` the branch is under the cap
outright and mode 1's argument applies at every depth. When it is not, the
excess is positive, so scaling it by `y² ≤ y_hi²` only shrinks it, and the
recorded inequality at `y_hi` therefore covers every smaller depth in the box.
Monotonicity in `y` is doing the work, and it runs the right way only because
the excess is nonnegative in that branch. -/
theorem dam_le_of_mode2 {y yhi s c Rsq : ℝ} (hy0 : 0 ≤ y) (hy : y ≠ 0)
    (hyhi : y ≤ yhi)
    (hR : (Qim y s / y) ^ 2 ≤ Rsq)
    (h : yhi ^ 2 * (Rsq - c) ≤ Qre y s ^ 2) :
    Dam y s ≤ c * y ^ 2 := by
  refine dam_le_of_branch hy ?_
  by_cases hc : Rsq ≤ c
  · have hle : (Qim y s / y) ^ 2 - c ≤ 0 := by linarith
    have : y ^ 2 * ((Qim y s / y) ^ 2 - c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) hle
    exact this.trans (sq_nonneg _)
  · push_neg at hc
    have hpos : 0 ≤ Rsq - c := by linarith
    have hsq : y ^ 2 ≤ yhi ^ 2 := by nlinarith
    calc y ^ 2 * ((Qim y s / y) ^ 2 - c)
        ≤ y ^ 2 * (Rsq - c) := by nlinarith [sq_nonneg y]
      _ ≤ yhi ^ 2 * (Rsq - c) := by nlinarith
      _ ≤ Qre y s ^ 2 := h

end Retention

#print axioms Retention.dam_zero_le
#print axioms Retention.dam_le_of_branch
#print axioms Retention.dam_le_of_mode1
#print axioms Retention.dam_le_of_mode2
