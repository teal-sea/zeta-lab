import Zeta23Ext.EForm3.O9Bridge
import Zeta23Ext.EForm3.O9Sound
import Zeta23Ext.EForm3.O9Check2

/-!
# The two-mode arithmetic

`O9Check2.o9Box` is a `Bool`. It re-evaluates a recorded leaf and checks one of
two inequalities *in the kernel's fixed-point interval arithmetic*. `O9Sound`
proves that those two inequalities, **stated over the reals**, imply the damage
bound `Dam y s ≤ c · y²`. Between them sits the step this file is: turning the
`Bool` into the real hypotheses `dam_le_of_mode1` and `dam_le_of_mode2` want.

Three things have to happen, and none of them is analysis:

1. **Read the enclosures back.** `rIv` encloses `R = Qim y s / y` and `qreIv`
   encloses `Qre y s` (`O9Bridge`, on top of `O9NumShape`). Squaring is
   `Iv.sqr_mem`; the cap is a point interval, so `EIv.pt_mem` gives it.
2. **Turn `hi ≤ 0` and `l.hi ≤ q2.lo` into real inequalities.** `Iv.mem` is
   `lo ≤ 2⁶⁴·x ≤ hi`, so each `Bool` comparison is one multiplication by
   `2⁶⁴ > 0` away from the real inequality.
3. **Supply `Rsq` and `yhi`.** Mode 2's soundness lemma is stated with the
   recorded supremum and the box's top depth abstract. Here they are
   `e.hi / 2⁶⁴ + c` and `yHi / 2⁶⁴`, and `y ≤ yhi` is the box membership itself.

## What this closes and what it does not

`dam_le_of_box` is conditional on `o9Box b = true` for that box, and on nothing
else: the `y = 0` case is discharged inside it, the `y ≠ 0` case goes through
the enclosure chain, and every field hypothesis is supplied.
`dam_le_of_mem_walk` joins it to a decided chunk, so a box the kernel actually
accepted carries the real bound; `dam_le_box0` instantiates that at the first
recorded row, at a concrete interior point, with every hypothesis discharged by
`norm_num` rather than assumed.

What is **not** claimed here is O9 soundness end to end. Two things still stand
between this file and the retention obligation, and neither is in it:

* the recorded boxes have to be shown to **cover** `[28/5, 60] × [0, 1/2]` (the
  generator produced a cover, the Lean side does not yet carry that fact), and
* the per-box bound has to be assembled into the form `Gap`/`FarField` consume.

No `sorry` stands in for either. Nothing here is evidence for or against the
Riemann hypothesis.
-/

namespace Retention

open BandDual

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## Reading a fixed-point comparison as a real inequality -/

/-- A point interval encloses exactly its own value. -/
theorem pt_mem' (n : ℤ) : Iv.mem ⟨n, n⟩ ((n : ℝ) / (SO : ℝ)) := by
  have := EIv.pt_mem n
  simpa [EIv.pt] using this

/-! ## The two modes, with the interval facts supplied -/

/-- **Mode 1, wired.** The recorded test is `sup (R² − c) ≤ 0`; that is the
hypothesis `dam_le_of_mode1` wants, once the enclosure is read back. -/
theorem dam_le_mode1_of_iv {sLo sHi yLo yHi cap : ℤ} {r : Iv} {s y : ℝ}
    (hrv : rIv sLo sHi yLo yHi = some r)
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy0 : 0 ≤ y) (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hyz : y ≠ 0)
    (hcap : (0:ℝ) ≤ (cap : ℝ) / (SO : ℝ))
    (htest : (Iv.sub (Iv.sqr r) ⟨cap, cap⟩).hi ≤ 0) :
    Dam y s ≤ ((cap : ℝ) / (SO : ℝ)) * y ^ 2 := by
  have hR : Iv.mem r (Qim y s / y) := by
    have h := rIv_mem_R hs hy hy1 hyz
    rw [hrv] at h
    simpa using h
  have he : Iv.mem (Iv.sub (Iv.sqr r) ⟨cap, cap⟩)
      (Qim y s / y * (Qim y s / y) - (cap : ℝ) / (SO : ℝ)) :=
    Iv.sub_mem (Iv.sqr_mem hR) (pt_mem' cap)
  have hhi : (SO:ℝ) * (Qim y s / y * (Qim y s / y) - (cap : ℝ) / (SO : ℝ))
      ≤ ((Iv.sub (Iv.sqr r) ⟨cap, cap⟩).hi : ℝ) := he.2
  have hz : ((Iv.sub (Iv.sqr r) ⟨cap, cap⟩).hi : ℝ) ≤ 0 := by exact_mod_cast htest
  refine dam_le_of_mode1 hy0 hcap ?_
  rw [if_neg hyz]
  have hkey : Qim y s / y * (Qim y s / y) - (cap : ℝ) / (SO : ℝ) ≤ 0 := by
    nlinarith [SOR_pos]
  nlinarith [hkey]

/-- **Mode 2, wired.** The recorded test is `y_hi² · sup (R² − c) ≤ inf Qre²`.
`Rsq` is the recorded supremum shifted back by the cap, and `yhi` is the box's
top depth; `y ≤ yhi` is the box membership itself. -/
theorem dam_le_mode2_of_iv {sLo sHi yLo yHi cap : ℤ} {r q : Iv} {s y : ℝ}
    (hrv : rIv sLo sHi yLo yHi = some r)
    (hqv : qreIv sLo sHi yLo yHi = some q)
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy0 : 0 ≤ y) (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hyz : y ≠ 0)
    (htest : (Iv.mul (Iv.ofQ (yHi * yHi) (SO * SO))
        ⟨(Iv.sub (Iv.sqr r) ⟨cap, cap⟩).hi, (Iv.sub (Iv.sqr r) ⟨cap, cap⟩).hi⟩).hi
      ≤ (Iv.sqr q).lo) :
    Dam y s ≤ ((cap : ℝ) / (SO : ℝ)) * y ^ 2 := by
  have hSO := SOR_pos
  set c : ℝ := (cap : ℝ) / (SO : ℝ) with hcdef
  set e : Iv := Iv.sub (Iv.sqr r) ⟨cap, cap⟩ with hedef
  set E : ℝ := (e.hi : ℝ) / (SO : ℝ) with hEdef
  set yhi : ℝ := (yHi : ℝ) / (SO : ℝ) with hyhidef
  -- the enclosures
  have hR : Iv.mem r (Qim y s / y) := by
    have h := rIv_mem_R hs hy hy1 hyz
    rw [hrv] at h
    simpa using h
  have hQ : Iv.mem q (Qre y s) := by
    have h := qreIv_mem_Qre hs hy hy1 hyz
    rw [hqv] at h
    simpa using h
  have he : Iv.mem e (Qim y s / y * (Qim y s / y) - c) :=
    Iv.sub_mem (Iv.sqr_mem hR) (pt_mem' cap)
  have hEle : Qim y s / y * (Qim y s / y) - c ≤ E := by
    have h := he.2
    rw [hEdef, le_div_iff₀ hSO]
    nlinarith [h]
  -- the box's top depth
  have hSSpos : (0:ℤ) < SO * SO := mul_pos SO_pos SO_pos
  have hysq : Iv.mem (Iv.ofQ (yHi * yHi) (SO * SO)) (yhi ^ 2) := by
    have h := Iv.ofQ_mem (n := yHi * yHi) hSSpos
    have heq : ((yHi * yHi : ℤ) : ℝ) / ((SO * SO : ℤ) : ℝ) = yhi ^ 2 := by
      rw [hyhidef]
      push_cast
      ring
    rwa [heq] at h
  have hprod : Iv.mem (Iv.mul (Iv.ofQ (yHi * yHi) (SO * SO)) ⟨e.hi, e.hi⟩) (yhi ^ 2 * E) :=
    Iv.mul_mem hysq (pt_mem' e.hi)
  -- the recorded comparison, as reals
  have hcast : ((Iv.mul (Iv.ofQ (yHi * yHi) (SO * SO)) ⟨e.hi, e.hi⟩).hi : ℝ)
      ≤ ((Iv.sqr q).lo : ℝ) := by exact_mod_cast htest
  have hmain : yhi ^ 2 * E ≤ Qre y s ^ 2 := by
    have h1 := hprod.2
    have h2 := (Iv.sqr_mem hQ).1
    have : (SO:ℝ) * (yhi ^ 2 * E) ≤ (SO:ℝ) * (Qre y s * Qre y s) := by
      linarith [h1, h2, hcast]
    nlinarith [this]
  -- the box's depth bound
  have hyle : y ≤ yhi := by
    have h := hy.2
    rw [hyhidef, le_div_iff₀ hSO]
    nlinarith [h]
  refine dam_le_of_mode2 (yhi := yhi) (Rsq := E + c) hy0 hyz hyle ?_ ?_
  · have : Qim y s / y * (Qim y s / y) ≤ E + c := by linarith
    nlinarith [this]
  · have heq : E + c - c = E := by ring
    rw [heq]
    exact hmain

/-! ## The checker's verdict, as the damage bound -/

/-- **The two-mode arithmetic.** A box the checker accepts bounds the damage at
every point of that box. -/
theorem dam_le_of_box {b : O9Box} (hb : o9Box b = true) (hcap : 0 ≤ b.cap)
    {s y : ℝ}
    (hs : EIv.mem (some ⟨b.sLo, b.sHi⟩) s)
    (hy : EIv.mem (some ⟨b.yLo, b.yHi⟩) y)
    (hy0 : 0 ≤ y) (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) :
    Dam y s ≤ ((b.cap : ℝ) / (SO : ℝ)) * y ^ 2 := by
  have hcapR : (0:ℝ) ≤ (b.cap : ℝ) / (SO : ℝ) :=
    div_nonneg (by exact_mod_cast hcap) (le_of_lt SOR_pos)
  by_cases hyz : y = 0
  · subst hyz
    exact dam_zero_le s _ hcapR
  -- `unfold` then `split`: the checker's own case analysis, read off rather
  -- than simplified. `simp only [o9Box]` here asks the elaborator to whnf
  -- `rIv b.sLo …`, which unfolds the whole leaf layer symbolically and does not
  -- terminate in any reasonable budget.
  unfold o9Box at hb
  split at hb
  · rename_i r q hrv hqv
    -- Every step between the checker's `let` and the two comparisons is
    -- definitional (`EIv.sub`/`sqr`/`mul`/`sqrScaled` on `some`), so the cast
    -- below is `hb` itself at a readable type.
    have hb2 : (if b.mode = 1 then
          decide ((Iv.sub (Iv.sqr r) ⟨b.cap, b.cap⟩).hi ≤ 0)
        else
          decide ((Iv.mul (Iv.ofQ (b.yHi * b.yHi) (SO * SO))
              ⟨(Iv.sub (Iv.sqr r) ⟨b.cap, b.cap⟩).hi,
               (Iv.sub (Iv.sqr r) ⟨b.cap, b.cap⟩).hi⟩).hi ≤ (Iv.sqr q).lo)) = true := hb
    split_ifs at hb2 with hmode
    · rw [decide_eq_true_eq] at hb2
      exact dam_le_mode1_of_iv hrv hs hy hy0 hy1 hyz hcapR hb2
    · rw [decide_eq_true_eq] at hb2
      exact dam_le_mode2_of_iv hrv hqv hs hy hy0 hy1 hyz hb2
  · exact absurd hb (by simp)

/-- A decided walk decides each of its boxes. -/
theorem o9Box_of_mem {l : List O9Box} (h : o9Walk2 l = true) {b : O9Box} (hb : b ∈ l) :
    o9Box b = true := by
  induction l with
  | nil => cases hb
  | cons a as ih =>
      rw [o9Walk2, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact h.1
      · exact ih h.2 hmem

/-- **The bound, for a box the kernel accepted.** -/
theorem dam_le_of_mem_walk {l : List O9Box} (hl : o9Walk2 l = true)
    {b : O9Box} (hb : b ∈ l) (hcap : 0 ≤ b.cap) {s y : ℝ}
    (hs : EIv.mem (some ⟨b.sLo, b.sHi⟩) s)
    (hy : EIv.mem (some ⟨b.yLo, b.yHi⟩) y)
    (hy0 : 0 ≤ y) (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) :
    Dam y s ≤ ((b.cap : ℝ) / (SO : ℝ)) * y ^ 2 :=
  dam_le_of_box (o9Box_of_mem hl hb) hcap hs hy hy0 hy1

/-! ## Instantiation at a recorded box

`box0_in_table` (O9NumShape) says the row is in `o9boxes`; this says it is in
the chunk the kernel decided, which is what carries the verdict. The point
`(23/4, 1/8)` is interior to it, and every hypothesis below is discharged. -/

theorem box0_in_chunk0 :
    (⟨103301766812773489049, 107547284961337742355, 0, 4611686018427387904, 0, 2⟩ :
      O9Box) ∈ (o9boxes.drop 0 |>.take 40) := by
  decide +kernel

/-- **The damage bound at a recorded box, from the kernel's own verdict.**

`Dam (1/8) (23/4) ≤ 0`, because the row's recorded cap is `0`. Every hypothesis
is discharged: the verdict is `o9_box_chunk0`, the memberships are `norm_num`. -/
theorem dam_le_box0 :
    Dam (1/8 : ℝ) (23/4 : ℝ) ≤ ((0:ℤ) : ℝ) / (SO : ℝ) * (1/8 : ℝ) ^ 2 :=
  dam_le_of_mem_walk o9_box_chunk0 box0_in_chunk0 (by norm_num)
    s_in_box0 y_in_box0 (by norm_num) y_small_box0

end Retention

#print axioms Retention.dam_le_mode1_of_iv
#print axioms Retention.dam_le_mode2_of_iv
#print axioms Retention.dam_le_of_box
#print axioms Retention.o9Box_of_mem
#print axioms Retention.dam_le_of_mem_walk
#print axioms Retention.box0_in_chunk0
#print axioms Retention.dam_le_box0
