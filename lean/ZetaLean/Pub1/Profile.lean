/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Setting
import ZetaLean.Pub1.Aristotle.K

/-!
# Pub 1 strong closure: the ambient variational upper bound

The half of the theorem that needs nothing about admissibility.  With
`w = A⁻¹1`, the identity `⟨1, v⟩ = ⟨Aw, v⟩` and Cauchy-Schwarz in the energy
inner product give

```
      ⟨1,v⟩²  ≤  ⟨Aw,w⟩ ⟨Av,v⟩  =  ⟨1,w⟩ ⟨Av,v⟩  =  c* ⟨Av,v⟩
```

for *every* `v`, so `c(v) ≤ c*` throughout.  The source-admissible class only
has to supply the reverse inequality, which is what the taper sequence does.
-/

open MeasureTheory

namespace ZetaLean.Pub1

/-- The abstract form specialises to the concrete energy. -/
theorem bil_self_eq_energyA (v : ℝ → ℝ) : AristotleK.bil clampedKernel v v = energyA v := by
  unfold AristotleK.bil energyA normSqI
  congr 1
  · exact intervalIntegral.integral_congr (fun x _ => by ring)
  · exact kerForm_eq_clamped v

/-- **The representation identity `⟨Aw, w⟩ = ⟨1, w⟩`.**  Discharges the
`energy_w` field of `StrongClosureData`. -/
theorem energyA_eq_massI_of_profile {w : ℝ → ℝ} (hw : IsProfile w) :
    energyA w = massI w := by
  rw [← bil_self_eq_energyA]
  exact AristotleK.bil_repr clampedKernel clampedKernel_continuous clampedKernel_symm
    w hw.1 hw.2.2 w hw.1

/-- **The ambient upper bound `⟨1,v⟩² ≤ c*·⟨Av,v⟩`.**  Discharges the `upper`
field of `StrongClosureData`.  Note it holds for every continuous `v`
whatsoever: admissibility is not used. -/
theorem massI_sq_le_of_profile {w : ℝ → ℝ} (hw : IsProfile w) (v : ℝ → ℝ)
    (hv : Continuous v) : massI v ^ 2 ≤ massI w * energyA v := by
  have hrepr_v : AristotleK.bil clampedKernel w v = massI v :=
    AristotleK.bil_repr clampedKernel clampedKernel_continuous clampedKernel_symm
      w hw.1 hw.2.2 v hv
  have hpsd : ∀ u : ℝ → ℝ, Continuous u → 0 ≤ AristotleK.bil clampedKernel u u := by
    intro u hu
    rw [bil_self_eq_energyA]
    exact energyA_nonneg u hu
  have hcs := AristotleK.bil_cauchy_schwarz clampedKernel clampedKernel_continuous
    clampedKernel_symm hpsd w v hw.1 hv
  rw [hrepr_v, bil_self_eq_energyA, bil_self_eq_energyA,
    energyA_eq_massI_of_profile hw] at hcs
  exact hcs

end ZetaLean.Pub1
