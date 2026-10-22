module

public import RHHeight.Main

/-! Pins the final theorems of hunt #137 to statements that mention only Mathlib (and, for
the count on the contour, `zeta23`'s `Ncount`), and prints their axioms. -/

open Complex

-- The target with every definition of this package unfolded: Mathlib's own `riemannZeta`
-- and `analyticOrderAt`, the open strip, `0 < Im ρ ≤ 50`. The theorem inhabits it as written.
example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 50 →
    ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1 :=
  RHHeight.rh_height_fifty

-- The same to height 52, the top of the contour.
example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 52 →
    ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1 :=
  RHHeight.rh_up_to_height_fiftytwo

-- The count up to height 50, unfolded: exactly ten distinct zeros in the window.
example :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ 50}.ncard = 10 :=
  RHHeight.zero_count_fifty

-- `zeta23`'s count with multiplicity over the window `3 < Im ρ ≤ 52`.
example : Zeta23.Ncount 3 52 = 10 := RHHeight.ncount_three_fiftytwo

#check @RHHeight.rh_height_fifty
#check @RHHeight.zero_count_fifty
#print axioms RHHeight.ncount_three_fiftytwo
#print axioms RHHeight.rh_up_to_height_fiftytwo
#print axioms RHHeight.rh_height_fifty
#print axioms RHHeight.zero_count_fifty
