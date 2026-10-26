module

public import RHHeight.Skeleton

/-! Pins the statements of hunt #137 by type and prints the axioms of every proved
declaration in the package. Nothing here proves `RHHeight50`: the skeleton theorems are
conditional on the four pieces named in `RHHeight/Skeleton.lean`. -/

open Complex

-- The target, unfolded: Mathlib's own `riemannZeta`, the open strip, `0 < Im ρ ≤ 50`.
example : RHHeight.RHHeight50 =
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 50 →
      ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1 := rfl

-- The multiplicity is `zeta23`'s: `Zeta23.zeroMult` is `(analyticOrderAt riemannZeta ρ).toNat`.
example (ρ : ℂ) : Zeta23.zeroMult ρ = (analyticOrderAt riemannZeta ρ).toNat := rfl
example (ρ : ℂ) : Zeta23.zeroMult ρ = 1 ↔ analyticOrderAt riemannZeta ρ = 1 :=
  RHHeight.toNat_analyticOrderAt_eq_one_iff ρ

-- The window is `zeta23`'s `zerosIn 0 T`.
example (T : ℝ) : RHHeight.stripZerosUpTo T = Zeta23.zerosIn 0 T :=
  Set.ext fun _ =>
    ⟨fun ⟨h0, h1, h2, h3, h4⟩ => ⟨⟨h0, h1, h2⟩, h3, h4⟩,
     fun ⟨⟨h0, h1, h2⟩, h3, h4⟩ => ⟨h0, h1, h2, h3, h4⟩⟩

-- The input from hunt #133 has the type of `HardyTenZeros.ten_zeros_on_line_below_fifty`
-- (`hunts/hardy_ten_zeros/lean/CheckAxioms.lean` pins that type with the same text).
example : RHHeight.TenZerosOnLine =
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * I) = 0 := rfl

#check @RHHeight.rhHeight50_of_pieces
#print axioms RHHeight.toNat_analyticOrderAt_eq_one_iff
#print axioms RHHeight.mem_stripZerosUpTo
#print axioms RHHeight.rhUpToHeight_iff
#print axioms RHHeight.RHUpToHeight.mono
#print axioms RHHeight.RHHeight100.toRHHeight50
#print axioms RHHeight.count_eq_ten_of
#print axioms RHHeight.mem_and_simple_of_Ncount_le
#print axioms RHHeight.on_line_and_simple_of_count
#print axioms RHHeight.rhUpToHeight52_of_pieces
#print axioms RHHeight.rhHeight50_of_pieces
#print axioms RHHeight.zeroCount50_of_pieces
