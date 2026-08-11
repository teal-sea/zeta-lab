import Mathlib.Data.Complex.Basic

/-!
# Exact obstruction to the withdrawn frontier-math transplant

The upstream zero-side summand is `u * u`, the one-dimensional form of
`u uᵀ`.  It is not `u * conj u`.  The conjugate pair `I, -I` therefore has
sum `-2`, giving a negative interaction with the on-line vector `1`.
-/

namespace ZetaLean.FrontierMathObstruction

def transposeRankOne (u : ℂ) : ℂ := u * u

def offPair (u : ℂ) : ℂ := transposeRankOne u + transposeRankOne (starRingEnd ℂ u)

theorem offPair_I : offPair Complex.I = -2 := by
  simp [offPair, transposeRankOne]
  ring

theorem crossInteraction_I_negative :
    (((1 : ℂ) * offPair Complex.I).re : ℝ) < 0 := by
  rw [offPair_I]
  norm_num

/-- Five unit on-line labels and the pair `I, -I` violate the proposed
additive strengthening: its left side is 9 and its claimed right side is 13. -/
theorem proposedAdditiveBound_false :
    let p1 : ℤ := 5
    let q' : ℤ := -2
    let cross11 : ℤ := 20
    (p1 + q') ^ 2 < 4 * (p1 + q') - 3 * 5 - 4 * 1 + cross11 := by
  norm_num
  omega

end ZetaLean.FrontierMathObstruction
