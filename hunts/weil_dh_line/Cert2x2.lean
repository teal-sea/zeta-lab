/-
Kernel certificate: the band-64 even Davenport–Heilbronn form at window c = 55
has a negative direction.

The three entries below are the exact rational midpoints of the Arb enclosures of
`M 54 54`, `M 54 55` and `M 55 55` computed by the hunt's assembly
(`hunts/weil_dh_line/cert_2x2_c55.json`; entry radii below 1e-72). This file
checks only the rational algebra: for the symmetric 2x2 block `[[a, b], [b, d]]`
the vector `(d, -b)` has quadratic form `d * (a * d - b * b) < 0`, so the block,
and hence the full form, has a negative direction. The step from the true Arb
matrix to these rationals is the enclosure, not formalized here.
-/
import Mathlib.Tactic

namespace ZetaLab

/-- Midpoint enclosure of `M 54 54`. -/
def a : ℚ :=
  31103271688505081125159639407567424241478732085557475447922473001014584817973 /
    28948022309329048855892746252171976963317496166410141009864396001978282409984

/-- Midpoint enclosure of `M 54 55`. -/
def b : ℚ :=
  -92776165202690759339519621866470968260106160554965592145775191025917715918243 /
    28948022309329048855892746252171976963317496166410141009864396001978282409984

/-- Midpoint enclosure of `M 55 55`. -/
def d : ℚ :=
  41953437038247505062294836289888893624887970761131761512216382739606710460247 /
    7237005577332262213973186563042994240829374041602535252466099000494570602496

/-- The quadratic form of the block in the direction `(d, -b)` is negative. -/
theorem two_by_two_negative : d * (a * d - b * b) < 0 := by
  norm_num [a, b, d]

/-- The same statement phrased as indistinctness of direction: the block has both
signs, since the diagonal entry `d` is positive. -/
theorem two_by_two_indefinite : 0 < d ∧ d * (a * d - b * b) < 0 := by
  refine ⟨by norm_num [d], two_by_two_negative⟩

end ZetaLab