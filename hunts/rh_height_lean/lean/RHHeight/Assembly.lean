module

public import RHHeight.Skeleton
public import HardyTenZeros.TenZeros

@[expose] public section

/-!
# The assembly point of hunt #137 (`rh_height_lean`)

Hunt #133's theorem `HardyTenZeros.ten_zeros_on_line_below_fifty` is used here at the type
`RHHeight.TenZerosOnLine` that the skeleton consumes, so that the target is conditional on
the four missing pieces of `RHHeight/Skeleton.lean` alone. Nothing here proves `RHHeight50`.
Once the pieces are theorems, the target is
`rhHeight50_of_four gamma_increment horizontal_legs exact_argument low_height`.

This module imports hunt #133's generated bracket files, so it is compiled by `build.sh` after
the modules of hunts #132 and #133 (about 17 minutes serially on a 4-core container, by that
hunt's own measurement).
-/

namespace RHHeight

/-- Hunt #133's ten zeros on the line, at the type the skeleton consumes. -/
theorem tenZerosOnLine : TenZerosOnLine := HardyTenZeros.ten_zeros_on_line_below_fifty

/-- **The target, conditional on the four missing pieces only.** -/
theorem rhHeight50_of_four (hΓ : GammaIncrement) (hH : HorizontalLegs) (hE : ExactArgument)
    (hL : LowHeight) : RHHeight50 :=
  rhHeight50_of_pieces hΓ hH hE hL tenZerosOnLine

/-- **Exactly ten zeros with `0 < Im ρ ≤ 50`, conditional on the four pieces only.** -/
theorem zeroCount50_of_four (hΓ : GammaIncrement) (hH : HorizontalLegs) (hE : ExactArgument)
    (hL : LowHeight) : ZeroCountUpTo 50 10 :=
  zeroCount50_of_pieces hΓ hH hE hL tenZerosOnLine

end RHHeight
