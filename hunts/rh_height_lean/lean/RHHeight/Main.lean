module

public import RHHeight.Assembly
public import RHHeight.GammaIncrement
public import RHHeight.HorizontalLegs
public import RHHeight.ExactArgument
public import RHHeight.LowHeight

@[expose] public section

/-!
# Hunt #137 (`rh_height_lean`): RH with simplicity to height 50, for Mathlib's zeta

The reduction of `RHHeight/Skeleton.lean`, with every hypothesis discharged by a theorem:

* `GammaIncrement` by `gamma_increment_holds` (`RHHeight/GammaIncrement.lean`):
  `92/10 ≤ ∫_3^52 μ ≤ 109/10`, from the vendored Stirling bound `digamma_stirling`;
* `HorizontalLegs` by `horizontalLegs` (`RHHeight/HorizontalLegs.lean`): `Re ζ > 0` on the
  legs `[1/2, 2] + 3i` and `[1/2, 2] + 52i`, `-1/5 ≤ arg ζ(1/2 + 3i) ≤ 0` and
  `-1/3 ≤ arg ζ(1/2 + 52i) ≤ 0`, from interval boxes the kernel decides;
* `ExactArgument` by `exact_argument_holds` (`RHHeight/ExactArgument.lean`): under that
  positivity the folded argument principle of the vendored `zeta23` package is the exact
  identity `Ncount T₁ T₂ = ∫ μ + (arg ζ(1/2 + iT₂) - arg ζ(1/2 + iT₁))/π`;
* `LowHeight` by `low_height` (`RHHeight/LowHeight.lean`): no zero with `0 < Im ρ ≤ 3`,
  from hunt #132's Euler-Maclaurin representation at `N = 1`;
* `TenZerosOnLine` by `tenZerosOnLine` (`RHHeight/Assembly.lean`), which is hunt #133's
  `HardyTenZeros.ten_zeros_on_line_below_fifty`.

The three enclosures put the count of zeros with `3 < Im ρ ≤ 52` in `(9, 11)`, so it is `10`
(`ncount_three_fiftytwo`). Hunt #133's ten distinct zeros on the line lie in that window,
so they are all of its zeros, each simple; `LowHeight` covers `0 < Im ρ ≤ 3`.

**What this does not say.** Nothing above height 52 and nothing about the Riemann
hypothesis (`docs/08`). Like every finite-height verification it cannot tell `ζ` from the
Davenport-Heilbronn function below that function's first off-line zero (height 85.699,
`hunts/rh_height_lean/MISSION.md`). The results and their checks are in
`hunts/rh_height_lean/RESULTS.md`.
-/

namespace RHHeight

/-- **The count on the contour**: exactly ten zeros of `riemannZeta`, counted with
multiplicity (`Zeta23.Ncount`), with `0 < Re ρ < 1` and `3 < Im ρ ≤ 52`. -/
theorem ncount_three_fiftytwo : Zeta23.Ncount 3 52 = 10 :=
  count_eq_ten_of gamma_increment_holds horizontalLegs exact_argument_holds

/-- **RH with simplicity to height 52**, for Mathlib's `riemannZeta`. -/
theorem rh_up_to_height_fiftytwo : RHUpToHeight 52 :=
  rhUpToHeight52_of_pieces gamma_increment_holds horizontalLegs exact_argument_holds
    low_height tenZerosOnLine

/-- **The first target of hunt #137.** Every zero `ρ` of Mathlib's `riemannZeta` with
`0 < Re ρ < 1` and `0 < Im ρ ≤ 50` has `Re ρ = 1/2` and analytic order exactly `1`. -/
theorem rh_height_fifty : RHHeight50 :=
  rhHeight50_of_four gamma_increment_holds horizontalLegs exact_argument_holds low_height

/-- **Exactly ten zeros** of `riemannZeta` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 50`
(distinct zeros; each is simple by `rh_height_fifty`). -/
theorem zero_count_fifty : ZeroCountUpTo 50 10 :=
  zeroCount50_of_four gamma_increment_holds horizontalLegs exact_argument_holds low_height

end RHHeight
