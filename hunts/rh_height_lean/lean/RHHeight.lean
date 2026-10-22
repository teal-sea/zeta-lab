module

public import RHHeight.Statement
public import RHHeight.Skeleton

/-!
# Hunt #137 (`rh_height_lean`): a kernel-checked RH to finite height for Mathlib's zeta

* `RHHeight.Statement`: the target `RHHeight50` (and `RHHeight100`) as `Prop`s, against
  Mathlib's own `riemannZeta`, with simplicity in the multiplicity `zeta23` counts.
* `RHHeight.Skeleton`: the four missing pieces as `Prop`s and the proved reduction
  `rhHeight50_of_pieces` from them and hunt #133's ten zeros to the target.

`RHHeight.Assembly` (not imported here, because it pulls in hunt #133's generated bracket
files) plugs hunt #133's theorem in: `rhHeight50_of_four` needs the four pieces only.

This root module proves nothing about zeta and stays light (Mathlib and seven `zeta23`
modules). The target is proved in `RHHeight.Main`, as `RHHeight.rh_height_fifty`, from the
four pieces (`RHHeight.GammaIncrement`, `RHHeight.HorizontalLegs`, `RHHeight.ExactArgument`,
`RHHeight.LowHeight`) and the assembly point; it is not imported here for the same reason.
The plan is `hunts/rh_height_lean/PLAN.md`, the results `hunts/rh_height_lean/RESULTS.md`; the
build is `build.sh` in this directory (`--full` for the theorem).
-/
