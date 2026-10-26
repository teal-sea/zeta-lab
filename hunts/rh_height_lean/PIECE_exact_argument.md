# PIECE `exact_argument` (hunt #137): the folded count as an exact identity

**Written 2026-10-21 by the `exact_argument` role of the campaign workflow.** Grades as in
`MISSION.md`. **Status: closed.** The theorem below is kernel-checked at the root package's
pins (Lean v4.35.0-rc2, Mathlib 0653561, vendored `zeta23`), with zero `sorry` and only the
axioms `propext`, `Classical.choice` and `Quot.sound`. Nothing is committed: the two Lean
files and this note are untracked in the worktree.

It is one of the four hypotheses of `rhHeight50_of_four` (`lean/RHHeight/Assembly.lean`). It
does not prove the target `RHHeight50`: `gamma_increment`, `horizontal_legs` and `low_height`
are other roles' pieces, and this role did not check their state.

## The statement

The plan's signature (`PLAN.md` section 4.3), unchanged:

```lean
theorem RHHeight.exact_argument (T₁ T₂ : ℝ) (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hleg₁ : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₁ * I)).re)
    (hleg₂ : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₂ * I)).re) :
    (Zeta23.Ncount T₁ T₂ : ℝ) = (∫ t in T₁..T₂, Zeta23.mu t) +
      ((riemannZeta (1 / 2 + T₂ * I)).arg - (riemannZeta (1 / 2 + T₁ * I)).arg) / Real.pi

theorem RHHeight.exact_argument_holds : RHHeight.ExactArgument
```

`riemannZeta` is Mathlib's; `Ncount` (zeros with `T₁ < Im ρ ≤ T₂`, with multiplicity) and `mu`
are `zeta23`'s. `lean/RHHeight/CheckExactArgument.lean` pins `ExactArgument` to this text by
`rfl` and checks that `count_eq_ten_of hΓ hH exact_argument : Ncount 3 52 = 10` typechecks, so
the skeleton's integer step now needs only the two enclosures `GammaIncrement` and
`HorizontalLegs`.

## The proof

`lean/RHHeight/ExactArgument.lean`, 155 lines (the seven declarations take about 100), no
numerics:

1. `goodHeight_of_re_pos`. Positivity on a leg makes its height a `GoodHeight`, so no
   `GoodHeight` hypothesis is needed. A nontrivial zero at height `T` with `Re ρ ≥ 1/2` lies
   on the leg, where `ζ ≠ 0`. One with `Re ρ < 1/2` has the reflected zero `1 - conj ρ`
   (`zetaSeam.reflect_zero`) at the same height, with real part in `(1/2, 1)`.
2. `integral_logDeriv_horizontal`. Where `Re ζ(σ + iT) > 0` the value is in the slit plane,
   so `σ ↦ log ζ(σ + iT)` has derivative `ζ'/ζ(σ + iT)` at every point of `[1/2, 2]`
   (Mathlib's `HasDerivAt.clog_real` composed with the vendored
   `hasDerivAt_riemannZeta_horizontal`), and the fundamental theorem of calculus
   (`intervalIntegral.integral_eq_sub_of_hasDerivAt`, integrability from the vendored
   `intervalIntegrable_logDeriv_horizontal`) evaluates the leg.
3. `integral_logDeriv_vertical`. The same on `σ = 2`, with the vendored primitive
   `hasDerivAt_log_riemannZeta_two`.
4. `halfContour_logDeriv_riemannZeta`. The three legs telescope: the corner values at
   `σ = 2` cancel and `log ζ(1/2 + iT₂) - log ζ(1/2 + iT₁)` is left. `Complex.log_im` turns its
   imaginary part into the difference of principal arguments
   (`im_halfContour_logDeriv_riemannZeta`). There is no winding term, because the principal
   `Complex.log` is a single continuous branch on all three legs.
5. `exact_argument`. The vendored `N_eq_halfContour_completedZeta` and
   `halfContour_completedZeta_split` (`Zeta23/RvM/MainTerm.lean`) and `gamma_side`
   (`Zeta23/RvM/GammaSide.lean`), then `ring`.

The plan's route went through as written. Two details differ from what it anticipated. Mathlib's
`HasDerivAt.clog_real` gives the slit-plane derivative in one step, so the sign-splitting
pattern of the vendored `im_integral_le_two_pi` was not needed. And the instance-hygiene line
that the vendored files carry for this import closure
(`attribute [-instance] LieAlgebra.ofAssociativeAlgebra`) is not needed here: the file
compiles without it.

## Axioms

From `lean/RHHeight/CheckExactArgument.lean`:

```
'RHHeight.goodHeight_of_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.integral_logDeriv_horizontal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.integral_logDeriv_vertical' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.halfContour_logDeriv_riemannZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.im_halfContour_logDeriv_riemannZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.exact_argument' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.exact_argument_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The compile logs of both files hold no warning, no error and no `sorry`.

## Second kernel check

`nanoda_bin` 0.4.17 is an independent type checker for Lean 4, written in Rust. It ships in
this box's v4.35.0-rc2 toolchain directory, and it rechecked the whole dependency closure of
`exact_argument` and `exact_argument_holds`: **62,109 declarations, no errors**, in 258 s wall
(138 s of CPU) at 0.54 GB peak RSS, exit code 0.

* The export came from `leanexport` (lean4export 3.1.0, same toolchain), restricted to the
  closure of the two theorems: 434 MB, made in 81 s at 4 GB peak.
* The configuration permitted exactly `propext`, `Classical.choice` and `Quot.sound`, with
  `unpermitted_axiom_hard_error: true`. Any other axiom anywhere in the closure (`sorryAx`,
  `Lean.ofReduceBool`, ...) would have stopped the check, and the export holds exactly those
  three. nanoda's Nat and String literal extensions were on, as in Lean's own kernel.
* nanoda's printout of `exact_argument` and of `ExactArgument` matches the statement above.
* Decoding the export's name table shows the closure includes Mathlib's `riemannZeta` and
  `completedRiemannZeta`, and 146 `zeta23` theorems and definitions (82 public, 64 private).
  Among them are the fold `Ncount_eq_im_halfContour` with its rectangle argument principle and
  residue calculus, `gamma_side`, `zeta_reflect_zero` and `re_riemannZeta_two_pos`. So the
  vendored counting machinery the identity rests on was rechecked with it.

What this does not cover: nanoda checks the declarations stored in the oleans. It does not
show that those oleans were compiled from this tree's sources; the build section says what
was compiled where.

To repeat it, with `LEAN_PATH` set as in the build below:

```bash
TC="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin"
"$TC/leanexport" RHHeight.ExactArgument -- RHHeight.exact_argument \
    RHHeight.exact_argument_holds > /path/to/exact.ndjson
"$TC/nanoda_bin" /path/to/exact.json
```

with `exact.json`:

```json
{
  "export_file_path": "/path/to/exact.ndjson",
  "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true,
  "nat_extension": true,
  "string_extension": true,
  "pp_declars": ["RHHeight.exact_argument", "RHHeight.exact_argument_holds", "RHHeight.ExactArgument"],
  "pp_to_stdout": true,
  "print_success_message": true
}
```

The same two commands, with the final theorem's module and name, are the second kernel check
that `MISSION.md` asks of the final statement (`PLAN.md` section 9 lists it as not set up). At
this piece's size it costs a few minutes and well under 5 GB.

## The build

**What ran** (campaign box, 2026-10-21, load average 75 to 90, raw `lean`, never lake):

* The 33 `zeta23` modules of the import closure of `Zeta23.RvM.MainTerm` were **not rebuilt by
  this role.** Their oleans are a copy of the plan role's scratch build, which compiled them
  with raw `lean` from this worktree's `lean/vendor/zeta23` between 16:14 and 16:50 UTC. No
  vendored `.lean` file is newer than those oleans, and `git status` is clean under `lean/`.
* Against that copy, in this role's own output directory, with
  `-DautoImplicit=false -DrelaxedAutoImplicit=false`: `RHHeight/Statement.lean` (6 s wall),
  `RHHeight/Skeleton.lean` (15 s), `RHHeight/ExactArgument.lean` (9 s) and
  `RHHeight/CheckExactArgument.lean` (9 s), each at about 2 GB peak RSS.

**To build from source**, from the worktree root (the module order is a topological sort of
the closure; the first seven are `build.sh`'s skeleton stage, in a different but valid order):

```bash
export PATH="$HOME/.elan/bin:$PATH"
OUT=/path/to/a/fresh/dir
LEAN="$(cd lean && elan which lean)"
LP="$OUT"; for p in "$PWD"/lean/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP"
Z23="$PWD/lean/vendor/zeta23"; H="$PWD/hunts/rh_height_lean/lean"
for m in Zeta23.Defs Zeta23.Hypotheses Zeta23.Defs.Counting Zeta23.Statement \
    Zeta23.Statement.Seam Zeta23.ZetaReflect Zeta23.Statement.SeamClosed Zeta23.RvM.Defs \
    Zeta23.Prelude.InstancePriorities Zeta23.FromPNTPlus.StrongPNTPrefix \
    Zeta23.FromPNTPlus.Auxiliary Zeta23.FromPNTPlus.Sobolev Zeta23.FromPNTPlus.Fourier \
    Zeta23.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic \
    Zeta23.FromPNTPlus.Rectangle Zeta23.FromPNTPlus.Tactic.AdditiveCombination \
    Zeta23.FromPNTPlus.ResidueCalcOnRectangles Zeta23.FromPNTPlus.EulerMaclaurin \
    Zeta23.FromPNTPlus.ZetaBounds Zeta23.RvM.ZetaGrowth Zeta23.RvM.Halving \
    Zeta23.RvM.LocalCount Zeta23.WeilEF.XiLogDeriv Zeta23.Analytic.RectangleLogDeriv \
    Zeta23.RvM.GammaSide Zeta23.RvM.BacklundDefs Zeta23.RvM.ReZeroCount Zeta23.RvM.Backlund \
    Zeta23.RvM.CountByIntegral Zeta23.FromPNTPlus.ZetaConj Zeta23.RvM.Fold \
    Zeta23.RvM.NcountWindow Zeta23.RvM.MainTerm; do
  rel="${m//.//}"; mkdir -p "$OUT/$(dirname "$rel")"
  ( cd "$Z23" && "$LEAN" --root="$Z23" -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
      "$rel.lean" -o "$OUT/$rel.olean" )
done
for m in RHHeight.Statement RHHeight.Skeleton RHHeight.ExactArgument; do
  rel="${m//.//}"; mkdir -p "$OUT/$(dirname "$rel")"
  ( cd "$H" && "$LEAN" --root="$H" -DautoImplicit=false -DrelaxedAutoImplicit=false \
      "$rel.lean" -o "$OUT/$rel.olean" )
done
( cd "$H" && "$LEAN" --root="$H" -DautoImplicit=false -DrelaxedAutoImplicit=false \
    RHHeight/CheckExactArgument.lean )
```

On this box, wait for `MemAvailable` above 30 GiB before each `lean` process, as `build.sh`
does. The zeta23 loop is `build.sh`'s own loop extended to the closure. This role ran the
block above as written, extracted from this file with only `OUT` changed and the zeta23 loop
cut to its first module (`Zeta23.Defs`, recompiled from source; the other 32 from the copied
oleans): exit 0 in 32 s, the seven axiom lines above, no warning. The full zeta23 loop was not
rerun. By its olean times, the plan role's build of the closure took about 41 minutes of wall
time at six jobs in parallel (16:14 to 16:55), along the chain `StrongPNTPrefix`, `ZetaBounds`,
`ZetaGrowth`, `LocalCount`, `ReZeroCount`, `Backlund`, `MainTerm`, which more jobs would not
shorten. A CI run is the natural receipt for it.

**Not edited, because the sibling roles share them:** `lean/build.sh`, `lean/check_axioms.py`,
`lean/CheckAxioms.lean` and the root module `lean/RHHeight.lean`. Integrating the piece means a
`build.sh` stage with the 26 further `zeta23` modules above, then `RHHeight.ExactArgument`
and `RHHeight/CheckExactArgument.lean`, and the seven names above in the expected set of
`check_axioms.py`.

## What this does not say

* The identity is exact and conditional. At `T₁ = 3`, `T₂ = 52` its hypotheses are the
  positivity half of `horizontal_legs`, which is open as far as this role knows. It gives no
  numerical information about either argument or about `∫ μ`; those are the enclosures of
  `horizontal_legs` and `gamma_increment`.
* It needs `1 ≤ T₁`, the vendored fold's condition. Below the contour, zeros are the business
  of `low_height`.
* The same theorem serves the second target unchanged: at `(3, 99.85)` its hypotheses are
  `Re ζ > 0` on the leg at `99.85`, where the sibling numeric plan's Arb lower bound is `1.191`
  (`NUMERIC_PLAN.md`). That is a hardened measurement there, not a theorem here.
* A lighter import is possible and was not taken. From `MainTerm`'s closure the proof calls
  the two `MainTerm` wrappers (over `Fold` and `XiLogDeriv`), `gamma_side`, `zetaSeam` and
  four `Backlund` helpers. The closure of `Fold`, `GammaSide` and `XiLogDeriv` alone is 17
  modules and avoids the long chain above. Using it would mean restating
  `halfContour_completedZeta_split` and the four helpers, two of which rest on the bound
  `‖ζ(s) - 1‖ ≤ π²/6 - 1` of `RvM.ZetaGrowth`. The brief was reuse, and build time is a CI
  concern.
