# RESULTS: `rh_height_lean` (hunt #137), first target T = 50

**Grade: kernel-checked** (Lean v4.35.0-rc2, Mathlib 0653561, zero `sorry`, axioms
`propext`, `Classical.choice`, `Quot.sound` only). Second kernel check: not run.

## The theorems

In `lean/RHHeight/Main.lean`, for Mathlib's own `riemannZeta`:

- `RHHeight.rh_height_fifty : RHHeight.RHHeight50`. Every zero `rho` with
  `0 < Re rho < 1` and `0 < Im rho <= 50` has `Re rho = 1/2` and
  `analyticOrderAt riemannZeta rho = 1`.
- `RHHeight.zero_count_fifty : RHHeight.ZeroCountUpTo 50 10`. There are exactly 10
  distinct such zeros.
- `RHHeight.rh_up_to_height_fiftytwo : RHHeight.RHUpToHeight 52`, the same statement to
  height 52, and `RHHeight.ncount_three_fiftytwo : Zeta23.Ncount 3 52 = 10`, the count
  with multiplicity for `3 < Im rho <= 52`.

The statements are the definitions in `lean/RHHeight/Statement.lean`. They quantify over
`riemannZeta` directly, with no auxiliary hypothesis.

## How it is proved

`Skeleton.lean` reduces the statement to four hypotheses, and each piece discharges one:

| Piece | File | What it proves |
|---|---|---|
| Gamma-side increment | `GammaIncrement.lean` | `92/10 <= integral of mu over [3, 52] <= 109/10`, from the vendored Stirling bound `digamma_stirling` |
| Horizontal legs | `HorizontalLegs.lean` and `Legs*.lean` | `Re zeta > 0` on `[1/2, 2] + 3i` and `[1/2, 2] + 52i`, with the two end arguments enclosed, from interval boxes the kernel decides |
| Exact argument | `ExactArgument.lean` | under that positivity, the vendored `zeta23` folded argument principle is the exact identity `Ncount T1 T2 = integral of mu + (arg zeta(1/2 + i T2) - arg zeta(1/2 + i T1))/pi` |
| Low height | `LowHeight.lean` | no zero with `0 < Im rho <= 3`, from hunt #132's Euler-Maclaurin representation at `N = 1` |

The three enclosures put the count for `3 < Im rho <= 52` strictly between 9 and 11, so it
is 10. Hunt #133's ten distinct zeros on the line lie in that window, so they are all of
its zeros, and each is simple. `LowHeight` covers `0 < Im rho <= 3`.

## Checks

- Each piece was compiled once by its builder and again by a separate checker from its
  own from-source build, on 2026-10-21.
- The integrated build ran on 2026-10-22 from 04:28 to 04:47 UTC on the campaign box:
  `LAKE_DIR=<root>/lean/.lake bash hunts/rh_height_lean/lean/build.sh --full <OUT>`.
  It compiled 74 modules from source plus seven check files and exited 0 with no error.
- `python3 lean/check_axioms.py <log> --full` accepted all 72 axiom reports with only the
  three standard axioms.
- Numerical cross-check, not part of the proof: mpmath `nzeros(50) = 10` and
  `nzeros(52) = 10`, with `gamma_10 = 49.7738...` and `gamma_11 = 52.9703...`.

## What this does not say

Nothing above height 52 and nothing about the Riemann hypothesis (`docs/08`). Like every
finite-height verification it cannot tell `zeta` from the Davenport-Heilbronn function
below that function's first off-line zero, at height 85.699. RH has been verified
numerically far higher (Platt and Trudgian, 2021, to 3.0e12). What is new here is the
kernel check, not the range. The campaign's two web searches found no earlier
kernel-checked finite-height verification. That is not a literature search, so no novelty
is claimed.

## Open

- The second target, T = 100 (29 zeros), with `plan_T100.json` as its numerical plan.
- A second kernel check (NanoDa or Comparator), named in the mission's oracles. Not run.
