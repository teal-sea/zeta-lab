# PIECE `low_height` (hunt #137): no zero of zeta with `0 < Im rho <= 3`

**Written 2026-10-21 by the `low_height` role of the campaign workflow.** Grades as in
`MISSION.md`. **Status: closed.** The theorem below compiles at the root package's pins
(Lean v4.35.0-rc2, Mathlib 0653561), with zero `sorry` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`, so it is kernel-checked as a file. Nothing is committed:
the two Lean files and this note are untracked in the worktree.

It is one of the four hypotheses of `rhHeight50_of_four` (`lean/RHHeight/Assembly.lean`). It
does not prove the target `RHHeight50`: `gamma_increment`, `horizontal_legs` and
`exact_argument` are other roles' pieces, and this role did not check their state.

## The statement

The plan's signature (`PLAN.md` section 4.4), unchanged:

```lean
theorem RHHeight.low_height : RHHeight.LowHeight
-- `RHHeight.LowHeight` unfolds, by `rfl`, to
--   ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 3 → False
```

`riemannZeta` is Mathlib's. `lean/RHHeight/CheckLowHeight.lean` pins `LowHeight` to that text
by `rfl`, checks that `low_height` has the plan's signature verbatim, and checks that
`rhHeight50_of_pieces hΓ hH hE low_height h10 : RHHeight50` typechecks, with the other three
pieces and hunt #133's input left as hypotheses. On the way, in `lean/RHHeight/LowHeight.lean`
(`P4 s = s(s+1)(s+2)(s+3)`, `QP` the open quarter plane, both from hunt #132):

```lean
theorem RHHeight.norm_tail_one_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖∑' k : ℕ, HardyFirstZero.eBlock s ((k + 1 : ℕ) : ℝ)‖
      ≤ ‖HardyFirstZero.P4 s‖ * (1 + 1 / (s.re + 3)) / 720
theorem RHHeight.norm_zeta_sub_main_one_le {s : ℂ} (hs : s ∈ HardyFirstZero.QP) :
    ‖riemannZeta s - (s + 2) * (s + 3) / (12 * (s - 1))‖
      ≤ ‖HardyFirstZero.P4 s‖ * (1 + 1 / (s.re + 3)) / 720
theorem RHHeight.riemannZeta_ne_zero_of_im_le_three {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (h2 : 0 < s.im) (h3 : s.im ≤ 3) : riemannZeta s ≠ 0
```

`norm_zeta_sub_main_one_le` holds on the whole quarter plane `Re s > 0, Im s > 0`: zeta to
within an explicit error of a rational function, with no interval arithmetic.

## The proof

The plan's route, with a simpler last step.

1. `HardyFirstZero.zeta_em4` at `N = 1` (hunt #132): on the quarter plane
   `zeta(s) = 1/(s-1) + 1/2 + s/12 - sum_{k >= 0} e(s, k+1)`. The partial sum is `0^(-s) = 0`
   (`Complex.zero_cpow`, as `s ≠ 0`), and `1/(s-1) + 1/2 + s/12 = (s+2)(s+3)/(12(s-1))`.
2. The tail is summable (`norm_eBlock_le` against `sum (k+1)^(-sigma-4)`), so it splits after
   its first block: `norm_eBlock_le` at `x = 1` bounds that block by `‖P4 s‖/720`, and
   `norm_tail_le` at `N = 2` bounds the rest by `‖P4 s‖/(720(sigma+3))`.
3. At a zero, `‖(s+2)(s+3)/(12(s-1))‖ <= ‖P4 s‖ (1 + 1/(sigma+3))/720 <= ‖P4 s‖/540`.
   Cancelling `‖s+2‖ ‖s+3‖ > 0` leaves `45 <= ‖s-1‖ ‖s‖ ‖s+1‖`. On `0 < sigma < 1`,
   `0 < t <= 3` the three squared norms are at most `10`, `10` and `13`, so the product
   squared is at most `1300 < 2025 = 45^2`.

Step 3 differs from the plan's in form only. The plan squares
`60(sigma+3) <= ‖s‖ ‖s+1‖ ‖s-1‖ (sigma+4)` and uses `(sigma+4)^2/(sigma+3)^2 <= 16/9`; here
`1/(sigma+3) <= 1/3` comes first, the same factor `4/3`, and the coarse `‖s‖^2 <= 10`,
`‖s-1‖^2 <= 10` replace the plan's `(sigma^2+t^2)((1-sigma)^2+t^2) <= 1/16 + t^2 + t^4`. The
proved bound on the product is then `sqrt(1300)/45 = 0.80` of the threshold, against the
plan's `sqrt(2082/3600) = 0.76`. Every step is `nlinarith`, `gcongr`, `field_simp` or a
rewrite; nothing evaluates zeta.

## Build and axioms

From the worktree root, into a fresh directory, never lake:

```bash
export PATH="$HOME/.elan/bin:$PATH"
OUT=$(mktemp -d); LEAN="$(cd lean && elan which lean)"
LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh "$OUT"   # skeleton stage
LP="$OUT"; for p in "$PWD"/lean/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP"; mkdir -p "$OUT/ZetaLean" "$OUT/HardyFirstZero"
( cd lean && "$LEAN" --root=. ZetaLean/HardyZ.lean -o "$OUT/ZetaLean/HardyZ.olean" )
( cd hunts/hardy_first_zero/lean &&
  "$LEAN" --root=. HardyFirstZero/Spine.lean -o "$OUT/HardyFirstZero/Spine.olean" &&
  "$LEAN" --root=. HardyFirstZero/Phase.lean -o "$OUT/HardyFirstZero/Phase.olean" &&
  "$LEAN" --root=. HardyFirstZero/EulerMaclaurin.lean -o "$OUT/HardyFirstZero/EulerMaclaurin.olean" )
LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh --file RHHeight/LowHeight.lean "$OUT"
( cd hunts/rh_height_lean/lean && "$LEAN" RHHeight/CheckLowHeight.lean )
```

`build.sh` reaches hunt #132's modules only through `--assembly`, which also compiles hunt
#133's twelve modules; the middle lines compile just the import chain
`ZetaLean.HardyZ`, `HardyFirstZero.Spine`, `Phase`, `EulerMaclaurin`, with the invocations and
options `build.sh --assembly` uses. After `build.sh --assembly "$OUT"` the last two lines
suffice.

Measured on the campaign box on 2026-10-21, at load averages from 46 to 80: the sequence
above ran from an empty directory in 149 s and, in a second run under `set -euo pipefail`,
245 s (exit 0 both times); `LowHeight.lean` alone takes 26 s wall
and 2.05 GB peak resident memory, and the check about 6 s. The piece's compile printed
nothing. The check printed:

```
RHHeight.low_height : RHHeight.LowHeight
'RHHeight.norm_tail_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.norm_zeta_sub_main_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.riemannZeta_ne_zero_of_im_le_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.low_height' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To integrate: compile `RHHeight.LowHeight` in `build.sh`'s `--assembly` stage after hunt
#132's modules, run `RHHeight/CheckLowHeight.lean` there, and add the four names to the
`--assembly` set of `check_axioms.py`. The module that states the final theorem (`PLAN.md`
section 6) imports `RHHeight.LowHeight`. This role did not edit `build.sh`, `check_axioms.py`,
`RHHeight.lean` or any other shared file.

## Checks

- **A planted fault is refused.** The same proof with `Im s <= 4`, and its norm bounds raised
  honestly to `17`, `17` and `20`, fails at its last step and nowhere before it (`linarith
  failed`: `17 * 17 * 20 = 5780` is not below `2025`). The height bound is used where the
  argument says it is.
- **Measured** (mpmath at 30 digits, one route, floating point: a cross-check, not the proof,
  and not pinned by a test). On a 100 by 301 grid of `(0,1) x (0,3]`, the proved bound
  `‖P4 s‖ (1 + 1/(sigma+3))/720` is at most `0.711` of the main term's norm, with supremum
  `0.7126` at the corner `sigma -> 1`, `t = 3` (the plan's `0.713`); the coarser `‖P4 s‖/540`
  has supremum `3 sqrt(130)/45 = 0.7601` at the same corner (grid maximum `0.758`);
  `‖s-1‖ ‖s‖ ‖s+1‖` has supremum `3 sqrt(130) = 34.21` there, against the `45` the argument
  needs and its proved bound `sqrt(1300) = 36.06`; and the true remainder `|zeta(s) - main|`
  is at most `0.204` of the bound, near `s -> 0`. Maximized over `sigma` (at `sigma -> 1` at
  every height checked), the bound-to-main ratio is `0.989` at `t = 3.4`, `1.029` at `3.45` and
  `1.069` at `3.5`, and it crosses `1` at `t = 3.4125`, so this route stops there, as the
  plan says. mpmath gives `nzeros(3) = 0` and a first ordinate of `14.1347`.

## What it does not say

It is a statement below height 3 and nothing more. The first zero sits at height `14.1347`
(mpmath), and this piece proves nothing between 3 and there; it also says nothing about
`Re rho` outside `(0, 1)`, which the plan does not need. No novelty is claimed and no search
was run.

## The doors

What binds is the order-4 remainder at the corner `sigma -> 1`, `t = 3`, where the proved
bound is `0.713` of the main term; the ratio reaches `1` at `t = 3.4125` (measured). The
frozen choices are `N = 1`, which keeps the main term rational at the cost of the largest
tail; the split after the first block; and the relaxations `1/(sigma+3) <= 1/3` and
`10, 10, 13`, which cost margin (`0.80` against `0.7126`) and nothing else. A larger `N`
shrinks the tail by `(N-1)^(-sigma-3)` but puts `n^(-s)` into the main term, which then needs
interval enclosures, the information class of `horizontal_legs`. This route (rational main
term, order-4 remainder, no value of zeta) stops at `t = 3.4125`; that is a measured limit of
the route, not a proved ceiling for every exclusion of this kind.
