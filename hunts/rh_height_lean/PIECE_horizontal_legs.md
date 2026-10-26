# PIECE `horizontal_legs` (hunt #137): `Re zeta > 0` on both horizontal legs

**Written 2026-10-21 by the `horizontal_legs` role of the campaign workflow.** Grades as in
`MISSION.md`. **Status: closed.** The theorem below compiles at the root package's pins
(Lean v4.35.0-rc2, Mathlib 0653561), with zero `sorry` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`, so it is kernel-checked as a file (pending external
verification, like everything in this hunt). Nothing is committed: the Lean files, the
generator, its test and this note are untracked in the worktree.

It is one of the four hypotheses of `rhHeight50_of_four` (`lean/RHHeight/Assembly.lean`). It
does not prove the target `RHHeight50`: `gamma_increment`, `exact_argument` and `low_height`
are other roles' pieces, and this role did not check their state.

## The statement

The plan's signature (`PLAN.md` section 4.2), unchanged:

```lean
theorem RHHeight.horizontal_legs :
    (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 3 * I)).re) ∧
    (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 52 * I)).re) ∧
    -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧ (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 ∧
    -(1 / 3 : ℝ) ≤ (riemannZeta (1 / 2 + 52 * I)).arg ∧
      (riemannZeta (1 / 2 + 52 * I)).arg ≤ 0

theorem RHHeight.horizontalLegs : RHHeight.HorizontalLegs
```

`riemannZeta` is Mathlib's. `lean/RHHeight/CheckHorizontalLegs.lean` pins `HorizontalLegs`
to this text by `rfl`, checks that `horizontal_legs` has the plan's signature verbatim, and
checks that `rhHeight50_of_pieces hΓ horizontal_legs hE hL h10 : RHHeight50` typechecks, with
the other three pieces and hunt #133's input left as hypotheses.

## The files

| file | what it is |
|---|---|
| `lean/RHHeight/LegSupport.lean` | the analysis, general in the point (671 lines, hand-written) |
| `lean/RHHeight/LegsBottom.lean` | three segments of the leg `[1/2, 2] + 3i` (generated) |
| `lean/RHHeight/LegsTop1.lean`, `LegsTop2.lean` | six segments of the leg `[1/2, 2] + 52i` (generated) |
| `lean/RHHeight/LegsArg.lean` | boxes for `zeta(1/2 + 3i)` and `zeta(1/2 + 52i)`, and the arguments (generated) |
| `lean/RHHeight/HorizontalLegs.lean` | `horizontal_legs` and `horizontalLegs`, from the above |
| `lean/RHHeight/CheckHorizontalLegs.lean` | the pins and the axiom report |
| `gen_legs.py` | writes the four generated files; `--check` compares, `--report` prints mpmath values |
| `test_gen_legs.py` | 12 tests: files match the generator, every check closes, four kinds of planted fault refused, three cross-checks by other routes |

## The proof

**The segment inequality** (`RHHeight.Legs.re_pos_of_segment`). Let `0 < a <= sigma <= b`,
`0 < y`, `2 <= N < 64`, `w = a + iy`, and let `M_N` be the order-4 Euler-Maclaurin main term
that hunt #132's `zeta_em4_error` subtracts. Then

    Re zeta(sigma + iy) >= Re M_N(w) - (sigma - a) L - R,
    L = sum_{n<N} log n |n^(-w)| + |N^(-w)| (log N (N/y + 1/2 + (b+y)/(12N)) + N/y^2 + 1/(12N)),
    R = P |(N-1)^(-w)| / ((N-1)^3 * 720 * (a+3)),   P^2 >= prod_{j<4} ((b+j)^2 + y^2).

1. *The main term at the left end* (`mainBoxG_contains`): `M_N(w) = sum_{n<N} n^(-w) +
   N^(-w) c_N(w)` (hunt #132's `main_eq`), with `c_N(w) = N/(w-1) + 1/2 + w/(12N)` an exact
   Gaussian rational (`cReG`, `cImG`), and a table of term boxes for `m^(-w)`, `m <= N`: an exp
   tower (`dirichletTermBox2`, which accepts any box for `s`) for each prime, a coarsened
   product for each composite, as in hunt #133.
2. *The variation along the segment* (`norm_mainTerm_sub_le`). Termwise:
   `n^(-(sigma+iy)) = n^(-w) n^(-(sigma-a))` (`cpow_split`) and `0 <= 1 - n^(-d) <= d log n`
   (`Real.add_one_le_exp`) give `|n^(-s) - n^(-w)| <= (sigma - a) log n |n^(-w)|`; for the
   last term, `|c_N(s)| <= N/y + 1/2 + (b+y)/(12N)` and
   `|c_N(s) - c_N(w)| <= (sigma - a)(N/y^2 + 1/(12N))`. This is the mean value bound of order
   1, written out termwise, with no derivative taken.
3. *The remainder, uniformly* (`norm_zeta_sub_mainTerm_le`): `zeta_em4_error` at
   `s = sigma + iy`, with `|P4 s|` bounded at `b` (each `|s + j|` grows with `sigma`),
   `(N-1)^(-sigma-3)` bounded at `a`, `1/(sigma+3)` at `a`, and
   `(N-1)^(-a) = |(N-1)^(-w)|` (`norm_natCast_cpow_of_pos`).
4. *The rational check* (`segSlack`). Every `|n^(-w)|` is replaced by `normUp` of its box (the
   octagon bound `max(X, Y) + (5/12) min(X, Y)` on the componentwise maxima, `norm_le_normUp`)
   and every `log n` by `logTab n = (Interval.logQ 20 (kOf n) n).hi` (`log_le_logTab`). So the
   check reads only the table at the left end, and `0 < segSlack` is one rational inequality
   that the kernel decides.

**The legs** (`HorizontalLegs.lean`). Nine segments cover the two legs; each one is a generated
`seg` theorem, and `re_zeta_pos_bottom`, `re_zeta_pos_top` glue them by cases on `sigma`:

| leg | segment | `N` | box lower end of `Re M_N(w)` | variation `(b-a)L` | radius `R` | slack | measured `min Re zeta` |
|---|---|---|---|---|---|---|---|
| `3i` | `[1/2, 43/64]` | 2 | 0.5345 | 0.1542 | 0.0798 | 0.3004 | 0.5327 |
| `3i` | `[43/64, 19/16]` | 2 | 0.5680 | 0.4158 | 0.1022 | 0.0500 | 0.5658 |
| `3i` | `[19/16, 2]` | 2 | 0.6669 | 0.4673 | 0.1479 | 0.0517 | 0.6640 |
| `52i` | `[1/2, 39/64]` | 12 | 1.7749 | 0.9015 | 0.7004 | 0.1729 | 1.5884 |
| `52i` | `[39/64, 3/4]` | 12 | 1.6157 | 0.9460 | 0.5227 | 0.1469 | 1.4399 |
| `52i` | `[3/4, 15/16]` | 12 | 1.4594 | 0.9761 | 0.3593 | 0.1240 | 1.3002 |
| `52i` | `[15/16, 9/8]` | 10 | 1.2598 | 0.6024 | 0.4914 | 0.1659 | 1.2064 |
| `52i` | `[9/8, 23/16]` | 10 | 1.1799 | 0.7423 | 0.3111 | 0.1265 | 1.1128 |
| `52i` | `[23/16, 2]` | 10 | 1.0997 | 0.8246 | 0.1459 | 0.1291 | 1.0409 |

The four middle columns are the exact rationals the kernel decides, rounded here (slacks
rounded down). The slack is a lower bound for `Re zeta` on its segment that the proof establishes on
the way, though the theorem states positivity only. The last column is measured (mpmath at 30
digits, 65 samples per segment, floating point, one route).

**The two arguments** (`LegsArg.lean`, `zeta_mem_pointBox`, `arg_mem_of_box`). The same
machinery at the single point `a = b = 1/2` gives a box containing `zeta(1/2 + iy)`: the
main-term box inflated by `R`. For a box `B` with `Re lo > 0` and `Im hi <= 0`,
`Im lo / Re lo <= arg z <= 0` for every `z` in it: `arg z = arctan(Im z / Re z)`
(`Complex.tan_arg`, `Real.arctan_tan`, `Complex.abs_arg_lt_pi_div_two_iff`) and
`x <= arctan x` for `x <= 0` (`Real.self_le_arctan`). Kernel-checked, with the endpoints
rounded outward here:

* at `1/2 + 3i`, `N = 4`: `zeta` lies in `[0.5313, 0.5347] + i [-0.0809, -0.0775]`, and
  `Im lo / Re lo = -0.1522 >= -1/5`;
* at `1/2 + 52i`, `N = 28`: `zeta` lies in `[1.7103, 1.7705] + i [-0.5304, -0.4702]`, and
  `Im lo / Re lo = -0.3102 >= -1/3`.

Measured (mpmath): `zeta(1/2 + 3i) = 0.532737 - 0.078897 i` (`arg = -0.147028`) and
`zeta(1/2 + 52i) = 1.739361 - 0.501857 i` (`arg = -0.280901`), inside both boxes.

## Where it differs from the plan's route

The plan's four steps went through; three choices differ, and the statement does not.

1. **Expansion from the left end, not the midpoint.** The variation bound is one-sided, so
   `n^(-(sigma-a))` lies in `(0, 1]` and every constant in `L` is read off the table at the
   left end. The price is a variation term twice the midpoint one. The sibling's Arb
   partitions (`NUMERIC_PLAN.md` section 3) were sized for a midpoint expansion with exact
   norms, so they were not used; the partitions above were re-sized against the exact Lean
   quantities, by a dynamic program over the dyadic grid of step 1/64 (fewest prime towers,
   every slack above 1/20; scratch work, not kept). The prime-tower count is the same as the
   sibling's projection, 41: 3 on the bottom leg, 27 on the top leg, 2 and 9 at the points.
2. **No separate rational bounds for powers.** The plan suggested a rational bound for
   `(N-1)^(-sigma-3)`; here `(N-1)^(-a)` is `|(N-1)^(-w)|`, which the table's box for
   `(N-1)^(-w)` already bounds.
3. **The point boxes come from the same lemma**, not from hunt #133's `zeta_mem_mainBox`.
   Its remainder reads `(N-1)^(-1/2)` off a box through the octagon bound, up to 8% looser
   than hunt #133's `r^2 <= N - 1`, so the truncations are a little larger than the plan's:
   `N = 4` at `1/2 + 3i` (plan 3) and `N = 28` at `1/2 + 52i` (plan 24). Neither costs a tower:
   4, 24, 25, 26, 27 and 28 are composite. `N = 24` also closes with this lemma, with
   `Im lo / Re lo = -0.3295`, only `0.004` inside `-1/3`; 28 leaves `0.023`.

## Build and axioms

The piece needs hunt #132's `HardyFirstZero.BoxSupport` chain, hunt #133's
`HardyTenZeros.TenSupport` (for `contains_cpow_mul_coarsen` and `contains_one_cpow`) and the
skeleton. From the worktree root, into a fresh directory, never lake:

```bash
export PATH="$HOME/.elan/bin:$PATH"
OUT=$(mktemp -d)
LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh --assembly "$OUT"
for f in LegSupport LegsBottom LegsTop1 LegsTop2 LegsArg HorizontalLegs; do
  LAKE_DIR="$PWD/lean/.lake" bash hunts/rh_height_lean/lean/build.sh --file "RHHeight/$f.lean" "$OUT"
done
LP="$OUT"; for p in "$PWD"/lean/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
( cd hunts/rh_height_lean/lean && LEAN_PATH="$LP" "$(cd ../../../lean && elan which lean)" \
    -DautoImplicit=false -DrelaxedAutoImplicit=false RHHeight/CheckHorizontalLegs.lean )
```

`--assembly` also compiles hunt #133's nine bracket files, which the piece does not need; the
minimal chain is `ZetaLean.Rigor`, `IntervalExp`, `IntervalCExp`, `HardyZ`, then
`HardyFirstZero.Spine`, `Phase`, `EulerMaclaurin`, `BoxSupport`, then `HardyTenZeros.PhaseShort`,
`TenSupport`, beside the skeleton stage. The four generated files are independent of each
other and may be compiled in parallel.

What ran, on the campaign box on 2026-10-21 at load averages from 50 to 100: that minimal
chain from the sources in this worktree, into an empty directory, with `ZetaLean` taken from
the root package's own build (`lean/.lake/build/lib/lean`), the seven zeta23 statement modules
and `RHHeight.Statement`, `RHHeight.Skeleton` compiled beside it, then the piece. Wall times:
`LegSupport` 47 s, `LegsBottom` 42 s, `LegsTop1` 144 s, `LegsTop2` 105 s, `LegsArg` 103 s
(the four generated files in parallel), `HorizontalLegs` 17 s, the check 18 s; the whole run,
dependencies included, took 5 min 35 s and exited 0. In the development runs each `lean`
process peaked between 3.8 and 6.6 GB resident (`/usr/bin/time`). No module of the piece
printed a warning or an error. The check printed, abridged (29 axiom reports, all alike, and a
fail-closed scan of the log found no other axiom, no `sorry` and no error):

```
RHHeight.horizontal_legs : (∀ σ ∈ Set.Icc (1 / 2) 2, 0 < (riemannZeta (↑σ + 3 * I)).re) ∧
  (∀ σ ∈ Set.Icc (1 / 2) 2, 0 < (riemannZeta (↑σ + 52 * I)).re) ∧
    -(1 / 5) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧
      (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 ∧
        -(1 / 3) ≤ (riemannZeta (1 / 2 + 52 * I)).arg ∧ (riemannZeta (1 / 2 + 52 * I)).arg ≤ 0
'RHHeight.horizontal_legs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.horizontalLegs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.Legs.re_pos_of_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.Legs.H52S1.seg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHHeight.Legs.Arg52.arg_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The six `build.sh --file` lines and the check above were then run as written, against an
output directory holding the modules of that first run and copies of the four `ZetaLean`
oleans of the root package's build (copied files, no lake): 336 s serially, exit 0, the same
29 reports. `build.sh --assembly` itself was not run by this role.

To integrate: compile the six modules in `build.sh`'s `--assembly` stage after hunt #133's
`TenSupport`, run `RHHeight/CheckHorizontalLegs.lean` there, and add `RHHeight.horizontal_legs`,
`RHHeight.horizontalLegs` and the `RHHeight.Legs.*` names of the check file to the
`--assembly` set of `check_axioms.py`. The module that states the final theorem (`PLAN.md`
section 6) imports `RHHeight.HorizontalLegs`. This role did not edit `build.sh`,
`check_axioms.py`, `RHHeight.lean` or any other shared file.

## Checks

- **Planted faults are refused by the kernel.** Against the generated tables, in scratch:
  the first bottom table stretched over all of `[1/2, 2] + 3i`; the second bottom segment
  stretched from `19/16` to `5/4` (slack `-0.0049`, against `+0.0501` at `19/16`); the bound
  `-1/10 <= Im lo / Re lo` at `1/2 + 3i` (the box gives `-0.152`); and one term box shifted by
  `2^-60`. Each `decide +kernel` fails, and each negation is proved by `decide +kernel`, so the
  kernel evaluates the planted claim and finds it false rather than failing to evaluate it.
  The control, the second segment as generated, passes.
- **The generator refuses them too** (`test_gen_legs.py`): the two stretched segments, the
  first top segment moved to height 50 (where `Re zeta(1/2 + 50i) = -0.0817`, measured), the
  same segment at `N = 8`, and argument bounds of `-1/10` at `3` and `-3/10` at `52`.
- **Other routes** (measured, not proofs): Arb values of `m^(-s)` from python-flint lie in the
  mirror's term boxes (three tables checked), mpmath's `zeta` lies in both point boxes, and
  the segment lower bound `Re M_N(w) - (sigma - a) L - R` lies below mpmath's `Re zeta` at
  nine points of every segment.
- `gen_legs.py --check` reports that the four files on disk match the generator.

## What it does not say

Positivity of `Re zeta` on the two horizontal legs and the two corner arguments, nothing more.
It says nothing about the vertical leg `sigma = 2` (the vendored `re_riemannZeta_two_pos`),
about counts, or about any height other than 3 and 52. No novelty is claimed and no search
was run.

## The doors

1. **Active constraints.** On the bottom leg the variation term binds: at `N = 2` it takes
   `0.42` and `0.47` of main terms near `0.57` and `0.67` on the last two segments, and moving
   one end from `19/16` to `5/4` flips the slack's sign. On the top leg the variation and the
   remainder together take 87 to 92% of the main term on every segment, the remainder most
   at `sigma = 1/2` (`0.70` at `N = 12`). At `1/2 + 52i` the radius (`0.030` at `N = 28`) is
   what the argument bound spends.
2. **Frozen constants.** The left-end expansion (a midpoint expansion halves the binding
   variation term, at the price of a two-sided bound with an `n^rho` factor: the one door
   here with genuine trade shape); Taylor order 1 (orders 2 and 3 cut the sub-segments to a
   handful in the sibling's table, at the price of derivative boxes); the octagon constant
   `5/12` (`sqrt 2 - 1 = 0.4142`, up to 8% on every norm); `logTab`'s order 20 (slack: its
   error is near `1e-6`); hunt #133's term-box parameters `(36, 16, 80, 8)`; the dyadic grid
   1/64, the range `N <= 16` and the margin `1/20` of the partition search; `P` rounded up to
   four decimals.
3. **Information class.** Everything reads main-term boxes at finitely many points and the
   order-4 remainder: hunt #133's class, off the line. The `T = 100` analogue needs no new
   class: `re_pos_of_segment` is general in `(a, b, y)`, so the leg at `99.85` is a new
   partition in `gen_legs.py`, and its corner argument (`0.1999`, measured, positive) needs
   the mirror image of `arg_mem_of_box` for a box with `Im lo >= 0`.

The partitions are a measured optimum of one search, not a proved ceiling for this route.
