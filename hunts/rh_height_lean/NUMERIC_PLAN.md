# NUMERIC_PLAN: the contour plan for `rh_height_lean` at T = 50 and T = 100

**2026-10-21. Hunt #137, the numeric contour plan.** Files: `numeric_plan.py` (the generator
and the verifier), `plan_T50.json`, `plan_T100.json` (the plans), `test_numeric_plan.py`
(pins and planted faults). Nothing here is a theorem and nothing here is Lean. It is the
plan a Lean proof would replay, with every number it would need, and the evidence that the
plan holds.

**Plan of record.** The statement-and-skeleton role of this workflow fixed the Lean contour
in `PLAN.md` and in `lean/RHHeight/Skeleton.lean` (which PLAN.md reports as kernel-checked;
this plan did not build it). The skeleton derives `Ncount 3 52 = 10` from three stated pieces
and the target from a fourth: bottom height 3, top heights 52 (for T = 50) and 99.85 (for
T = 100). Section 3 hardens that contour and reports three corrections to its numbers.
Sections 4 to 6 are a second, independent Lean-shaped contour from `T1 = 10`, planned before
the skeleton existed; it stays as a cross-check and as the fallback if the skeleton's
low-height bound at 3 fails.

**Integration note (2026-10-21, end of the wave).** The skeleton's contour of section 3 is now
a kernel-checked proof at T = 50 (`RESULTS.md`). Its `horizontal_legs` piece was built with
its own partitions, sized for an expansion from each segment's left end, not the ones in
section 3. For T = 100 the top height must be at least 100, not `99.85`: `RHUpToHeight 99.85`
says nothing about zeros with `99.85 < Im rho <= 100`. At 100 the top leg is the one of
section 4.5 (all `+1`, Arb lower bound `1.189`); `RESULTS.md` section 7.

**Grades** (`CLAUDE.md`, the certainty ladder). Every enclosure below is Arb ball arithmetic
(python-flint 0.9.0) with every step carried. The two counts agree across routes that share
no contour code (section 1), so the counts, the enclosures and the margins are *hardened*.
The Lean-side bounds are explicit formulas evaluated in Arb; that a Lean proof built on them
closes is a projection, *measured*. The telescoping identity and the derivative bounds of
section 4 are ordinary derivations written out here, not reviewed and not kernel-checked.
Nothing bears on RH beyond the stated heights (`docs/08`). No novelty is claimed.

Reproduce from the repository root:

```bash
.venv/bin/python hunts/rh_height_lean/numeric_plan.py           # rebuild both plans
.venv/bin/python hunts/rh_height_lean/numeric_plan.py --check   # rebuild, verify, compare; exit 1 on drift
.venv/bin/python -m pytest -q hunts/rh_height_lean               # pins, controls, planted faults
```

## 1. The counts, by every route

| route | T = 50 | T = 100 | what it shares with the others |
|---|---|---|---|
| `zeta/rigor.py` zero-count routine (line 763), its own report | 10 | 29 | Arb; contour from the real axis |
| the same routine, replayed step by step here | 10 | 29 | identical computation, checked equal to the report |
| `zeta/rigor.py` RH-to-height routine (line 1110) | 10 | 29 | calls the zero count |
| proven sign changes of Hardy Z in that routine (scan at line 639) | 10 | 29 | a lower bound only |
| the skeleton's contour (section 3), exact Arb values | 10 | 29 | Arb; contour from 3 to 52 or 99.85 |
| the same, under the skeleton's Gamma route and Lean boxes | 10 | 29 | as above |
| the contour from T1 = 10 (section 4), exact Arb values | 10 | 29 | Arb; another contour, partition and argument bookkeeping |
| the same, under the vendored `mu_stirling` budget | 10 | 29 | as above |
| rigor.py's count at T minus its count at 10 | 10 | 29 | Arb |
| Arb's own zero counter, `arb.zeta_nzeros` (Turing's method) | 10 | 29 | Arb; no contour |
| mpmath `nzeros` (Gram points and Rosser blocks, floating point) | 10 | 29 | none |
| mpmath `zetazero(k)` ordinates below T | 10 | 29 | none |

The mission's last kill condition, *the count disagrees with mpmath's nzeros*, is not
triggered at either height. The ordinates around the heights (mpmath, measured) are
`49.7738324777` and `52.9703214777` around 50 and 52, and `98.8311942182` and
`101.3178510057` around 100 and 99.85. Arb's Backlund `S(T)` agrees with the replayed `S(T)` to
all 18 stored digits (`0.577085577939301453` at 50, `-0.00240990227181677983` at 100), and
Gram's law holds at every Gram point from `g_{-1}` to the first one past T.

## 2. The template: rigor.py's two routines, replayed

Both routines carry the reserved word in their names, so `numeric_plan.py` finds them by
role (their exact parameter lists, `ZERO_COUNT_ROLE` and `RH_HEIGHT_ROLE`) and the plans record
the lines they were found at (763, 1110, and 639 for the sign scan). The replay uses the
routine's own primitives (`_pick`, `_segment_delta`, the adapter's `zeta_native`,
`native_arg_right_half`, `rs_theta`) with the routine's stack discipline, and is checked equal
to the routine's report: the same number of sub-segments and the same `N(T)` enclosure,
endpoint for endpoint.

### 2.1 The zero count (line 763)

`N(T) = 1 + theta(T)/pi + S(T)` with `pi S(T)` the argument change of zeta along
`2 -> 2 + iT -> 1/2 + iT`. There is **no bottom height**: the contour starts at `s = 2` on the
real axis, and the `1` carries the real-axis part. The vertical leg is one step,
`arg zeta(2 + iT)`, because `|zeta(2 + iy) - 1| <= zeta(2) - 1 < 1` (re-verified in Arb). The
horizontal leg at height T is bisected until each piece passes two tests: the Arb box of
zeta over the whole piece misses 0 (so zeta has no zero there and the argument moves by less
than pi), and `Re(zeta(xb)/zeta(xa)) > 0` (so the argument change is exactly `Arg` of the
quotient). At 192 bits, the routine's default:

T = 50: vertical step `arg zeta(2 + 50i) = 0.161315576988`, `theta(50) = 26.4613660702`,
`S(50) = 0.577085577939`, `N(50)` in `[9.99999999999999999, 10.0000000000000001]` (the stored
decimal ends; the ball itself is `1.3e-56` from 10). Twelve sub-segments:

| sub-segment (sigma) | min abs zeta on the box | min Re of the quotient | argument change |
|---|---|---|---|
| `2 -> 5/4` | 0.2535 | 0.7697 | 0.232400 |
| `5/4 -> 17/16` | 0.2697 | 0.8811 | 0.120805 |
| `17/16 -> 31/32` | 0.2899 | 0.9212 | 0.084166 |
| `31/32 -> 7/8` | 0.1692 | 0.9041 | 0.110791 |
| `7/8 -> 25/32` | 0.02032 | 0.8843 | 0.152800 |
| `25/32 -> 47/64` | 0.1567 | 0.9371 | 0.099624 |
| `47/64 -> 11/16` | 0.1223 | 0.9355 | 0.120444 |
| `11/16 -> 41/64` | 0.09694 | 0.9381 | 0.145431 |
| `41/64 -> 19/32` | 0.0657 | 0.9481 | 0.172906 |
| `19/32 -> 35/64` | 0.02759 | 0.9694 | 0.198237 |
| `35/64 -> 67/128` | 0.1639 | 1.003 | 0.105942 |
| `67/128 -> 1/2` | 0.1512 | 1.013 | 0.108106 |

T = 100: vertical step `-0.0452259806106`, `theta(100) = 87.9721652318`,
`S(100) = -0.00240990227182`, `N(100)` in `[28.9999999999999999, 29.0000000000000001]`. Four
sub-segments, `2 -> 5/4 -> 7/8 -> 11/16 -> 1/2`, with min abs zeta on the boxes
`0.6084, 0.4529, 0.7996, 0.3672` and argument changes `-0.004198, 0.014176, 0.012670, 0.015007`.

**Why T avoids zeros.** The first test passes on every sub-segment, so zeta has no zero on
`[1/2, 2] x {T}`; `Re s >= 1` is zero-free, and the nontrivial zeros are symmetric under
`s -> 1 - conj s`, so T is the ordinate of no nontrivial zero. The worst margins are the
box at `7/8 -> 25/32` (0.0203 at 50: a wide box whose corner comes near 0, though zeta itself
stays above 0.29 there by section 4.4) and `11/16 -> 1/2` (0.367 at 100).

**Minimal precision.** The routine determines the count from **7 bits** at T = 50 (enclosure
width 1.37, one integer inside) and **8 bits** at T = 100 (width 1.28); one bit less leaves an
enclosure 2.73 wide (T = 50) and 3.21 wide (T = 100), holding several integers. Observed, not
explained: the number of sub-segments *grows* with precision at T = 50 (5 from 7 to 48 bits, 7
at 64, 9 at 96 and 128, 12 at 192), because Arb's box of zeta over a long sigma-interval comes
back wider at high precision. The plans record the scan in `rigor_template.precision_scan`.

### 2.2 RH to height T (line 1110)

The routine scans Hardy Z on the grid `t_k = T k/(n - 1)` with `n = 332` at T = 50 and
`n = 882` at T = 100, at 64 bits with up to 8 doublings, and compares the proven sign changes
with the zero count: 10 of 10 and 29 of 29, no undecided sample, so every zero below T is
simple and on the line, modulo the ball library. The replay finds the same brackets; each
holds exactly one mpmath ordinate, the k-th. The smallest `|Z|` on the grid is `0.00628`
(T = 50) and `0.00544` (T = 100), and every sample's sign is decided without escalation from
16 bits at T = 50 and 18 at T = 100.

The Lean route replaces the grid by hunts #132/#133's two-decimal brackets. The plans list
one per zero, with Arb enclosures of Z at both ends, all with proven sign changes. The first
ten are exactly the brackets hunts #132 and #133 kernel-checked. **For T = 100 nineteen more
are needed**, starting `(52.97, 52.98)` and ending `(98.83, 98.84)`
(`plan_T100.json`, `rh_template.hardy_brackets[10:]`).

## 3. The plan of record: the skeleton's contour, hardened

The skeleton counts between `T1 = 3` and `T2 = 52` (for T = 50; any `T2` in `[50, 52.970)`
holds the same ten zeros) and sketches `(3, 99.85)` for T = 100. On those four legs
`Re zeta > 0` throughout, so every sub-segment has direction `+1`, `Q = 0`, and the zeta half of
the count is `arg zeta(1/2 + iT2) - arg zeta(1/2 + iT1)` (the identity of section 4.2 with no
junctions; `ExactArgument` in the skeleton). The Gamma half uses the vendored
`digamma_stirling` directly, keeping `log|w|` and `Re 1/(2w)` exactly, with budget
`(6/pi)(1/T1 - 1/T2)`; the low region `0 < Im rho <= 3` is the skeleton's analytic `LowHeight`.
This plan recomputes all of it (`skeleton_contour` in both files):

| | `(3, 52)` | `(3, 99.85)` |
|---|---|---|
| `int mu = (theta(T2) - theta(T1))/pi` (Arb) | 10.0426130 | 28.8895632 |
| digamma-route main term `F(T2) - F(T1)` | 10.0261883 | 28.8726496 |
| its true remainder, and the route's budget | 0.016425, **0.59989** | 0.016914, **0.61749** |
| `A1 = arg zeta(1/2 + 3i)` | -0.1470280 | -0.1470280 |
| `A2 = arg zeta(1/2 + iT2)` | -0.2809006 | 0.1999195 |
| count, exact Arb values | 10 | 29 |
| count under the route budget and Lean boxes | `[9.3718, 10.5947]`, margin **0.3718** | `[28.3535, 29.6124]`, margin **0.3535** |
| the same with the arctan-free argument bound | margin 0.3202 | margin 0.2552 |
| sub-segments generated here (direction `+1`, 3/2 on both error terms) | bottom 3, top 7 | bottom 3, top 8 |
| worst Lean margin, worst Arb true margin | 0.00849, 0.486 | 0.0707, 0.486 |
| prime exp towers, projected kernel time | 41, 125 s | 71, 217 s |

The generated partitions: bottom leg at 3, `[1/2, 7/8]`, `[7/8, 5/4]`, `[5/4, 2]`, all `N = 2`;
top leg at 52, breakpoints `1/2, 19/32, 11/16, 7/8, 17/16, 5/4, 13/8, 2` with
`N = 12, 11, 12, 11, 9, 9, 8`; top leg at 99.85, breakpoints
`1/2, 19/32, 11/16, 25/32, 7/8, 17/16, 5/4, 13/8, 2` with `N = 23, 21, 19, 18, 19, 16, 16, 12`.
The Arb lower bound of `Re zeta` is `0.486` on the bottom leg, `1.039` at 52, `1.191` at 99.85,
and `0.668` on the right side.

**What the skeleton states, checked.** `GammaIncrement` (`9.2 <= int_3^52 mu <= 10.9`) holds,
and the digamma route's own interval `[9.4263, 10.6261]` fits inside it with `0.2263` to spare.
`HorizontalLegs`' argument bounds hold: `A1` is in `[-1/5, 0]` and `A2` in `[-1/3, 0]`. The count
from the stated rational bounds alone is `[9.0939, 10.9637]`, so `Ncount 3 52 = 10`.

**Three corrections**, each pinned by a test:

1. **The `A2` box needs `N = 24`, not 23.** PLAN.md sizes the box at `1/2 + 52i` around zeta's
   value. The Lean box is centred at the main term `M_23`, and there the arctan-free interval
   reaches `-0.3353`, outside `[-1/3, 0]` (centred at zeta it is `-0.33324`, inside by `9e-5`).
   `N = 24` fits (`-0.3264`), and `N = 26` with the 3/2 factor on the radius. `N = 3` at
   `1/2 + 3i` is confirmed.
2. **The stated partitions close on the bare bounds, not with the factor on both terms.**
   Recomputed with PLAN.md's own rule (expand from each segment's left end), every segment
   closes on the bare bounds (smallest margins `0.082` on the bottom leg, `0.417` on the top)
   and with 3/2 on the remainder radius only (`0.0357`, `0.268`), which is hunt #133's
   convention. With 3/2 also on the variation term, this plan's convention, five segments go
   negative: `[1/2, 15/16]` and `[15/16, 25/16]` at 3, and `[9/16, 21/32]`, `[7/8, 33/32]` and
   `[33/32, 5/4]` at 52. The mathematics is sound either way; the partitions above close under
   the stricter convention at the same cost (`N = 2` on the bottom leg).
3. **The stated count leaves `0.036` at the top.** `10.9 + (1/5)/pi = 10.9637`. The route
   itself reaches `10.6261`; stating the Gamma upper bound nearer that would widen the margin
   at no cost.

For T = 100 the skeleton states heights only. The record above supplies the rest: the
partition at 99.85, `A2` with `N = 55` at the 1/50 tolerance of section 4.6, and the count
with margin 0.3535. The nineteen located zeros of section 2.2 remain the missing input.

## 4. An independent contour from T1 = 10

### 4.1 The identity, and why there is a bottom height

The vendored `zeta23` fold `Zeta23.RvM.N_eq_halfContour_completedZeta` needs good heights
`1 <= T1 < T2` and the right half-contour `1/2 + iT1 -> 2 + iT1 -> 2 + iT2 -> 1/2 + iT2`. With
`halfContour_completedZeta_split` and `gamma_side` it reads

    Ncount T1 T2 = int_{T1}^{T2} mu + (1/pi) Im halfContour (logDeriv riemannZeta) T1 T2,

`Ncount T1 T2` counting nontrivial zeros of Mathlib's `riemannZeta` with `T1 < Im rho <= T2`,
with multiplicity. rigor.py's contour starts on the real axis instead, so a Lean contour
needs a bottom height. This section takes **T1 = 10** and the top heights 50 and 100, with the
vendored `mu_stirling` as stated (section 6 says why 10 for that route).

### 4.2 The exact-argument lemma, and the quarter turns

Cut each horizontal leg into sub-segments, and give each sub-segment an axis direction
`c = i^e` in `{+1, +i, -1, -i}` such that `Re(zeta(s) conj c) > 0` on the **closed**
sub-segment. That condition is a plain sign condition: `Re zeta > 0`, `Im zeta > 0`,
`Re zeta < 0` or `Im zeta < 0`.

*On one sub-segment.* `sigma -> log(zeta(sigma + iT) conj c)` (principal branch) is
differentiable there with derivative `zeta'/zeta(sigma + iT)`, since `zeta(sigma + iT) conj c`
stays in the right half-plane where `Complex.log` is differentiable. This is the pattern of the
vendored `Zeta23.RvM.hasDerivAt_log_riemannZeta_two`, with `conj c` in front. So

    Im int_a^b zeta'/zeta(sigma + iT) dsigma = Arg(zeta(b + iT) conj c) - Arg(zeta(a + iT) conj c).

*At a junction.* If `z` has `Re(z conj c) > 0` and `Re(z conj c') > 0` with `c' = c i^d`, then
`d` is in `{-1, 0, 1}` (opposite directions share no half-plane) and
`Arg(z conj c) = Arg(z conj c') + d pi/2` exactly: the two sides are congruent mod `2 pi` and
both lie in an interval shorter than `2 pi`. The right side `sigma = 2` has direction `+1`
throughout (`re_riemannZeta_two_pos`), and the corners are junctions like any other.

*Along the whole chain* (bottom leg left to right, right side up, top leg right to left)
everything but the two critical-line ends telescopes:

    Im halfContour (logDeriv riemannZeta) T1 T2 = A2 - A1 + (pi/2) Q,
    A1 = Arg(zeta(1/2 + iT1) conj c_first),   A2 = Arg(zeta(1/2 + iT2) conj c_last),

with `Q` the signed number of quarter turns. Hence

    Ncount T1 T2 = (theta(T2) - theta(T1))/pi + Q/2 + (A2 - A1)/pi.

With every direction `+1` this is the skeleton's `ExactArgument`. `numeric_plan.leg_arg_change`
adds the per-sub-segment changes directly and agrees with rigor.py's replayed top leg to 18
digits at both heights (`cross_check_with_rigor`).

### 4.3 What closes one sub-segment

Let `p` be the midpoint, `rho` the half-length, `c` the direction, and `M_N` the order-4
Euler-Maclaurin main term that hunt #132's kernel-checked `zeta_em4_error` subtracts,

    M_N(s) = sum_{n<N} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + s N^{-s-1}/12,
    |zeta(s) - M_N(s)| <= |s(s+1)(s+2)(s+3)| (N-1)^{-sigma-3} / (720 (sigma+3))   (Re s > 0, Im s > 0, N >= 2).

For every sigma in `[a, b]`, with Taylor order `k` about `p`,

    Re(zeta(sigma + iT) conj c) >= m - sum_{1<=j<k} rho^j |d_j|/j! - rho^k L_k/k! - R,

where `m` and `d_j` are box values of `Re(M_N^(j)(p + iT) conj c)` at one point, `R` bounds the
order-4 radius on the sub-segment (`|P4(b + iT)| (N-1)^{-a-3}/(720 (a+3))`: the product grows
with sigma, the rest shrinks), and `L_k` is the triangle-inequality bound on `|M_N^(k)|`,

    L_k = sum_{2<=n<N} (log n)^k n^{-a} + N^{1-a} sum_i C(k,i) (log N)^{k-i} i!/T^{1+i}
          + (log N)^k N^{-a}/2 + (|b + iT| (log N)^k + k (log N)^{k-1}) N^{-a-1}/12.

`k = 1` is the mean value inequality. A sub-segment is accepted when this stays positive with
`R` and the Taylor tail multiplied by **3/2** and a box allowance of `1e-5` subtracted; the
recorded `lean_margin` is that number and `safety_achieved` the factor the errors could
actually grow by. The generator bisects `[1/2, 2]` dyadically and takes, per sub-segment, the
smallest `N` that closes it. Each sub-segment's `true_margin` is separate evidence: an Arb
lower bound of `min Re(zeta conj c)` over the sub-segment from boxes no longer than `1/128`,
checked against mpmath: the bound lies below every sample, and within 12.5% of the sampled
minimum (measured with 33 samples per sub-segment, worst at T = 50 near sigma = 1/2; the test
asks for 20% with 17 samples).

### 4.4 T = 50, Taylor order 1 (recommended)

Bottom leg at `T1 = 10`: two sub-segments, `[1/2, 5/4]` and `[5/4, 2]`, both `+1`, `N = 3`, Lean
margins `0.1405` and `0.589`. Right side: one segment, `+1`. Top leg at 50, in increasing
sigma (the path runs the other way):

| sub-segment (sigma) | dir | N | main term m | Taylor tail | order-4 radius | Lean margin | safety | true margin |
|---|---|---|---|---|---|---|---|---|
| `[1/2, 131/256]` | `+i` | 17 | 0.3406 | 0.06561 | 0.152 | 0.01418 | 1.565 | 0.2976 |
| `[131/256, 67/128]` | `+i` | 17 | 0.3406 | 0.064 | 0.1467 | 0.0246 | 1.617 | 0.299 |
| `[67/128, 35/64]` | `+i` | 21 | 0.3314 | 0.1545 | 0.06447 | 0.002974 | 1.514 | 0.2899 |
| `[35/64, 73/128]` | `+i` | 19 | 0.337 | 0.1328 | 0.08676 | 0.007731 | 1.535 | 0.2926 |
| `[73/128, 19/32]` | `+i` | 19 | 0.3362 | 0.1261 | 0.08055 | 0.02618 | 1.627 | 0.2947 |
| `[19/32, 79/128]` | `+i` | 17 | 0.3374 | 0.1076 | 0.1142 | 0.004591 | 1.521 | 0.2962 |
| `[79/128, 41/64]` | `+i` | 17 | 0.3357 | 0.1025 | 0.1063 | 0.02246 | 1.608 | 0.2973 |
| `[41/64, 85/128]` | `+i` | 17 | 0.3337 | 0.09759 | 0.09901 | 0.03883 | 1.698 | 0.2978 |
| `[85/128, 11/16]` | `+i` | 16 | 0.3184 | 0.08788 | 0.1168 | 0.0114 | 1.556 | 0.2978 |
| `[11/16, 91/128]` | `+i` | 15 | 0.3328 | 0.07897 | 0.1405 | 0.003628 | 1.517 | 0.2973 |
| `[91/128, 47/64]` | `+i` | 15 | 0.3299 | 0.07541 | 0.1312 | 0.01996 | 1.597 | 0.2965 |
| `[47/64, 97/128]` | `+i` | 15 | 0.3268 | 0.07202 | 0.1226 | 0.03492 | 1.679 | 0.2953 |
| `[97/128, 25/32]` | `+i` | 15 | 0.3236 | 0.0688 | 0.1145 | 0.0486 | 1.765 | 0.2938 |
| `[25/32, 53/64]` | `+i` | 18 | 0.308 | 0.1533 | 0.05136 | **0.001002** | 1.505 | 0.2901 |
| `[53/64, 7/8]` | `+1` | 15 | 0.3354 | 0.1201 | 0.09342 | 0.01519 | 1.571 | 0.2952 |
| `[7/8, 59/64]` | `+1` | 14 | 0.3678 | 0.1038 | 0.1087 | 0.04905 | 1.731 | 0.3364 |
| `[59/64, 31/32]` | `+1` | 12 | 0.4187 | 0.08419 | 0.1834 | 0.01727 | 1.565 | 0.3742 |
| `[31/32, 17/16]` | `+1` | 13 | 0.4482 | 0.1651 | 0.1147 | 0.0285 | 1.602 | 0.4089 |
| `[17/16, 37/32]` | `+1` | 11 | 0.4923 | 0.1239 | 0.1863 | 0.02699 | 1.587 | 0.4703 |
| `[37/32, 5/4]` | `+1` | 10 | 0.5381 | 0.09942 | 0.2274 | 0.0478 | 1.646 | 0.5225 |
| `[5/4, 23/16]` | `+1` | 10 | 0.6004 | 0.1718 | 0.1812 | 0.07099 | 1.701 | 0.5673 |
| `[23/16, 13/8]` | `+1` | 8 | 0.7155 | 0.1134 | 0.3508 | 0.01909 | 1.541 | 0.6395 |
| `[13/8, 2]` | `+1` | 8 | 0.7636 | 0.1756 | 0.2342 | 0.1489 | 1.863 | 0.6947 |

One junction, at `53/64 + 50i`, from `+1` to `+i`: **Q = 1**. The top leg's argument change
is `1.65165223516`. The worst Lean margin, `0.001002` at `[25/32, 53/64]`, still leaves the
error terms room to grow by `1.505`; the worst true margin is `0.2899`. At 50 the leg needs a
quarter turn because `zeta(1/2 + 50i) = -0.0817 + 0.3308i` is in the second quadrant; that is
why the skeleton moved its top to 52, where the leg stays in `Re zeta > 0`.

### 4.5 T = 100, Taylor order 1

The same bottom leg and a right side from 10 to 100. Top leg, all `+1`, **Q = 0**:

| sub-segment (sigma) | dir | N | main term m | Taylor tail | order-4 radius | Lean margin | safety | true margin |
|---|---|---|---|---|---|---|---|---|
| `[1/2, 19/32]` | `+1` | 22 | 2.481 | 0.6822 | 0.9361 | 0.05379 | 1.533 | 2.328 |
| `[19/32, 11/16]` | `+1` | 20 | 2.313 | 0.5032 | 0.982 | 0.08503 | 1.557 | 2.096 |
| `[11/16, 7/8]` | `+1` | 26 | 1.95 | 1.02 | 0.264 | **0.02423** | 1.519 | 1.766 |
| `[7/8, 17/16]` | `+1` | 19 | 1.684 | 0.5276 | 0.4908 | 0.1562 | 1.653 | 1.555 |
| `[17/16, 5/4]` | `+1` | 16 | 1.426 | 0.3238 | 0.5712 | 0.08313 | 1.593 | 1.419 |
| `[5/4, 13/8]` | `+1` | 16 | 1.305 | 0.4581 | 0.3287 | 0.1243 | 1.658 | 1.266 |
| `[13/8, 2]` | `+1` | 12 | 1.195 | 0.2149 | 0.4595 | 0.1833 | 1.772 | 1.189 |

The top leg's argument change is `0.0376550493376`. On the right side the vendored bound
`Re zeta(2 + it) >= 2 - pi^2/6 = 0.3551` is what Lean uses; Arb bounds the true minimum on
`[10, 50]` and `[10, 100]` below by `0.6681`.

### 4.6 Taylor orders compared, and the critical-line ends

| T | order k | sub-segments (bottom / top) | term boxes | prime exp towers | worst Lean margin | projected kernel time |
|---|---|---|---|---|---|---|
| 50 | 1 | 2 / 23 | 369 | 150 | 0.001002 | 459 s |
| 50 | 2 | 1 / 4 | 108 | 43 | 0.003201 | 132 s |
| 50 | 3 | 1 / 3 | 87 | 34 | 0.01280 | 104 s |
| 100 | 1 | 2 / 7 | 187 | 70 | 0.02423 | 214 s |
| 100 | 2 | 1 / 4 | 131 | 49 | 0.06162 | 150 s |
| 100 | 3 | 1 / 3 | 111 | 40 | 0.04875 | 122 s |

Term boxes and towers include the two endpoint evaluations below. The projection is towers
times hunt #133's measured 52 s per 17 towers, so it is a *measured* rate times a count, not a
measurement; for `k > 1` the derivative boxes add products it does not count. **Order 1 is
recommended**: its only analytic lemma beyond what exists is the mean value inequality for a
finite sum, and at about eight kernel minutes for T = 50 the saving from orders 2 or 3 (a
Taylor lemma and derivative boxes) is minutes, the same judgement hunt #133 made about
Euler-Maclaurin orders 6 and 8. The skeleton's contour (section 3) is cheaper still, 41 and 71
towers, because its legs never turn.

| | point | direction | A (Arb) | Lean N | Lean half-width | arctan-free interval |
|---|---|---|---|---|---|---|
| A1 | `1/2 + 10i` | `+1` | -0.0745182573 | 6 | 0.0152 | `[-0.0930, 0]` |
| A2, T = 50 | `1/2 + 50i` | `+i` | 0.2421714854 | 45 | 0.0194 | `[0, 0.2733]` |
| A2, T = 100 | `1/2 + 100i` | `+1` | -0.0075709313 | 55 | 0.0191 | `[-0.0274, 0.0117]` |

The Lean box is `M_N(1/2 + iT)` inflated by 3/2 times the order-4 radius plus the allowance;
a disc of radius `r` around `w0` moves the argument by at most `arcsin(r/|w0|)`, and `N` is the
smallest truncation keeping that under `1/50`. The arctan-free interval uses only the sign of
arctan and `|arctan x| <= |x|` on the box: `[min(0, x_lo), max(0, x_hi)]` with `x = Im/Re`.

## 5. The Gamma side and the count from T1 = 10

`int_{T1}^{T2} mu = (theta(T2) - theta(T1))/pi` exactly (`gamma_side`, with `mu = theta'/pi`).
Arb: `theta(10) = -3.0670743963`, `theta(50) = 26.4613660702`, `theta(100) = 87.9721652318`, so
the increment over pi is `9.3991945241` (to 50) and `28.9786900043` (to 100). This contour
integrates the vendored `Zeta23.StirlingVert.mu_stirling`,
`|mu(tau) - (1/(2 pi)) log(tau/(2 pi))| <= (20/(2 pi))/tau^2` for `tau >= 1` (the constant is in
its proof; the statement says only that one exists, so a Lean proof needs a restatement that
exposes it). The main term is `G(T2) - G(T1)`, `G(t) = (t log(t/(2 pi)) - t)/(2 pi)`:
`9.3997254255` and `28.9792872230`, true remainders `-0.000531` and `-0.000597`, budgets
`(20/(2 pi))(1/T1 - 1/T2)` = **0.2546** and **0.2865**.

| | T = 50 | T = 100 |
|---|---|---|
| count, exact Arb values | `[9.99999999999999999, 10.0000000000000001]` | `[28.9999999999999999, 29.0000000000000001]` |
| count, Lean budget (Stirling budget, arcsin half-widths) | `[9.7356, 10.2669]` | `[28.7037, 29.2985]` |
| margin to the other integers | **0.7331** | **0.7015** |
| count, arctan-free variant | `[9.6451, 10.2709]` | `[28.6841, 29.2991]` |
| its margin | 0.6451 | 0.6841 |

The Stirling constant could be about 3.9 times worse at T = 50 and 3.4 times worse at T = 100
before the count stopped being pinned (margin plus budget over budget: `0.9877/0.2546` and
`0.9880/0.2865`). A test pins the edge: with the numerator 20 replaced by 77 the T = 50 count
is still pinned and by 78 it is not; at T = 100 the edge is between 68 and 69. An error `e` in a
Lean bound for `log(2 pi)` moves the main term by `(T2 - T1) e/(2 pi)`, that is `6.4 e` and
`14.3 e`, so four correct digits leave the margin intact.

## 6. The bottom height

`T1` must satisfy `1 <= T1`, be a good height, sit below the first ordinate `14.1347`, and leave
a low region `(0, T1]` that a low-height exclusion can cover. Under the `mu_stirling` route
of section 5, with order 1:

| T1 | Stirling budget (to 50) | margin (to 50) | margin (to 100) | bottom sub-segments | true margin on the bottom leg |
|---|---|---|---|---|---|
| 2 | 1.528 | does not close | does not close | 3 | 0.3858 |
| 4 | 0.7321 | 0.2567 | 0.2251 | 3 | 0.5627 |
| 6 | 0.4669 | 0.5231 | 0.4915 | 2 | 0.7895 |
| 8 | 0.3342 | 0.6529 | 0.6214 | 2 | 1.117 |
| **10** | 0.2546 | **0.7331** | **0.7015** | 2 | 1.197 |
| 12 | 0.2016 | 0.7856 | 0.7540 | 3 | 0.9551 |
| 14 | 0.1637 | 0.8232 | 0.7917 | 20 | 0.05638 |

Under that route `T1 = 10` takes most of the margin while keeping the bottom leg easy:
`|zeta(1/2 + 10i)| = 1.549`, close to the largest `|Z|` below the first zero (a float scan
during planning, not pinned), the whole leg stays in `Re zeta > 0`, and the leg costs two
sub-segments with `N = 3`. Below it, three routes agree that there is nothing: rigor.py's count
at 10 is 0 (its contour runs along the real axis, so this is an enclosure-carrying statement
that no zero has `0 < Im s < 10`), Arb's Turing count is 0 and mpmath's `nzeros` is 0. The cost
of 10 is the low region: PLAN.md reports (measured, section 4.4) that the analytic `N = 1`
exclusion it uses below 3 stops working near `Im rho = 3.4`, so a bottom height of 10 needs a
two-dimensional covering or a second count. The digamma route's budget, `6/pi` instead of
`10/pi`, is what lets the skeleton afford `T1 = 3` (section 3).

## 7. What the Lean proof needs, piece by piece

The skeleton's four pieces, with what this plan supplies for each at its heights:

1. **`GammaIncrement`.** `int_3^52 mu` in `[9.2, 10.9]`; the route interval `[9.4263, 10.6261]`
   needs bounds on `pi`, `log pi` and the logarithms of two rationals; `0.2263` to spare.
   (From 10: `int mu` within `0.2546` or `0.2865` of `G(T) - G(10)`, through `mu_stirling` with
   its constant exposed.)
2. **`HorizontalLegs`.** Per sub-segment of section 3: one order-4 main-term box (hunt #133's
   term boxes, exp towers for primes and products for composites), the order-4 radius from
   `zeta_em4_error`, a rational upper bound for `L_1`, and the mean value inequality for `M_N`
   along the segment; and the two argument boxes, `N = 3` at `1/2 + 3i` and **`N = 24`** at
   `1/2 + 52i`.
3. **`ExactArgument`.** Section 4.2 with every direction `+1`: the log primitive on each leg,
   `hasDerivAt_log_riemannZeta_two` on the right side. No numerics.
4. **`LowHeight`.** Below 3, analytic (PLAN.md section 4.4); not planned here. From 10 it
   would need its own covering (section 6).

And, for T = 100 only, the nineteen extra located zeros of section 2.2.

The JSON carries everything a generator needs, exactly: for every sub-segment its endpoints
and midpoint as rationals, its direction `e`, its truncation `N`, and the bounds above; for
each contour `T1`, `T2`, `Q`, the junctions, `A1`, `A2`, the Gamma side and its route.

## 8. Controls and planted faults

`numeric_plan.verify_contour` recomputes a contour from its stated heights, partitions,
directions and truncations: tiling of each leg, each Lean margin, each true margin (fresh Arb
boxes), the junctions and `Q`, the endpoint arguments and the Gamma side (which must agree with
the stored enclosures), and the count under the exact values, the Lean budget of its route and
the arctan-free variant; `verify_plan` adds the plan-level heights. `verify_template` re-adds
rigor.py's replayed argument changes. Both plans verify at all three orders, and both skeleton
contours verify. Each fault below is a permanent test, and each turns red:

- **a top height moved onto a zero**: 49.77383, within `3e-6` of the tenth ordinate, in the
  T1 = 10 plan, and 52.97032, within `2e-6` of the eleventh, in the skeleton contour; each
  stored top leg fails at its first sub-segment from `1/2`;
- **a top height moved past a zero**: a contour regenerated at 53.5 counts 11, and the only
  failure is `count 11 is not the mission's 10`;
- **a stale plan**: the heights edited to 50.01 with nothing recomputed; the stored `A2` and
  Gamma increment are refused;
- **a dropped sub-segment**, on either leg: the tiling check reports the gap;
- **a dropped template segment**, each of the 12 (T = 50) and 4 (T = 100) in turn: the
  enclosure, about `3e-17` wide once rebuilt from the stored digits, holds no integer;
- **a lost quarter turn**: `Q` stated as 0 is refused; every top-leg direction set to `+1`
  fails at least ten sub-segments (`Re zeta(1/2 + 50i) < 0`);
- **no room beyond the safety factor**: with the error terms times 2, the order-1 plan at
  T = 50 fails;
- **a Stirling constant four times worse**: the Lean budget no longer pins either count;
- **a wrong main term**: the Bernoulli term with the wrong sign, or `N^{-s}/2` dropped, leaves
  the order-4 radius at `N = 60` at no fewer than 20 of the 25 midpoints of the T = 50 plan,
  while the correct main term stays inside it at the stored `N` and at 60 at every midpoint of
  both plans;
- **lexical**: no file of this plan carries the reserved word or an em dash, and the JSON
  writer refuses output that would.

The slow test rebuilds both plans from nothing and requires byte-for-byte agreement.

## 9. What binds, and what was chosen

**Active constraints.** On the skeleton's contour the count is bound by the Gamma route's
budget (`0.5999` of the available `1.0`, against a true remainder of `0.0164`) and, as stated
in the skeleton, by its rational Gamma upper bound (`0.036` left). The binding sub-segment of
the generated skeleton partition is `[17/16, 5/4]` at 52 (`N = 9`, Lean margin `0.0085`, errors
may grow by `1.511`). In the T1 = 10 plan it is `[25/32, 53/64]` at 50 (`N = 18`, Lean margin
`0.001`, `1.505`); the greedy rule "smallest N that closes" puts every sub-segment near the
edge by design.

**Chosen, not optimized**, with what relaxing each would trade:

- the bottom height (3 in the skeleton, 10 here): higher buys Stirling budget and costs
  low-region area (section 6);
- the safety factor 3/2, applied to both error terms here and to the radius only in PLAN.md:
  lower means fewer sub-segments and less protection against a Lean box wider than Arb's;
- the box allowance `1e-5`: far above hunt #133's box widths, near `1e-8` per term;
- axis directions only: a general direction would allow longer sub-segments where zeta points
  diagonally, at the price of an enclosed angle at every junction instead of an exact quarter
  turn;
- dyadic bisection and the smallest closing N: a cost optimizer could trade N against length;
- the endpoint tolerance `1/50` rad: the arctan-free variant shows it is not binding;
- Euler-Maclaurin order 4: the only order kernel-checked (hunt #132); order 6 or 8 would cut
  N, as hunt #133 measured, at the price of a new analytic development.

**Information class.** Every door above stays inside the data the contour reads (zeta on the
three legs and Gamma on the line). None needs more.

## 10. Cost

Both plans: 22 s of CPU on the campaign box, 36 s of wall time (2026-10-21; an earlier build
under a load average near 230 from other workflows took 2 min 23 s of wall time for 19.5 s of
CPU). The fast tests: under 10 s of CPU. No Lean was run for this plan; the kernel times in
sections 3 and 4.6 are projections.
