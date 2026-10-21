# Results: which step of the quasi-Riemann argument fixes the number 7/8

**Hunt #139 (opened as #134), 2026-10-16. Status: answered within its stated scope;
unreviewed by any person.** Grades: *cited* (a line of the paper, quoted and checked
against the pinned file), *derived* (algebra done here from cited formulas and checked
in exact rational arithmetic by `test_seven_eighths_pin.py`), *inferred* (a reading of
a lemma's proof that no computation here checks). A composite claim takes the grade of
its weakest step. Nothing here is a statement about RH, and nothing here checks the
paper's lemmas: they are taken as cited inputs, at the exponents the paper proves them
with.

Source: `github.com/openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`, 16,677
lines, sha256 `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`.
Line numbers below refer to that file. `probe.py --paper PATH` checks that each of the
39 cited snippets sits on its stated line (all 39 do).

> **Landing note, 2026-10-21.** Opened as hunt #134 and renumbered #139 at landing,
> because #134 on main is `gauss_positivity` and #136 to #138 are taken by other
> open hunts and landings. The prior-art search this page had not run was run at
> landing and extended the same day to the three works its first source names and to
> the follow-ups' own manuscripts (section 10 lists what was read, with commits). Much
> of this page was public before the hunt opened on 2026-10-16, so it was derived here
> independently and is not novel:
>
> - a model computation by tomoto0 (7 October 2026) has the target formula of Summary
>   item 1 with its ζ_F(6z) pole, the floor-row ceiling 13/15 of Summary item 5 at the
>   same corner, a geometry optimum near 0.87496 with the zero-detected rows binding (the
>   two ends of section 6), and on a grid the worst point and margin of Summary item 4 at
>   the paper's geometry;
> - J. Guo and B. Liu (8 October 2026) give the exact optimum of the re-optimized geometry
>   of Summary item 3 and section 4, σ* = (1507 − 2√921)/1653 ≈ 0.8749570698, and the
>   further gain of section 7's tied capacity; Guo derives the binding bin
>   δ* = (49 − √921)/48 at x = 1/2 from the vanishing coefficient of the offset;
> - the total accounting of section 3, marked inferred below, is a proof step on the line
>   M + ℓ = 1 in Z. Gao's draft (7 October) and in Guo's and Argonaut Math's papers
>   (8 October).
>
> Section 10 also records two consequences checked at landing against this hunt's own
> formulas (the exact bound 0.874942 is valid but loose, and the scan optimum 0.874958 is
> a grid reproduction of σ*), what was not found in the sources read, and one
> disagreement with tomoto0 over the slope α. The rest of this page is as the hunt wrote
> it.

## Summary

1. **The target is set by the direct ("low") bound, and both stages lie on one line.**
   The paper continues 1/L past a hypothetical zero by comparing a smoothed sum with a
   Mellin integral `Z^{C(s)}`. The target is the point where the direct bound on that
   sum equals `C(σ₀)`. Written in the free geometry (ℓ the total prime-slot length,
   M the two averaging lengths together, b their offset), that point is
   `σ₀ = 1 − h/6 + b/12 = 5/6 + (M − 2ℓ)/12` (derived). Part I (no slots, M = 1) gives
   11/12; Part II (ℓ = 1/6, M = 5/6) gives 7/8. On the paper's line M + ℓ = 1 this is
   `σ₀ = 11/12 − ℓ/4`: every unit of slot length lowers the target by a quarter. The
   1/6 in `h/6` is the pole at z = 1/6 of the sextic factor ζ_F(6z), not the slot
   length (cited, lines 5586, 8641).
2. **The paper's geometry is the corner of two direct-bound conditions, and one of them
   alone gives exactly 7/8.** The reflected dual length must not exceed the row length,
   `M + ℓ ≤ 1` (line 8246, used there as an equality). The row-norm lemma has a
   second-branch loss `(1 + 3ℓ' − 2M')/4` (line 8306); asking for no loss in every
   rescaled summand means `M − 2ℓ ≥ 1/2`, hence `σ₀ ≥ 5/6 + 1/24 = 7/8` for every
   choice of ℓ, M and b (derived). The two lines meet at ℓ = 1/6, M = 5/6, which is
   the paper's geometry.
3. **That second condition is stricter than the argument needs, but the high side then
   binds at the same place.** Each rescaled summand also gains `Z^{−d}` (line 8631),
   which absorbs the loss; only the unrescaled summand must be lossless, `M ≥ (1+3ℓ)/2`
   (inferred). Under that accounting the direct bound alone would allow targets down
   to 13/15. The high side does not: the paper's endpoint inequality (Lemma
   "Compensated endpoint certificate", lines 15994 to 16072) fails below the following,
   with the paper's row counts held fixed.
   - **Exact bound, every geometry with M + ℓ ≤ 1 and b ≥ 0:**
     `σ₀ ≥ 5655673/6464057 ≈ 0.874942` (derived; one witness point δ = 223/576, x = 1/2).
   - With the paper's Gram condition `b ≤ 3(M − 2ℓ)/8` added:
     `σ₀ ≥ 44117/50422 ≈ 0.874955` (derived; witness δ = 7/18, x = 1/2).
   - Float optimum of the scan: **0.874958** at b ≈ 0.12, ℓ ≈ 0.166836 (measured).
     The paper's (ℓ, b) = (1/6, 1/8) is within 1.7 × 10⁻⁴ in ℓ and 4.2 × 10⁻⁵ in the
     target of the best its own high side allows.

   So 7/8 is the corner of the direct bound, and the high side's optimum sits
   4.2 × 10⁻⁵ below it. The number is not slack left on the table: re-choosing the
   geometry inside this assembly can gain at most 5.8 × 10⁻⁵.
4. **The binding rows** are those whose twisted L-functions have a zero near real part
   0.69 (δ = 2a − 1 ≈ 0.39) and whose prime-slot polynomials are as large as that zero
   allows (x = q/δ = 1/2). At the paper's point the margin there is exactly
   `−E_* = 7/30672 ≈ 2.3 × 10⁻⁴`, about twice the paper's printed lower bound
   49/440640 (derived). The mechanism: in the high exponent the slot amplitude costs
   `+qℓ` and the constant `C₀ = −1/4 + 5ℓ/4 + b/6` grows with ℓ, while the moment
   lemmas' row-count gain is capped by their capacities and does not grow with ℓ
   (cited formulas, lines 15192 and 15729; the reading that the counts are ℓ-free is
   cited at 15192 and inferred for the lemmas behind it).
5. **Even perfect row counts stop at 13/15.** Rows with no zero beyond the floor are
   counted in full (exponent R = 1), which no lemma can improve, and they need
   `C₀ = 1/2 + ℓ/2 − 3M/4 + b/6 ≤ 0`. Together with `M + ℓ ≤ 1` the smallest target is
   13/15 at ℓ = 1/5, M = 4/5, b = 0, where the unrescaled-summand condition is tight
   too (derived). Scaling the row-count excess `R_* − (1 − δ)` by λ moves the best
   target almost linearly from 0.874958 (λ = 1) to 13/15 (λ = 0) (measured, section 6).
   This floor holds for this assembly's three forms (direct bound, Mellin signal,
   high-exponent shape), not for the method family.
6. **What does not fix 7/8** (section 7): the Euler regions and the contraction of
   H_η (7/8 is plugged in; they hold down to about 2/3); the contour Re z = 17/50
   (it cancels at d = h); the principal margins (contour choices); the 11/12 input
   (it only caps δ ≤ 5/6; the α = 5/6 in the row counts is the sextic amplification
   slope (1 + 5r)/6, not the bootstrap); Lemma plain's κ ≥ 3/4; the slot supply
   (a lower bound only).

## 1. What was read

The final section, "The seven-eighths bound" (lines 15495 to 16466), in full, and the
Part II setup (6807 to 6918), the compensated low estimate (8559 to 8651), the
row-norm lemma's second branch (8196 to 8334), the definition of the stage data (5586)
and the no-slot inverse count (15276 to 15310) directly. Four separate readings, each
writing verbatim formulas with line numbers to a report and checking its own
arithmetic, covered the row counts (14985 to 15495 and the statements of Lemmas
marked, plain and the detector propositions), the shared analytic lemmas (5460 to
6700, including the Part I conclusion), the probe geometry (3313 to 3723, 6807 to 6918,
8061 to 8651) and the Euler regions and moment hypotheses (3723 to 4201, 8651 to 9209,
9209 to 14985 for hypotheses only). Those reports are model readings; every number
this page uses from them is either re-derived in `probe.py` or marked inferred. The
proofs of the moment lemmas (Sections 9 to 12 of Part II, about 5,800 lines) were not
checked.

## 2. The target on the direct-bound side

Cited:

- `C_II(s) = l_x/2 + s − 1 + h/6 = s − 11/16` (line 8641), with `h = 1 − l_x + ℓ` by
  definition (line 5586). Part I: `C_I(s) = s − 2/3` (line 190).
- Direct bound `|I_mod| ≪ Z^{l_x/2 + b/12 + ε} = Z^{3/16 + ε}` (line 8570), and
  `C_II(7/8) = 3/16 = l_x/2 + b/12` (line 8642). Part I: `Z^{1/4}` (line 3717).
- Geometry `b = 1/8, h = 13/16, ℓ = 1/6, l_x = 17/48, l_y = 23/48, M = 5/6, M + ℓ = 1`
  (lines 6860 to 6864).

Derived (exact, `test_target_closed_form`): with `l_x = (M − b)/2`, `l_y = (M + b)/2`,

    σ₀ = 1 − h/6 + b/12 = 5/6 + (M − 2ℓ)/12,

so b cancels, `σ₀ = 11/12 − ℓ/4` on M + ℓ = 1, and the two stages are the points
(ℓ, M) = (0, 1) and (1/6, 5/6) on the same formula.

## 3. The paper's corner

Cited: line 8246, "Since `M'+ℓ'−1=−3d`", shows the reflected dual length `T_d` stays
below the row length; with general parameters the same subtraction leaves an extra
`M + ℓ − 1`, so `M + ℓ ≤ 1` suffices (derived from the cited display). Line 8306 gives
the second-branch energy `M' + (1 + 3ℓ' − 2M' − 2Δ_H + θ_N)/4`, with `M' = M − 2d`
and `ℓ' = ℓ − d` for a summand rescaled by `Z^d` (the paper's own substitution at
M = 5/6, ℓ = 1/6 gives its `(d − 1/6)/4`). The general loss is therefore
`((1 + 3ℓ − 2M + d)/4)₊` for `0 ≤ d ≤ ℓ`.

- **Per summand:** the summand with every slot rescaled (d = ℓ, so ℓ' = 0) falls in
  the lossless first branch (line 8326), but the summands just below it, d = ℓ − ℓ/K
  with the fine slot mesh the paper takes (K large, line 16246), carry
  `(1 + 4ℓ − 2M − ℓ/K)/4`. Zero loss for all of them, as K grows, needs
  `1 + 4ℓ − 2M ≤ 0`, that is `M − 2ℓ ≥ 1/2`, so `σ₀ ≥ 7/8` whatever ℓ, M, b (derived,
  `test_per_summand_reading_forces_seven_eighths`). The paper's (1/6, 5/6) satisfies it
  with equality.
- **In total:** summand d carries `−d + loss(d)/2` in its exponent (`f(d) = −d`,
  line 8631), so only d = 0 must be lossless: `M ≥ (1 + 3ℓ)/2` (inferred that the
  low estimate may be assembled this way; the paper never needs to, since its loss is
  zero; arithmetic in `test_total_accounting_needs_only_the_d0_summand`).

## 4. The high side and its endpoint inequality

Cited: the high exponent `E(d) = a − 7/8 + h(17/50 − 1/6) − a l_y − (1−a)ℓ
− (δ/2 − q)ℓ + d(R + δ/2 − 17/50)` with `C₀ = −1/48` (lines 15729 to 15734); the row
counts `D_x = 3 − 17x/9`, `P_x = (2 − 8x/9)(1 − x)` (line 15192),
`R_* = 1 − δ + (α − δ)δP_x/(2𝒥)` with `𝒥 = (α − δ)D_x + δP_x` (line 16019); the
certificate `−E_* ≥ 49/440640` (line 16000) and its completed-square identity (line
16048); and the requirement `E_actual(h) − Δ ≤ −49/440640 − (51/64)Δ` (line 16101).

The requirement is relative to the hypothetical zero, `Δ = β* − 7/8 > 0`, and the
capacity allowance `hΔ/4` is smaller than Δ, so what the argument needs is `−E_* ≥ 0`
at every (δ, x); the printed 49/440640 is room on top. As Δ → 0 the condition is
necessary for this assembly's bound.

Derived, with M free:

    −E_* = (−1/2 − ℓ/2 + 3M/4 − b/6) + δ(ℓ + b)/2 − ℓxδ − (h/2)·K(δ, x),
    K = (α − δ)δP_x/𝒥,   h = 1 + ℓ − M/2 + b/2.

The offset is bounded below by a hypothesis of the Gram bound, `P_a = Y'²/Q ≥ 1`
(Prop. probe-gram, line 8345), and `P_a = Z^b` up to fixed constants (line 8591), so
`b ≥ 0` (cited). This matters: at the witness below, smaller b helps, so `b < 0`
would weaken the bound; it lies outside the lemma as stated and would change the
direct bound's form (`P_a^{1/12}` no longer below the other Gram terms), which is not
explored here. At fixed (δ, x), both −E_* and σ₀ are affine in (ℓ, M, b). Along a line of constant σ₀
and b, `d(−E_*)/dℓ = 1 + δ(1/2 − x) > 0` (`test_constant_target_slope`), so the best
geometry has `M + ℓ = 1`. There −E_* decreases in ℓ, and each fixed (δ, x) gives an
exact lower bound on σ₀ by a two-variable linear program:

| bound | value | witness | uses |
|---|---|---|---|
| every geometry, M + ℓ ≤ 1, b ≥ 0 | 5655673/6464057 ≈ 0.8749417 | δ = 223/576, x = 1/2 | b-coefficient ≤ 0 there, so no upper limit on b is used |
| adding b ≤ 3(M − 2ℓ)/8 (Gram condition of Prop. probe-gram at d = ℓ) | 44117/50422 ≈ 0.8749554 | δ = 7/18, x = 1/2 | the Gram limit |
| float scan, best over b ∈ {0, 0.01, …, 0.18} | 0.874958 at b ≈ 0.12, ℓ ≈ 0.166836 | grid 1201 × 201 | measured only |

The paper's own point has `min −E_* = 7/30672` at δ = 79/204, x = 1/2 (derived; the
completed square `(4vδ − 79)²` at v = 51 places it there).

## 5. The floor-row ceiling 13/15

Cited: the floor bin `a = 51/100` uses no zero witness, count R = 1, and
`E(h) ≤ C₀ + (3/4)δ₀ = −7/1200` (line 15847). Derived: in general the floor rows give
`E(h) = C₀ + (1 + ℓ − M/2)δ₀` with `C₀ = 1/2 + ℓ/2 − 3M/4 + b/6`, and as the floor
approaches 1/2 the condition becomes `C₀ ≤ 0`. Rows counted in full cannot be counted
better, so this survives any improvement of the moment lemmas. Minimizing
`σ₀ = 5/6 + (M − 2ℓ)/12` subject to `C₀ ≤ 0`, `M + ℓ ≤ 1`, `b ≥ 0` gives the infimum
13/15 at ℓ = 1/5, M = 4/5, b = 0, where `C₀`, the dual-length slack and the
unrescaled-summand slack are all zero (`test_floor_corner_is_thirteen_fifteenths`,
`test_no_geometry_beats_the_floor_corner`).

## 6. How much better row counts would buy

Scaling the excess `R_* − (1 − δ)` by λ and re-optimizing (ℓ, b) on M + ℓ = 1 (still
optimal for every λ, since the constant-target slope does not involve K), float scan:

| λ | best ℓ | best b | target |
|---|---|---|---|
| 1 (the paper's counts) | 0.166836 | 0.12 | 0.874958 |
| 0.75 | 0.175245 | 0.10 | 0.872856 |
| 0.5 | 0.183600 | 0.07 | 0.870767 |
| 0.25 | 0.191864 | 0.04 | 0.868701 |
| 0 (ideal count 1 − δ) | 0.200000 | 0 | 0.866667 = 13/15 |

The curve is close to linear, about 0.0021 per quarter of the excess removed (measured).

## 7. What does not fix 7/8

- **Euler regions and the contraction of H_η.** `sup_{Re s > 7/8} |H_η − 1| ≤ 1/2`,
  the second Euler region `x_r ≥ 7/8` (line 4056) and `B_p = −1 + O(Q^{−7/8})`
  (line 9074) all plug in the target. The local sextic term `Q^{3 − 6s}` at z = 1/6
  keeps the products under control for targets above about 2/3 (inferred, from the
  fourth reading). The four shared lemmas headed "σ₀ ∈ [7/8, 1)" (lines 5811, 6024,
  6178, 6345) use only those regions (inferred).
- **The contour Re z = 17/50.** Its coefficient in E(d) is `h − d`, so it cancels at
  d = h where the endpoint inequality lives (derived).
- **The principal margins** `m_w = l_y/20`, `m_z = h/600` (lines 15674, 15675) are
  contour placements at the edge of the second Euler region and never bind.
- **The 11/12 input.** It caps bins at `δ ≤ 5/6` and gives `Δ ≤ 1/24` (line 6817).
  The α = 5/6 inside `R_*` is defined at line 15101 and is the sextic amplification
  slope `e(r) = (1 + 5r)/6 = 1 − α + αr` (line 15300), equal to `2·(11/12) − 1` by
  coincidence. Feeding the 7/8 output back would only cap δ ≤ 3/4; the binding point
  is δ ≈ 0.39. An earlier scratch scan in this session that also lowered α was wrong
  for that reason and is not used.
- **Lemma plain's κ ∈ [3/4, 1]** (line 12532). Its baseline capacity `1/(6κ₀)` with
  `κ₀ = 2σ₀ − 1` is where every ninth in D_x, P_x comes from. Tying it to the target
  (`c = 1/(3(2σ₀ − 1))`) changes the optimum by less than 10⁻⁶ (measured). The one
  numerical use of κ ≥ 3/4 in its proof survives down to targets of 3/4 (inferred).
- **The slot supply** `ℓ/d ≥ 8/39 > 7/37` (line 16116) is a lower bound on ℓ.

## 8. Controls

- **Reproduction:** 38 constants the paper prints are rebuilt from the general
  formulas at the paper's values, all exactly (`test_every_printed_constant_is_reproduced`),
  among them 11/16, 3/16, 7/8, 11/12, 2/3, 1/4, −1/48, −7/1200, −529/2400, 25/96,
  −49/14400, −79/800, 23/960, 13/9600, 53/32, 51/64, 8/39, 23/1443, 1/48, 2/185, and
  the certificate's completed-square identity on 101 points.
- **Two forms of every central formula** (transcribed and closed) agree on exact grids.
- **Planted faults:** changing the contour 17/50, the slope α or the capacity
  coefficient 4/9 breaks at least one reproduction (`test_planted_fault_is_caught`).
- **Citations:** 39 of 39 snippets on their stated line of the pinned file.
- **Cross-reading:** the four readings and this page agree on every shared number
  (C₀, the worst point 79/204, 7/30672, the role of α); the one disagreement found
  (whether M + ℓ = 1 is required) was resolved in favour of `≤` by reading line 8246.

## 9. Limitations and kill conditions

- The lemmas are inputs. If Lemma marked, Lemma plain or the detector propositions
  are wrong, everything here is about a different argument. Nobody here has checked
  them, and no person has checked the paper (`docs/38`).
- The general-parameter forms are readings of proofs written at fixed numbers. The
  ones that only substitute (the target, C₀, −E_*) are checked by reproduction; the
  ones that change which inequality is used (`M + ℓ ≤ 1` suffices, only d = 0 must be
  lossless, the Euler regions hold below 7/8) are inferred.
- The exact bound 0.874942 is a statement about the endpoint inequality with the
  paper's row counts. It does not say no other assembly of the same lemmas does
  better; it says re-choosing (ℓ, M, b) in this one cannot.
- Kill conditions (from `MISSION.md`): a printed constant not reproduced (none); a
  parameter treated as free being fixed by an unread lemma that moves the binding
  constraint (open for the moment-lemma proofs); the target relation failing at either
  stage (it holds at both).

## 10. Prior art

*As written on 2026-10-16:* Not searched. This is a reading of a two-week-old
preprint's internal constants; the paper itself does not say which inequality fixes
7/8, and `docs/38` records that nobody here had read past its section 3. Original to
this laboratory as a reading; whether anyone else has published the same observation
is unknown.

**Searched 2026-10-21, at landing.** Searched: the follow-up that main already cites in
`hunts/qrh_nonresidue/RESULTS.md`, J. Guo's `github.com/aster2024/openai-math-followups`,
directory `zero-free-beyond-7-8` (its README as of commit `5750cc81e489`, 9 October
2026, unchanged at the repository's head on 2026-10-21); the arXiv abstract of B. Liu,
arXiv:2610.12234 (v1 8 October, v2 12 October 2026); and one web search for the Xu and
Sang figure that hunt #136 records. No paper's proofs were read. Found:

- **The re-optimized geometry was public before this hunt opened, so it is not novel
  here.** Guo's README states that optimising the skew parameter (the offset b here)
  gives the endpoint σ* = (1507 − 2√921)/1653 ≈ 0.8749570698, and that widening Lemma
  plain's fourth-moment range from [3/4, 1] to [37/50, 1] gives σ† ≈ 0.8749570194, the
  root of 7884s³ − 18819s² + 14643s − 3686 in (0.8749570194, 0.8749570195). It credits B. Liu
  with σ* independently (8 October) and Z. Gao with 20999/24000 at ℓ = 1001/6000,
  b = 1/8 (a draft of 7 October), whose fixed-offset envelope it gives as about
  0.8749572006. Liu's v2 abstract varies b, ℓ and κ, gives σ† in closed form as
  B_new = (18ξ + 7)/(18ξ + 9) with ξ the root of 1188ξ³ − 2160ξ² + 171ξ + 190 in
  (0.38858, 0.38859), and states that its optimality is proved "within the explicitly
  specified exponent comparison system". Gao's 20999/24000 is this page's target line
  11/12 − ℓ/4 at ℓ = 1001/6000, exactly.
- **Checked at landing against this hunt's own formulas** (the last three tests of
  `test_seven_eighths_pin.py`, which run the exact code at 45-digit rational
  approximations of the closed forms):
  - *The exact bound of Summary item 3 is valid but loose.* The one-witness program
    holds at every witness where its b-coefficient is at most zero. At x = 1/2 that
    coefficient vanishes at δ* = (49 − √921)/48 ≈ 0.3885837, and the recorded witness
    223/576 ≈ 0.3871528 sits below it. At δ* the same program returns σ* itself: with
    the paper's row counts, no geometry with M + ℓ ≤ 1 and b ≥ 0 passes the endpoint
    inequality below σ* (derived, at the grade of the recorded bound; the closed forms
    come from an exact symbolic computation at landing and are pinned to 35 digits; they
    are Guo's, as the extension below found). The inequality is tight at δ* for
    ℓ* = 11/551 + 8√921/1653 ≈ 0.1668384 and b* = −4/29 + 230√921/26709 ≈ 0.1234054.
    So re-choosing the geometry gains at most 7/8 − σ* ≈ 4.29 × 10⁻⁵, inside the "at
    most 5.8 × 10⁻⁵" of Summary item 3, and Guo and Liu state that this gain is attained
    (cited). That the inequality holds at every other (δ, x) at that geometry is shown in
    Guo's section 8 by an exact decomposition of the endpoint numerator (read in the
    extension, not re-run or checked here); a refinement of this page's float scan at
    landing agrees (measured, `RUNS.md`).
  - *The scan optimum 0.874958 at b = 0.12 is a grid reproduction.* The offset grid of
    0.01 leaves it 5.9 × 10⁻⁷ above σ* (measured).
  - *Section 7's tied capacity is Liu's κ.* Liu's κ_new = (18ξ + 5)/(18ξ + 9) =
    2B_new − 1 is the tie c = 1/(3(2σ₀ − 1)). With it, this page's endpoint formula at
    Liu's ξ, ℓ_new and b_new is zero at δ = ξ and x = 1/2, a minimum in δ and flat in b,
    with B_new on the target line. So Liu's ξ is this page's binding δ, and the "less
    than 10⁻⁶" measured in section 7 is the step of 5.0 × 10⁻⁸ from σ* to σ†.

**Extended 2026-10-21, the same day.** The first search stopped at Guo's README, whose
related-work paragraphs name three more works, and it read none of the follow-ups' own
manuscripts. Read in the extension, as data, with the pinned `paper.tex` (sha256 as
above) at hand for the cited lines:

- tomoto0, `github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification` at
  `b83a73c6cb62` (the repository's only commit, 7 October 2026): the README, and
  `reports/barrier_analysis.md` and `reports/improvement_exploration.md` in full (both in
  Japanese); `scripts/numerical_checks.py` and `data/numerical_checks_results.json`
  searched, with the grid check C18 read;
- Argonaut Math, `github.com/Argonaut-Math/argonaut-math-quasi-riemann-boundary` at
  `5971383edcb0` (8 October 2026): the README with its announcement; in
  `preprints/Beyond_the_Seven_Eighths_Barrier.tex` the introduction, the outline and
  section 3 (the low side) read, the rest searched;
- LW56e2, `github.com/LW56e2/quasi-riemann-improved` at `b83dbbd914c5` (8 October 2026):
  the README (the repository holds Lean files and no manuscript);
- Guo's paper source, in the directory and commit above: sections 3 (the low bound), 8
  (the quadratic endpoint) and 11 (the limit of his envelope) read, sections 1 and 6
  searched;
- Z. Gao, `github.com/Gaozhongpai/seven-eighths-refinement-certificates` at
  `309a757ea539` (the version Guo cites, committed 8 October 2026, draft dated 7 October):
  the README and `REPORT.md`, the low-side lemma and its use in manuscript sections 2 and
  3, the rest of the manuscript searched.

Liu's note itself was not read, only its abstract, and no proof was checked. Every
translation below between this page's variables and a source's is pinned in exact
arithmetic by the block of tests just before the landing checks in
`test_seven_eighths_pin.py`; the sources' own numbers are cited, not re-derived. Found:

- **tomoto0 had much of this page nine days before the hunt opened.** It calls its
  figures model computations that use the paper's exponent formulas outside their stated
  ranges. As far as those files show:
  - the target σ₀ = 1 − h/6 + b/12 at both stages, with the 1/6 from the pole of ζ_F(6z),
    and σ₀ = 2/3 + l_x/2 + b/4 on M + ℓ = 1, the same line as 11/12 − ℓ/4
    (`barrier_analysis.md` section 1): Summary item 1;
  - the floor-row ceiling (section 2, its "barrier B"): rows near Re s = 1/2 are counted
    with R = 1, which no row count improves, and E = 1 − (5/2)l_x − (13/12)b < 0 forces
    σ₀ > 13/15, the limit at l_x = 2/5, b = 0, that is ℓ = 1/5, M = 4/5. Its E is this
    page's C₀ on M + ℓ = 1. Scenarios 5 and 6 of `improvement_exploration.md` give
    0.86979 with ideal counts R = 1 − δ and the floor 51/100 binding, and the infimum 13/15
    with the floor removed: Summary item 5 and the λ = 0 end of section 6;
  - a geometry optimum 0.87496 at (l_x, b, ℓ, h) = (0.3545, 0.1241, 0.1668, 0.8123),
    4 × 10⁻⁵ below 7/8, with the adaptive range (the zero-detected rows) binding
    (`barrier_analysis.md` section 3, scenario 1): the scan optimum of Summary item 3 and
    the λ = 1 end of section 6;
  - at the paper's geometry, the minimum of −E_* on a 401 × 401 grid, 2.28 × 10⁻⁴ at
    δ = 0.3875, x = 1/2, about twice 49/440640 (README section 2, check C18), where
    Summary item 4 has the exact 7/30672 at δ = 79/204.

  These were derived here independently (the hunt read only the paper, `RUNS.md`) and
  are not novel.
- **The low-side loss behind section 3 is handled in three follow-ups.** Gao's draft,
  Guo's section 3 and Argonaut Math's section 3 each bound the row energy of a summand
  rescaled by Z^d by M' + (5ℓ − 1 + d)₊/4 on the line M + ℓ = 1, which is this page's loss
  ((1 + 3ℓ − 2M + d)/4)₊ on that line, and show that the rescaling absorbs it,
  −d + (5ℓ − 1 + d)₊/8 ≤ −7d/8, which holds once ℓ ≤ 1/5. That is the total
  accounting section 3 marks inferred, used there as a proof step of an unreviewed
  preprint, so its grade here does not change. In the parts read, none of them says that
  per-summand losslessness is what places the paper's geometry at 7/8. tomoto0 explains
  the Part II corner by the paper's sufficient condition l_x − ℓ ≥ 3/16, that is
  h ≤ 13/16 (`barrier_analysis.md` section 1). That condition is M − 2ℓ ≥ 3/8 + b: the
  same line as this page's M − 2ℓ ≥ 1/2 at the paper's b = 1/8, and a different one at
  any other b.
- **Guo names the binding bin.** His section 8 takes d_* = (49 − √921)/48, the root of
  288δ² − 588δ + 185 where the coefficient of b in the endpoint numerator at x = 1/2
  vanishes, with ℓ_* = (33 + 8√921)/1653, the same b_* as above and σ_* = 11/12 − ℓ_*/4.
  His section 11 shows that at this bin the high exponent is (3/4 + 3d_*/2)(ℓ − ℓ_*)
  whatever b is, so every admissible geometry has ℓ ≤ ℓ_*: section 4's one-witness bound,
  placed at its best witness, inside his envelope with M + ℓ = 1.
- **Argonaut Math and LW56e2** (both 8 October 2026, with Lean files) state the boundaries
  7/8 − 1/4000000 = 3499999/4000000 and 4374785349/5000000000, a rational just above σ*.
  Argonaut Math moves ℓ up and M down by τ = 10⁻⁶ along M + ℓ = 1 at b = 1/8. LW56e2's
  README records an exact two-bin obstruction to lowering its boundary by 10⁻¹² with the
  same two parameters; its Lean files were not read.
- **A disagreement with tomoto0, over the slope α.** tomoto0's bootstrap scenarios
  (`barrier_analysis.md` section 3 and `improvement_exploration.md` scenarios 2 and 3:
  0.87451 at α = 3/4, and a fixed point near 0.8745) set α = 2β* − 1 from the prior
  bound on the zero. The paper, at lines 15100 to 15104, sets κ = 2β* − 1 = 3/4 + 2Δ and
  α := 5/6, and says: "The parameter κ remains dynamic; α is the fixed slope from
  sixth-power amplification." On that reading
  (section 7), feeding 7/8 back caps the bins at δ ≤ 3/4, far above the binding
  δ ≈ 0.39, and through κ moves only Lemma plain's capacity, which is section 7's tied
  capacity (less than 10⁻⁶, and only if that lemma's range extends below κ = 3/4). The
  follow-ups read agree: Gao and Argonaut Math both take κ = 3/4 from the 7/8 bound and
  keep α = 5/6 (Argonaut Math's bins stop at δ ≤ 3/4), and Guo's envelope keeps 5/6 while
  κ = 2β − 1 varies. So, as read here, tomoto0's 0.87451 and 0.8745 do not follow from
  the paper as written. This page's own early scratch scan made the same substitution,
  reached the same apparent fixed point near 0.8745 and was discarded for that reason
  (`RUNS.md`).
- **Not found in the sources read,** and so this hunt's own as far as this search goes:
  the reading that 7/8 is the corner of M + ℓ ≤ 1 (read as an inequality from line 8246;
  Gao, Guo, Argonaut Math and tomoto0 all fix M + ℓ = 1) and of per-summand losslessness
  M − 2ℓ ≥ 1/2, which alone forces 7/8 for every (ℓ, M, b), with section 4's
  constant-target slope putting the optimum on M + ℓ = 1; the exact rational bounds
  5655673/6464057 and 44117/50422 and the
  exact margin 7/30672 at δ = 79/204; the pricing of the row-count excess between the two
  ends of section 6; and the use of lines 15100 to 15104 against the bootstrap figure.
  This is a statement about the sources listed, not a novelty claim.
- **Open check.** Xu and Sang's 0.8748867, as hunt #136 (`below_seven_eighths/`, open on
  branch `hunt/below-seven-eighths`) records it, and the 0.874887 for Hecke
  L-functions over every number field that the same record attributes to Liu, both lie
  below σ*, the bound above for every geometry with the paper's row counts. Each must
  therefore change an input beyond the geometry (row counts, capacities, the comparison
  system or the probe). Neither source was read here, and the web search did not find
  Xu and Sang's. If either changed only the geometry, that would refute this page's
  bound, which is a kill condition.

## The doors

The hunt locates a ceiling of one assembly, so this section is owed. Candidate status:
the target 7/8 is the corner of the direct bound, and the high side's optimum is
0.874958 (measured) with exact lower bound 0.874942 (derived) over every geometry, with
the paper's row counts; parameter range ℓ, M, b ≥ 0 with M + ℓ ≤ 1; proof status:
exact arithmetic on transcribed formulas, unreviewed.

### Active constraints at the optimum

Ranked by what relaxing them buys:

1. **The endpoint inequality at δ ≈ 0.39, x = 1/2.** Zero margin at the optimum. Its
   shadow price: at the robust witness `∂(−E_*)/∂ℓ = −6464057/4850304 ≈ −1.333` on M + ℓ = 1,
   and `∂σ₀/∂ℓ = −1/4`, so each 10⁻⁴ of margin added there buys about 1.9 × 10⁻⁵ of
   target. Removing a fraction of the row-count excess buys about 0.0083 per unit
   (section 6), down to 13/15.
2. **The direct-bound corner** `M − 2ℓ = 1/2` (per summand) and `M + ℓ = 1`. Tight at
   the paper's geometry. The first is a bookkeeping choice that total accounting
   removes, but removing it buys nothing while (1) binds.
3. **The floor rows,** `C₀ ≤ 0`. Slack 1/48 at the paper's point; binds only once (1)
   is gone, at 13/15.
4. **The slot supply** `ℓ/h > 7/37`. Slack 23/1443; a lower bound, never binding.

### The frozen-constant inventory

| constant | value | what relaxing it trades | trade shape |
|---|---|---|---|
| slot length ℓ | 1/6 | lowers the target by ℓ/4; raises C₀ by 5/4 and the amplitude cost qℓ | genuine, already at its optimum to 1.7 × 10⁻⁴ |
| offset b | 1/8 | appears in C₀ (+b/6) and helps at δ > 0 (+δb/2); optimum ≈ 0.12 | genuine, flat near the optimum |
| total length M | 5/6 | lower M lowers the target 1/12 per unit and costs the high side 3/4 per unit | genuine, the corner is optimal |
| contour Re z | 17/50 | cancels at d = h; matters only for intermediate rows, allowed roughly (49/150, 0.35) (inferred, second reading) | none for the target |
| principal contours | Re w = 19/20, Re z = 33/200 | margins m_w, m_z only | none |
| floor | 51/100 | lower floor shrinks the floor-row exponent but needs witnesses nearer 1/2 | genuine, slack 7/1200 |
| capacity coefficient | 4/9 = 1/(3κ₀) | follows the target; tied, it moves the optimum by < 10⁻⁶ | none here |
| amplification slope α | 5/6 | an input from the sextic large sieve; smaller α shrinks K | genuine, outside this assembly |
| t-window, x-cap | t ≤ 3/2, x ≤ 1/2 | structural (capacities vanish at t = 3/2; x ≤ 1/2 from the bin rectangle) | none |

### The information class

- **Inside the current data, recomputation only:** re-choosing ℓ, M, b, the contours
  and the floor. Exhausted: at most 5.8 × 10⁻⁵ below 7/8 with the paper's counts, and
  the corner 7/8 is where the direct bound puts it.
- **Inside the current family, better inputs:** stronger moment lemmas (larger
  capacities `z_M = (1 − r)/2`, `z_P = (1 − 2m)/(6κ)`), or a better amplification slope
  than (1 + 5r)/6, shrink the excess in `R_*`. The whole excess is worth 13/15 − 7/8
  ≈ −0.0083, no more.
- **Reading or building more:** below 13/15 needs a different direct bound, a different
  Mellin signal or a different high-exponent shape: the `h/6` comes from the pole of
  ζ_F(6z), and the floor rows are counted in full. That is a different probe, not a
  re-tuning of this one, and no candidate for it is proposed here.
