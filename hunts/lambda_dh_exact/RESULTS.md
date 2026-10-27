# RESULTS: hunt #119, `lambda_dh_exact`

**Status: OPEN. There is no result here, and this file exists to say so
precisely rather than to leave the question to a reader's charity.**

The hunt asked whether hunt #61's bracket

    0.0576 < Lambda_DH <= 0.19242481458026887663805      (narrow frame)

collapses to its upper endpoint Delta^2/2. It derived a mechanism that predicts
**no**, registered nine numbered predictions in `MISSION.md` before evaluating
any of them, ran one screen at height 10^6, and then stopped: the three
evaluation agents and the adjudicator all terminated on API 529 errors on
2026-08-18. Compiled 2026-09-12 from what reached disk.

## 1. What the hunt is entitled to say

Nothing about Lambda_DH. Hunt #61's bracket is unchanged by anything here, in
either direction and in every digit. The pre-registered verdict is an
expectation that was never scored, and `MISSION.md` labels it as one.

## 2. What was measured, and at what grade

Every number below is *measured*: one float route, no enclosure carried, no
independent implementation, and no adversary. The two reserved regimes of this
repository are absent from this directory by construction.

| Claim | Value | Grade | Where |
|---|---|---|---|
| Isolated-pair landing law t* = y0^2/2 reproduced under exact polynomial flow | agrees to 3e-13 at y0 = 0.2 | measured | `theory_results.json.isolated_pair` |
| Closed-form quartic landing time vs measured | agrees to 4e-13, 4 real roots after landing | measured | `.quartic_control` |
| Forward flow created no off-axis pair | 400 trials, 400 admitted, 0 decreases | measured | `.no_creation` |
| Shave model on hunts/flow_repair's nine landings | rms 0.54 percent | measured | `.crowding`, `.calibration` |
| Same model on the census holdout | 0.79 percent | measured | `.crowding` |
| Mean neighbour-spacing ratio d/h | 1.4284417709796269 | measured | `.calibration` |
| Model ceiling on sup t* | 0.14709208930872253, i.e. 0.7644 of the #61 upper bound | measured, and an extrapolation | `.criterion` |
| Two-pair configurations landing later than y0^2/2 | 6 of 300 | measured | `.delay` |
| Float64 route vs mpmath at dps 25 | worst abs error 1.09e-12 | measured | `deep_zeros.json.validation` |
| Screen t in [8, 10000], Re s in [0.85, 2.05] | complete, 21 flagged windows, each winding 1 | measured | `deep_zeros.json.screen` |
| Screen t in [10^6, 1001200] | complete, 1 flagged window | measured | `deep_zeros_1e6.json.screen_1e6` |
| Off-line zero at height 10^6 | gamma 1000459.7433532759, beta 0.8583118590734415, y0 0.35831185907344154, winding 1, defect 2.2e-16, abs f 4.35e-11 | measured, float grade | `deep_zeros_1e6.json.zeros` |

## 3. The one control that did run, and what it shows

The screen's inner abscissa was varied over a fixed height range, which the
argument principle constrains: widening the contour can only add flagged
windows, never remove one.

| inner abscissa Re s | flagged windows in t = [8, 600] | total winding |
|---|---|---|
| 0.85 | 1 | 1 |
| 0.75 | 7 | 7 |
| 0.55 | 13 | 14 |

The sets nest strictly, 0.85's inside 0.75's inside 0.55's, and the one window
the shallowest screen flags below height 600 is [228, 248]: the window holding
the pair at gamma = 240.4046 that hunts/flow_repair measured independently and
earlier. That is a real agreement and it was not arranged. It is also the only
control this hunt ran on its instrument.

Reproduce the table from the committed artifacts, without re-screening:

```bash
.venv/bin/python - <<'PY'
import json, sys
sys.path.insert(0, "hunts/lambda_dh_exact")
import deep_zeros as dz
main = json.load(open("hunts/lambda_dh_exact/deep_zeros.json"))["screen"]
ctl = json.load(open("hunts/lambda_dh_exact/deep_zeros_control.json"))
w85 = [w for w in dz.flagged_windows(main) if w["t_hi"] <= 600.0]
for name, fw in [("0.85", w85),
                 ("0.75", dz.flagged_windows(ctl["screen_c75"])),
                 ("0.55", dz.flagged_windows(ctl["screen_c55"]))]:
    print(name, len(fw), sum(w["count"] for w in fw))
PY
```

## 4. The directional datum, stated as weakly as it deserves

The mechanism says depth should *fall* as height rises, because crowding shaves
the landing time. The two deepest depths this laboratory has located are:

| height gamma | depth y0 | source |
|---|---|---|
| 240.4046 | 0.3695261 | hunts/flow_repair, hunts/lambda_dh_bounds |
| 1000459.7433532759 | 0.35831185907344154 | this hunt, `deep_zeros_1e6.json` |

Shallower at four thousand times the height, which is the direction the theory
predicts. **Two points are not a trend, and the second point is censored by its
own instrument.** Three separate reasons not to lean on that row, the third of
which was found while writing the doors section and is the worst of them:

1. The second screen covers 1200 units of height at one place on the line, and
   it is one zero rather than a supremum over a decade. Prediction 4 in
   `MISSION.md` asks for a fitted exponent that nobody fitted.
2. The zero is float grade, not an enclosure.
3. **The screen's inner abscissa is Re s = 0.85, so it cannot see any zero of
   depth y0 <= 0.35 at all, and the zero it found has y0 = 0.35831185907344154.
   That is 0.0083 inside the wall.** So the measurement is left-censored at
   almost exactly the value it returned: it cannot distinguish "the deepest zero
   near height 10^6 has depth 0.3583" from "every other zero there is shallower
   than the instrument's floor and this is the only one visible". A depth *below*
   0.35 is what the theory predicts at that height, and it is precisely the
   outcome this screen was incapable of reporting. Re-screening below 0.85 is
   the only way to turn the row into evidence, and the information class below puts it in the
   class that requires new data.

Read this row as consistency, not as evidence.

## 5. Limitations, in the order a referee would raise them

1. **Nothing was adjudicated and nothing was attacked.** No adversary read any
   number in this directory. Hunt #61's numbers went through four adversaries
   before they were quoted; none of these did.
2. **The zero is float grade.** Winding count 1 with defect 2.2e-16 is a
   convincing float computation and not an enclosure. The instrument that could
   decide it exists in `hunts/lambda_dh_bounds` and was not pointed at this
   zero.
3. **The screens are incomplete as a survey.** `screen_hi` over
   [10^4, 10^5] stopped mid-sweep with `complete: false`. Neither it nor the
   low screen ever ran `stage_locate`, so their 21 and 88 flagged windows are
   candidate locations and nothing more: no zero in them is located and no
   window in them is excluded. Any sentence of the form "no deeper zero exists
   below height X" is unsupported by this directory.
4. **The model's reach exceeds its training set.** The calibration is fitted at
   y0 <= 0.37 and the question is about y0 approaching Delta = 0.62036249819.
   The ceiling 0.147 is an extrapolation across nearly a factor of two in the
   variable that matters, from a one-parameter fit. `MISSION.md`'s own dead
   routes already record one earlier fit of this family failing exactly this
   way when extrapolated.
5. **The no-creation step is sampled, not proved.** 400 trials with 0 failures
   is support. The step it supports, Lambda_DH = sup t*, is what converts every
   landing time from a lower bound into the constant itself; without a proof,
   every landing time remains a lower bound only. Kill condition 3 is written
   against precisely this.
6. **Lesion evidence is published, not resolved.** `lesion_degree52` records a
   planted fault that the detector's own health metric does not flag correctly,
   inherited from the same blind spot documented in
   `hunts/lambda_dh_bounds/M2-LEMMA.md`.

## 6. Kill conditions: which fired

None, because none was evaluated. Listing them explicitly so that "no kill
condition fired" is not misread as "the hunt survived its kill conditions":

| # | Condition | State |
|---|---|---|
| 1 | a decided landing time exceeds the model by more than 1.25x | never tested |
| 2 | a zero with y0 > 0.55 below height 10^4, or none with y0 > 0.40 below 10^4 | never tested; the relevant screens never located a zero |
| 3 | the no-creation step fails | sampled 400 times without failure, not proved |
| 4 | sup of landing times rises with height over two decades | never tested; one zero at one height |
| 5 | the model's sup falls below the decided floor 36/625 | **fires for one of the four sampled exponents.** At p = 0.5 the model's own sup is 0.05574992380295127 < 36/625 = 0.0576, so that branch is self-inconsistent and is excluded by the hunt's decided floor rather than by any measurement. It holds at p = 1.0, 1.5 and 2.0 (0.0609, 0.0661, 0.0704). See the doors section. |

## 7. What whoever resumes should do first

In this order, because each step makes the next one worth doing:

1. Decide the height-10^6 zero with ball arithmetic on both backends, using the
   winding instrument from `hunts/lambda_dh_bounds`. One enclosure turns the
   only evaluation datum from float grade to decided.
2. Run `stage_locate` on the completed low screen. Its 21 flagged windows are
   already paid for and would give the depth distribution below height 10^4 that
   kill condition 2 needs.
3. Finish or abandon `screen_hi` explicitly. A screen marked `complete: false`
   in a committed artifact is an invitation to misread it.
4. Only then extend the depth-versus-height fit, and only with the exponent
   prediction 4 registered.

Nothing in this directory is evidence about the Riemann Hypothesis, and nothing
in it is evidence about Lambda_DH either.

## The doors

Required of every hunt that measures a ceiling (`CLAUDE.md`, "Door analysis:
what every ceiling hunt owes"), and it earns its place here rather than filling
a slot: the ceiling this hunt reports is 0.7644 of hunt #61's upper bound, and
writing this section out is what showed that one of the five kill conditions
already fires.

### Active constraints at the optimum

The model's predicted range for sup t*, pre-registered in `MISSION.md` as
[0.058, 0.075] narrow, is not a confidence interval. It is the span swept by one
unfitted exponent. `theory.py` stage 6 assumes a depth-versus-height law

    y_max(gamma) = Delta (1 - c_p / L(gamma)^p),    L(gamma) = log(5 gamma / 2 pi)

and reports the sup separately for p = 0.5, 1.0, 1.5, 2.0:

| p | sup t* | at gamma | at y0 | consistent with the decided floor 36/625 |
|---|---|---|---|---|
| 0.5 | 0.05574992380295127 | 3000 | 0.3970 | **no** |
| 1.0 | 0.060860504648711886 | 3000 | 0.4214 | yes |
| 1.5 | 0.0660619102748729 | 10000 | 0.4776 | yes |
| 2.0 | 0.07044359379445239 | 10000 | 0.5021 | yes |

Ranked by how much each binds:

1. **p, and nothing else comes close.** It is the only quantity in the model
   that moves the sup across the whole registered range, and it is the only one
   nobody fitted. Its lowest sampled value is already refuted, not by data but
   by the hunt's own decided floor: at p = 0.5 the model's sup falls below
   36/625, which is kill condition 5. So the registered range is really the
   p = 1 to 2 span, and its lower end is set by an assumption rather than a
   measurement.
2. **The height at which the ceiling is quoted.** The headline
   0.14709208930872253 is `t_star_gap(Delta, gamma = 85.6993)`, evaluated at the
   *lowest* height in `flow_repair`'s census, which is the most favourable height
   available. It is the value of the landing law at one height, not a supremum
   over heights. Nothing in the hunt shows that no height gives more, and the
   crossover table says the opposite of a comfortable margin: the height above
   which no pair at any depth up to Delta can beat the floor 0.0576518 is
   3.05e6, and this hunt's only located zero sits at 1.0e6.
3. **The sup is a maximum over an eight-point grid** (600, 3e3, 1e4, 1e5, 1e6,
   1e8, 1e12, 1e20), and for p = 0.5 and p = 1.0 it is attained at 3e3, an
   interior grid point with neighbours a factor 5 and 3 away. The true maximum
   is off-grid and the reported sup is a lower bound on the model's own sup.

### The frozen-constant inventory

Every number in the construction that was chosen rather than optimized, with
what relaxing it trades against. The first is the only one with real trade
shape.

| Frozen | Value | Where | What relaxing it trades |
|---|---|---|---|
| the depth-law exponent p | 0.5, 1.0, 1.5, 2.0 sampled, none fitted | `theory.py` stage 6 | Everything. Fitting it against measured depths replaces the registered range with an interval, and excludes p = 0.5 on evidence rather than on self-consistency. Costs new depths at new heights. |
| the depth-law anchor | y_max(600) = 0.3695261 | stage 6, sets c_p | One data point, `flow_repair`'s deepest pair, pins the whole law. A deeper pair anywhere re-anchors it upward and raises every sup in the table. |
| local-gap parameter DBAR | 1.4284 | module constant, fitted as mean d/h over nine landings | Fitted, not guessed, but it is one scalar standing for all gap geometry, with nine samples and a spread of 1.335 to 1.568. Re-fitting per height, or carrying the spread rather than the mean, trades a tighter model against more parameters than nine points can support. |
| lattice phase theta | 0.5 | `t_star_lattice` | The pair sits exactly midway between its neighbours, the most symmetric and plausibly the most favourable position. Sampling theta trades a cheap recomputation against a sup that may only fall. |
| lattice truncation K | 6000 terms | `t_star_gap` | Pure numerics. Cheap to push; expected to move nothing, which is why it should be checked once rather than assumed. |
| the sup grid | 8 heights, 600 to 1e20 | stage 6 | Grid resolution, per the third active constraint above. Cheap. |
| the screen contour | Re s in [0.85, 2.05], 20-unit windows, 16 points per unit | `deep_zeros.py` | Depth reach against cost. The 0.85 inner abscissa cannot see a zero shallower than y0 = 0.35, and this hunt's only located zero has y0 = 0.3583, which is 0.008 inside the wall. That is uncomfortably close to the instrument's own limit and is the strongest argument for re-screening deeper before trusting the shallowness. |
| the conductor factor 5 in L(gamma) | 5 | `L()` | Derived from the gamma factor in `MISSION.md` section 4.5, not chosen. Listed so it is not mistaken for a fitted constant. |

### The information class of each door

Whether a door stays inside the data this hunt already holds, or requires
reading more.

**Inside the current data, recomputation only.** The lattice phase, the
truncation K, the sup grid resolution, and re-fitting DBAR with its spread
rather than its mean. All four are answerable from the committed artifacts and
`theory.py` alone, none needs a new zero, and together they decide whether the
reported sup is the model's real sup or an artifact of three convenient choices.
Do these first because they are nearly free and they bound how much the
expensive door can be worth.

**Inside the current data, but underexploited.** `stage_locate` on the completed
low screen. Its 21 flagged windows are already paid for and would give the depth
distribution below height 10^4, which is the input kill condition 2 asks for and
the beginning of a fit for p. This is the highest ratio of value to cost in the
whole hunt: no new screening, one stage of an existing script.

**Requires reading more.** The exponent p itself, past what 21 windows can say.
A fit needs depths across at least two decades of height, which means finishing
`screen_hi` over [10^4, 10^5] and screening at least one decade above it, at
roughly the 763 s per 1200 units of height that `screen_1e6` measured. Also in
this class: re-screening below Re s = 0.85, which is the only way to learn
whether the height-10^6 zero's depth of 0.3583 is the real depth there or the
instrument's wall, and deciding that zero with ball arithmetic, which changes its
grade rather than the model.

The door to go through next is `stage_locate` on the low screen, because it is
inside data already held, it is the input p needs, and it is the cheapest thing
here that can move a number.

---

## 8. Resumption, 2026-10-26: what the first wave decided

Appended on resumption; sections 1 to 7 and the doors above are the record of
2026-09-12 and are not rewritten. Where this section corrects them it says so
and leaves the original sentence standing. Branch
`hunt/lambda-dh-exact-resume`, draft PR #357. Vocabulary as in `MISSION.md`:
*decided* is a ball enclosure whose exact endpoints settle an integer or a
sign, on both backends unless one is named.

### 8.1 Corrections met on the way

1. **The floor.** The decided floor is 36/625 = 0.0576, as the bracket on
   line 8 and kill condition 5's row (line 152) state it. The number
   0.05765184035 is a *measured* landing at gamma = 240.4046 and is not
   decided. Where the doors section (line 212, the crossover height 3.05e6)
   and P5 call 0.0576518 "the floor", they compare against that measured
   landing, not against the decided floor.
2. **The depth of the floor pair.** `MISSION.md` section 0, the huntspec
   frontier, P2 ("y_max(600) = 0.3695261"), section 4 of this file,
   `theory.py` (calibration row and the stage-6 depth-law anchor) and
   `landing.py` all carry y0 = 0.3695261 for the pair at gamma = 240.4046.
   That digit string is a transcription slip in
   `hunts/flow_repair/NOTES.md:111`: flow_repair's own `results.json` records
   y0 = 0.369530579640643..., its y0^2/2 = 0.0682764 in the same NOTES row
   matches 0.3695306, not 0.3695261, and the decided enclosure below is
   [0.3695305721, 0.3695305871] (rounded outward; requoted 2026-10-26 in
   review, section 8.16). The slip is 4.5e-6 in y0, 1.2e-5 relative.
   It moves the stage-6 anchor c_p by about that much and changes no number
   this hunt reports at the digits it reports them. `theory.py` and its
   results are left as recorded, not re-run. (Dated note, 2026-10-26 in
   review: superseded the same day by section 8.9, which corrected the
   inputs in `theory.py`; `theory_results.json` is still as recorded and was
   not re-run.)

### 8.2 Step 1: the height-10^6 zero is decided

`decide_deep_zero.py`, `decide_deep_zero.json`, Run 7 in `RUNS.md`.

**Decided on both backends: f has exactly one zero, counted with
multiplicity, in the exact rectangle**

    sigma in [943723861105, 943723877489] / 2^40, inside [0.8583118516, 0.8583118666]
    t     in [537117734833355, 537117734833363] / 2^29, inside [1000459.74335326, 1000459.74335329]

so its depth is **y0 in [0.3583118516, 0.3583118666]**, the rectangle lies
wholly in Re s > 1/2, and the 2026-08-18 float location (beta
0.8583118590734415, gamma 1000459.7433532759) is inside it. The row in
section 2 moves from float grade to decided. Its by-symmetry partner at
1 - beta needs no separate count (F(s) = F(1 - s), conjugate-symmetric
coefficients). (Decimals requoted 2026-10-26 in review, rounded outward. The
first version rounded to nearest, which narrowed the upper sigma and y0
endpoints and both t endpoints, so as printed they were not enclosures. The
dyadic endpoints are the decided statement; section 8.16.)

| | Arb (python-flint) | mpmath.iv (hand-rolled) |
|---|---|---|
| route to f | Arb `acb.zeta(s, a)`, four Hurwitz pieces | Euler-Maclaurin, N = 199153, p = 293, explicit remainder; Taylor model K = 14 about the centre |
| precision | 128 bits | 128 bits |
| bound on abs f'' (Cauchy, square of half-width 2^-13) | 4.99e6 | 4.07e4 |
| segments, count | 16, **1** | 16, **1** |
| winding enclosure | [0.9999999999999991, 1.0000000000000009] | same |
| worst clearance / tube | 1420 | 174151 |
| planted faults | kappa + 1e-3: **0**; rectangle shifted 4 half-widths right: **0** | shifted rectangle: **0** |

The two routes share the formula f = sum a_n n^{-s} and the closed form
kappa = sqrt(1 + phi^2) - phi (cited, Bombieri-Ghosh 2011 section 6; decided
equal to the self-duality kappa in `hunts/lambda_dh_bounds/KAPPA-CLOSED-FORM.md`)
and no evaluator. (Corrected 2026-10-26 in review: this sentence first said
"and no evaluator, rounding code or error bound". The routes do share the
counting driver `count_zeros` in `decide_deep_zero.py`: the chord-tube bound
M2 ell^2 / 8, the Cauchy bound on |f''|, the float conversions with their
2^-50 fudges, and the sum of the Arg enclosures in mpmath.iv. A defect there
would reach both routes. The clearance functions and every evaluation of f
are separate.) Their enclosures of f intersect at two corners and the
centre, compared on exact rational endpoints with no slack (Run 22): in the
real part the midpoints differ by at most 2.7e-33 against widths 3.7e-33
(Arb) and 1.04e-30 (iv), in the imaginary part by at most 1.3e-33 against
1.4e-32 and 1.06e-30. (Corrected 2026-10-26 in review. The first check, which
gave the same verdict, compared float64 midpoints with a slack of
radii + 1e-30. At |f| about 1.3e-8 the float64 spacing is about 1e-24, so it
passed exactly when the two midpoints rounded to the same double, and it
could not fail on the property it named. A claim that the routes "agree with
mpmath to 1e-33 at height 1000" stood here and is withdrawn: no artifact,
test or run log backed it.)

What it changes: the only evaluation datum the hunt had is no longer float
grade. What it does not change: it is a location, not a landing time, so it
bears on no landing prediction directly, and section 4's warning stands in
full: the screen that found it cannot see y0 <= 0.35, so it is not shown to
be the deepest zero near 10^6.

### 8.3 Step 2: the low screen located and decided, screen_hi closed

`stage_locate` on the completed low screen (t in [8, 10^4], Re s > 0.85,
written to the copy `deep_zeros_locate_20261026.json`): **21 zeros, one per
flagged window**, every one with unit float winding. `decide_low_zeros.py`
then decided all 21 on both backends (count 1 in an exact rectangle of
half-width 2^-27 each, `decide_low_zeros.json`):

| gamma | y0 enclosure (both backends; rounded outward, requoted 2026-10-26 in review) |
|---|---|
| 240.4047 | [0.3695305721, 0.3695305871] |
| 783.6530 | [0.3530014426, 0.3530014576] |
| 857.2959 | [0.3561094084, 0.3561094234] |
| 1092.4545 | [0.3546296114, 0.3546296264] |
| **2442.5303** | **[0.3977501475, 0.3977501625]** |
| 2887.9392 | [0.3604422749, 0.3604422899] |
| 3059.5187 | [0.3678568615, 0.3678568765] |
| 3214.1444 | [0.3612643315, 0.3612643465] |
| 3294.6092 | [0.3603604982, 0.3603605132] |
| 4237.9692 | [0.3576562360, 0.3576562510] |
| 4392.3764 | [0.3535286435, 0.3535286585] |
| 4935.6178 | [0.3551060612, 0.3551060763] |
| 5090.3177 | [0.3663990726, 0.3663990877] |
| 5833.2823 | [0.3740914934, 0.3740915084] |
| 5913.7059 | [0.3594353089, 0.3594353239] |
| 6113.9288 | [0.3581936446, 0.3581936596] |
| 7011.5119 | [0.3662883173, 0.3662883323] |
| 7909.4450 | [0.3545747216, 0.3545747366] |
| 8235.5925 | [0.3753363088, 0.3753363238] |
| 8561.5942 | [0.3836407511, 0.3836407661] |
| 9694.5786 | [0.3516309902, 0.3516310052] |

**screen_hi: finished.** The sweep over [10^4, 10^5] that stopped on
2026-08-18 at t = 82480 was resumed from its own checkpoint on a copy,
`deep_zeros_hi_20261026.json`, which now reads `complete: true`: 111 flagged
windows, each of winding 1 (worst defect 4.4e-12), and `stage_locate` there
found 111 distinct zeros, one per window. The recorded
`deep_zeros.json["screen_hi"]` still reads `complete: false` and is
**superseded** by the copy; it is left unedited because it is the record of
what the interrupted run did. The deepest zero in that decade is y0 =
0.437058 at gamma = 49688.34 (measured, float; not decided). Per decade-tenth
maxima, 10^4 to 10^5: 0.3906, 0.4186, 0.3871, 0.4371, 0.3946, 0.3888,
0.4183, 0.4072, 0.3870.

### 8.4 P2 and kill condition 2, evaluated as written

**P2** registered `y_max(10^4)` in [0.40, 0.52], "below 0.40 or above 0.52
refutes". The deepest zero below height 10^4 that the screen sees has decided
depth y0 in [0.3977501475, 0.3977501625] (rounded outward; requoted
2026-10-26 in review), at gamma = 2442.53. **P2 is
refuted** (ALIGNMENT section 5, disposition 1, at the stated parameters). Its
grade is *measured*, the grade of its weakest step: the location is decided,
but "there is no deeper zero below 10^4" rests on the float screen at
Re s = 0.85. The margin is 0.0022 below the band's lower end.

**Kill condition 2** reads "a zero with y0 > 0.55 is found below height 10^4,
or no zero with y0 > 0.40 is found below height 10^4". The first clause does
not fire (no zero above y0 = 0.398 is seen). **The second clause fires**,
measured grade, on the same evidence. Its consequence as registered: "the
depth-versus-height law is falsified". That law is `theory.py` stage 6,
y_max(gamma) = Delta (1 - c_p / L^p). Its four sampled exponents predicted,
at gamma = 10^4:

| p | y_max(10^4) predicted | observed (decided location, measured completeness) |
|---|---|---|
| 0.5 | 0.4125 | 0.39775 |
| 1.0 | 0.4481 | 0.39775 |
| 1.5 | 0.4776 | 0.39775 |
| 2.0 | 0.5021 | 0.39775 |

All four over-predict at 10^4. The decade above is the one place the law
fits: the [10^4, 10^5] maximum 0.4371 (measured) sits on the p = 0.5 curve
(0.4349 at 10^5) and below p = 1 to 2. That is the branch kill condition 5
already excluded as self-inconsistent, which leaves the stage-6 law with no
sampled exponent consistent with both the data and the decided floor. What the
firing withdraws: every registered number derived from the stage-6 law, which
is P1's stronger band [0.058, 0.075], P4's point estimate and P5's location
of the sup. They are not refuted. Their derivation's input is withdrawn, so
they are *unresolved* (disposition 3). P1's weak form, sup t* < 0.14432,
does not rest on stage 6 and is untouched. Lower-than-predicted depths point
toward a smaller sup, which is the direction of P1, but a falsified law
cannot carry that inference and this record does not draw it.

### 8.5 Kill condition 2, second clause, decided

`decide_kc2.py`, `kc2/`, `decide_kc2.json`, Run 10 in `RUNS.md`.
**Decided on Arb: f has no zero with beta >= 0.90 and |t| <= 10^4.** Two
rectangles, each an argument-principle count of 0 with every boundary point
shown non-vanishing:

| rectangle | count | winding ball | cost |
|---|---|---|---|
| [0.90, 2.05] x [8, 10^4] | **0** | [-5.4e-12, 8.0e-12] | 448092 Arb evaluations, 1.83 core-hours |
| [0.90, 2.05] x [-8, 8] (s = 1 kept strictly inside) | **0** | [-8.5e-15, 4.0e-15] | 824 segments, seconds |

with the right edge Re s = 2.05 handled by the decided bound
sum_{n>=2} |a_n| n^{-2.05} = 0.2459783663... < 1, and planted faults on
[0.89 or 0.90, 2.05] x [2400, 2500] returning 1 and 0 as they must. (Two
steps of "|t| <= 10^4", stated 2026-10-26 in review, both elementary and
neither computed: heights t < -8 follow from t > 8 by conjugate symmetry,
the a_n being real; and Re s > 2.05 holds no zero, since the same sum
decreases in sigma and is already below 1 at 2.05.) So the
second clause of kill condition 2, "no zero with y0 > 0.40 is found below
height 10^4", now holds at **decided** grade (Arb alone; the iv route would
cost about 120 core-hours here and was not run), and with it the refutation
of P2 also moves to decided on Arb: y_max(10^4) < 0.40, and the decided
location of the zero at gamma = 2442.53 gives y_max(10^4) >= 0.3977501475.
The one sentence that stays measured is the identification of that zero as
*the* maximum: whether some zero has y0 in (0.39775016, 0.40) is not decided,
and it does not matter to P2, which fails either way.

### 8.6 The landing census to height 10^4

`census_1e4.py`, `census_1e4.json`, Run 11 in `RUNS.md`. All 21 zeros with
beta > 0.85 below 10^4 (positions decided, section 8.3; completeness of the
list measured), each landed by the N-body ODE of `hunts/flow_repair/probe.py`
in a window of +-40 whose zero accounting closed in **21 of 21** windows
(N_strip = N_line + 2 N_right, every off-line zero with beta > 0.505 located
and fed to the ODE as a neighbour). Grade: **measured** (one float route; the
ODE matched the Xi-plane contour measurement to 0.04 percent on flow_repair
pairs 1 to 5, and the control below).

**Control.** The floor pair at gamma = 240.4047 lands at 0.0576657 against
its recorded Xi-plane landing 0.05765184035, +0.024 percent, inside the band.

| gamma | y0 | ODE t* | y0^2/2 | shave | model `t_star_gap` | ODE / model | d/h |
|---|---|---|---|---|---|---|---|
| 2442.5303 | 0.397750 | 0.055865 | 0.079103 | 29.4% | 0.056678 | 0.986 | 1.240 |
| 8561.5942 | 0.383641 | 0.043468 | 0.073590 | 40.9% | 0.049527 | 0.878 | 0.610 |
| 8235.5925 | 0.375336 | 0.046619 | 0.070439 | 33.8% | 0.048110 | 0.969 | 1.105 |
| 5833.2823 | 0.374092 | 0.047600 | 0.069972 | 32.0% | 0.048925 | 0.973 | 1.176 |
| 240.4047 (control) | 0.369531 | 0.057666 | 0.068276 | 15.5% | 0.057986 | 0.994 | 1.118 |
| 3059.5187 | 0.367857 | 0.046425 | 0.067659 | 31.4% | 0.049648 | 0.935 | 0.824 |
| 5090.3177 | 0.366399 | 0.044363 | 0.067124 | 33.9% | 0.047842 | 0.927 | 0.739 |
| 7011.5119 | 0.366288 | 0.045404 | 0.067084 | 32.3% | 0.046893 | 0.968 | 1.182 |
| 3214.1444 | 0.361264 | 0.044304 | 0.065256 | 32.1% | 0.048152 | 0.920 | 0.675 |
| 2887.9392 | 0.360442 | 0.047805 | 0.064959 | 26.4% | 0.048290 | 0.990 | 1.179 |
| 3294.6092 | 0.360361 | 0.044306 | 0.064930 | 31.8% | 0.047897 | 0.925 | 0.713 |
| 5913.7059 | 0.359435 | 0.045889 | 0.064597 | 29.0% | 0.046072 | 0.996 | 1.206 |
| 6113.9288 | 0.358194 | 0.041455 | 0.064151 | 35.4% | 0.045743 | 0.906 | 0.688 |
| 4237.9692 | 0.357656 | 0.042813 | 0.063959 | 33.1% | 0.046646 | 0.918 | 0.755 |
| 857.2959 | 0.356109 | 0.050651 | 0.063407 | 20.1% | 0.050817 | 0.997 | 1.192 |
| 4935.6178 | 0.355106 | 0.027887 | 0.063050 | 55.8% | 0.045729 | 0.610 | 0.101 |
| 1092.4545 | 0.354630 | 0.048963 | 0.062881 | 22.1% | 0.049792 | 0.983 | 1.239 |
| 7909.4450 | 0.354575 | 0.040100 | 0.062862 | 36.2% | 0.044372 | 0.904 | 0.681 |
| 4392.3764 | 0.353529 | 0.044027 | 0.062491 | 29.5% | 0.045734 | 0.963 | 1.089 |
| 783.6530 | 0.353001 | 0.050002 | 0.062305 | 19.7% | 0.050341 | 0.993 | 1.329 |
| 9694.5786 | 0.351631 | 0.042299 | 0.061822 | 31.6% | 0.043306 | 0.977 | 1.211 |

**What it says.** No pair below height 10^4 lands above the measured landing
0.05765184 beyond the instrument's band; the best landing below 10^4 is still
the pair at gamma = 240.4046. The deepest pair (2442.53, y0 = 0.3978) has the
largest naive landing, 0.0791, and is shaved 29.4 percent to 0.0559. Coverage
gap, stated: pairs with y0 in (0.3396, 0.35] were not landed. They could beat
the floor only with a shave under 5.9 percent, against a minimum of 15.5
percent over these 21.

### 8.7 The predictions and kill conditions the census touches, as written

| item | as registered | finding | disposition, grade |
|---|---|---|---|
| P2 | y_max(10^4) in [0.40, 0.52] | y_max(10^4) in [0.39775014, 0.40) (lower end rounded outward; requoted 2026-10-26 in review, it read 0.39775015) | **refuted**, decided (Arb), section 8.5 |
| P3 | the deepest pair below 10^4 lands within [0.85, 1.25] x model | 2442.53: ODE / model = 0.986 | **holds**, measured. Its registered point (0.061084 at (0.45, 10^4)) is at the wrong depth: the deepest pair is at 0.3978 |
| P4 | a complete census to 10^4 *raises* the best landing to [0.055, 0.079], point 0.061 | not raised; best stays 0.05765 | **unresolved, evidence against**, measured (relabelled 2026-10-26 in review; it read "refuted in its 'raises' clause"). P4's antecedent, a *complete* census to 10^4, was not run: pairs with y0 in (0.3396, 0.35] were not landed, and neither was any shallower pair a delay could lift. Within coverage y0 > 0.35 the best landing is not raised. The band contains the old value trivially. The point estimate derives from stage 6, already withdrawn by kill condition 2 |
| P5 | the maximizing pair has height in [10^3, 10^5] and depth in [0.40, 0.52] | below 10^4 the maximum is at height 240, depth 0.3695; the decade [10^4, 10^5] is unlanded | **unresolved** (needs the 10^5 leg); derivation withdrawn |
| P6 | at a new quadruple d/h lands in [1.1, 1.8], not near 0.5 | 20 new pairs: 10 of 20 in band; mean 0.947, sd 0.317, range 0.101 to 1.329 | **refuted**, measured: the calibration value 1.4284 +- 0.0749 (nine flow_repair pairs) does not survive out of sample |
| P8 | at least one pair below 10^4 lands later than its own y0^2/2 | 0 of 21 (every shave positive, minimum 15.5%) | **not observed** at this coverage, measured; unresolved for the shallower pairs it did not land. The 15% rate that would widen P1 is not approached |
| KC1 | a *decided* landing exceeds the model by more than 1.25x | no landing exceeds the model at all (max ratio 0.997); none is decided | **does not fire**, measured |
| KC2 | ...or no zero with y0 > 0.40 below 10^4 | none, decided | **fires**, decided (Arb) |
| KC4 | the sup of landings rises with height over two decades | one decade landed past 10^3 | **not tested** |

One instrument note that P6's failure explains: at gamma = 4935.6 a line zero
sits at d/h = 0.10 from the pair's ordinate, the ODE shave is 55.8 percent, and
the model (which assumes the local gap 1.4284 h) over-predicts the landing by
a factor 1.64. The model's DBAR is a fitted mean, and pairs near a line zero
land much earlier than it says. Every other pair sits at ratio 0.88 to 1.00,
so the model is a near-ceiling for the ODE here, not a central estimate.

**What this hunt is entitled to say after 2026-10-26**, in addition to
section 1, which still stands for Lambda_DH: one off-line zero at height 10^6
and 21 below 10^4 are decided (that the 21 are all the zeros with
beta > 0.85 below 10^4 is measured); P2 and P6 are refuted, P2 at decided
grade; P4 is unresolved with evidence against;
kill condition 2 fires at decided grade, and the stage-6 depth law and every
number derived from it are withdrawn; no landing below 10^4 beats 0.0576518
(measured). Hunt #61's bracket is unchanged in every digit. Nothing here is
evidence about the Riemann Hypothesis (P9; `docs/08`).

### 8.8 A targeted check above 10^4 (not a census)

`census_deep4_1e5.json` (the name is from the plan for four pairs; it holds
nine), Run 12 in `RUNS.md`. **Selection rule, stated plainly:** every zero
with y0 > 0.40 in [10^4, 10^5] in the completed `screen_hi`
(float locations, not decided), chosen because the registered model gives
them the highest landings in that decade. It is a targeted check. It can show
a pair beating the floor; it cannot show that none does, because the 102
shallower zeros of the decade were not landed. Same instrument and grade as
section 8.6 (*measured*).

| gamma | y0 | ODE t* | y0^2/2 | shave | model | ODE / model | d/h | accounting |
|---|---|---|---|---|---|---|---|---|
| 49688.3426 | 0.437058 | 0.034848 | 0.095510 | 63.5% | 0.052391 | 0.665 | 0.122 | closed |
| 24415.4787 | 0.418601 | 0.048772 | 0.087614 | 44.3% | 0.052065 | 0.937 | 0.859 | closed |
| 74189.6448 | 0.418334 | 0.025400 | 0.087502 | 71.0% | 0.048234 | 0.527 | 0.008 | closed |
| 44838.4752 | 0.416138 | 0.047116 | 0.086585 | 45.6% | 0.049565 | 0.951 | 1.000 | closed |
| 46714.5723 | 0.410310 | 0.046690 | 0.084177 | 44.5% | 0.048535 | 0.962 | 1.139 | closed |
| 43488.4705 | 0.408969 | 0.047769 | 0.083628 | 42.9% | 0.048561 | 0.984 | 1.432 | closed |
| 88167.4022 | 0.407177 | not landed | 0.082897 | | 0.046081 | | 0.556 | **open**: strip 142 vs 128 line + 2 x 6 |
| 77163.4089 | 0.405686 | 0.026805 | 0.082291 | 67.4% | 0.046269 | 0.579 | 0.045 | closed |
| 20011.1603 | 0.400223 | 0.049020 | 0.080089 | 38.8% | 0.049694 | 0.986 | 1.240 | closed |

The window at gamma = 88167.40 has two zeros the census could not place,
even with the line grid refined to 1/240 of a gap: either an off-line pair
with beta in (0.5, 0.505) or two line zeros closer than the grid. The pair is
recorded unlanded rather than landed with an incomplete neighbour list.

**What it says.** None of the eight landed pairs comes near the floor: the
best is 0.04902 (gamma = 20011.16), 15 percent under 0.0576518, and the
deepest pair this lab has located below 10^5 (y0 = 0.437) lands at 0.0348.
The shaves are 38.8 to 71.0 percent, against 15.5 to 55.8 below 10^4, and the
model is again a near-ceiling (ODE / model 0.53 to 0.99, never above 1). The
three pairs with ratios under 0.7 all have a line zero within d/h < 0.123,
the same signature as gamma = 4935.6 below 10^4.

**P5 and kill condition 4, only as far as this supports.**

- *P5* (the maximizing pair has height in [10^3, 10^5], depth in
  [0.40, 0.52]): every landed pair of depth 0.40 to 0.44 in [10^4, 10^5] lands
  below the best pair of [10^3, 10^4] (0.05586) and below the γ = 240 pair
  (0.05767). The largest measured landing anywhere in the hunt is at height 240
  and depth 0.3695, outside both of P5's ranges. **Unresolved**, measured
  evidence against: a shallower pair in [10^4, 10^5] beating the floor would
  need a shave under 6 to 28 percent at y0 in (0.35, 0.40), and the decade's
  measured shaves are all above 38.
- *Kill condition 4* (the sup of landings rises with height over two
  decades): the largest measured landing per decade is 0.05767 in
  [10^2, 10^3], 0.05586 in [10^3, 10^4], and at least 0.04902 in
  [10^4, 10^5] (the last over the targeted pairs only, so a lower bound on
  that decade's maximum). **Does not fire** on what was measured. The
  measured per-decade maxima fall over three decades. That is the
  peak-and-decline P5 asks for, with the peak below 10^3 rather than inside
  P5's window. The 10^4 to 10^5 entry is a targeted lower bound, so the
  decline in that decade is not shown.
- *P8* (a pair landing later than its own y0^2/2): its registered scope is
  pairs below 10^4, where it stands at 0 of 21 (section 8.6). The 8 pairs
  here lie above 10^4, outside that scope, and 0 of 8 land later than
  y0^2/2, a description only. (Restricted 2026-10-26 in review; it read
  "0 of 8 here as well, 0 of 29 over sections 8.6 and 8.8. Not observed,
  measured.")


### 8.9 Follow-up, 2026-10-26: pins, the slips corrected, the d/h refit

**Pins.** `test_lambda_dh_exact.py` now pins every number section 8 calls
decided or measured, against the artifact it came from. Each test's
docstring names that artifact. It also re-derives every verdict of sections
8.4 to 8.8 from those numbers, not from the prose. It recomputes too: one
low-screen zero (gamma = 240.4047) decided again on both backends, the
|t| <= 8 rectangle of the kill-condition-2 count and a five-unit window at
gamma = 2442.53 on Arb, and, in the slow tier, the whole lowest left-edge
shard (0.90 + i[8, 1257], about 2 minutes) against its recorded arg-variation
ball. Default tier: 31 tests in about 13 s. Both tiers: 32. Planted faults,
each shown red (Run 13 in `RUNS.md`): with `LDH_PLANT_FAULT=1` the zero is
pushed four half-widths past its interval and the counts are put off by one,
and exactly the four recomputation tests fail. Separate tests feed each
checker a faulted input it must reject.

Writing the pins caught one overstatement of mine in sections 8.8 and the
doors below: the four large model misses sit at d/h < 0.123, not "<= 0.12"
(the largest is 0.1223). Corrected in place, same day.

**The slips, corrected in this hunt.** Section 8.1 recorded one slip, y0 =
0.3695261 for the floor pair. Checking the other eight inherited depths
against `hunts/flow_repair/results.json` found **three more of the same
kind**, pairs 2 to 4, in the same table of `hunts/flow_repair/NOTES.md`
section 1. In each row the y0 digits are wrong, while the y0^2/2 column next
to them matches the `results.json` value:

| pair | gamma | NOTES.md y0 (slip) | results.json y0, 7 dp | NOTES y0^2/2 matches |
|---|---|---|---|---|
| 2 | 114.1633 | 0.1508270 | 0.1508301 | 0.1508301 |
| 3 | 166.4793 | 0.0743505 | 0.0743561 | 0.0743561 |
| 4 | 176.7025 | 0.2242763 | 0.2242577 | 0.2242577 |
| 5 | 240.4046 | 0.3695261 | 0.3695306 | 0.3695306 |

**Where the corrections live (revised 2026-10-26 in review).** A first
version of this follow-up also corrected the slip in place, with dated
notes, inside the registered 2026-08-18 text of `MISSION.md` and the
2026-09-12 text of this file. Those in-place edits are reverted, byte for
byte, because `MISSION.md` section 8 and the opening of this section say
that recorded text is not rewritten. The registered sentences therefore
still read 0.3695261, and this table is where each one is corrected:

| registered sentence (as recorded, still reads 0.3695261) | corrected value |
|---|---|
| `MISSION.md` huntspec `frontier:` line: "best measured landing 0.05765184035 at gamma = 240.4046, y0 = 0.3695261" | y0 = 0.3695306 |
| `MISSION.md` section 0 table, row "best measured landing": "`y0 = 0.3695261`" | y0 = 0.3695306 |
| `MISSION.md` section 5.2, C3: "anchored at `y_max(600) = 0.3695261`" | 0.3695306; the C3 table was computed with the old anchor and moves by at most 4e-6 (below) |
| `MISSION.md` section 6, P2, its "For scale" sentence: "`y_max(600) = 0.3695261` today" | 0.3695306. P2's band [0.40, 0.52] is not touched |
| this file, section 4 table, row "240.4046 \| 0.3695261" | 0.3695306 |
| this file, the 2026-09-12 doors, frozen-constant row "the depth-law anchor \| y_max(600) = 0.3695261" | 0.3695306 |

Pairs 2 to 4 appear in no registered sentence of either file; their only
quotation is the slip table above.

Code and data, where the corrected values stay, each with a dated note at
the point of use:
- `theory.py`: the calibration table `NINE` and the stage-6 anchor. This
  changes computed values: a rerun of stage 5 gives mean d/h 1.42519 instead
  of the recorded 1.42844, and stage 6 moves by under 4e-6 (below).
  `theory_results.json` stays as recorded, computed with the old values.
- `landing.py`: `PUBLISHED`. Its y0 is written into the census entries'
  `y0` field as metadata, and `stage_fit` uses it as the depth of any pair
  without a polished value. A future fit run therefore changes with it. No
  recorded artifact came from `stage_fit`, and the recorded census reads
  gamma, not y0.
- `landing.json`: four y0 fields, plus a `corrections_2026_10_26` note.
- `slip_effect.py`: its "recorded" branch now sets the four old values
  explicitly (2026-10-26 in review). It had read them from `theory.NINE`,
  which carries the corrected ones since this follow-up. A rerun would then
  have compared corrected with corrected. `slip_effect.json` was computed
  before `theory.py` changed, and the fixed script reproduces it (Run 22).

**`hunts/flow_repair/NOTES.md` is untouched and still carries all four old
values** (pinned by `test_flow_repair_notes_still_carries_the_old_values`).
It belongs to another hunt. That the registered text still carries the old
value and that this table names each sentence is pinned by
`test_registered_text_keeps_the_slip_and_8_9_points_at_it`.

What the corrections move, measured by `slip_effect.py` / `slip_effect.json`
(recomputing stage 5 and stage 6 with old and corrected values; the
old-value recomputation reproduces `theory_results.json` to 1e-15): the
fitted mean d/h goes from 1.42844 to 1.42519. `DBAR = 1.4284` stays as
registered, because every model number of sections 8.6 to 8.8 was computed
with it. Every stage-6 number (y_max(10^4) and the sup, all four exponents)
moves by less than 4e-6. No verdict changes, and kill condition 5's p = 0.5
branch stays below 36/625 (0.055751). `theory_results.json` is kept as
recorded (computed with the old values), and the difference is in
`slip_effect.json`.

**The per-pair d/h refit** (`refit_dh.py`, `refit_dh.json`, Run 14;
*measured*). This is the door section 8.7 ranked first: feed each pair's
measured d/h to `t_star_gap` in place of DBAR, over all 29 ODE landings.

| model | ODE / model, mean | rms deviation from 1 | range |
|---|---|---|---|
| frozen, DBAR = 1.4284 | 0.907 | 0.160 | 0.527 to 0.997 |
| plug-in, dfac = measured d/h | 1.235 | 0.393 | 0.982 to 2.088 |

**The plug-in is worse**: it overcorrects in 28 of 29 pairs, by up to a
factor 2.09 at the pairs with a line zero almost on top of them. The inverse
asks what dfac reproduces each ODE landing exactly (brentq). It tracks the
measured d/h closely, Pearson r = 0.967, with dfac_inverse = 0.567 +
0.674 d/h (rms residual 0.071, max 0.155). The reading this supports
(measured, one instrument, 29 points) is a mechanism, not a fit. `t_star_gap`
places the local gap symmetrically, a line zero at distance dfac h on *both*
sides of the pair, while a real pair has one close neighbour and a farther
one, so the gap the model needs sits between the two sides rather than at the
near one (slope 0.674 < 1, intercept 0.567 > 0). That reading is a
conjecture about the shape of the correction, untested here: the census rows store only the
nearest line zero, so the two-sided model needs the second-nearest distance,
which `census_1e4.py` computes and discards.


### 8.10 PREREG (written 2026-10-26, before the run): the two-sided local gap

Registered and pushed before `twosided.py` was run; the outcome is appended
below it as section 8.11, whatever it is.

**Model (zero free parameters).** For a pair at height gamma, depth y0, mean
gap h = 2 pi / log(5 gamma / 2 pi): let d_L = gamma - (nearest line zero
below gamma) and d_R = (nearest line zero above gamma) - gamma, from a line
scan of the pair's own accounted window. Then

    S2(y) = sum_{k=0}^{5999} [ 1/((d_L + k h)^2 + y^2) + 1/((d_R + k h)^2 + y^2) ],
    t*_2  = int_0^{y0} y dy / (1 + 2 y^2 S2(y)),

which is `theory.t_star_gap` exactly when d_L = d_R = DBAR h. One of d_L,
d_R is the nearest line zero, and the other is the nearest on the other side.
That other one is the second-nearest overall unless two line zeros sit on the
same side closer than any on the other. How often that happens is recorded,
and it does not change the model.

**Data.** The 29 accounted, landed windows: 21 in `census_1e4.json` and 8 in
`census_deep4_1e5.json`. The window at gamma = 88167.40 is excluded because
its accounting is open. Line zeros come from `census_1e4.line_zeros` (grid
1/60 mean gap, 30 bisections) on [gamma - 4h, gamma + 4h].

**Gate (fixed in advance).** For every window, min(d_L, d_R) / h must
reproduce the census's recorded `gap_ratio_d_over_h` to within 1e-4.
Otherwise the run is void and nothing is graded.

**Metric.** rms over the 29 of (ODE t* / t*_2 - 1), on the same footing as
section 8.9's frozen-DBAR 0.160 and one-sided plug-in 0.393, with the same
ODE landings and the same integral.

**Pass/fail rule (fixed in advance).**

- **PASS:** rms <= 0.080 (half the frozen value) *and* every one of the 29
  ratios in [0.85, 1.25] (P3's band).
- **IMPROVES, does not pass:** rms < 0.160 but not PASS.
- **FAIL:** rms >= 0.160.

A PASS supports, at measured grade, the reading that the gap correction is
two-sided. It is not a theorem and says nothing about pairs near Delta,
which no window here reaches. A FAIL refutes this form of it
(ALIGNMENT section 5, disposition 1, at these 29 windows).


### 8.11 Outcome of the 8.10 PREREG: IMPROVES, does not pass

`twosided.py`, `twosided.json`, Run 15 in `RUNS.md`; *measured*.

**Gate: clean.** min(d_L, d_R)/h reproduces the census's recorded d/h in all
29 windows, max defect 1.3e-11. **Verdict under the pre-registered rule:
IMPROVES.** rms 0.112, below the frozen 0.160 but above the pass bar 0.080.
26 of 29 ratios are in [0.85, 1.25], against 25 of 29 for the frozen model.
Ratio range 0.981 to 1.339, mean 1.066. In one window the second-nearest line
zero sits on the same side as the nearest.

| model | rms | ratios in [0.85, 1.25] | range |
|---|---|---|---|
| frozen, DBAR h on both sides | 0.160 | 25 of 29 | 0.527 to 0.997 |
| one-sided plug-in, d/h on both sides | 0.393 | 22 of 29 | 0.982 to 2.088 |
| **two-sided, d_L and d_R** | **0.112** | **26 of 29** | **0.981 to 1.339** |

The three misses are the three near-collision windows, gamma = 4935.62,
49688.34 and 77163.41, each with a line zero at d/h < 0.123 (0.101, 0.122,
0.045). The fourth such window, 74189.64 at d/h = 0.008, lands at 1.173, just
inside the band. The sign flipped: the frozen model over-predicted these
landings by up to a factor 1.9, and the two-sided model under-predicts them by
up to a factor 1.34. A line zero that close is pushed away as the pair falls,
and both models hold it fixed. This is the frozen-neighbour bias `MISSION.md`
section 4.7 measured on polynomials, now seen in F at measured grade. The
fit everywhere else is tight: excluding the four near-collision windows
(not a pre-registered cut, reported only as a description), all 25 ratios
lie in [0.981, 1.11].

What it settles: the gap correction is two-sided (the one-sided plug-in is
refuted, section 8.9, and the two-sided form improves on the frozen DBAR
with zero free parameters). What it does not settle: the pre-registered PASS
bar, which this form misses because of moving neighbours. Disposition: the
two-sided frozen-neighbour model is **refuted as a sub-0.08 description at
these 29 windows** (disposition 1, measured). The two-sided mechanism with
moving neighbours is **unresolved** (disposition 3). It needs the
neighbour's own motion, which the ODE has and this model does not.


### 8.12 PREREG (written 2026-10-26, before any trigger): the census over [10^4, 10^5]

Registered before `RUN_REQUEST.json` exists. The run is
`.github/workflows/lambda-dh-census.yml` driving `census_shard.py` over the
36 shards of `census_plan_1e5.json` (sha256 461079f9...26eaa9). Each shard
screens at Re s = 0.82, locates, and lands every zero with y0 > 0.3396 with
the section 8.6 instrument. Results will be appended as a new section,
whatever they are.

**What it decides** (all *measured*; coverage: zeros with beta > 0.82 that
the float screen sees, landed if y0 > 0.3396):

1. **The floor in this decade.** Does any landed pair exceed
   0.0576518 x 1.0004 (the instrument band)? *Yes* raises the measured floor
   and names the pair. *No* means no pair in [10^4, 10^5] with
   y0 > 0.3396 beats it.
2. **Kill condition 4.** Let m4 be the largest landing in [10^4, 10^5],
   against m2 = 0.05767 ([10^2, 10^3]) and m3 = 0.05586 ([10^3, 10^4]). The
   registered text asks for a rise "over at least two decades", and m2 > m3
   already, so the only rise these decades can show is across [10^3, 10^5].
   Fixed reading: **KC4 fires iff m4 > m3**, and m4 > m2 is reported
   separately. Otherwise KC4 does not fire up to 10^5.
3. **P5 as registered.** P5 *holds up to 10^5* iff the largest measured
   landing below 10^5 has height in [10^3, 10^5] and depth in [0.40, 0.52].
   Otherwise it is *refuted up to 10^5*. Beyond 10^5 it stays unresolved.
4. **P8.** The count of pairs landing later than y0^2/2. More than 15
   percent would widen P1's band (as registered).
5. **The two-sided model, out of sample.** rms of (ODE / t*_2 - 1) over the
   new windows (excluding the 29 of section 8.11), against the in-sample
   0.112. Expectation registered here: rms < 0.160, the IMPROVES class.
   Its failure would undo section 8.11's reading.

**Kill conditions for the run itself:**

- *K-a*: preflight fails (pins, plan hash, smoke row): nothing runs, and
  nothing is read.
- *K-b*: a shard is missing or its screen incomplete at merge: no
  decade-wide statement. Per-shard results are reported as such.
- *K-c*: more than 10 percent of candidate windows unaccounted: statement 1
  is not made, and the unaccounted windows are listed.
- *K-d*: replication. The eight pairs already landed in
  `census_deep4_1e5.json` are landed again. If any differs by more than 1e-6
  relative, the census is void as instrument drift. Measured locally: the
  re-landing of gamma = 24415.48 differs by 6e-14.
- *K-e*: the calibration projects more than 30 core-hours: stop and re-ask
  before `full`.


### 8.13 Outcome of the 8.12 PREREG: the census is void (K-d)

Run 17 in `RUNS.md`. The run is GitHub Actions run 40360558359, mode full,
36 of 36 shards, merge success. Its output is
`census_runs/full_r1/census_1e5.json`, sha256 84e8ec88...31af72, equal to
the merge job's printed hash, in an artifact zip whose digest matches.
`evaluate_census.py` applies section 8.12 as written and writes
`census_runs/full_r1/evaluation.json`.

**Kill conditions of the run:**

| | condition | outcome |
|---|---|---|
| K-a | preflight | passed on all 9 jobs (smoke landing exact) |
| K-b | every shard present and complete | passed (36 of 36) |
| K-c | unaccounted windows <= 10 percent | passed (1 of 162, γ = 88167.40 again) |
| **K-d** | **the 8 targeted landings replicate to 1e-6** | **fails**: 7 replicate to <= 3e-12; γ = 20011.16 is absent |
| K-e | <= 30 core-hours | passed (11.05 core-hours; projected 9.95) |

**By K-d the census is void**, so none of the five measured items is stated
as a verdict. The computed values, all voided, are kept for the record:
- no landing above the floor band;
- m4 = 0.04877 at γ = 24415.48 (KC4 would not fire);
- the largest landing below 10^5 is still at height 240 (P5 would be
  refuted up to 10^5);
- 0 of 161 later than y0^2/2;
- the two-sided model out of sample: rms 0.158 over 154 windows, 126 in
  band. That is under the 0.160 expectation but well above the in-sample
  0.112.

**Why K-d fired: an instrument defect, found by the kill condition built to
find it.** The census's first window at γ = 20011.16, [20000, 20020], was
correctly flagged with one zero at β > 0.82. `deep_zeros.stage_locate`
then accepted a root at γ = 20017.93 with β = 0.727, outside the counted
box, because its acceptance test checks height only. **16 of the 282
located census zeros are mislocated this way**
(`census_runs/full_r1/mislocated.json`). A constrained search on each window
(`relocate_missed.py`, `relocated.json`, measured) finds exactly one root
inside the box in all of them. 8 of the 16 have y0 > 0.3396, so they were
census candidates that were never landed; the deepest is γ = 20011.16 at
y0 = 0.4002. The 162 census rows therefore cover 162 of about 170
candidates.

**Correction to section 8.3 (and Run 9), recorded here.** The completed 0.85
`screen_hi` has the same defect once. Window [16620, 16640] lists a root at
γ = 16637.67 with β = 0.7132, and its true zero is γ = 16620.38 with
y0 = 0.3742 (measured). The count of 111 zeros with β > 0.85 in
[10^4, 10^5] stands. The list of 111 has one wrong entry. Every claim
that read the list is unaffected:
- the deepest is still 0.437058;
- the per-decade-tenth maximum for [10^4, 2 x 10^4] is still 0.3906, above 0.3742;
- the nine zeros with y0 > 0.40, and hence section 8.8's selection, are unchanged.

The low screen below 10^4 is clean: none of its 21 roots lies outside its
box, and all 21 are decided (section 8.3).

**What is left open by it.** The decade's census needs a locate step that
rejects roots outside the counted box. It also needs the 8 missed candidates
landed, or the full run repeated with that guard. Both need a new request,
which is the coordinator's decision (they asked to be told before any
re-request). The kill condition did its job: a census that had read only its
own landings would have reported "no pair beats the floor" over a list
missing 8 candidates.


### 8.14 Unit 4 (2026-10-26): the locate guard, the audit, the window at 88167.40

**The guard.** `deep_zeros.stage_locate` now accepts a root only inside the
box its count was taken on: SIGMA_C < beta < SIGMA_R, and inside the part's
t-range. A refused root triggers a search constrained to the box
(`locate_part`, `locate_in_box`). A part that counts n zeros now gets n,
where the old code took the first and stopped. A shortfall is written to an
`unlocated` list instead of vanishing. Tests (section 9 of the test module):
- a planted out-of-box start is refused and relocated;
- the three lowest of the 17 known windows (fast tier) and all 17 (slow tier)
  give in-box roots equal to `relocated.json`'s;
- with the guard switched off under `LDH_PLANT_FAULT=1`, they fail.

**The audit, dated corrections.** Every result that consumed located roots
was re-located under the guard, from scratch copies of the recorded screens
with the roots stripped (`census_runs/audit_u4/guarded_locate.json`,
Run 19; measured):

| screen | recorded roots | under the guard | change |
|---|---|---|---|
| low, [8, 10^4] at 0.85 | 21 | 21, bit-identical, none refused | **none** |
| `screen_hi`, [10^4, 10^5] at 0.85 | 111 | 110 bit-identical; 16637.67 (beta 0.7132) refused, replaced by **16620.3825, y0 0.3742** | **one root**, as 8.13 already recorded |
| 10^6, [1000000, 1001200] at 0.85 | 1 | 1, within 1.3e-13 | **none** |

The 0.55 and 0.75 control screens and `deep_zeros.json` hold no located
roots.

**Claims that do not change, stated explicitly:**
- every decided enclosure (8.2, 8.3, 8.5);
- the census below 10^4, its 21 landings and every verdict of 8.7;
- the 10^6 zero;
- the count of 111 at beta > 0.85 in [10^4, 10^5], its maximum y0 0.437058,
  its per-decade-tenth maxima, and its nine zeros with y0 > 0.40, hence the
  targeted check of 8.8;
- the two-sided model's 29 windows (8.11), which come from the decided low
  zeros and the targeted pairs.

**Claim that changes:** 8.3's list of 111 has one corrected entry, as
recorded in 8.13.

**Window gamma = 88167.40: resolved, and the fix rides in attempt 2.**
Diagnosis (Run 20, about 0.3 core-hours of the 1 core-hour cap):
- strip 142, line 128, and 6 zeros counted at beta > 0.505, so 2 zeros were
  unaccounted;
- a count at beta > 0.5005 (and at 0.501 and 0.502) gives **7**, so the
  missing pair is near the line, not two missed line zeros;
- isolated by bisection and located at **gamma = 88132.180, beta = 0.50479
  (y0 = 0.0048)**, |f| = 4e-11, just under the old 0.505 edge. A pair that
  shallow makes no sign change on the line.

**Fix** (`census_1e4.census_one`): when a window's accounting fails after the
refined line scan, it recounts at beta > 0.5005 and searches with grid rows
just right of it. Windows whose accounting closes on the first try, which is
every other window so far including the smoke row, never reach the fallback
and are unchanged. Re-landed under the fix, the window closes
(142 = 128 + 2 x 7), all 7 off-line zeros are located, and the pair at
88167.40 lands at **0.04012** (shave 51.6 percent; measured,
`census_runs/audit_u4/w88167_relanded.json`). That is not a census result;
attempt 2 measures it afresh.

**Attempt 2.** Same plan, same plan_sha256, the 8.12 text unchanged, and
evaluated mechanically on attempt 2 alone. Attempt 1 stays void, with its
values recorded in 8.13.


### 8.15 Outcome of the 8.12 PREREG, attempt 2 (guarded code): valid

Run 21 in `RUNS.md`. GitHub Actions run 40379449770, request attempt 2,
commit 912d89a75, same plan (sha256 461079f9...26eaa9) and the 8.12 text
unchanged. 36 of 36 shards, merge success. The output is
`census_runs/full_r2/census_1e5.json`, sha256 3787b389...645d643e, equal to
the merge job's printed hash, in an artifact zip whose digest matches.
`evaluate_census.py` was run on attempt 2 alone, giving
`census_runs/full_r2/evaluation.json`.

**Kill conditions of the run, attempt 1 beside attempt 2:**

| | condition | attempt 1 (8.13) | attempt 2 |
|---|---|---|---|
| K-a | preflight | passed | passed (smoke landing exact) |
| K-b | 36 shards present and complete | passed | passed |
| K-c | unaccounted <= 10 percent | passed (1 of 162) | passed (**0 of 170**; 88167.40 closed by the fallback) |
| K-d | the 8 targeted landings replicate to 1e-6 | **failed** (20011.16 missing) | **passed** (all 8, max 2.8e-12) |
| K-e | <= 30 core-hours | passed (11.05) | passed (**13.16**; projected 12.0) |

Reported beside K-c (not part of 8.12's text): 0 unlocated windows; 16
roots refused and relocated by the guard, the 16 known ones; 1 window
closed on the 0.5005 accounting fallback.

**The five items, attempt 2 beside attempt 1.** Every verdict is
*measured*. The coverage is zeros with beta > 0.82 that the float screen
sees in [10^4, 10^5], landed if y0 > 0.3396: 170 pairs, all accounted and
all landed.

| item | attempt 1 | attempt 2 verdict |
|---|---|---|
| 1. the floor in this decade | void | **no pair with y0 > 0.3396 in [10^4, 10^5] lands above 0.0576518 x 1.0004.** The largest landing is 0.04902 (γ = 20011.16, y0 0.4002). No landing exceeds 0.9 x the floor. Shaves run from 29.9 to 71.0 percent. |
| 2. KC4 (fires iff m4 > m3 = 0.05586) | void | **does not fire up to 10^5.** m4 = 0.04902 < m3 < m2 = 0.05767, so the measured per-decade maxima fall over three decades. |
| 3. P5 up to 10^5 | void | **refuted up to 10^5** (ALIGNMENT section 5, disposition 1, within that range). The largest measured landing below 10^5 is at height 240, depth 0.3695, outside both of P5's ranges. Beyond 10^5 it is unresolved. *Scope, stated 2026-10-26 in review:* "below 10^5" means the pairs this lab has landed there: y0 > 0.35 below 10^4, y0 > 0.3396 in [10^4, 10^5], as far as the float screens see them, plus `flow_repair`'s nine below 600; every landing is measured (ODE). *A stronger reading at the same grade:* P5 puts the maximizing pair at any height inside height [10^3, 10^5] and depth [0.40, 0.52]. No zero below 10^4 has y0 >= 0.40 (decided, Arb, section 8.5), and all 9 pairs with y0 >= 0.40 that the 0.82 screen sees in [10^4, 10^5] are landed, the largest at 0.04902, below the γ = 240 pair. So no pair of P5's region is the maximizer, wherever the maximum lies, and P5 as registered is refuted, not only up to 10^5. That reading's scope: completeness of the [10^4, 10^5] screen at y0 >= 0.40 (measured) and the ODE landings (measured). A pair of the region that the screen missed would reopen it. |
| 4. P8 | void | **not observed** within P8's registered scope, pairs below 10^4: 0 of 21 (section 8.6), measured. The census above 10^4 lies outside that scope; there, 0 of 170 land later than y0^2/2, a description only. (Restricted 2026-10-26 in review; it read "0 of 170 land later than y0^2/2. With the 21 below 10^4, that is 0 of 191 census landings.") |
| 5. the two-sided model, out of sample | void | **expectation met**: rms 0.154 < 0.160 over 162 new windows, 134 in [0.85, 1.25]. It is well above the in-sample 0.112, so most of section 8.11's improvement does not carry out of sample. Recorded as met, as registered, and not re-read. |

**Attempt 2 against attempt 1, as a consistency check** (not part of the
evaluation): attempt 2 contains all 161 of attempt 1's landings, agreeing to
2e-12 relative. It adds exactly 9 windows: the 8 candidates the mislocation
had dropped (15442.11, 16620.38, 20011.16, 54447.38, 65942.07, 74280.37,
86726.64, 90724.37) and the formerly open 88167.40. The latter lands at
0.0401154, equal to the local re-landing of 8.14 to 1e-14. The void
attempt 1 stays recorded as it was, and nothing here was spliced onto it.

**What the hunt is now entitled to say, in addition to section 8.7:**
- no pair below height 10^5 that this lab has landed lands above the
  measured floor 0.0576518 (measured; coverage y0 > 0.35 below 10^4 and
  y0 > 0.3396 above). The closest is gamma = 2442.53 at 0.05586, 3.1
  percent under, and nothing in [10^4, 10^5] comes within 10 percent;
- the measured sup of landings peaks below 10^3 and falls over the next two
  decades (measured);
- P5 is refuted up to 10^5, and KC4 does not fire up to 10^5 (measured,
  coverage as in item 3 of the table above; item 3 also states the stronger
  reading of P5 and its scope).

Hunt #61's bracket is unchanged in every digit. Nothing here is evidence
about the Riemann Hypothesis (P9; `docs/08`).

### 8.16 Review corrections (2026-10-26)

An adversarial review of PR #357 found no defect in any decided count or
any verdict. It did find defects in how the decided results were quoted and
cross-checked, and in the record's own bookkeeping. The operator's rulings
were applied as follows. **No verdict and no grade moves.** One computation
was rerun (Run 22).

1. **Decided intervals, requoted rounded outward.** The decimal renderings
   of decided intervals had been rounded to nearest, so every one was
   narrower than its exact interval on at least one side. As printed they
   were not enclosures: 21 of 21 rows of the 8.3 table, the depth and both
   coordinates in 8.2, the floor pair in 8.1, the 2442.53 depth in 8.4, the
   P2 row of 8.7 (0.39775015 for 0.39775014...), and the case log in
   `hunts/README.md`. All are now rounded outward. The dyadic endpoints in
   the artifacts were always exact and are unchanged.
   `test_quoted_decided_intervals_contain_the_artifact_intervals` parses
   every quoted interval and checks that it contains the artifact's exact
   interval. Under `LDH_PLANT_FAULT=1` it plants one inward digit and goes
   red.
2. **The Arb-versus-iv cross-check, rerun on exact endpoints** (section 8.2,
   Run 22). The recorded check compared float64 midpoints and could not fail
   on the property it named. On exact endpoints with no slack the enclosures
   intersect at all three recorded points. The test reads the exact
   endpoints and recomputes the intersection, and a planted shift of one
   enclosure by twice its width turns it red. A sentence that the routes
   "agree with mpmath to 1e-33 at height 1000" is withdrawn: nothing in the
   tree backed it. The independence sentence of 8.2 now names the shared
   counting driver `count_zeros`.
3. **Registered text restored.** The in-place slip corrections inside
   `MISSION.md`'s 2026-08-18 text and this file's 2026-09-12 text are
   reverted byte for byte. Section 8.9 now holds the correction for each
   sentence, with the sentence quoted. `slip_effect.py` was fixed so that it
   reproduces `slip_effect.json` again (section 8.9, Run 22).
4. **Workflow scope.** `.github/workflows/lambda-dh-census.yml` stays. Its
   authorization and a dated scope amendment are appended to `MISSION.md`
   section 8 and `RUNS.md`. The two `RUNS.md` statements it made false are
   kept, each followed by a dated correction.
5. **Labels.**
   - P4 is *unresolved, evidence against* (8.7), since its antecedent, a
     complete census to 10^4, was not run.
   - P5's verdict in 8.15 now states its coverage, and also a stronger
     reading at the same measured grade, with that reading's exact scope.
   - P8 is restricted to its registered scope, pairs below 10^4: 0 of 21
     (8.8, 8.15 and the doors). The pairs above 10^4 are a description only.
   - "decided" for the census is now "measured" in 8.13 and in the doors.
     The heading "What it decides" in the 8.12 PREREG is left as
     registered. Its own parenthesis says "all *measured*", and 8.14 and
     8.15 state that the 8.12 text is unchanged, so the word reads "settles,
     at measured grade".
6. **The Euler-Maclaurin remainder constant.** The code sums through
   k = p - 1. The remainder of that truncation is bounded with
   C_p = 4 (1 - 2^{-2p}) zeta(2p), about 4 (1 + 3^{-2p}). The text had cited
   2 zeta(2p), which applies when the k = p term is included. The code's
   constant 4 falls short of C_p by under 1e-279 relative at p = 293, and
   the 2^-50 fudge every bound passes through covers that, so every
   enclosure stands. Corrected in the `decide_deep_zero.py` docstring and
   `MISSION.md` section 8, and pinned by
   `test_em_remainder_constant_is_covered_by_the_fudge`.
7. **Two known limits of the census evaluation, recorded and not changed.**
   - A pair with no ODE crossing by t_end = 1.25 y0^2/2 gets
     `beats_floor` False, and `evaluate_census.py` drops it from the landed
     rows, although such a pair lands above the floor.
   - Unlocated windows enter no kill condition.

   Neither occurred: 170 of 170 landed, 0 unlocated. Both are commented at
   the point of use and pinned by tests that show the behaviour and its
   absence from the recorded runs.
8. **Smaller fixes.**
   - The count's docstring described the segment-ball test that Run 7
     replaced.
   - The steering route was mislabelled "mpmath Hurwitz zeta". It is Arb
     midpoints: fixed in the code, with a note in the artifact.
   - The stale line in `decide_kc2.py`.
   - The left-edge door in the doors below needs Re s = 987086726043 / 2^40,
     not 0.8978.
   - 8.1's "left as recorded" now carries a dated note.
   - The reversed sentences of the case log now carry dates.
   - 8.5 now states the two elementary steps, conjugate symmetry and
     Re s > 2.05, that complete "|t| <= 10^4".

Left as they are, and why:
- The mpmath.iv route never ran the perturbed-kappa planted fault that the
  `MISSION.md` section 8 gate names (only the shifted rectangle). Closing
  that costs one more iv head, about 6 minutes.
- The census's per-window screen outputs live only in the Actions artifacts,
  which expire. The merged rows and their sha256 are committed.
- `landing.json` keeps its four hand-corrected y0 fields and its
  `corrections_2026_10_26` note (section 8.9). Whether a recorded artifact
  should be corrected in place is the operator's call.

### The doors (updated 2026-10-26)

The 2026-09-12 doors above stand as written; this is what changed in them.

**Active constraints at the optimum.** The ceiling the hunt reports is still
the model's, and its first-ranked constraint, the exponent p, is gone rather
than binding: kill condition 2 withdrew the stage-6 law it lived in, and the
data put y_max at or below the p = 0.5 curve (0.3978 against its 0.4125 at
10^4, 0.4371 against 0.4349 at 10^5), the branch kill condition 5 excludes.
What binds the *measured* sup of landings below 10^4 is now the shave, ranked
by the census: 15.5 to 55.8 percent at y0 in (0.35, 0.40), growing with
height at fixed depth (the γ = 240 pair is shaved 15.5 percent, pairs of
like depth between 4200 and 6200 by 29 to 36, one at 55.8). Second, the local gap d/h: the one
quantity that moves a single landing by a factor 1.6 (γ = 4935.6), and the
one the model froze at its mean.

**The frozen-constant inventory**, the resumption's own:

| frozen | value | where | what relaxing it trades |
|---|---|---|---|
| decided-count left edge | Re s = 0.90 | `decide_kc2.py` | Pushing it to Re s = 987086726043 / 2^40 (about 0.8977501475, the left side of the decided rectangle at γ = 2442.53), with a count of exactly 1, would decide the deepest zero below 10^4 as the maximum outright, at about 2 core-hours more, and buys only a sentence P2 does not need. Genuine trade shape: no. (Corrected 2026-10-26 in review: it read "Pushing it to 0.8978", which would leave y0 in (0.3977501625, 0.3978) undecided.) |
| candidate depth for landing | y0 > 0.35 (the 0.85 screen) | `census_1e4.py` | Screening at 0.84 closes the (0.3396, 0.35] coverage gap at about 0.5 core-hours. It can only add pairs that need a shave under 5.9 percent. |
| census half-window | 40 | `census_1e4.py` | The ODE tail term was 0.6 percent of the mirror term at γ = 240. A wider window costs O(n^2) and is expected to move landings by less than the 0.04 percent band. |
| rectangle half-width (decided zeros) | 2^-27 | `decide_*.py` | Pure resolution, margins 1420x to 174151x. Nothing trades. |
| ODE steps | 800 RK4 to 1.25 y0^2/2 | inherited | Inherited from the validated instrument; not re-tuned. |

**The information class of each door.** *Inside the current data:* re-reading
the 29 landings against a per-pair model (feeding each pair's measured d/h to
`t_star_gap` instead of DBAR) costs nothing new and says whether the model's
failures are all the local gap. *Requires reading more:* the 10^5 leg, and in
it the nine pairs with y0 > 0.40 in [10^4, 10^5] (`deep_zeros_hi_20261026.json`;
deepest 0.437 at γ = 49688.34, model landing 0.0524, the highest model
landing in that decade), which were the cheapest test of P5 and kill condition 4 and
have now been landed (section 8.8, none near the floor); the full 10^5
census (about 15 core-hours) for the 102 shallower pairs; and any decided
landing, which needs the Xi-plane route, out of reach above about 10^3 on
this box. After section 8.8 the door with the most left in it was inside the
current data: refit the shave model with each pair's measured d/h in place of
DBAR. All 29 landings (21 + 8) already carry it, the model's four large
misses (ODE / model under 0.7) all sit at d/h < 0.123, and it is the step that decides whether a
model of this family can say anything about pairs near Delta. *Walked
through 2026-10-26 (section 8.9):* the one-sided plug-in fails (rms 0.393
against 0.160), and the inverse says the gap the model needs is two-sided.
The next door is the two-sided local gap, nearest and second-nearest line
zero, which needs only a re-scan of the 29 windows already accounted (inside
data the census reads, about 0.1 core-hours; the line-zero lists were
computed and not stored).

**Unit 3 update (2026-10-26).** The two-sided local gap was walked through
(sections 8.10 and 8.11). It improves on the frozen model, but the misses are
neighbours that move. The door after it is a moving-neighbour gap, which
needs the neighbour's own drift from the ODE (inside data the census
reads). The census over [10^4, 10^5] is prepared (section 8.12, workflow and
shard plan), not triggered.

**Every still-open item, with its ALIGNMENT section 5 disposition:**

| item | state | disposition |
|---|---|---|
| The hunt's question: does the bracket collapse to Delta^2/2? | no landing anywhere near Delta^2/2 = 0.1924; the best is 0.0577 | 3, unresolved |
| P1, weak form (sup t* < 0.14432) | untouched; no landing above 0.058 | 3, unresolved |
| P1, stronger band [0.058, 0.075] | derivation withdrawn by KC2 | 3, unresolved |
| P5 | measured maximum at height 240, outside its window | 3, unresolved (to be settled up to 10^5, at measured grade, by the census of 8.12; it read "decided up to 10^5", corrected 2026-10-26 in review) |
| P7 / KC3, no creation | 400 samples, not proved; not touched this wave | 3, unresolved |
| P8 | 0 of 21 below 10^4, its registered scope (the 8 landed above 10^4 lie outside it; it read "0 of 29", restricted 2026-10-26 in review) | 3, unresolved (shallower pairs below 10^4 not landed) |
| KC4 | does not fire on what was measured | 4, paused by allocation until the census runs |
| census over [10^4, 10^5] | prepared, not triggered | 4, paused by allocation (awaiting 'go') |
| window gamma = 88167.40 | accounting open | 4, paused; the census re-scans it |
| below 10^4, y0 in (0.3396, 0.35] not landed | needs a shave under 5.9 percent; measured minimum 15.5 | 4, paused by allocation (about 0.5 core-hours) |
| moving-neighbour gap model | the next door | 3, unresolved |
| two-sided frozen-neighbour model as a sub-0.08 description | rms 0.112 > 0.080 | 1, refuted at these 29 windows |
| second backend for the KC2 count | about 120 core-hours of iv | 4, paused by allocation |
| decided landing times | Xi-plane route out of reach above about 10^3 on this box | 4, paused by allocation (no theorem obstructs it) |
| depth near 10^6 below y0 = 0.35 | the 0.85 screen cannot see it | 4, paused by allocation |

No item is *obstructed* (disposition 2): nothing here is ruled out by a
theorem.

**Census update (2026-10-26, after run 40360558359).** The census ran and is
void by K-d (section 8.13). Rows of the table above that change: *census
over [10^4, 10^5]* becomes "ran, void by K-d; a guarded re-request awaits
the coordinator", disposition 4 (paused by allocation). *KC4* and *P5*
stay as they were: void computations are no evidence, though both voided
values lean the same way as the measured data below 10^4. *Window
γ = 88167.40* stays open (unaccounted again). New row: *`stage_locate`
accepts roots outside the counted box*, an instrument defect, measured on
17 windows. Repair: a beta > sigma_c guard plus the constrained search of
`relocate_missed.py`. Disposition 4, paused until the re-request. The
cheapest next door is a guarded re-request of the 8 missed candidates
(about 1 core-hour on Actions); a full guarded re-run costs about 11.

**Unit 4 update (2026-10-26, after attempt 2).** The guarded census ran
valid (section 8.15). The rows of the dispositions table that change:

| item | state after attempt 2 | disposition |
|---|---|---|
| census over [10^4, 10^5] | ran valid; 170 of 170 accounted and landed | closed (its verdicts are in 8.15) |
| P5 | refuted up to 10^5; beyond, unresolved (measured, coverage as in 8.15 item 3; that item also states the stronger reading, refuted at any height at measured grade, with its scope) | 1, refuted within [0, 10^5]; 3 beyond |
| KC4 | does not fire up to 10^5 | closed up to 10^5; 3, unresolved beyond |
| P8 | 0 of 21 below 10^4, its registered scope; 0 of 170 above 10^4 is a description outside it (it read "0 of 191 census landings", restricted 2026-10-26 in review) | 3, unresolved (shallower pairs not landed) |
| window γ = 88167.40 | closed by the 0.5005 fallback; landed 0.0401 | closed |
| `stage_locate` accepting out-of-box roots | repaired (box guard), tested, audited | closed |
| two-sided frozen-neighbour model | out of sample rms 0.154, in sample 0.112 | 1 as a sub-0.08 description (unchanged); the improvement over the frozen model is mostly in-sample |
| moving-neighbour gap model | the next door | 3, unresolved |
| census above 10^5 | not estimated; the 10^6 exhaustive census is out of scope | 4, paused by allocation |

Unchanged: the hunt's question, P1 (both forms), P7 / KC3, the second
backend for the KC2 count, decided landing times, the depth near 10^6, and
the band y0 in (0.3396, 0.35] below 10^4. Each keeps its disposition from the
unit 3 table. Nothing is obstructed (disposition 2).

**The doors after attempt 2, in brief.** *Active constraints:* the shave.
Between 10^4 and 10^5 it is 29.9 to 71 percent, and it grows with height at
fixed depth, so every landing in the decade sits below 0.9 x the floor. The
deepest pair located below 10^5 (y0 = 0.437) lands at 0.0348. Depth does
grow with height, but crowding takes more than it gives. *Frozen constants
that now bind:* the census depth cut y0 > 0.3396, since a pair below it
would need a shave under 6 percent, against a decade minimum of 29.9; and
the accounting fallback edge 0.5005, since a pair at beta < 0.5005 would
still go uncounted. *Information class:* closing the ceiling question past
10^5 needs reading more (a census above 10^5 or decided landings). The
moving-neighbour model is inside the data the census already holds. It is
the cheapest door, and the one that says whether any model of this family
can extrapolate to depths near Delta.

