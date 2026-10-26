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
   [0.3695305722, 0.3695305871]. The slip is 4.5e-6 in y0, 1.2e-5 relative.
   It moves the stage-6 anchor c_p by about that much and changes no number
   this hunt reports at the digits it reports them. `theory.py` and its
   results are left as recorded, not re-run.

### 8.2 Step 1: the height-10^6 zero is decided

`decide_deep_zero.py`, `decide_deep_zero.json`, Run 7 in `RUNS.md`.

**Decided on both backends: f has exactly one zero, counted with
multiplicity, in the exact rectangle**

    sigma in [943723861105, 943723877489] / 2^40 = [0.8583118516, 0.8583118665]
    t     in [537117734833355, 537117734833363] / 2^29 = [1000459.74335327, 1000459.74335328]

so its depth is **y0 in [0.3583118516, 0.3583118665]**, the rectangle lies
wholly in Re s > 1/2, and the 2026-08-18 float location (beta
0.8583118590734415, gamma 1000459.7433532759) is inside it. The row in
section 2 moves from float grade to decided. Its by-symmetry partner at
1 - beta needs no separate count (F(s) = F(1 - s), conjugate-symmetric
coefficients).

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
and no evaluator, rounding code or error bound. Their enclosures of f
intersect at two corners and the centre (radii 7e-33 Arb, 5e-31 iv), and they
agree with mpmath to 1e-33 at height 1000.

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

| gamma | y0 enclosure (both backends) |
|---|---|
| 240.4047 | [0.3695305722, 0.3695305871] |
| 783.6530 | [0.3530014427, 0.3530014576] |
| 857.2959 | [0.3561094084, 0.3561094233] |
| 1092.4545 | [0.3546296115, 0.3546296264] |
| **2442.5303** | **[0.3977501475, 0.3977501624]** |
| 2887.9392 | [0.3604422750, 0.3604422899] |
| 3059.5187 | [0.3678568616, 0.3678568765] |
| 3214.1444 | [0.3612643316, 0.3612643465] |
| 3294.6092 | [0.3603604983, 0.3603605132] |
| 4237.9692 | [0.3576562361, 0.3576562510] |
| 4392.3764 | [0.3535286436, 0.3535286585] |
| 4935.6178 | [0.3551060613, 0.3551060762] |
| 5090.3177 | [0.3663990727, 0.3663990876] |
| 5833.2823 | [0.3740914934, 0.3740915083] |
| 5913.7059 | [0.3594353089, 0.3594353238] |
| 6113.9288 | [0.3581936447, 0.3581936596] |
| 7011.5119 | [0.3662883174, 0.3662883323] |
| 7909.4450 | [0.3545747216, 0.3545747365] |
| 8235.5925 | [0.3753363089, 0.3753363238] |
| 8561.5942 | [0.3836407511, 0.3836407660] |
| 9694.5786 | [0.3516309903, 0.3516310052] |

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
depth y0 in [0.3977501475, 0.3977501624], at gamma = 2442.53. **P2 is
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
[0.89 or 0.90, 2.05] x [2400, 2500] returning 1 and 0 as they must. So the
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
| P2 | y_max(10^4) in [0.40, 0.52] | y_max(10^4) in [0.39775015, 0.40) | **refuted**, decided (Arb), section 8.5 |
| P3 | the deepest pair below 10^4 lands within [0.85, 1.25] x model | 2442.53: ODE / model = 0.986 | **holds**, measured. Its registered point (0.061084 at (0.45, 10^4)) is at the wrong depth: the deepest pair is at 0.3978 |
| P4 | a complete census to 10^4 *raises* the best landing to [0.055, 0.079], point 0.061 | not raised; best stays 0.05765 | **refuted** in its "raises" clause, measured, coverage y0 > 0.35. The band contains the old value trivially. Derived from stage 6, already withdrawn by kill condition 2 |
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
and 21 below 10^4 are decided; P2 and P6 are refuted, P2 at decided grade;
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
three pairs with ratios under 0.7 all have a line zero within d/h <= 0.12,
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
- *P8* (a pair landing later than its own y0^2/2): 0 of 8 here as well,
  0 of 29 over sections 8.6 and 8.8. Not observed, measured.

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
| decided-count left edge | Re s = 0.90 | `decide_kc2.py` | Pushing it to 0.8978 would decide the deepest zero below 10^4 as the maximum outright, at about 2 core-hours more, and buys only a sentence P2 does not need. Genuine trade shape: no. |
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
this box. After section 8.8 the door with the most left in it is inside the
current data: refit the shave model with each pair's measured d/h in place of
DBAR. All 29 landings (21 + 8) already carry it, the model's four large
misses (ODE / model under 0.7) all sit at d/h <= 0.122, and it is the step that decides whether a
model of this family can say anything about pairs near Delta.
