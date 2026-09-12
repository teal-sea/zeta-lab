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
