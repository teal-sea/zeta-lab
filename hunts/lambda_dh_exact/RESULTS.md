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
predicts. **Two points are not a trend.** The second screen covers 1200 units
of height at one place on the line, it is one zero rather than a supremum over
a decade, and prediction 4 in `MISSION.md` asks for a fitted exponent that
nobody fitted. Read this row as consistency, not as evidence.

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
| 5 | the model's sup falls below the decided floor 36/625 | holds, 0.147 > 0.0576, on the model's own arithmetic |

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
