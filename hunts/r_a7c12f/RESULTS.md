# R-A7C12F — `637/1000` survives at depth 1; the table row compares two different ranges

**2026-08-23.** Run `e09a7f8a`. Reads: `hunts/frontier_math/K2-TWO-SPECIES.md`
section 2, `two_species.py`, `Zeta23Ext/EForm3/FarField.lean`,
`Zeta23Ext/EForm3/Counting.lean`. Instruments: `probe.py` here,
`hunts/r_a97060/ball_field.py` (Arb at 96 bits). Nothing here is evidence for
or against RH (`docs/08`).

## Verdict

**The claim is withdrawn.** `637/1000` does survive at depth 1 on the range it
is asserted on, with 0.82% to spare, and the ball pass says so at
enclosure-carrying grade. The `0.6636` is real as a number and wrong as a
refutation: it is a supremum taken over `s in [8, 400]`, while `637/1000` is
only ever claimed for `s >= 37.0135`. The two starred rows of that table both
sit under the constant that actually applies where they are attained.

There is a genuine defect underneath the false one, and it is the one a
`k >= 3` pass will meet. It is not the constant. It is the derivation route.

## The four questions the one sentence had merged

### 1. `Wt_tail_le` has no depth in it

`Counting.lean:93` reads, in full:

```lean
lemma Wt_tail_le {w : ℝ} (hw : 1368 ≤ w) : Wt w ≤ (637/1000)/w
```

with `Wt w = (5/8)/w + (611/50)/w^2 + (6711/100)/w^3 + (2583/25)/w^4`
(`FarField.lean:35`). That is an inequality between two explicit rational
functions of one variable. No `y` occurs in the statement, in the hypothesis,
or in the proof, which is `nlinarith` on a quartic. It cannot fail at depth 1
because it cannot see depth at all.

The lemma that does carry the depth is `Qim_far_sq` / `Qim_far_sq_abs`
(`FarField.lean:227, 232`):

```lean
theorem Qim_far_sq {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) (hs : 28/5 ≤ s) :
    Qim y s ^ 2 ≤ y^2 * Wt (s^2 - 2)
```

`hy : y ≤ 1/2` is the hypothesis at issue. K2-TWO-SPECIES.md named the wrong
lemma, and naming the wrong lemma is what made a range mismatch look like a
crossed constant.

### 2. The sup is attained ~8.7x below the threshold

`w = s^2 - 2 >= 1368` is `s >= 37.0135`. `two_species.far_constant` scans
`[8, 400]`. Where the sups actually sit:

| depth | far constant on [8,400] | argmax `s` | `w` at argmax | `w >= 1368`? | proved envelope `Wt(w)*w` there |
|---|---|---|---|---|---|
| 1/2 | 0.6219968 | 12.7150 | 159.67 | no | 0.70419 |
| 1 | **0.6635917** | 12.6250 | 157.39 | no | **0.70538** |

Both rows are attained near `s ~ 12.7`, in the second window, nowhere near the
tail regime. And at their own argument the proved envelope is `0.705`, so
neither `0.6220` nor `0.6636` was ever in conflict with anything proved. The
depth-1/2 row's parenthetical "(proved <= 0.637)" is the same mismatch, and it
happened to flatter rather than alarm.

`Wt(w)*w` falls from `0.840` at `s = 8` to `0.634` at the threshold and to
`5/8 = 0.625` as `s -> inf`. `637/1000` is the value of that envelope at
`w = 1368` rounded up, which is why it is stated there and not earlier.

### 3. On its own range, the constant holds at depth 1 — enclosure-carrying

Arb at 96 bits through `ball_field.D_enclosure`, over `s in [37.0135, 400]`,
adaptive cells bisected wherever the running bound exceeds 0.50, floor
`1e-4`. `Dam <= max(0, D_upper)` and `y^2 >= y_lo^2`, so every cell bound is
outward.

| depth | ball upper bound | float scan sup | enclosure cost | closed-form asymptote | vs `637/1000` | margin |
|---|---|---|---|---|---|---|
| 0.25 | 0.5844395 | 0.5844080 | 1.000054 | 0.5809884 | holds | +0.0526 |
| 0.50 | 0.5937078 | 0.5936767 | 1.000052 | 0.5901137 | holds | +0.0433 |
| 0.75 | 0.6093687 | 0.6093373 | 1.000052 | 0.6055774 | holds | +0.0276 |
| **1.00** | **0.6317735** | 0.6317408 | 1.000052 | 0.6277706 | **holds** | **+0.0052** |

The enclosure costs a factor `1.00005`, so the verdict is not an artifact of
interval width. 45,030 cells and 18,885 bisections at depth 1; whole probe
96.6 s.

Depth as a genuine interval, which is what `D_enclosure` takes:

| depth interval | ball upper bound | `(y_hi/y_lo)^2` inflation | vs `637/1000` |
|---|---|---|---|
| [0.99, 1.0] | 0.6450388 | 1.02030 | fails |
| [0.995, 1.0] | 0.6383542 | 1.01008 | fails |
| [0.999, 1.0] | 0.6330815 | 1.00200 | holds |

That is arithmetic about the normalisation, not about the field: dividing by
the cell's smallest `y` inflates by the square of the cell's relative width,
and the true margin at depth 1 is 0.82%, so cells wider than ~0.4% cannot
close however tight the enclosure is. Anyone wanting a depth-interval
statement over `[1/2, 1]` needs ~174 geometric cells, not a coarse grid.

### 4. Where the constant does break, and what actually breaks first

On the asserted range, `sup Dam*(s^2-2)/y^2` first exceeds `637/1000` at
**depth 1.0494** (float scan; asymptotic break depth 1.0855). Depth 1 sits
inside that with room; depth `2y` for `y <= 1/2` sits exactly on its edge,
which is the case `k >= 3` needs.

What breaks *before* the constant is the lemma that delivers it.
`Qim^2 <= y^2 Wt(s^2-2)` measured as a ratio:

| depth | max `Qim^2 / (y^2 Wt(s^2-2))` | argmax `s` | holds? |
|---|---|---|---|
| 0.50 | 0.9441368 | 395.836 | yes |
| 0.75 | 0.9688757 | 395.836 | yes |
| 0.95 | 0.9963791 | 395.836 | yes |
| 0.97 | 0.9995243 | 395.836 | yes |
| **1.00** | **1.0043806** | 395.836 | **no** |
| 1.25 | 1.0515569 | 395.835 | no |

The ratio grows with `s`, so this is asymptotic and not an edge effect. To
leading order `Im ghat(y+is) = -2 sinh(y/2) cos(1/sqrt2) cos(s/2)/s + O(1/s^2)`,
so the normalised quantity has limsup

    4 sinh(y/2)^2 cos(1/sqrt2)^2 / y^2

and `Wt(w)*w -> 5/8`, so `Qim_far_sq` holds asymptotically iff that limsup is
at most `5/8`, i.e. iff **`y <= 0.972659`**. The closed form is checked, not
asserted: it predicts `0.6277706` at depth 1 and `0.5901137` at depth 1/2,
against float sups of `0.6278055` and `0.5901440` on `[400, 4000]`, agreeing
to five digits. It also predicts the ratio `0.6277706/0.625 = 1.004433`
against the measured `1.0043806`.

So the correction a depth-1 argument must carry is real, and it is this: the
`y <= 1/2` hypothesis of `Qim_far_sq` is load-bearing and fails just below
depth 1. The value `637/1000` is fine. The route to it is not.

## What this changes for `k >= 3` (R-B9552D's declared dependency)

The dependency edge said a constant in `K2-TWO-SPECIES.md` being wrong is an
input to the two-species centre-gas split. The edge holds, with the content
replaced:

* **Nothing downstream needs a new constant.** `637/1000` dominates the true
  quantity at every depth up to 1.0494, so a `k >= 3` pass at depth `2y <= 1`
  may keep quoting it as a *value*.
* **Something downstream needs a new proof.** Quoting it as a *proved* value
  at depth `> 0.9727` requires re-deriving `Qim_far_sq` for `y <= 1`. Its
  coefficients `1.57, 3.6, 0.79, 3.8` (`base_poly_le`, `FarField.lean:50`)
  come from bounds on `P = y cosh(y/2)` and `S = sinh(y/2)` at `y <= 1/2`;
  at `y <= 1` those become `cosh(1/2) = 1.12763` and `sinh(1/2) = 0.52110`
  and the cubic majorant has to be re-fitted. That is a bounded piece of work
  and it was not attempted here.
* **The `k = 2` far rows are unaffected either way**, as the brief expected.

## Honest scope

Grade: the depth ladder over `s in [37.0135, 400]` is **enclosure-carrying**
(Arb, 96 bits, outward, cross-checked against an independent float scan at
`1.00005`). Everything else here is **measured**: the break depths, the
`Qim_far_sq` ratios, the asymptotic constant, and the argmax locations are
double-precision scans. Nothing compiles to Lean.

What is *not* closed, precisely:

* **`s > 400` has no enclosure at depth 1.** The `k = 2` far rows close that
  tail by composing `Wt_tail_le` with `Qim_far_sq`, and `Qim_far_sq` is
  exactly the step that fails at depth 1. So the tail is float-grade only
  here (`0.6278055` on `[400, 4000]`). The crude bound
  `|ghat| <= cosh(y/2)(1/(s+sqrt2)+1/(s-sqrt2))` is 8x too weak because it
  drops the `cos(s/2)cos(1/sqrt2)` interference; recorded so nobody re-derives
  it. A depth-1 `Wt` is the real route.
* **The other starred entry was not examined.** `no_damage`'s `28/5`
  shrinking to `5.3984` at depth 1 is a different lemma with a different
  quantifier structure, and this hunt says nothing about it. Given that the
  far row turned out to be a range mismatch, it deserves the same read before
  it is carried as a correction.
* **The margin at depth 1 is thin.** `+0.0052`, 0.82%. It holds, but it is
  not a bound with room in it, and any downstream step that pads caps will
  eat it.

## Ledger

`harness/departments/review_ledger.py` now carries `k2-far-constant-depth1`
as a `ClaimUnderReview` with this run's `AttackOutcome` (white-box) appended.
`harness.review.standing_reasons` reports the claim as **not standing**,
because no blind attack has run — which is the true state, not a formality.
This hunt's task came from the thread roster (`threads.json` R-A7C12F), not
from a harness generator: it was in no generator's output before this commit
and could not be removed from one. See `notes_for_operator` in `HANDBACK.json`.

## Loose threads

* **`no_damage`'s `28/5` at depth 1 (the other starred row).** The table
  reports the no-damage radius shrinking from `6.0653` to `5.3984 < 28/5`.
  That is a different claim shape from the far row, so this hunt's finding
  does not transfer, but the two entries were produced by the same scan in
  the same session and one of them turned out to be a range artifact.
  *Why it might matter:* if it is also sound-but-misattributed, the depth-1
  landscape has no corrections at all and the `k >= 3` brief loses an
  obstruction. *First step:* read `no_damage`'s Lean statement for its own
  `y` hypothesis, then bound `D(1,s)` from above on `s in [28/5, 6.0653]`
  with `ball_field.D_enclosure` and see whether the sign change at `5.3984`
  is inside or outside the range the lemma claims.
* **A depth-1 `Wt`.** Re-fitting `base_poly_le`'s cubic majorant with
  `cosh(1/2)` and `sinh(1/2)` in place of `cosh(1/4)` and `sinh(1/4)` would
  give `Qim_far_sq` for `y <= 1` and restore the whole far-field chain,
  including the tail, at depth 1. *Why it might matter:* it is the only thing
  standing between the measured `0.6318` and a proved depth-1 far row.
  *First step:* recompute the four coefficients by the same route
  `FarField.lean` uses, check the resulting `Wt1(w)*w` limit against the
  measured limsup `4 sinh(1/2)^2 cos(1/sqrt2)^2 = 0.62777`, and see what
  threshold `w` it needs to get under a clean rational.
* **The scan range in `two_species.far_constant` is undocumented as a
  choice.** `[8, 400]` is a default argument with no comment saying why 8,
  and the mismatch that produced this whole thread is that 8 is below every
  threshold the lemmas use. *Why it might matter:* the same function is the
  one a `k >= 3` pass would call. *First step:* one line in its docstring
  naming `s >= 37.0135` as the range `637/1000` applies to, so the next
  reader compares like with like. Left undone because `hunts/frontier_math/`
  is outside this hunt's write scope.
