# The k=2 tau-table under enclosures

**2026-08-17.** Hunt `r_a97060`, run `78b4ce8e`. Instrument: `probe.py`
(+ `ball_field.py`), data: `results.json`. Reads: `K2-TWO-SPECIES.md` §3 and
§6, `hunts/frontier_math/k2_closure.py`. Nothing here is evidence about RH
(`docs/08`), and nothing here claims `k >= 3` or the unequal-depth quantifier.

## 0. The answer

**The table closes under enclosures.** Outcome (a) of the brief, in all three
cap modes, over the same 6600 cells, with no cap widened and no cell split
beyond the depth dimension.

| cap mode | worst margin | at tau | nonpositive cells | measured pass, same mode |
|---|---|---|---|---|
| signed field | **+0.0677054** | 12.850 | **0 of 6600** | +0.0529 |
| unsigned | **+0.0145634** | 6.310 | **0 of 6600** | +0.0033 |
| unsigned, the measured pass's own 1.05 pad retained | **+0.0016260** | 6.310 | **0 of 6600** | +0.0033 |

Read the three rows together, because only the third is a like-for-like
comparison. The measured table pads every zone cap by a flat `INFL = 1.05`;
that pad was the scan's substitute for an enclosure, and an enclosure pass
that keeps it is paying twice. Rows 1 and 2 are the honest hardened table,
with the pad deleted and a rigorous bound in its place. Row 3 keeps the pad
on top of the enclosure and is therefore strictly more conservative than
anything the measured pass ever claimed: it still closes, at +0.0016.

So the `k = 2` equal-depth verdict no longer rests on sampling. It rests on
outward bounds over whole cells, in the ball representation the brief named,
cross-checked against a second interval backend. **The grade of this step
moves from measured to enclosure-carrying.** The composite `k=2` claim does
not automatically move with it, because the composite takes the grade of its
weakest step, and two of its steps were never in this table: see §5.

## 1. What was replaced, and by what

The geometry is untouched: same nine `I_k` windows, same merge into
components, same 0.25 zones, same integer branch-and-bound trade, same O8
budget floor, same 0.02 cells on `[0,132]`. Four scans became bounds.

| quantity | measured pass | this pass |
|---|---|---|
| near-field zone cap | `1.05 x sup` over x-step 0.01, **3 tau-samples** per cell | ball envelope of `D(1/2,.)` at step `1e-4`, tau-sup as a 201-wide running maximum, so the whole cell in both variables; pad deleted |
| zone-pair credit | `Kpair(min(dmax, 6))` | running **minimum** of a `Kpair` envelope over `[0, dmax]` |
| cell credit `min Kpair` | min over 7 samples | enclosure lower bound over the interval |
| centre-centre row `C1` | max over an **18-point y-grid** | branch-and-bound in `u = 2y` **plus a second-order bound** that reaches `u -> 0` |
| far rows, budget floor | float arithmetic on proved constants | exact rationals (`fractions`), plus a documented `1e-9` float slack in the trade |

The representation is Arb's complex ball, centre plus radius, per the brief:
rung 3 measured rectangles losing 13.7x of width to balls on a squared
rotating complex value, and `D(y,s) = -Re ghat(y+is)^2` is one. `python-flint`
at 96 bits is the producer; `mpmath.iv` is only a cross-check.

**Cost of the enclosure, measured.** On six binding cells the enclosure near
deficit exceeds the *unpadded* scan by a factor of **1.0000 to 1.0004**, that
is the entire inflation the interval pass costs on the dominant term. The
1.05 pad it replaces was between 100 and 400 times larger than the enclosure
error it was standing in for.

**Cells needing splitting.** None in tau: every cell closed at the original
0.02 width. The depth dimension is a different story, see §2.

## 2. The one thing that genuinely resisted, and what fixed it

A first full pass reported **one nonpositive cell**, `tau in [6.62, 6.64]`,
at `-0.0063` unsigned. It was not the near field (ratio 1.0004 there) and not
a real gap: it was my own bound on the centre-centre row.

`C1(tau) = sup_{0<y<=1/2} Dam(2y,tau)/y^2` is a supremum over an OPEN depth
interval with the variable in the denominator. A branch-and-bound over
`u = 2y` bounds a box `[a,b]` by `4 max(0, sup D)/a^2`, and as `a -> 0` that
multiplies a `1/a^2` against an enclosure whose width is set by the TAU-cell,
not the `u`-box. At `tau = 6.63`, which is a root of `G(tau) = ghat(i tau)`,
the enclosure stalled at 0.1142 against a true value of 0.0673.

The fix came out of the ball layer rather than out of more grid. `ghat` is an
**even** function with real Taylor coefficients, so `ghat'(i tau)` is purely
imaginary and

    d/du D(u,tau)|_{u=0} = -2 G(tau) Re ghat'(i tau) = 0

**identically**: `D` has no depth-linear term. Hence for every `u <= b`

    D(u,tau) <= -G(tau)^2 + (u^2/2) sup_{[0,b]} |D''|
    =>  4 max(0,D)/u^2 <= 4 max(0, sup|D''|/2 - G^2/b^2).

Taking the smaller of that and the direct box bound closes the `u -> 0` corner
in one step, and it brought the failing cell to `C1 <= 0.0703` and the table to
0 nonpositive cells. Two things worth separating here:

* **this is a fact about the problem, not a trick**: the vanishing linear term
  is why `Dam(2y,tau)/y^2` is bounded at all as `y -> 0`, which the measured
  pass's y-grid assumed without stating;
* **no scan can check that corner.** An 18-point y-grid starting at `y = 0.05`
  says nothing about `y < 0.05`, and the region it cannot see is exactly where
  the ratio has a `0/0`. The enclosure pass had to prove it to proceed. That
  is the clearest case in this run of hardening finding something rather than
  just re-confirming something.

`C1` upper bounds still carry real slack: 0.0850 worst over the table against
a fine-scan value near 0.083, and 0.0703 against 0.0673 at the resonance cell.
The tau-cell width, not the method, sets that floor.

## 3. Controls

| control | result |
|---|---|
| **(H1) enclosure vs scan, near field** | ratio 1.0000–1.0004 on six binding cells, both modes. The enclosure is not quietly larger. |
| **(H2) the measured b&b's inner prune** | `k2_closure.zone_trade` prunes branches whose value drops, which is a heuristic, not an admissible bound, and it prunes the ADVERSARY's search, the unsound direction. Re-run exhaustively on six binding cells: **delta 0.0 everywhere.** The prune costs nothing there. It is still a heuristic on the other 6594 cells. |
| **(H3) depth sup vs y-grid** | the enclosure's lower witness never exceeds the measured scan's value, so the 18-point grid did not miss the sup at any binding cell. Its blindness is qualitative (`y < 0.05`), not numerical. |
| **(H4) planted cap fault** | inflating the enclosure table's own caps kills the resonance cell at **1.10x** (margins +0.01459, +0.01207, +0.00956, +0.00200, −0.01058 at 1.00/1.01/1.02/1.05/1.10). The measured pass fired at 1.02x. The detector still has power; the margin is simply larger. |
| **(H5) cross-backend** | `mpmath.iv` rectangles on the same four boxes **contain** the Arb balls in every case, and are 1.8x to 3.5x wider. Direction agrees with rung 3's 13.7x; the ratio is smaller because this is one squaring, not a tower of them. |
| **(H6) clamp check** | the widest near component over the whole table is **1.9894**, so the measured pass's `min(dmax, 6.0)` clamp never binds. See §4. |

## 4. Two things found in `k2_closure.py` that a reader should know

Neither changes the verdict. Both are recorded because the next pass over this
code should not have to rediscover them.

1. **The pair-charge clamp is sound only by accident of geometry.**
   `qmat[a][b] = Kpair(min(dmax, 6.0))/200` is a valid lower bound on the true
   charge `Kpair(d)`, `d <= dmax`, only if `Kpair` is monotone on `[0, dmax]`.
   `Kpair` has roots, `G` has one near 6.65, so for `dmax` past the first
   root the clamp would credit the accounting with repulsion that is not
   there, and over-crediting understates the deficit, which is the unsound
   direction. It never bites here because zone pairs live inside one connected
   component and the widest component in the whole table is 1.9894. This pass
   uses a running minimum instead and needs no such argument.
2. **The inner prune in `zone_trade` is a heuristic in the adversary's
   favour**, as (H2) describes. Measured delta 0.0 on the binding cells, not
   checked exhaustively on all of them.

Neither is a defect in the published numbers. Both are load-bearing
assumptions that were unstated.

## 5. Honest scope: what this does and does not upgrade

**Upgraded.** The tau-table step of the `k = 2` equal-depth argument. Every
supremum in it is now an outward bound over a whole cell, every credit an
inward bound, in ball arithmetic, cross-checked against a second backend.
`K2-TWO-SPECIES.md` §6's "no interval enclosures" no longer describes this
table.

**Not upgraded, and the composite claim still takes the weakest step.**

* The **v-convexity transfer** from `v = 1/4` to all `y in (0,1/2]` is an
  argument, not a table. This pass evaluates the table at `v = 1/4` exactly as
  the measured pass does. `k2_closure.NAMED_GAPS` G3 stands verbatim: the
  signed caps are `[a v - b]^+` with `b = Kpair(near zone)`, and a hardened
  transfer wants O3-style rational floors on those `b`. Not done here.
* The **far rows** rest on `Wt_tail_le <= 637/1000` and the window table, which
  are results of the surrounding tree, taken as given. Recomputing them in
  exact rationals removes float rounding; it does not re-derive them.
* The **O8 budget floor** `2 x (51944/100000) x 1/4` is used as the
  kernel-checked constant it is.
* **`k >= 3`** and the **unequal-depth quantifier** are untouched. `k = 2`,
  `y_1 = y_2` is what closes, and the quantifier discipline of defect #19
  applies verbatim: this is the first multi-pair case of blocker 2, not
  blocker 2.

So: the *tau-table* is enclosure-carrying; the *`k=2` equal-depth claim* is a
composite whose remaining weakest step is the convexity transfer, which is
argued rather than enclosed. Saying the claim is now hardened, full stop,
would round a rung upward for an audience.

**Budget.** The brief allowed 75 minutes; this run took roughly 100. The
overrun bought §2, the first full table reported a failing cell, and stopping
at the buzzer would have shipped "the unsigned mode does not survive
enclosure", which is false and would have sent the next attempt to widen a cap
that did not need widening. Recorded as an overrun, not as free.

## 6. Reproduction

```bash
.venv/bin/python hunts/r_a97060/probe.py            # full table, ~5 min after the envelope
.venv/bin/python hunts/r_a97060/probe.py --quick    # binding cells + controls
```

The `D(1/2,.)` envelope (1.9M ball evaluations, 22 s) caches to
`data/k2_ball_envelope_h0.0001.npz`, gitignored per house rule; delete it if
you change `H` or the field.

## Loose threads

1. **The `zone_trade` prune, exhaustively.** (H2) checked six cells and found
   delta 0.0. The prune is in the adversary's favour, so a cell where it bites
   would silently understate a deficit. *Why it might matter:* it is the only
   remaining place in the table where a heuristic sits on the unsound side.
   *First step:* re-run the full table with `exhaustive=True` in
   `probe.zone_trade` and diff the worst margins, one flag, one run, and the
   b&b's own admissible bound already makes it affordable.
2. **The v-convexity transfer is now the weakest step, and it is the cheapest
   remaining one.** The table is enclosure-carrying at `v = 1/4`; the transfer
   to `y < 1/2` is prose. *Why it might matter:* until it is discharged the
   composite claim cannot be described as hardened, so this pass's gain is
   partly stranded. *First step:* enclose `b = Kpair(near zone)` as an O3-style
   rational floor per zone, the running-minimum envelope in `probe.py` already
   produces exactly that number, it just is not being fed to the convexity
   argument.
3. **The `C1` slack is set by the tau-cell width, not the method.** Worst
   `C1` upper 0.0850 against a fine-scan 0.083. *Why it might matter:* it is
   0.002 of margin, cheap now and possibly not cheap for `k >= 3`. *First
   step:* subdivide only the ~40 cells with `C1 > 0.05` to 0.005 in tau and
   see how much of the gap is cell width.
4. **The even-ness of `ghat` was used here for the first time in this tree.**
   `ghat(-z) = ghat(z)` with real Taylor coefficients killed the depth-linear
   term outright. *Why it might matter:* the same fact should collapse other
   small-depth corners, and the unequal-depth convex-majorant route of
   `K2-TWO-SPECIES.md` §4 is exactly a small-depth argument, its majorant is
   reported "too fat by ~0.015" at the `(1/4, 0)` vertex, which is a `v -> 0`
   vertex. *First step:* recompute that majorant with the linear term known to
   vanish in each depth variable separately and see whether 0.015 survives.
5. **The far-field constant at depth 1.** `K2-TWO-SPECIES.md` §2 records that
   `637/1000` does NOT survive at depth 1 (measured 0.6636). The far rows here
   are depth-1/2 and unaffected, but a `k >= 3` pass that pushes depth up will
   meet it. *Why it might matter:* it is a proved constant going invalid, not
   a loose bound. *First step:* re-derive the depth-1 far constant with the
   same ball layer; `ball_field.D_enclosure` takes the depth as an interval
   already.
