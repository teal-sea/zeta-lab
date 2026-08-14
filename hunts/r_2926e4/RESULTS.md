# R-2926E4: the 1-D O9 table is 476 cells on kernel leaves, not 344

**Settled.** Issue #23's claim holds, and the outstanding item it named now has
a number. `o9_leaf.py`'s LEAF CAVEAT is false as a safety argument, its 344 is
low by **38%**, and the corrected 1-D count is **476 cells** at max depth 22,
every cell decided.

Run `.venv/bin/python hunts/r_2926e4/probe.py` (0.6 s end to end); the numbers
below are `results.json` verbatim.

## 1. The caveat, put to a number

The caveat says the Arb leaves and `BandCert/Leaves.lean`'s Taylor leaves
"agree to well under `2^-60`". Sampled over 24 cells drawn across the whole
`[28/5, 60]` range from the module's own 344-cell table, the ratio of kernel
width to Arb width per leaf:

| leaf | min | mean | max |
|---|---|---|---|
| `sinX2` | 1.000 | **1.544** | 4.695 |
| `cosX2` | 1.000 | **8.154** | **43.538** |
| `sinh` | 0.333 | 0.333 | 0.333 |
| `cosh` | 0.333 | 0.333 | 0.333 |
| `SQ2` | 0.111 | 0.111 | 0.111 |
| `SINC` | 0.778 | 0.778 | 0.778 |
| `COSC` | 0.556 | 0.556 | 0.556 |

The split is exactly the mechanism issue #23 names. The four constant leaves
and the two hyperbolic ones are *narrower* in the kernel than in Arb-plus-4-ulp-pad
because they are point or small-argument evaluations where the 4-ulp pad is the
dominant term, so the caveat's "agree to `2^-60`" is fair there. The two trig
leaves of the cell are not: `sinCosIv` reduces mod `2π`, evaluates a Taylor
interval on a quarter, then applies `dbl` twice, and `dbl` squares an interval,
so its width grows with the cell. Those are the only two leaves whose argument
is the cell rather than a constant, and they are the two that blow up. The
worst sampled case is `cos` on the cell at `s = 31.478`, wider by **43.5×**.

This is a difference in *kind*, and the caveat's own framing of it as a
precision gap is what made it read as safe.

## 2. Why "passes with margin" was never the right test

The caveat's safety argument is that every cell passes by far more than a few
ulp, minimum `3.63e9`. Rechecking the 344 recorded cells against kernel leaves,
with nothing else changed:

| | |
|---|---|
| baseline cells checked | 344 |
| **fail on kernel leaves** | **85 (24.7%)** |
| pass rate | 75.3% |
| worst kernel margin | `-1.07e17` ulp |
| **largest Arb margin among the failures** | **`9.21e16` ulp** |
| module's cited minimum margin | `3.63e9` ulp |
| ratio of the two | **`2.5e7`** |

That last row is the finding. A cell whose recorded margin is twenty-five
million times the minimum the module offers as its safety evidence still fails.
The margin and the leaf-model error are not commensurable quantities, so no
threshold on the margin, not "a few ulp", not `3.63e9`, not `9.21e16`,
separates the safe predictions from the unsafe ones. The caveat is not
mis-calibrated; it is measuring the wrong thing.

### The mirror reproduces the kernel's disagreement pattern, chunk for chunk

`O9-2D-STATUS.md` §0 records the 2026-08-13 Lean build: `decide +kernel`
returned `false` on 7 of the 9 chunks, offsets 0, 40, 80, 120, 160, 240, 320,
and `true` on 200 and 280. Bucketing this hunt's 85 failures into the same
40-cell chunks, in the same sorted order `emit_lean` writes:

| chunk offset | 0 | 40 | 80 | 120 | 160 | 200 | 240 | 280 | 320 |
|---|---|---|---|---|---|---|---|---|---|
| failures found here | 35 | 14 | 10 | 3 | 8 | **0** | 8 | **0** | 7 |
| Lean's verdict | false | false | false | false | false | **true** | false | **true** | false |

Nine for nine, including both passing chunks. This is the load-bearing control
for everything above: the mirror is not merely wider than Arb in the right
direction, it agrees with the kernel on exactly which chunks survive. It is
also the only comparison in this hunt against a real `decide +kernel` run
rather than against a model, and it was not used to tune anything.

**A correction to the issue.** Item 1 of "What is still outstanding" says the
344-cell table "has never been put to the kernel". It has: that is the
2026-08-13 build recorded in `O9-2D-STATUS.md` §0, and it refuted the table.
What had never been done is the rebuild, which is §3.

## 3. The corrected count

The same adaptive walk, the same seed cuts at every window endpoint, the same
`WINDOWS`/`CAPS` and the same integer target, with `o9_leaf.leaves` replaced by
`o9_leaves_kernel.kernel_leaves`. Every other line is `o9_leaf.py`'s, imported
rather than copied.

| leaves | cells | undecided | max depth | min margin (ulp) | min margin (abs) |
|---|---|---|---|---|---|
| Arb + 4-ulp pad (recorded) | 344 | 0 | 20 | `3.63e9` | `1.97e-10` |
| kernel, depth cap 20 | 474 | **1** | 20 | n/a | n/a |
| **kernel, depth cap 30** | **476** | **0** | **22** | **`3.12e8`** | **`1.69e-11`** |

**476 cells, 1.38× the recorded 344.** Two things worth separating:

- **The table still closes.** The 1-D route survives the repair. That was not
  guaranteed: the complement test outside the windows demands `D <= 0`
  outright, and it holds only because §4's `I_k` are decimal-rounded outward
  past the true damage support by ~`2e-05` (`o9_leaf.py`'s L4b). Wider leaves
  could have eaten that slack; they did not.
- **The depth cap has to move.** At the baseline's own max depth of 20 the
  rebuilt walk leaves one cell undecided. Anyone regenerating this table with
  `max_depth=20` would get 474 cells and a silent failure.

The 1.38× here is much gentler than the 3.2× the 2-D table suffered
(598 → 1939). The plausible reason is the removable branch: the 2-D route
carries `y` as an interval down to `y = 0` and tests through `R = Qim/y`, so
its enclosures compound the leaf widths further. Sitting at `y = 1/2` with `y`
a point, the 1-D route exposes less surface to the wider trig leaves. That is a
conjecture about the mechanism, not a measurement; it would take a 2-D run at
fixed `y` to separate.

## 4. What this does and does not license

**Does.** 476 is a materially better prediction of the kernel's verdict than
344 was, because every step from the cell to the `Bool` is now either
`o9_leaf.py`'s mirrored integer arithmetic or `o9_leaves_kernel`'s mirror of
`Leaves.lean`, and the latter is pinned against Lean's own `#eval` output
integer for integer by `tests/test_o9_leaves_kernel.py` (5 passed, 1
deselected; the deselected one is the `slow`-marked Lean round-trip).

**Does not.** No Lean was built here. `zeta23ext` has no `.lake` cache in this
container, so obtaining the verdict would mean building Mathlib from source,
well past this hunt's budget. 476 is therefore a *prediction*, at the grade the
2-D repair already validated (its kernel-leaf table was accepted on all 49
chunks) but not itself checked. It is **measured**, rung 1: one route, and the
route is a model of the kernel rather than the kernel.

Two further gaps are unchanged and belong to `o9_leaf.py`, not to this hunt:
`damageIv_mem` still does not exist, so the table proves nothing about `Dam`
even once it passes; and the 1-D route still rests on the unproved depth
reduction `D(y,s)/y^2 <= 4 D(1/2,s)`. Nothing here is evidence about RH.

## 5. What could not be settled at this cost

The kernel verdict itself. Everything else asked was answered.

## Loose threads

- **`o9_leaf.py`'s `N_CELLS_KERNEL = 344` and its docstring are now known
  wrong, and this hunt may not fix them.** The constant is exported in
  `__all__`, so anything importing it inherits the stale figure, and the
  docstring still presents the caveat as a safety argument. *Why it matters:*
  the same shape of claim is what produced the refuted table. *First step:* in
  `hunts/frontier_math`, set `N_CELLS_KERNEL = 476`, switch `leaves` to
  `kernel_leaves`, raise the default `max_depth` above 20, and rewrite the LEAF
  CAVEAT to point at `O9-2D-STATUS.md` §0 rather than at a margin.

- **`O9-SCOPING.md` §3's 389-leaf estimate is still on the books** and issue #23
  already prices it as ~5× low against the measured 1939. *Why it matters:* it
  is quoted inside `o9_leaf.py`'s L4 as the reason the 2-D route is the better
  artifact, a comparison of 344 against 389 that, corrected, is 476 against
  1939, which reverses the direction. The routing advice may be backwards.
  *First step:* recompute §3's table with `kernel_leaves2d` at its recommended
  operating point and restate L4's trade against the corrected pair.

- **The `dbl`-squaring blow-up is a function of cell width, so the walk may be
  paying for it twice.** A cell that fails only because `cosX2` is 43× too wide
  gets bisected, which narrows the argument and shrinks the `dbl` penalty
  superlinearly. *Why it matters:* if the penalty falls faster than the cell
  count rises, a cheaper reduction (three quarterings instead of two doublings,
  or `sinCosSmall` on a finer split) could recover a chunk of the 132 extra
  cells without touching the mathematics. *First step:* plot kernel `cosX2`
  width against cell width across the 476 cells and check whether the exponent
  is above 1.

- **The two hyperbolic leaves and `SQ2` are 3× and 9× *narrower* in the kernel
  than in the Arb path.** *Why it matters:* it says the 4-ulp outward pad in
  `_to_iv` is doing nothing useful on constant leaves and is pure loss there;
  it also means an Arb-based model is not uniformly optimistic, which is a
  sharper statement than "Arb is too narrow". *First step:* re-run §1's table
  with `pad=0` to confirm the pad is the whole of those three ratios.
