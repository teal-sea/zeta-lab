# `zone_trade`'s inner prune, settled on every cell

**2026-08-17.** Hunt `r_401bbf`, run `2b9b08aa`. Instrument: `probe.py`, data:
`results.json`, pins: `test_prune_discharge.py`. Reads:
`hunts/frontier_math/k2_closure.py`, `hunts/r_a97060/RESULTS.md` §4. Nothing
here is evidence for or against RH (`docs/08`); nothing here claims `k >= 3` or
the unequal-depth quantifier, and no cap was widened and no zone re-tuned.

## 0. The answer

**Outcome (a) of the brief: the delta is zero on every cell, and the prune is
sound by argument as well as by measurement.**

| cap mode | cells | max abs delta | cells with delta > 1e-15 | worst margin, published search | worst margin, exhaustive | nonpositive cells |
|---|---|---|---|---|---|---|
| signed field | 6600 | 8.300e-17 | **0** | +0.0528969 @ tau 12.850 | **+0.0528969** @ tau 12.850 | 0 to **0** |
| unsigned | 6600 | 1.110e-16 | **0** | +0.0032601 @ tau 6.330 | **+0.0032601** @ tau 6.330 | 0 to **0** |

13,200 cell evaluations, every one of them audited, none sampled. Not one
margin moves anywhere in its first twelve decimals. The largest deviation in
the whole table is 1.1e-16, which is 3.4e-14 of the smallest margin, thirteen
orders of magnitude below anything that could flip a cell.

That residual is float summation order, not a trade difference, and the table
says so itself: **1467 cells in the signed pass and 965 in the unsigned one
have a *negative* delta**, which is arithmetically impossible for a genuine
bite, since the exhaustive maximum is over a superset and can only ever come
out higher. Its size agrees: a near total of order 0.16 has an ulp of 2.8e-17,
so 1.1e-16 is four of them, which is what re-associating a sum of twenty-odd
component trades costs. Cells whose delta is exactly `0.0` number 3428 and
3084.

So the published k=2 table does not depend on the prune. The assumption that
`hunts/r_a97060/RESULTS.md` §4 recorded as load-bearing and unchecked is
discharged, and the prune should stay in the code, documented, rather than be
removed: it costs nothing and it is what makes the search affordable.

## 1. What "disabled" was taken to mean

The brief says: re-run with the inner prune disabled. Deleting only that line
would have left the other cut standing:

```python
if val + rem * caps[idx] <= best:      # outer branch-and-bound bound
    return
...
    if v > val - 1e-18 or m == 0:      # the inner prune, the brief's target
        dfs(idx + 1, ms + [m], v, rem - m)
```

and the outer bound's admissibility rests on the *same* hypothesis the inner
prune needs. Auditing one while trusting the other would have left the question
half open. The surviving components in this table are small (at most **8** zones
carry a nonzero cap in any connected component of the whole table, at most 6 in
the signed mode), so every admissible multiplicity vector can simply be
enumerated: `C(Z+10, Z) <= 43758` vectors, evaluated as one vectorised
quadratic form. That is an exact maximum with **no cuts at all**, hence a strict
upper bound on what the inner-prune-free search would find, so a zero delta
against it settles the brief's question a fortiori and settles the outer bound
for free.

Both trades run on the **same** zone data, component by component, inside one
pass. Each cell's delta is therefore an exact difference of two solvers on one
input, not a comparison of two independently scanned tables. Everything outside
the trade (the far rows, `C1`, the budget floor) is identical by
construction, so the margin delta *is* the near delta.

## 2. Why the prune was never going to bite, and the hypothesis that makes it so

The measurement is the deliverable, but it came with an argument that explains
it, and the argument is worth more than the table because it covers cap values
this table never produces.

**Claim.** If every pair charge is nonnegative and every cap is nonnegative,
the inner prune removes nothing: the search still returns the exact maximum.

*Proof.* Write `F(ms, idx, rem)` for the best completion value from zone `idx`
given the prefix `ms` and budget `rem`. Two monotonicities:

1. `F` is nondecreasing in `rem`: the feasible set of completions grows.
2. `F` is nonincreasing in each prefix multiplicity: a prefix atom enters a
   completion only through the subtraction `-2*q_ji*ms_j*m_i`, which is
   nonnegative when `q >= 0`.

Now take a node with running value `val` and a branch `m` whose value `v` does
not improve it, `v <= val`. Its best completion is
`v + F(ms+[m], idx+1, rem-m)`, which by (2) is at most `v + F(ms+[0], idx+1,
rem-m)`, which by (1) is at most `v + F(ms+[0], idx+1, rem) <= val + F(ms+[0],
idx+1, rem)`. The right-hand side is exactly what the `m = 0` branch can reach,
and `m = 0` is *always* descended into (the `or m == 0` clause). So the pruned
branch cannot beat a branch the search already takes. ∎

The same hypothesis makes the outer bound admissible: with `q >= 0` no
completion gains more than `rem` copies of the largest remaining cap, which is
`rem * caps[idx]` once the caps are sorted descending.

**And the hypothesis holds by construction, not by geometry.** The charge is
`q_ab = Kpair(min(dmax, 6))/200` with `Kpair(u) = Re(ghat(0,u))**2`, a square
divided by 200. It is nonnegative for *every* input, so both cuts are sound for
any cap vector whatsoever, including the enclosure pass's caps in
`hunts/r_a97060/`, which this run did not re-enumerate. That is a strictly
stronger statement than "measured 0.0 on 6600 cells", and it is why the
recommended disposition is to document the prune rather than delete it.

This is a different situation from the *other* assumption `r_a97060` §4 named.
The pair-charge clamp really is sound only by accident of geometry (`Kpair` has
a root near 6.65 and the widest component in the table is 1.94, corroborated
here at 1.9404 over a coarse tau sweep). The prune is sound by the form of the
objective. Two unstated assumptions, two different kinds of luck, and only one
of them was luck.

One caveat kept in view: the `1e-18` tolerance in `v > val - 1e-18` makes the
test *more* permissive than the exact rule, so it descends into slightly-losing
branches too. That is the safe direction and it cannot cut anything the exact
rule keeps.

## 3. Controls

| control | question | result |
|---|---|---|
| solver agreement | does the exhaustive solver ever come out *below* the published search on a component of the table's shape? | 400 random instances, **0** below, max difference 3.3e-16 |
| transcription | is the switchable search in `probe.py` really `zone_trade`? | 200 instances, max difference **exactly 0.0** |
| **planted bite** | if the prune *did* bite, would this probe see it? | **yes**, see below |
| charge sign | is every pair charge the table builds nonnegative, and is the clamp inside `Kpair`'s first root? | min charge **+0.0031**, widest component **1.9404** |
| reproduction | do the audited cells still reproduce the published binding margins? | +0.0528969 and +0.0032601, to all printed digits |

The planted bite is the control that gives the zero delta its meaning. Break
exactly the hypothesis of §2, one negative off-diagonal charge, an attractive
pair instead of a repulsive one, and the cuts fail at once:

| search | value |
|---|---|
| published search (both cuts) | 0.184000 |
| inner prune off, outer bound on | 0.146000 |
| outer bound off, inner prune on | 0.226000 |
| both off | 0.226000 |
| exhaustive enumeration | **0.226000** |

The published search understates the true trade by 0.042 (18.6%) on that
instance, so the probe is a genuine detector and the table's 1e-16 is a real
negative rather than a blind one. The middle row is also the answer to why this
run enumerated instead of just deleting the line the brief named: with the
hypothesis broken, disabling the inner prune alone gives **0.146**, further from
the truth than leaving both cuts in. A half-audit would have been worse than
none.

## 4. Cost

713 s wall for the whole thing on the container's CPU: 255 s for the signed
pass, 450 s for the unsigned one, both at the published table's own scan
resolution (x-step 0.01, three tau-samples per cell, zones 0.25). The
exhaustive trade is not the expensive part: it is a single `(N, Z)` matrix
product per component, so auditing every cell cost roughly what running the
table once costs, and the "sample the binding cells" shortcut bought nothing
worth having. The census was affordable at 6600 cells; that is a fact about
this table's component sizes, not a general licence.

## 5. Honest scope

- This settles **the trade solver**, on the measured pass's zone data, plus (by
  §2) the solver for any nonnegative caps. It says nothing about the zone
  **caps** themselves, the component geometry, the far rows, `C1`, or the O8
  floor. The enclosure grade of those is `hunts/r_a97060/`'s business, not this
  run's.
- The delta is zero **to double precision**, not symbolically: both solvers are
  float, and the residual 1e-16 is their differing summation order. A reader who
  wants the trade in exact arithmetic still has that to do, and `r_a97060`
  already documented a `1e-9` float slack in the trade that dominates this by
  seven orders of magnitude.
- The `sum m <= 10` atom budget is inherited from `k2_closure.py` and was not
  re-derived here. Both solvers use it, so it cannot show up in the delta; if it
  is wrong, it is wrong in both columns.
- No number in the published table changes. Nothing here moves the composite
  k=2 claim's grade, which still takes it from the v-convexity transfer (G3),
  and nothing here is evidence about RH.

## Loose threads

1. **The atom budget `sum m <= 10` is an inherited constant.** Both solvers
   respect it, so this audit is blind to it by construction. If the true
   adversary can place an eleventh atom in a component, every column of the
   table shifts together and no delta of this kind would reveal it. *First
   step*: check whether `P`'s optimal multiplicity `m* = 1/2 + cap/(2q)` can
   reach 10 for the largest zone cap the table builds; if it cannot, the budget
   is provably slack and the constant can be retired to a lemma.
2. **The clamp's monotonicity is still geometric.** `r_a97060` replaced it with
   a running minimum in its own pass, but `k2_closure.py` still ships
   `Kpair(min(dmax, 6))` and is still sound only because the widest component is
   1.94 against a first root near 6.65. That margin is not enforced anywhere.
   *First step*: assert the widest component width in
   `hunts/frontier_math/test_k2_closure.py` so a geometry change that crosses
   the root fails a test instead of silently over-crediting.
3. **The exhaustive trade is cheap enough to be the default.** At most 8 zones
   per component and ~0.4 ms per component, the enumeration could replace the
   branch-and-bound in `k2_closure.zone_trade` outright, deleting the question
   this run had to answer rather than documenting it. *First step*: swap it in
   behind a keyword argument and time the full table; if the cost is within a
   factor of two, the heuristic has no reason to survive.
