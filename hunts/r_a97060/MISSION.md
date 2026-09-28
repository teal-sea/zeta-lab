# MISSION, `r_a97060`: the interval pass over the k=2 tau-table

## The question

`hunts/frontier_math/k2_closure.py` closes the `k = 2`, equal-depth case of
blocker 2 over 6600 tau-cells on `[0,132]`, and closes it at **measured**
grade: every supremum in that table is a double-precision scan, padded by a
flat 5% inflation. `K2-TWO-SPECIES.md` §6 names the obligation that keeps it
there: *"no interval enclosures"*, the interval pass over the same finitely
many cells.

This hunt is that pass. It does not extend the result, does not touch `k >= 3`,
and does not touch the unequal-depth quantifier. It asks one thing: **does the
same table close when every sup becomes an enclosure and every credit becomes a
lower bound**, and at what cost.

## Scope

**May write**: `hunts/r_a97060/`, and, by the operator addendum of
2026-08-17, which overrides the generic "do not touch `hunts/frontier_math/`"
line for this run only, `hunts/frontier_math/k2_closure.py`,
`two_species.py`, their tests, and `K2-TWO-SPECIES.md`, plus the case-log
entry in `hunts/README.md`.

**May not write**: `zeta/`, `ontology/`, `harness/`, `meta/`, `lean/`, any
root markdown file, `hunts/frontier_math/zeta23ext/` (a concurrent run owns
it), or `scripts/6*_rung3_*`.

**Standing**: nothing here is evidence for or against RH (`docs/08`). The
reserved word of `zeta/rigor.py` and the Lean arm does not appear in this
directory, disclaimers included -- the lexical guard reads the bytes.

## Representation, and why

The addendum's instruction, taken: rung 3 measured the RECTANGLE interval
representation losing 13.7x of width to the BALL representation (centre plus
radius) on exactly this shape of quantity, a squared rotating complex value,
and `Dam(y,s) = -Re ghat(y+is)^2` is one. So the enclosure layer is Arb's
complex balls via `python-flint`, the same arithmetic `lean/ZetaLean/Ball.lean`
fixes and `scripts/63_rung3_ball_mirror.py` mirrors, and the same backend
`zeta/rigor.py` uses for its enclosure-carrying paths. The `mpmath.iv`
rectangle context appears only as a cross-check, never as a producer.

```huntspec
id: r_a97060
question: Does the k=2 equal-depth tau-table of k2_closure.py still close when every scan-grade supremum is replaced by a ball-arithmetic enclosure over the same 6600 cells?
frontier: measured grade, 0 of 6600 cells nonpositive, worst margin +0.0529 signed-field caps and +0.0033 unsigned, both with a flat 1.05 cap inflation and no enclosures anywhere
proposed_attack: one ball-arithmetic envelope of D(1/2,.) on a uniform 1e-4 grid, reused by every cell, with the cell tau-sup as a running maximum; branch-and-bound plus a second-order small-depth lemma for the centre-centre row; exact rationals for the far rows and the budget floor
dead_routes:
  - rectangle interval arithmetic on the squared field, measured at rung 3 to cost 13.7x the width of balls on this shape of quantity
  - widening any cap to make a cell pass, which is forbidden by the brief and would void the comparison with the measured table
required_oracles:
  - Arb ball arithmetic via python-flint, outward-rounded at 96 bits
  - mpmath.iv rectangle interval arithmetic as an independent second backend
  - exact rational arithmetic in Python fractions for the far rows and the budget floor
kill_conditions:
  - a cell whose enclosure margin is nonpositive, which is reported as the cell and the amount rather than repaired
  - the enclosure of a quantity fails to contain the double-precision value the measured pass computed for it
  - the pass cannot be completed inside the run budget, which is reported as not-settled
agents_may:
  - build enclosure instruments under hunts/r_a97060/
  - re-run the existing table geometry unchanged and report the enclosure margins
  - record a correction to k2_closure.py or K2-TWO-SPECIES.md where the enclosure pass finds one
agents_may_not:
  - widen a cap, a window, or the budget floor to make a cell close
  - claim k >= 3, or claim the unequal-depth quantifier
  - promote the k=2 claim past the grade its weakest step earns
  - use the reserved word of zeta/rigor.py anywhere in this directory
```

## Kill conditions, as run

Stop and report if the package will not import after a genuine install, if the
run exceeds 75 minutes, or if closing a cell would require widening a cap.
"Not settled at this cost" is a valid result and is reported as one.
