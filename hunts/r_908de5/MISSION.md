# Hunt R-908DE5 — `beta := normLower`, and where the slack actually lands

## The question

`docs/25` §4.3 defect 2 and commit 44d3133 record the same defect from two
sides. The rung-3 grid sites carry a `pred_beta` drawn from mpmath point
evaluations *at the achievable bound*, so the site obligation

    normLower(B.inflate r)  >=  pred_beta                            (GRID)

sits at the line by construction — in ball arithmetic 12 of 104 sites clear it
by under 1 %, the thinnest (`g_right_15`) by 0.03 %. The named remedy is to
stop predicting the bound and read it off: **set `beta := normLower`**, which
the generator already computes exactly. (GRID) then holds by construction and
the question moves entirely into the obligation that consumes `beta`.

That obligation is not a modelling choice. It is the hypothesis of
`ZetaLean.DH.DH_lower_on_hcell` / `DH_lower_on_vcell`
(`lean/ZetaLean/DHCertSupport.lean`), one per endpoint of each grid cell:

    eps' + L * h_i / 2  <=  beta_i                                   (CELL)

with `L = 16`, `eps' = 1/2000`, `h_i` the gap to the next grid point.

`docs/25` §4.3 asserts that after the remedy "the cell condition then carries
>= 10x slack". **Whether that is true is the second half of this hunt**, and
the operator addendum names the outcome in advance: if the slack does not land
there as predicted, report it with the numbers rather than force the change
through.

## Scope

Permitted: `scripts/6*_rung3_*.py`, `lean/ZetaLean/` only where the remedy
needs it, this directory, and one case-log entry in `hunts/README.md`.
Not touched: `meta/`, `harness/`, root markdown, other hunts' lanes.

```huntspec
id: r_908de5
question: Does setting beta := normLower make the rung-3 grid obligation true by construction without breaking the cell condition that spends beta?
frontier: 104 grid sites pass (GRID) in ball arithmetic at margins 1.0003-1.5628 (commit 44d3133); docs/25 4.3 predicts >=10x slack in (CELL) after the remedy
proposed_attack: recompute normLower at every grid site in the arithmetic the generator actually emits, set beta to it, and re-check (CELL) in exact rational arithmetic
dead_routes:
  - raising nExp to widen the grid margins - the box width is bit-identical under nExp in 16, 20, 24, 28 (docs/25 4.3)
  - keeping a predicted beta and reporting its margin - the margin is an artifact of where the prediction was drawn, in any arithmetic
required_oracles:
  - exact rational arithmetic over the plan JSON, independent of any enclosure code
  - bit-exact Fraction mirror of the Lean interval arithmetic (scripts/61_rung3_mirror.py)
  - ball enclosure recomputation (scripts/63_rung3_ball_mirror.py) as a second, structurally different arithmetic
  - the Lean kernel, which refuses a literal equality the mirror got wrong
kill_conditions:
  - the remedy requires weakening any statement, including lowering L, widening eps' or dropping a grid point
  - (CELL) fails at any site under the measured betas and cannot be repaired inside the plan
  - the Lean toolchain will not install or Mathlib will not fetch
agents_may:
  - recompute enclosures in either arithmetic
  - change the generator's beta source and the validation script's grid verdict
  - report a prediction in docs/25 as wrong, with numbers
agents_may_not:
  - weaken a statement to make a site pass
  - claim the reserved word for anything in this directory
  - promote any number here to a result without the battery or the funnel
```
