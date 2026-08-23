# MISSION — hunt R-828C8B

**Fifth instance of the ceiling procedure: convex-program certificates for
Erdos's minimum overlap problem.** Opened from
[issue #111](https://github.com/teal-sea/zeta-lab/issues/111), run
2026-08-23, budget 30 minutes, no operator supervision.

## The question

For `n >= 1` let `A` be a subset of `{1..2n}` with `|A| = n` and `B` its
complement. With `M_k(A) = #{(a,b) in A x B : a - b = k}`, put
`M(n) = min_A max_k M_k(A)`. The minimum overlap constant is
`C = lim_n M(n)/n`.

The published record has an unusual shape: the **upper** bounds are explicit
step-function constructions (Haugland, 0.382002 in 1996 and 0.380926 in 2016)
and the **lower** bounds come from a convex program (White, arXiv:2201.05704,
0.379005, since augmented to 0.37912). Two records, two unrelated methods, and
only one of them is an object a checker can accept.

This hunt asks the ceiling question of both sides: **is the published value
what the parameterisation's own limit gives, or is it where somebody stopped?**

## What this hunt may write

`hunts/r_828c8b/` only, plus one case-log line in `hunts/README.md` and one
appended record in `harness/departments/guard_ledger.py`.

## Scope, stated before the numbers

Nothing here is evidence for or against RH (`docs/08`). The reserved word for
enclosure-carrying claims belongs to `zeta/rigor.py` and the Lean arm and is
not used here. No
new bound on `C` is claimed: this hunt's best exact upper bound is *weaker*
than Haugland's, and that is reported as such.

```huntspec
id: R-828C8B
question: is the published minimum-overlap record the limit of its own parameterisation, or the point at which the search stopped
frontier: 0.379005 <= C <= 0.380926 published (White 2022 convex program; Haugland 2016 step function); the augmented program reports 0.37912 on the lower side
dead_routes:
  - claiming a lower bound on C from an explicit construction: constructions bound C from above only, so no f whatsoever is evidence for a lower bound
  - the naive Fourier bound on the quadratic term: for any probability weight w, what(0) = 1 forces sup what = 1 and the resulting bound is at most zero for every w
  - reading a discretised dual value as a lower bound: restricting f to step functions is a restriction, so the discretised inner minimum bounds the true one from ABOVE
required_oracles:
  - exhaustive bitmask enumeration of all C(2n,n) splits for n <= 10
  - exact rational arithmetic (python fractions) re-evaluating every accepted step function with no floating point in the value
  - the published literature, cited by arXiv identifier and journal, used as a reference value and never as a check
kill_conditions:
  - the exact rational re-evaluation of an accepted step function exceeds the float value it was accepted on, and the hunt reports the exact number instead of the float
  - the m-piece minimax value stops decreasing while the published record sits strictly below it, in which case the stall is the solver's and must be reported as the solver's
  - any claimed lower bound on C that is not backed by a dual object valid for every measurable f
agents_may:
  - formulate the continuous relaxation and solve the m-piece minimax numerically
  - re-evaluate any accepted object in exact rational arithmetic
  - plant faults in this hunt's own evaluators and report which the guard catches
  - report the gap to the published constant in both directions
agents_may_not:
  - claim a new bound on C without a dual object that survives every measurable f
  - describe a numerically optimised step function as a proof of anything beyond the upper bound its exact re-evaluation gives
  - use the reserved word that zeta/rigor.py and the Lean arm own
  - edit hunts/frontier_math, meta/, lean/, or any root markdown file
```
