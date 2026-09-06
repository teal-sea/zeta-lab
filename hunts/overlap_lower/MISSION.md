# MISSION: hunt `overlap_lower`

**Sixth instance of the ceiling procedure, and the first one aimed at a
*lower* bound.** Erdos's minimum overlap constant `C`. Opened 2026-08-23.

## Why this side

The upper bound on this constant has been pushed four times in twelve months
by four different systems: AlphaEvolve, TTT-Discover, TogetherAI, SimpleTES,
a crowd all standing on one side of the same number, moving it by `0.000059`
in total. The lower bound moved once in sixty-three years before 2022 and once
since. It is also the side a checker can attack, because a lower bound is a
statement about *every* admissible function and therefore needs a dual object,
not a construction.

So the question this hunt asks is the lab's usual one, asked where nobody is
standing: **is the published lower bound the limit of its own method, or the
point at which the search stopped?**

The method is E. P. White's convex program (arXiv:2201.05704, Acta Arithmetica
208 (2023) 235-255). Its author wrote down an answer to exactly this question
in his concluding remarks, *"it seems that the limit of this method is not
much larger than 0.379"*, on the evidence of a single pair of solves. This
hunt turns that sentence into a sweep.

## The object

For `n >= 1` let `A` be a subset of `{1..2n}` with `|A| = n` and `B` its
complement. With `M_k(A) = #{(a,b) in A x B : a - b = k}`,
`M(n) = min_A max_k M_k(A)` and `C = lim_n M(n)/n`. In White's continuous
normalisation, `f : [-1,1] -> [0,1]` with `int f = 1`, `g = 1 - f`,
`M(x) = int_{-1}^{1} f(t) g(x+t) dt`, and `C = inf_f sup_{x in [-2,2]} M(x)`.

## Relation to hunt #85

`hunts/r_828c8b/` reproduced the *upper* side of this constant and explicitly
recorded that it did **not** reproduce the lower side, leaving as its first
loose thread: *"read section 3 of arXiv:2201.05704 and identify the
interpolation or rounding argument that closes the gap between the discretised
program and the continuous infimum."* This hunt is that thread pulled. Its
answer is recorded in `RESULTS.md` front A: the gap is closed because the
program discretises `M`, never `f`, so it is a relaxation and not a
restriction.

## What this hunt may write

`hunts/overlap_lower/` only, plus one case-log line in `hunts/README.md` and
one workflow file `.github/workflows/hunt-overlap-lower.yml` that exists so
the sweep runs on CI runners rather than on the operator's laptop.

## Scope, stated before the numbers

Nothing here is evidence for or against RH (`docs/08`). The reserved word for
enclosure-carrying claims belongs to `zeta/rigor.py` and the Lean arm and is
not used. **No new bound on `C` is claimed**: every value this hunt computes
is below the published lower bound, and that is reported as a reproduction
falling short, never as a result.

```huntspec
id: overlap_lower
question: is the published lower bound on Erdos's minimum overlap constant the limit of its own convex program, or the point at which the search stopped
frontier: 0.37912 <= C <= 0.380868 published (Kim-Pilanci 2026 preprint lower, SimpleTES 2026 upper); the peer-reviewed lower bound is White 2022 at 0.379005; the public catalogue teorth/optimizationproblems still lists 0.379005
proposed_attack: reimplement White's section 4 and section 5 programs from the paper's displayed constraints, sweep their free parameters N, T, R and the (h,p,q) box, and measure where the value saturates
dead_routes:
  - claiming a lower bound on C from an explicit construction: constructions bound C from above only
  - the naive Fourier bound on the quadratic term, killed in hunt r_828c8b: for any probability weight w, what(0) = 1 forces sup what = 1 and the bound is at most zero
  - single-weight averaging over the shift axis, capped at 0.2526 by explicit witnesses in hunt r_828c8b
  - restricting f to step functions: that is a restriction, so the discretised inner minimum bounds the true one from above, in the unsafe direction
  - relaxing f to its cell masses alone: the tight bound on the quadratic term given only cell masses is min(F_i, F_{i-k}), which is attained at the constant function and returns zero
required_oracles:
  - exact rational arithmetic (python fractions) with directed rounding of every irrational coefficient, so no floating point survives into an accepted value
  - the published literature, read at the source and cited by arXiv identifier, journal and access date, used as a reference value and never as a check
  - monotonicity of the program's optimum in its own parameters, which is provable and therefore a check the solver cannot talk its way out of
kill_conditions:
  - the exact rational re-evaluation of a dual point fails feasibility, in which case the float value is withdrawn and the exact number reported instead
  - the reimplementation's value at White's own parameters differs from his published value by more than the reproduction tolerance, in which case the reimplementation is reported as unfaithful and the sweep is reported as a sweep of something else
  - the sweep produces a value above the published bound without an exact dual object behind it, in which case no bound is claimed
  - a planted fault in the program builder raises the value and no check in this hunt catches it, in which case the miss is recorded as a miss
agents_may:
  - reimplement the published program from its displayed constraints
  - sweep the parameters and report where the value saturates
  - relax the program further when the solver available cannot handle it, provided the relaxation is in the direction that lowers the value
  - plant faults in this hunt's own builders and report which are caught
  - report the gap to the published constant in both directions
agents_may_not:
  - claim a new bound on C without an exact dual object valid for every admissible f
  - describe a floating-point solver output as a bound
  - present the section 4 value as a bound on C: it is a bound for even M only
  - use the reserved word that zeta/rigor.py and the Lean arm own
  - edit hunts/frontier_math, meta/, lean/, zeta/, harness/, or any root markdown file other than a regenerated CONTEXT.md
```
