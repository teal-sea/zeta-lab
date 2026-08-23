# RESULTS — hunt R-828C8B

**Fifth instance of the ceiling procedure: convex-program certificates for
Erdos's minimum overlap problem** (issue
[#111](https://github.com/teal-sea/zeta-lab/issues/111)).
Run `f0bbb14a-833d-456a-befa-2e4f74ba6947`, 2026-08-23, budget 30 minutes.

Grades on every figure: **VERIFIED** means exact arithmetic or exhaustive
enumeration with no floating point in the value. **MEASURED** means one
floating-point route. **INFERRED** means taken from the literature or argued
rather than computed here.

## Status: partly settled

Settled: the upper-bound side of the record is reproduced to within
`1.6e-4`, and the reproduction shows plainly which part of the procedure is
rigorous and which is not. Not settled: the published lower bound
`C >= 0.379005` was **not** reproduced, and this run establishes why the
plainest reconstruction of its skeleton cannot get there, which is a
different and smaller thing than reproducing it.

## The object

`A` a subset of `{1..2n}` with `|A| = n`, `B` the complement,
`M_k(A) = #{(a,b) in A x B : a - b = k}`, `M(n) = min_A max_k M_k(A)`,
`C = lim M(n)/n`. Rescaled, a step function `f : [0,2] -> [0,1]` with
integral 1 plays `1_A`, `g = 1_{[0,2]} - f` plays `1_B`,
`h_f(t) = int f(x) g(x-t) dx`, and `C = inf_f sup_t h_f(t)`.

The asymmetry that organises everything below: **any explicit `f` gives an
upper bound on `C` and no explicit `f` gives a lower bound.** That is why the
two published records were obtained by two unrelated methods.

## Reference values (INFERRED, literature check run 2026-08-23)

| bound | value | source |
| --- | --- | --- |
| upper | 0.382002 | Haugland 1996, step-function construction |
| upper | 0.380926 | Haugland 2016, *The minimum overlap problem revisited* |
| lower | 0.379005 | E. P. White, arXiv:2201.05704, Fourier reduction to a convex program |
| lower | 0.37912 | augmented program reported since |

Not re-derived here. Used as reference values, never as a check.

## A. The discrete truth (VERIFIED)

`M(n)` by exhaustive enumeration of all `C(2n,n)` splits, exact integers,
symmetry `M_k(B) = M_{-k}(A)` used to fix position 0 in `A`.

| n | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| M(n) | 1 | 2 | 2 | 3 | 3 | 3 | 4 | 4 | 5 |
| M(n)/n | .500 | .667 | .500 | .600 | .500 | .429 | .500 | .444 | .500 |

The ratio oscillates with parity and its minimum over this range is
`3/7 = 0.4286` at `n = 7`. Ten terms are nowhere near `0.38`, which is the
practical reason the constant is attacked through the continuous problem and
not through `M(n)` itself.

## B. The ceiling on the upper-bound side (MEASURED)

`min_f max_j h_j` over step functions with `m` equal pieces, by SLSQP on the
epigraph with analytic jacobians, restarts seeded from the upsampled previous
solution plus deterministic and random starts.

| m | value | seconds | gap to Haugland 2016 |
| --- | --- | --- | --- |
| 4 | 0.400000000 | 0.02 | +0.019074 |
| 8 | 0.385071709 | 0.05 | +0.004146 |
| 16 | 0.381833095 | 0.32 | +0.000907 |
| 32 | 0.381083768 | 1.68 | +0.000158 |
| 64 | 0.381083768 | 9.11 | +0.000158 |
| 128 | 0.381083768 | 27.37 | +0.000158 |

**The value stops moving at m = 32, and that stall is the solver's, not the
parameterisation's.** The argument is one line and it matters: an `m`-piece
step function upsamples to a feasible `2m`-piece one with the same value, so
the optimum is non-increasing in `m`; Haugland's `0.380926` is a step function
strictly below `0.381084`; therefore the `m`-piece optimum for large `m` is
strictly below what this solver returned. The three identical rows are SLSQP
reporting the upsampled point stationary, not the family running out of room.

So the honest reading of the ceiling question on this front is: **the
published upper bound is not obviously where somebody stopped, and a
half-hour of generic local optimisation does not reach it.** The refinement
cost grows roughly as `m^2.5` here (0.32 s to 27 s over a factor of 8 in `m`),
which sets the price of pushing further.

## C. The acceptance step (VERIFIED)

The value of an `m`-piece step function is a finite sum of products of its
pieces. Round the pieces to multiples of `1/D`, repair the mass constraint in
`Q` so the object is exactly feasible, then evaluate `max_j h_j` with
`fractions.Fraction`. No floating point survives into the value.

| m | D | exact value | penalty vs the float optimum |
| --- | --- | --- | --- |
| 32 | 64 | 0.381759644 | +6.76e-04 |
| 32 | 640 | 0.381152649 | +6.89e-05 |
| 64 | 128 | 0.381565094 | +4.81e-04 |
| 64 | 1280 | 0.381139717 | +5.60e-05 |
| 128 | 256 | 0.381321907 | +2.38e-04 |
| 128 | 2560 | 0.381094627 | +1.09e-05 |

Best exactly-evaluated upper bound obtained here:

> **C <= 9990167 / 26214400 = 0.381094627...**

exhibited by an explicit rational step function with 128 pieces
(`results.json`, `B_ceiling.best_f_by_m["128"]` rounded at `D = 2560`).
This is weaker than Haugland's 0.380926 by `1.7e-4` and is stated as a
reproduction, not as a result.

Two things about the acceptance step are worth stating because they are the
soundness read the issue asked for.

1. **The rounding penalty is always positive and it is not negligible at the
   obvious denominator.** At `D = 2m`, the natural "round to the grid"
   choice, rounding costs between `2.4e-4` and `6.8e-4`, which is larger than
   the entire remaining gap to the published constant. A procedure that
   optimises in floats to `1e-4` and then rounds coarsely has thrown away
   more than it gained. Ten times finer costs nothing in runtime here and
   drops the penalty to `1.1e-5`.
2. **On this side, "the dual certificate is checked" has a trivial answer:
   there is no dual.** The accepted object is primal, its value is a finite
   rational, and checking it is a finite exact computation any reader can
   rerun in seconds. That is the cleanest possible acceptance step, and it is
   available only because this is the upper-bound side. What a
   target-encoding defect would look like here is correspondingly specific:
   not a wrong arithmetic, but a wrong *enumeration* of shifts, which reports
   the value too small and so reports a bound better than the one the object
   supports. That is the failure this hunt guarded (front E).

## D. The lower-bound side, where the convex program lives (VERIFIED / MEASURED)

Any lower bound must survive every measurable `f`, so it cannot be a
construction. The one move available is averaging: for any probability
density `w` on the shift axis,

```
sup_t h_f(t)  >=  int w(t) h_f(t) dt  =  <f, w * 1_{[0,2]}>  -  <f, w * f>.
```

The first term is linear and easy. The second is the quadratic term and is
the entire difficulty.

**D1 (VERIFIED).** Uniform `w` on the whole shift range `[-2,2]`:
`int h_f = (int f)(int g) = 1` for every admissible `f`, and the range has
length 4, so `C >= 1/4` exactly and unconditionally. That is `0.129` below
the published lower bound and is the free part of the method.

**D2 (VERIFIED analytically, MEASURED over 200 random weights).** The naive
Fourier handling of the quadratic term is vacuous for *every* weight. Using
`0 <= f <= 1` and `int f = 1` gives `||f||_2^2 <= 1`, hence
`<f, w*f> = int what |fhat|^2 <= (sup what) ||f||_2^2 <= sup what`. But
`w >= 0` with `int w = 1` forces `what(0) = 1`, so `sup what = 1` for every
admissible weight, and the bound collapses to
`sup h >= <f, w*1> - 1 <= 0`. Measured over 200 random weight profiles:
`min sup|what| = 1.000000` to six places, best resulting bound `0.000000`,
number of weights giving anything positive: **0**. The published program
therefore cannot be discarding the quadratic term; it must be exploiting the
finite support of `f` in a way this reconstruction does not.

**D3 (MEASURED, and an upper bound by construction).** For a fixed weight
profile, the best the averaging skeleton could ever give is
`min_f int w h_f`. Local minimisation returns the value at an *explicit
admissible* `f`, so the number returned is a rigorous upper bound on what
that weight can yield:

| weight profile | the averaging bound with this w is at most |
| --- | --- |
| uniform on the shift range | 0.252632 |
| tent | 0.250000 |
| Gaussian, narrow | 0.190914 |
| linear in \|t\|, edge-weighted | 0.170139 |

All four are far below `0.379005`. **Plain single-weight averaging is not
White's program**, and this run says so with witnesses rather than by
assertion: concentrating the weight makes the bound worse, not better, which
is the opposite of the intuition that a sharper test function tests harder.

**What was not settled, plainly.** The reconstruction of the published convex
program was not completed inside the budget, so items 1, 2 and 3 of the issue
were answered for the upper-bound family and only item 4 was answered for the
lower-bound family. In particular this hunt did **not** reproduce
`0.379005`, did not read White's discretisation, and did not check whether
the published dual point is verified or merely reported. The one soundness
observation it can make from outside is stated as a thread below: a
discretised dual value is not automatically a lower bound, because
restricting `f` to step functions is a *restriction*, so the discretised
inner minimum bounds the true one from **above**, in the unsafe direction.
Whether the published program handles that is exactly what a next run should
read.

## E. The guard, and its power (MEASURED)

Every number in fronts B and C rests on: *for a step function, the supremum
over real shifts is attained on the shift grid.* It is true (a correlation of
two functions constant on a common grid is piecewise linear with breakpoints
on that grid), and its failure direction is the flattering one, so it was
guarded before any value was reported.

Guard: `grid_sufficiency_defect(f, evaluator)`, the 8x-refined reference
supremum minus the evaluator's reported maximum. Mutants, 40 random
admissible `f` at `m = 24` (`probe.py --mutant`, `guard_mutants.json`):

| planted fault | max defect | fired |
| --- | --- | --- |
| none (negative control) | 0.000000 | no |
| enumerate only shifts j >= 0 | 0.104411 | **yes** |
| enumerate every other shift | 0.066916 | **yes** |
| drop the outer half of the shift range | 0.000000 | no |

Two of three caught, and the third is a genuine known miss recorded as such:
the maximising shift is interior for every admissible step function tried, so
truncating the range to its inner half changes nothing the guard can see. The
guard establishes that the enumeration is not mis-strided or half-blind; it
does **not** establish that the range is wide enough. Recorded in
`harness/departments/guard_ledger.py` with that miss written into the record.

## Run manifest

| what | value |
| --- | --- |
| entry point | `.venv/bin/python hunts/r_828c8b/probe.py` (`--quick` for a 20 s pass, `--mutant` for front E) |
| wall clock, full pass | ~50 s for fronts A-D, ~1 s for front E |
| seed | `numpy.random.default_rng(0x828C8B)`, fixed |
| outputs | `results.json`, `guard_mutants.json` |
| dependencies | numpy, scipy, python `fractions`; no mpmath, no network |
| environment | recorded in `results.json.environment` |

## What this is not

Nothing here is evidence for or against RH (`docs/08`). No new bound on `C`
is claimed: the best exact upper bound obtained, `9990167/26214400`, is
weaker than the published one. The reserved word is not used anywhere in this
hunt.

## Loose threads

- **The discretised dual is not automatically sound, and nobody checked here
  whether the published program knows that.** Restricting `f` to step
  functions is a restriction, so `min over step functions >= min over all f`:
  a discretised inner minimum bounds the true dual value from above, in the
  direction that inflates a lower bound. Why it might matter: it is precisely
  the target-encoding defect shape this lab audits, and on the lower-bound
  side it would silently manufacture a bound that is not there. First step:
  read section 3 of arXiv:2201.05704 and identify the interpolation or
  rounding argument that closes the gap between the discretised program and
  the continuous infimum. If there is none, the bound needs one.
- **The m-piece optimum is not where SLSQP stops.** The stall at `m = 32` is
  a solver artifact and the true `m`-piece optimum is provably below it for
  large `m`. Why it might matter: the whole ceiling procedure depends on
  telling "the parameterisation ran out" from "the search ran out", and this
  run is a clean example where a naive reading would have confused them.
  First step: replace the epigraph SLSQP with an alternating scheme that
  solves the linear program in `f` for a fixed active shift set and updates
  the set, which is the structure Haugland's constructions suggest.
- **The averaging bound gets worse as the weight concentrates.** Uniform
  0.2526, tent 0.2500, Gaussian 0.1909, edge 0.1701. Why it might matter: it
  is a measured contradiction of the natural intuition, and it localises
  where White's extra strength has to come from (the interaction between the
  support constraint on `f` and the quadratic term, not the choice of test
  weight). First step: compute `min_f int w h_f` for the two-parameter family
  interpolating uniform and tent and see whether the maximum over the family
  sits exactly at uniform.
- **`M(n)/n` has a parity structure worth one cheap look.** Every even `n` in
  the computed range gives exactly `1/2`; the odd ones fall below. Why it
  might matter: if `M(2k) = k` holds for all `k` it is a clean finite
  statement, and if it fails at some `n` that failure is the interesting
  case. First step: extend the exhaustive search to `n = 11, 12` with a
  bitset-parallel inner loop, and check `M(2k) = k` against the OEIS entry
  for the sequence before spending anything larger.
