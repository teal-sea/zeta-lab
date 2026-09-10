# MISSION: `quotient_exponent` — the barrier law as a surface, not a diagonal

`hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/RESULTS.md`
section 4.6 reports the attainable-quotient floor `T*(y, N) - psi(N)` at four
cutoffs, all on the diagonal `y = floor(sqrt N)`, and reads a law off them:

> T* = (0.18 to 0.23) N^{3/4} over four decades, the fitted exponent from 10^3
> to 10^6 is 0.73.

and, of the barrier conjecture stated for the all-cell floor `V*`:

> The conjecture in BARRIER.md Section 3 should be read for T* as well as V*,
> with the constant 0.2 in place of 0.32; nothing in this note proves either.

The conjecture's shape is `E >= c N / sqrt(y)`. On the diagonal `y` and `N`
move together, so a diagonal cannot separate the `N` exponent from the `y`
exponent, and a floor effect in `y = floor(sqrt N)` is indistinguishable from
either. The doors section of `hunts/quotient_certificate/RESULTS.md` names the
support bound as the one frozen constant with trade shape and asks for exactly
this.

## Two obstacles, and what this hunt does about them

**The objective cancels.** Minimising `sum_j c_j log(floor(N/j)!)` asks a float
solver for a quantity near `1e4` as a difference of quantities near `1e8`. The
Chebyshev identity rewrites the same programme as `sum_q w_q e_q` over
attainable cells with every `w_q >= 0` and every `e_q >= 0`, so the objective is
a sum of nonnegative terms equal to the excess itself and nothing cancels. The
two are algebraically identical, and the identity that makes them so is
measured here rather than assumed.

**The diagonal is one line.** So the measurement is a grid in `(y, N)`, and the
reported quantity is `E sqrt(y) / N`, which the conjecture's shape says is a
constant.

```huntspec
id: quotient_exponent
question: Is the attainable-quotient excess of the shape c N / sqrt(y), and where in y does it reach zero?
frontier: T*(floor(sqrt N), N) - psi(N) published at 41.28, 226.83, 1035.23, 6414.83 for N = 10^3..10^6, read as (0.18 to 0.23) N^{3/4} with fitted exponent 0.73; the barrier conjecture for T* is stated with constant 0.2 and is unproved
proposed_attack: rewrite the objective so that it is the excess itself, extend the diagonal to 10^7, then measure the two-variable surface E(y, N) and bisect in y for the support at which the excess reaches zero
dead_routes:
  - reading a two-variable law off the diagonal y = floor(sqrt N)
  - inferring zero excess from a column count, which hunts/quotient_certificate refuted with an exact N = 27, y = 9 example whose minimum excess is log 2
required_oracles:
  - the Chebyshev identity sum_q w_q floor(q/j) = log(floor(N/j)!) and sum_q w_q = psi(N), measured at every cutoff before the solve is trusted
  - recomputation of the objective from the returned coefficients through the constraint definition, which the solver's own objective does not pass through
  - the four published diagonal values as a control on the reformulation
kill_conditions:
  - the reformulated programme disagrees with a published diagonal value
  - a reported zero has a returned coefficient vector that violates a constraint by more than the solver's own residual
  - the identity defect exceeds the scale of the excess being reported
agents_may:
  - solve, sweep, bisect and fit inside hunts/quotient_exponent/
  - report where a published reading is narrower or wider than the measurement supports
agents_may_not:
  - claim an asymptotic exponent from a finite ladder
  - describe a floating LP value as an exact one
```
