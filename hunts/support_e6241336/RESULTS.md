# Support run `e6241336`: one Epstein value, checked

**The answer: yes.** At `dps=60`,

```
abs(epstein_completed(0.8+85.7i, (2,1,3))) = 1.617452632377971461454064e-58
```

which is `1.0109 x` the claimed `1.6e-58`. That is 1.1% away, so it agrees to
within an order of magnitude by a wide margin: `log10` of the ratio is 0.0047,
against the 1.0 an order of magnitude would allow.

The full complex value at `dps=60` is

```
-1.566243383527633990474456e-58 - 4.037755336103688597427175e-59 i
```

Reproduce with `python hunts/support_e6241336/measure.py` (about 80 s). Data:
`results.json`.

## How much of that number is real

`dps=60` does not buy 60 digits here. `epstein_completed` splits the Mellin
transform of the form's theta series at `t = 1`; at `s = 0.8 + 85.7i` the pole
terms alone are of size 1e-3 while the answer is of size 1e-58, so about 55
digits cancel. The working precision is `dps + 10`, which leaves roughly 15.

Measured, rather than argued:

| `dps` | `abs(Lambda_Q(s))` |
|---|---|
| 40 | `4.216375003267013250951888e-53` |
| 50 | `1.617483602520170735821834e-58` |
| 60 | `1.617452632377971461454064e-58` |
| 80 | `1.617452632377971296327251e-58` |
| 120 | `1.617452632377971296327251e-58` |

`dps=40` is still the roundoff floor and is 5 orders too large. `dps=50` has
about 5 correct digits, `dps=60` has 16.0 (relative error 1.021e-16 against the
`dps=120` value), and 80 and 120 agree to all 25 digits printed. So the
`dps=60` return answers the question asked and is good to 16 digits, but a
caller who prints 25 of them is printing 9 digits of noise.

This reproduces `hunts/dps_cap` (Hunt #12), which measured the same quantity
for a different reason: 80 and 120 here match its recorded converged value
`1.617452632377971296327251e-58` digit for digit.

## The three checks, none of which is "run it again"

The ladder above only says the routine converges. It does not say it converges
to the right thing, so three checks were run against routes that do not share
its cancellation.

**A. Normalisation, at a point where the Dirichlet series converges.**
`Lambda_Q(s) / ((sqrt(d)/pi)^s Gamma(s))` must equal
`sum_{(m,k) != (0,0)} Q(m,k)^{-s}`. At `s = 4`, summed over a 801 x 801 lattice,
the relative difference is 1.9e-17 for `(1,1,6)` and 3.7e-17 for `(2,1,3)` and
`(2,-1,3)`. So the completion the routine applies is the one the docstring
claims, with `d = |D|/4 = 5.75`.

**B. The Dedekind identity, at the actual point.** Discriminant `-23` has class
number 3 with reduced forms `(1,1,6)`, `(2,1,3)`, `(2,-1,3)`, and

```
sum_Q Lambda_Q(s) = 2 (sqrt(23)/2pi)^s Gamma(s) zeta(s) L(s, chi_-23)
```

the 2 being the number of units. The right-hand side was built from mpmath's
`zeta` and Hurwitz `zeta`, with `chi_-23` the Legendre symbol `(n/23)`. That
route reaches a quantity of size 1e-58 with **no cancellation at all**: the
smallness comes from `Gamma(0.8+85.7i)` directly, which mpmath evaluates to full
relative accuracy. The two sides agree to 4.0e-17 at `dps=60` and 6.3e-76 at
`dps=120`.

This is the check that makes the number quotable. A defect in the lattice sums
would have to conspire across three forms to leave that identity standing, and
the identity is the one place where a route with no cancellation meets a route
with 55 digits of it.

**C. The functional equation across the inverse class.**
`Lambda_(2,1,3)(s)` against `Lambda_(2,-1,3)(1-s)`: relative difference 4.4e-16
at `dps=60` and 1.5e-75 at `dps=120`.

## One defect found, in this run's own instrument

The first pass built `s = mpc("0.8","85.7")` at module scope, where `mp.dps` is
mpmath's default 15. That rounds the argument to 53 bits. Since
`d/ds log Lambda` is about `log|s|`, roughly 4.5, at this point, a half-ulp
error in 85.7 moves the magnitude in its 15th digit: the low-precision argument
returns `1.617452632377967865948261e-58`, which is 2.1e-15 off. The first pass
therefore disagreed with Hunt #12 at the 16th digit and, briefly, took its own
value for the reference one.

`epstein_completed` cannot repair this. It calls `mpmathify` on whatever it is
handed, inside `workdps(dps + _GUARD)`, but an `mpf` that arrives short of
digits stays short. Passing a string or building `s` inside a high-precision
block both work; passing a Python `complex`, or an `mpc` built at the ambient
default, does not. The same trap silently capped this run's first version of
check C at 2.5e-15, because `1 - s` was formed at the ambient precision.

Recorded as a thread in `HANDBACK.json`, not acted on: touching `zeta/` is
outside this run's scope.

## Scope

One point, one form, two routines. Nothing here is evidence for or against the
Riemann hypothesis (`docs/08-why-it-is-hard.md`). Nothing here says anything
about where the Davenport-Heilbronn off-line zero sits, even though
`0.8 + 85.7i` is near it: `epstein_completed` on the form `(2,1,3)` and the
Davenport-Heilbronn function are different objects, and this run evaluated only
the first. The word this run is entitled to is *measured*, at the first rung of
the ladder for the value itself and at the second for the agreement between
independent routes.
