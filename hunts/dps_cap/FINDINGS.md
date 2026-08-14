# Measured: the cap costs every digit at this point

Exploratory. Nothing here is a result (see `hunts/README.md`).

## The two numbers

`abs(epstein_completed(mpc('0.8','85.7'), (2, 1, 3), dps=D))`, mpmath 1.4.1,
this tree's `zeta/epstein.py`:

| D | magnitude | seconds |
| --- | --- | --- |
| 20 | 4.84638192796e-35 | 1.8 |
| 60 | 1.61745263238e-58 | 7.8 |
| 80 | 1.61745263238e-58 | 14.1 |

Raw values, real and imaginary parts included, in `results.json`.

## Reading

The `D = 20` value is **23 orders of magnitude too large, with no correct
digits at all**, not a value with fewer digits. `D = 60` and `D = 80` agree to
all twelve digits printed, so the reference is stable under refinement and the
gap is the low-precision run's, not the reference's.

The mechanism is visible in the code. `epstein_completed` builds `Lambda_Q(s)`
as `first + second/sqrt(d) + 1/(sqrt(d)(s-1)) - 1/s`
(`zeta/epstein.py:960-971`), a sum of terms of size `O(1)` at this point, and
at `s = 0.8 + 85.7i` the answer is `1.6e-58`. Reaching it requires roughly 58
digits of cancellation. At `dps = 20` plus the internal guard there are not 58
digits to cancel, so what comes out is the round-off floor of the largest term
rather than the function. This is the standard signature: the value does not
improve as precision rises, it is replaced.

A second route, in `sanity_stirling.py`, confirms which of the two is the
function. `Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)` with `d = 5.75`,
and `|(sqrt(d)/pi)^s Gamma(s)| = 2.6400016e-58` at this `s` (Stirling gives
`3.2768565e-58` for `|Gamma(s)|` against `3.2768529e-58` exact). So the two
candidate magnitudes imply

- `D = 60`: `|zeta_Q(0.8 + 85.7i)| = 0.613`, an ordinary value for a Dirichlet
  series just left of its abscissa of convergence;
- `D = 20`: `|zeta_Q(0.8 + 85.7i)| = 1.8e+23`, which no Epstein zeta function
  of a positive definite form takes at height 85.7.

That check touches neither lattice sum, so it is independent of the route it
is checking, and it points the same way as the refinement test.

## What this does and does not say

It says: at one point off the critical line at height 85.7, evaluating
`epstein_completed` at `dps = 20` returns noise, and `zeta/epstein.py:1091-1093`
is the one place in the file that forces that precision regardless of what the
caller asked for.

It does not say that any battery verdict is wrong. `count_zeros_box` winds an
argument, and a winding number can survive magnitudes being wrong when the
*phase* is not, or can be defended by the box being placed where the function
is `O(1)`. That is a separate measurement and this hunt did not run it. It is
recorded as a thread in `HANDBACK.json`, not answered here.

## Reproduce

```bash
.venv/bin/python hunts/dps_cap/measure.py
.venv/bin/python hunts/dps_cap/sanity_stirling.py
```
