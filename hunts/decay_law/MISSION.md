# MISSION: is the covering margin's decay the same in two families?

**Scope:** `hunts/decay_law/`. Nothing outside this directory is modified, apart from
the case-log entry this hunt owes in `hunts/README.md`.
**Status:** exploratory. Nothing here is a result about the Riemann Hypothesis.

The kill condition in the HuntSpec block below was written from the landed
rectangle table, before any tent row was computed. A quadrature check of the
tent formulas, run while building the instrument, printed two endpoint margins
before this file was committed. The tolerance was not changed after that print.
The tent measurement that RESULTS.md records is a fresh run, after this block.

## The question

Hunt #157 measured one family of rectangles. Its covering margin falls from
3.04e-2 at `b = 2` to 1.59e-4 at `b = 8`. The local exponents between those
five widths run from 2.23 to 5.58, so a single power is not a defensible
summary even of that one family (first written "roughly `b^{-2.5}`", corrected
in that hunt on 2026-10-30). This hunt asks whether a second family, of
independent shape and on an overlapping width window, has the same decay,
including the same split between the zero-side sum and the prime cost.

## The margin is a ratio, by construction

For either family, with `||f||^2 = 1` and `g` the autocorrelation,

    C = -prime_term = sum_p cost_p
    W_zeros = sum h(gamma)          both signs, verified ordinates, gamma <= 10^4
    cover - 1 = W_zeros / C

The margin is `W` normalized by the prime cost. It is not an independent
statement about the archimedean term. On the shared endpoints the log-log
exponents

    alpha_X = ln(X(2) / X(8)) / ln(4)

satisfy `alpha_m = alpha_W - alpha_C` exactly, for `X` the margin, the
zero-side sum, and the prime cost. That identity is the decomposition this
hunt compares across families.

From `hunts/weil_split/results.json`, the rectangle side of the kill (not
recomputed for the threshold) is

    alpha_m = 3.7902,   alpha_W = 1.3953,   alpha_C = -2.3949

The denominator carries 0.632 of that endpoint decay, the numerator 0.368.
The local exponents of the prime cost on that table run from 2.10 to 3.04 in
magnitude and move smoothly. The local exponents of `W_zeros` change sign
between `b = 4.5` and `b = 6`. Some of the margin's local-exponent scatter is
already, on the landed table, a zero-side oscillation rather than a steady
decay.

## The two families

Both are parameterized by `b`, the length of the support of `f`, so `g` is
supported on `[-b, b]` in both cases and the windows `b = 2` to `b = 8`
overlap. Both have `g(0) = 1`.

1. **Rectangle** (hunt #157, recomputed here only as a cross-check).
   `f = b^{-1/2} 1_{[-b/2, b/2]}`, `g(u) = (1 - |u|/b)_+`,
   `h(r) = b sinc^2(b r / 2)` with `sinc x = sin(x)/x`. This `h` decays as
   `1/r^2`. It is a scalar multiple of the Fejer pair at half-width `b/2`,
   which does not change the margin.

2. **Tent**, computed only after the kill block below.
   `f(x) = sqrt(3/b) (1 - 2|x|/b)_+` on `[-b/2, b/2]`. The autocorrelation is
   the piecewise cubic

       g(u) = 1 - 6v^2 + 6v^3          if 0 <= v <= 1/2
       g(u) = 2(1 - v)^3               if 1/2 <= v <= 1
       g(u) = 0                        if v >= 1

   with `v = |u|/b`, and `h(r) = (3b/4) sinc^4(b r / 4)`. This `h` decays as
   `1/r^4`. The nodes of `h` sit at half the rectangle's spacing. The shape is
   not a rescaling of the rectangle.

## What would kill the universal reading

The universal reading says the decay, including the split, is a property of
the width and not of the family.

**Quantity.** `alpha_X = ln(X(2)/X(8))/ln(4)`, for `X` the zero-side sum, the
prime cost, and the margin, rectangle against tent, at the shared endpoints
`b = 2` and `b = 8`.

**Tolerance.** 0.5. The rectangle's own local margin exponents already span
3.35 (2.23 to 5.58). A tolerance of 0.5 is a disagreement test, not a
restatement of that scatter, and it sits far above the numerical uncertainty
of the endpoint ratio (the landed margins are stable well below 1e-8 relative).

**Kill.** The reading is withdrawn if any one of the three exponents differs
by more than 0.5. A shared prime-cost exponent with a different zero-side
exponent fires this, which is the point of putting the kill on the
decomposition rather than on the margin alone.

A single exponent is called a defensible summary of a family only if that
family's local exponents, on the primary grid below, span at most 0.5. The
rectangle already fails this on the landed five-point grid. That fact is about
one family. It is not the kill. The kill is the cross-family comparison, so
that it can fire on the tent.

## Grid, fixed here

Primary grid: `b = 2 + 0.25 k` for `k = 0, ..., 24`. Twenty-five widths,
spacing 0.25, from 2 to 8 inclusive. The spacing is just over half the
rectangle node spacing `2π/γ_1` (about 0.444), so a zero-side oscillation is
visible if it is there. The kill uses only the endpoints, which are on this
grid and on the landed table.

## What this may not claim

- Not evidence for RH. Two compact families, one window.
- The zero side uses the verified ordinates up to `10^4`. The tail beyond that
  height is bounded and recorded. It is not zero. Where the arithmetic side
  and the zero side disagree, the covering ratio is taken from the zero side.
- A quadrature that is only good to a few digits is printed beside every
  number that depends on it, and that precision enters the fit residual of
  any such number. The margin itself is `W_zeros / C`, and `C` is a finite
  prime-power sum, so the margin is not a quadrature.
- No human has reviewed any of this.

## HuntSpec

```huntspec
id: decay_law
question: Is the covering margin's decay, including its split between the zero-side sum and the prime cost, the same for a rectangle and a tent of equal support width?
frontier: rectangle endpoint exponents on b=2 against b=8 are alpha_m=3.790, alpha_W=1.395, alpha_C=-2.395, from hunts/weil_split/results.json; local margin exponents there span 2.23 to 5.58
proposed_attack: recompute the rectangle on a fixed grid as a cross-check, then measure a tent whose transform is a fourth power of a sinc, and compare endpoint exponents to tolerance 0.5
dead_routes:
  - a single power of b, already refused by the rectangle local exponents spanning 2.23 to 5.58
  - reading the margin as an independent archimedean statement, refused because cover minus 1 equals W_zeros over the prime cost by construction
required_oracles:
  - the verified zero ordinates, for the zero-side sum
  - the finite prime-power sum for the prime cost, checked against the per-place overlap sum
  - the landed rectangle table in hunts/weil_split/results.json, for the kill's rectangle side
kill_conditions:
  - the universal reading is withdrawn if alpha_X = ln(X(2)/X(8))/ln(4) differs between the rectangle and the tent by more than 0.5, for X the zero-side sum, or the prime cost, or the margin
agents_may:
  - measure
  - compare
  - code
  - decompose
agents_may_not:
  - declare a bound
  - promote an observation to a result
  - use the reserved vocabulary of zeta/rigor.py
```
