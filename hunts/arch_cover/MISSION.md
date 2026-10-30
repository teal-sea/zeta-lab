# MISSION: what has to cancel for the Weil form to be positive

**Scope:** `hunts/arch_cover/` only. Nothing outside this directory is modified.
**Status:** exploratory. Nothing here is a result about the Riemann Hypothesis.

## The question

Weil's functional, in this repository's own convention (`zeta/weil.py`),

    W(h) = pole + arch + prime,
    pole  = h(i/2) + h(-i/2)
    arch  = (1/2pi) * int h(r) [Re psi(1/4 + ir/2) - log pi] dr
    prime = -2 * sum_n Lambda(n) n^{-1/2} g(log n)     (negative for h > 0)

and `W(h) = sum_rho h(gamma_rho)`. Positivity on the admissible class (`h = |f^|^2`)
is equivalent to RH. Define the **cover ratio**

    C(f) = (pole + arch) / (-prime),      so   C - 1 = W / (-prime).

`C >= 1` for every admissible `f` is RH, restated with the two computable
pieces separated: the pole and archimedean contributions must *cover* the
prime-weighted sum.

A first look (Gaussian, a = 0.05) shows pole = +2.025, arch = -1.909,
prime = -0.116: the pole and the archimedean integral cancel to four digits and
the prime side is the small leftover. If that is generic, then any numerics-based
"enclosed positivity" is a statement about a cancellation, and the number of
digits of cancellation is the real difficulty parameter of the method, not the
size of `W`.

## What is measured

For each family member: the enclosure of `W` (Arb, `prec_bits`),
the piecewise enclosures `pole`, `arch`, `prime`, the cover ratio as an
interval, and

    cancel_digits = log10( max(|pole|, |arch|) / |W| ),

the number of digits by which the large pieces cancel to produce `W`.

## What this hunt may not claim

- Not evidence for or against RH. `C >= 1` on finitely many `f` is what it says.
- Not a uniform bound: no statement survives outside the listed grid.
- Not independent: the archimedean term has no second backend in this tree
  (`enclose_weil_functional` reports `two_backend_cross_check unavailable`), so
  a failure of the archimedean quadrature would appear here as a cover ratio
  moving, not as an error.

## The door this opens, if it opens

If `cancel_digits` grows without bound along a family while `C` stays above 1,
then positivity on that family is asymptotically critical and any proof through
this functional must control the archimedean integral at that depth, not merely
prove a positive lower bound. That would be a statement about the shape of a
proof, and it is falsifiable: find a family whose `cancel_digits` stay bounded
and whose `C` is bounded away from 1.

## Instruments

`cover.py`, which writes `results.json`. Entry points: `scan`, `row`, `summary`.

## HuntSpec

```huntspec
id: arch_cover
question: How do the pole, archimedean and prime pieces of the Weil functional balance, and how deep is their cancellation?
frontier: measured here from 0.27 to 39.1 digits of cancellation on the Gaussian family; the prime term runs from 1e-10 to 1.24 over the same range
proposed_attack: evaluate the three pieces separately under Arb enclosures, compare both sides of the explicit formula, and read the cancellation depth against the zero side
dead_routes:
  - a uniform positive lower bound on W for all admissible h, killed here by the Gaussian family driving W to zero with every piece at O(1)
  - a place by place positivity argument, already recorded as not assembling globally in hunts/local_positivity
required_oracles:
  - Arb ball arithmetic from zeta.rigor.enclose_weil_functional with explicit truncation bounds
  - the verified zero list to height 10^4 for the independent side of the formula
  - the closed form depth a gamma_1 squared over ln 10, checked against every measured row
kill_conditions:
  - the arithmetic side disagrees with the zero side beyond the reported truncation tails
  - the closed form depth fails to reproduce a measured row to the printed digits
  - a sign is reported while the enclosure still straddles zero
agents_may:
  - evaluate
  - measure
  - compare
  - code
agents_may_not:
  - declare a bound
  - promote an observation to a result
  - use the reserved vocabulary of zeta/rigor.py
```

*Note, 2026-10-30 (landing review).* The oracle above names the closed form
`a gamma_1^2 / ln 10`. That form omits the pole's `e^{a/4}`, and against it the
second kill condition fired (17.38 measured against 17.35 at `a = 0.2`). The
form that reproduces every row is `a (gamma_1^2 + 1/4) / ln 10`; `RESULTS.md`
section 4(b) records both. The HuntSpec is left as written.
