# Hunt: gate-5 property 6 — does "no zeros in a box off the critical line" distinguish?

**Status when this file was committed: nothing has been computed.** The
parameters below were fixed before a single truth value was produced. The
commit order is the evidence; see `git log` for this file versus
`results.json`.

## Scope

This hunt is exploratory. Nothing here is a result, and nothing here is
evidence for or against RH (`docs/08`). The question is only which
structural properties separate zeta from RH-violating look-alikes.

May write: `hunts/gate5_p6_c/`, and one case-log entry in `hunts/README.md`.
May not write: `zeta/`, `harness/`, `lean/`, `meta/`, any other `hunts/`
directory, any root markdown file.

## The question

`docs/09` gate #3 property 6:

> in a box strictly off the critical line, the completed function has no
> zeros

Does this **DISTINGUISH** (holds of zeta, fails on all three rivals in
`zeta.epstein.battery`) or is it **VACUOUS** (some rival satisfies it too)?

The four functions are the battery's: zeta (via ξ), Davenport–Heilbronn
(via f, equivalently F), and the Epstein zetas of discriminant −23,
forms (2,1,3) and (1,1,6) (via Λ_Q).

## The prior attempt, and why its parameters are not reused

A previous run computed `count_zeros_box(0.6+80i, 0.9+90i)` across four
functions at working precision and timed out at 50 minutes. That box has a
boundary of length 2·(0.3 + 10) = 20.6 and, at the module's forced
subdivision step for t ≈ 90, roughly 176 forced segments per function, each
costing at least two evaluations before adaptive refinement. The binding
cost is the Epstein evaluation. Timed here, blind to any zero location,
before choosing anything:

| function | seconds per evaluation at dps = 20 |
| --- | --- |
| ξ | 0.0006 |
| f (Davenport–Heilbronn) | 0.0067 |
| F (completed DH) | 0.0092 |
| Λ_Q, form (2,1,3) | 0.86 at t = 17, 1.45 at t = 86 |
| Λ_Q, form (1,1,6) | 1.00 at t = 17 |

So the Epstein arm alone is three orders of magnitude more expensive than
the other two, and the previous box asks it for something on the order of a
thousand evaluations at its most expensive height. That is the whole reason
that run did not finish. **The design constraint is therefore: total
boundary length, not box area.**

(These are timings of function evaluation. They are measurements of cost,
not of the property, and they were taken before any box was chosen. No
winding number had been computed at the time this file was committed.)

## What I am actually going to test, and why

Property 6 is **box-dependent by construction**: it quantifies over a box
that the statement does not name. So the first thing worth deciding is not
"does it distinguish" but **"is the question well posed"**. The design is
built to answer that directly rather than to gamble one box.

The instrument: hold the σ-band fixed and vary only the height window. If
the verdict flips between two windows of the *same* band, then the property
as stated has no truth value — the box is a free parameter carrying the
answer.

### The σ-bands

**Band A: σ ∈ [0.7, 0.9].** Strictly off the critical line (0.2 clear of
σ = 1/2), strictly inside the critical strip (0.1 clear of σ = 1, which is
where Λ_Q has its pole and where the meaning of the claim changes). It
contains 0.80852, the real part of the Davenport–Heilbronn off-critical-line
zero this repository pins in `OFFLINE_ZERO_RE`. **That containment is
deliberate and declared**: band A is chosen so that one preregistered window
is *known in advance* to fail for one rival, which is what makes the
flip-test meaningful. It is not a blind choice and is not reported as one.

**Band B: σ ∈ [1.05, 1.55].** Strictly right of σ = 1, clear of the Λ_Q
pole at s = 1. Zeta is zero-free here as a theorem (Euler product), with no
appeal to RH and no numerics needed; the rivals have no such theorem. This
band tests whether property 6 is anything other than the Euler product
already tested by property 5.

### The height windows

- **W1 = [85.5, 85.9]** — the literature-anchored window. Declared
  non-blind: Spira (*Math. Comp.* 1994) and this repository both place a
  Davenport–Heilbronn zero at 0.808517 + 85.699348·i inside it. Its job is
  to realise the "a rival fails" pole of the well-posedness question, not to
  supply a verdict.
- **W2 = [10.0, 14.0]** — blind. Chosen as a width-4 window at low height,
  where the boundary is short and the module's forced step is longest, hence
  cheapest. I do not know where any rival's zeros are in it.
- **W3 = [40.0, 44.0]** — blind, a second width-4 window at middling height,
  to check whether whatever W2 reports is typical rather than an accident of
  one window.

### The boxes, fixed now

| box | σ-band | t-window | boundary length | blind? |
| --- | --- | --- | --- | --- |
| B1 | [0.7, 0.9] | [85.5, 85.9] | 1.2 | no, declared |
| B2 | [0.7, 0.9] | [10.0, 14.0] | 8.4 | yes |
| B3 | [0.7, 0.9] | [40.0, 44.0] | 8.4 | yes |
| B4 | [1.05, 1.55] | [10.0, 14.0] | 9.0 | yes |

Total boundary length 27, against the prior attempt's 20.6 — but spread
over four boxes, three of which sit at heights where the Epstein evaluation
is roughly half the cost it has at t = 86, and only one of which sits high.

### Precision and route

- **dps = 20** for every count. This is `count_zeros_box`'s documented
  working precision and the value `zeta.epstein`'s own interfaces clamp to
  (`dps=min(_d, 20)`); the winding number is an integer and the routine
  raises if the residual exceeds 1e-6, so more digits buy nothing here and
  cost linearly.
- **Route: the argument principle**, `zeta.epstein.count_zeros_box`, driven
  through the battery interfaces so that each function is counted by the
  same code. The default forced step is used unchanged.
- **Truth rule, fixed now**: property 6 holds for a function on a box iff
  `count_zeros_box` returns exactly 0 on that box. An `ArithmeticError`
  (zero on the contour, or undersampled edge) is recorded as `undetermined`
  and is **not** silently read as either verdict; the box is not nudged
  after the fact.
- **Verdict rule, fixed now**: per box, DISTINGUISHES iff zeta's count is 0
  and every rival's count is non-zero; VACUOUS iff zeta's count is 0 and at
  least one rival's count is 0. If zeta's own count is non-zero the box is
  reported as invalidating itself, not as a result about zeta.

### One thing to keep straight about "completed"

The claim names the *completed* function. In every box above, σ > 0, and in
σ > 0 the completion factors are zero-free and pole-free: ξ vs ζ differ by
s(s−1)π^{−s/2}Γ(s/2)/2, F vs f by (π/5)^{−(s+1)/2}Γ((s+1)/2), Λ_Q vs ζ_Q by
(√d/π)^s Γ(s). Γ never vanishes and has no poles in σ > 0. So the counts are
the same whichever of the pair is used, and the battery's mixed convention
(zeta and Epstein counted on the completion, Davenport–Heilbronn counted on
f itself) does not affect any number below. That mixed convention is noted
as an observation about `zeta/epstein.py`, not as a defect this hunt fixes.

## Kill conditions, declared

- If zeta's count is non-zero on any box, that box is discarded and said to
  be discarded, not repaired into agreement.
- If the flip-test does not flip — every box agreeing on one verdict — I
  report that single verdict and say the well-posedness question came back
  negative, rather than adding boxes until it flips.
- If the Epstein arm does not finish inside budget, the hunt reports
  **not-settled for the Epstein rivals** and says what it would cost. It
  does not substitute a cheaper rival or a cheaper property.

```huntspec
id: gate5_p6_c
question: Does gate-5 property 6 (no zeros of the completed function in a box strictly off the critical line) distinguish zeta from the three battery rivals, or is it vacuous?
frontier: properties 1-3 of the gate-5 battery came back VACUOUS, properties 4-5 DISTINGUISHES, property 6 open; the prior attempt on box 0.6+80i to 0.9+90i did not finish in 50 minutes
proposed_attack: hold the sigma-band fixed and vary only the height window, so that any change of verdict is attributable to the box alone and settles well-posedness before it settles the verdict
dead_routes:
  - the box 0.6+80i to 0.9+90i at working precision across all four functions, cost-bound on the Epstein evaluation at t near 90
  - raising dps to sharpen an argument-principle count whose output is an integer with a 1e-6 residual guard
required_oracles:
  - argument-principle winding number over a closed rectangle with an integrality residual guard
  - the pinned Davenport-Heilbronn off-critical-line zero, independently reported by Spira, Math. Comp. 1994
  - the classical theorem that zeta has no zeros in sigma greater than 1
kill_conditions:
  - zeta itself is counted with a non-zero winding in a box strictly off the critical line
  - the winding residual exceeds the integrality guard and the count is therefore undetermined
  - every box agrees on one verdict, so the box-dependence claim has no support
  - the Epstein arm exceeds budget and the verdict for those rivals is unavailable
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - nudge a box after seeing its count
```
