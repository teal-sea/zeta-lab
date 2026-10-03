# MISSION: rh_resolve, direct RH resolution attempt

Question: does every nontrivial zero of zeta have real part 1/2.
Both proof and disproof count as success. No assumption of RH,
no equivalent, no stronger unproved claim, no extra axioms.

Scope: exploratory hunt under hunts/. Nothing here is a result
until it passes the battery, an enclosure, or a kernel check.
Lexical rule: the word certified is banned in this directory.
Use measured, derived, enclosure-carrying only where earned.

## Plan

1. Compare three mechanisms cheaply (ALIGNMENT 4): Li coefficients,
   Weil explicit-formula positivity, de Bruijn-Newman heat flow.
2. Develop the one with credible signal; challenge the actual
   construction, including Davenport-Heilbronn rival.
3. Any claimed resolution needs: complete argument, explicit
   dependencies, reproducible artifacts, and a formal-statement
   check against the original problem (not just proof vs encoding).

## Current status (2026-10-03)

Phase 1 only. No proof claimed. No disproof claimed.

```huntspec
id: rh_resolve
question: Do all nontrivial zeros of Riemann zeta have real part 1/2
frontier: RH verified to 3e12 by Platt-Trudgian 2021, Lambda >= 0 by Rodgers-Tao 2020, finite Li positivity to n=300 in this tree
dead_routes:
  - finite floating scan alone as uniform theorem (Littlewood, docs/08)
  - zeros-route Li scan as positivity evidence (structurally nonnegative, zeta/li.py docstring)
  - harness framework extension without live consumer (harness/VERDICT.md)
required_oracles:
  - mpmath independent oracle cross-check (tests/test_pari_oracle.py pattern)
  - ball-arithmetic enclosure via zeta/rigor.py (Arb and mpmath.iv cross-check)
  - Lean 4 plus Mathlib kernel with zero sorrys for any formal claim
kill_conditions:
  - a rival satisfying the same hypotheses but violating the conclusion (zeta.epstein.battery)
  - the signal reproduces on a matched null with no arithmetic
  - the effect does not respond to added precision
  - a planted violation is not detected while the claimed signal is
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```
