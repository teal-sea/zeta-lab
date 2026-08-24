# MISSION — R-2969B0: does a 2013 human construction beat AlphaEvolve's Problem 42 value?

## The question

DeepMind's `alphaevolve_repository_of_problems` marks Problem 42 (the
sum-difference problem) `world_record` in `status.json`. Issue #5 on that
repository, opened 2026-07-31 with no maintainer response, claims the record is
not a record: Penman and Wells, *On sets with more restricted sums than
differences*, INTEGERS **13** (2013) A57, Theorem 21, give an explicit family
reaching `ln(32/5)/ln(26/5) ~ 1.12594` in the same normalisation, above the
AlphaEvolve value 1.1219. That issue discloses it was AI-produced and
unreviewed. So an AI-generated challenge stands against an AI-generated record
and nobody has checked either.

This hunt checks both, from the primary sources, by exact enumeration.

## Scope

Writes only in `hunts/r_2969b0/`, plus one case-log entry in `hunts/README.md`.
Nothing is posted upstream: what, if anything, is said to DeepMind is the
owner's call. The separate `C = 2` claim in the same issue is **out of scope**
and untouched here.

Nothing in this hunt bears on RH (`docs/08`).

```huntspec
id: r_2969b0
question: Does Penman-Wells (2013) reach a higher value of DeepMind Problem 42's quantity than the AlphaEvolve construction?
frontier: AlphaEvolve construction g = 1.1219357375 (309 integers, repository notebook); challenger claim sup g = ln(32/5)/ln(26/5) = 1.125944426; Ruzsa/Granville upper bound C <= 2
proposed_attack: read both normalisations from the primary sources, instantiate the Penman-Wells family Q_j at concrete j, count |A|, |A+A|, |A-A| by enumeration, and compare exactly
dead_routes:
  - trusting the notebook's prompt-text score function, which returns the reciprocal ratio and is not the quantity the problem page defines
  - trusting the notebook's earlier scorer, which adds a size bonus of up to 0.01 to the ratio
required_oracles:
  - exact finite-set enumeration over the integers
  - the printed counts of Penman-Wells Corollary 13, recomputed rather than quoted
  - the printed values g(A_15) = 1.0717 and f(X) = ln(51)/ln(47) in the same paper, used as a normalisation calibration
  - 120-digit decimal comparison of the two log ratios, so the verdict does not rest on a float
kill_conditions:
  - the two normalisations turn out to differ, making the comparison apples to oranges
  - enumeration contradicts Corollary 13's counts at any j
  - the calibration values g(A_15) and f(X) fail to reproduce, meaning we are reading a different g than the paper
  - no finite Q_j exceeds the AlphaEvolve value, leaving only an unattained supremum
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - post anything to the upstream repository
```
