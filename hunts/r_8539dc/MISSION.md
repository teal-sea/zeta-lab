# MISSION — hunt r_8539dc

## The question

DeepMind's AlphaEvolve mathematics report claims `C_3 <= 1.4557` for the
"third autocorrelation inequality", improving a prior `1.4581`. Issue #1 on
`google-deepmind/alphaevolve_repository_of_problems` (opened 2025-11-11)
observes that the published verification cell computes

    abs(2 * len(height_sequence_3) * np.max(convolution_3) / np.sum(height_sequence_3)**2)

with the absolute value **outside** the max, whereas the stated inequality
`max |f*f(t)| >= C_3 (int f)^2` requires `max(abs(convolution_3))`, and that
under the stated reading neither `1.4581` nor `1.4557` is reached. Terence Tao
replied on 2025-11-12 that there are two different optimisation problems here,
both with literature, and that the statements would be corrected.

This hunt reads and recomputes. It settles:

1. both functionals on the published sequences, in exact rational arithmetic;
2. which convention each cited prior bound belongs to;
3. whether arXiv:2511.02864 corrected the section, and in which version;
4. which published number is stated against which functional, and whether the
   claimed improvement survives the definition the paper writes down.

Out of scope: any new bound, any posting upstream, any judgment about who
should be told what. This is a reading and a recomputation.

## Scope

Writes only `hunts/r_8539dc/`, one case-log line in `hunts/README.md`, and one
appended outcome in `harness/departments/review_ledger.py`. Touches no
mathematics in `zeta/`.

```huntspec
id: r_8539dc
question: Is the published bound 1.4557 attached to the functional the published verifier computes, and does the claimed improvement survive the inequality as written?
frontier: published C_3 <= 1.4557 (AlphaEvolve, n=400) against a prior 1.4581; the sibling problem's published pair is 1.4993 (Matolcsi-Vinuesa) improved to 1.4688 (n=150)
proposed_attack: evaluate both readings of the inequality on both published height sequences in exact rational arithmetic, and diff the published sources across their revisions
dead_routes:
  - re-running the published float cell and reading its printed value, which is the step whose ambiguity is under test
required_oracles:
  - exact rational arithmetic over the published ten-decimal heights (Fraction, no float in the chain)
  - the published artifacts themselves - git history of google-deepmind/alphaevolve_results, and the arXiv:2511.02864 v1/v2/v3 LaTeX sources
kill_conditions:
  - the exact recomputation fails to reproduce a published figure that both readings agree on, which would mean the discretisation formula is wrong rather than the statement
  - the piecewise-linear knot argument fails, so a max over knots is not the max over t
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - post anything upstream
```

## Kill conditions, in prose

The hunt stops and reports if the exact recomputation cannot reproduce
`1.4688`, the one published figure on which the two readings must agree; that
would indict the discretisation rather than the statement.
