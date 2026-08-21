# Hunt R-E2EE73: Scope caveat: compiler verdicts rest on a hand-written model, not LLVM semantics (Alive2 absent)

A standing limitation on every claim `compiler/` makes. Recording it publicly because it bounds what those verdicts mean.

## Mission

Characterize, measure, and record the exact boundaries and scope caveats of the compiler department's verdicts:
1. Document the absence of Alive2 (rung 3) and quantify the exposure of resting refinement verdicts on the hand-written Python interpreter (rung 2, `pymodel.refinement_i8`).
2. Verify the multi-layer cross-check against compiled Clang binaries (rung 1, `clang.exhaustive_i8`) across all 10 fixtures (655,360 total points evaluated) and identify what it does and does not bound.
3. Measure detector power and blind spots across all 4 planted lesions, establishing that while the concrete detector misses poison violations covering 50% of the domain, the pure-Python detector captures poison and immediate UB at declared magnitudes.
4. Formalize the verification path independence structure between concrete execution and the hand-written Python interpreter.
5. Systematically catalog unsupported LLVM IR constructs and verify that the parser raises `ModelUnsupported` safely rather than misinterpreting out-of-scope instructions.

```huntspec
id: r_e2ee73
question: What are the exact epistemic bounds and scope caveats of compiler verdicts resting on a hand-written Python interpreter in the absence of Alive2?
frontier: rung 1 (clang.exhaustive_i8) has 0 power on poison lesions; rung 2 (pymodel.refinement_i8) has full power over supported straight-line i8 IR; rung 3 (alive2.refinement) is absent
proposed_attack: audit backend census, cross-check 10 fixtures over 655360 points, evaluate 4 lesion power curves, audit unsupported IR rejection safety, and measure verification path independence
dead_routes:
  - treating compiled binary agreement as proof of refinement or absence of poison
  - treating -O0 and -O2 through the same clang as an independent second check
  - claiming equivalence or full formal proof rather than refinement over the enumerated i8 domain
required_oracles:
  - exhaustive 65536-point concrete evaluation compiled by clang at -O0 and -O2
  - exhaustive 65536-point poison-aware Python interpreter evaluation
  - cross-check verification across all 10 fixtures with 0 mismatches
kill_conditions:
  - the Python interpreter produces a defined value that disagrees with compiled clang output on any fixture point
  - an unsupported IR instruction or multi-block construct evaluates silently instead of raising ModelUnsupported or IRRejected
  - the Python interpreter detector fails to detect any planted lesion at its declared magnitude
agents_may:
  - measure
  - audit
  - catalog
  - attack
  - formalize
agents_may_not:
  - declare formal proof status
  - claim full LLVM semantics coverage while Alive2 is absent
  - declare equivalence beyond the enumerated i8 domain
```

```runmanifest
id: r_e2ee73-run-f482a6c6
hunt: r_e2ee73
started: 2026-08-20T09:32:32-05:00
finished: 2026-08-20T09:40:00-05:00
ran:
  - .venv/bin/python hunts/r_e2ee73/probe.py
outcome: verified 655360 cross-check points with 0 mismatches, confirmed alive2 absence, and bounded the hand-written interpreter scope
artifacts:
  - hunts/r_e2ee73/probe.py
  - hunts/r_e2ee73/results.json
  - hunts/r_e2ee73/RESULTS.md
  - hunts/r_e2ee73/HANDBACK.json
```
