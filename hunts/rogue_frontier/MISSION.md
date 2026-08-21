# rogue_frontier — a wide-portfolio search for one defensible new advance

Opened 2026-08-17 on branch `claude/riemann-hypothesis-research-ofds8s`.

This hunt is a research campaign, not a single conjecture. Its mandate: survey
the current RH-adjacent frontier from primary sources, generate a large
portfolio of concrete attack surfaces, and drive the most promising ones
through a discovery, destruction, and rigor pipeline until one produces the
largest defensible new mathematical statement this run can support. A closed
route with a witness counts as output. A rediscovery does not.

The campaign deliberately does not privilege the laboratory's existing
flagship (the critical-line proportion candidate in `hunts/frontier_math/`).
That work is prior art for this run: anything this hunt produces must be new
relative to it as well as to the literature.

```huntspec
id: rogue_frontier
question: Which RH-adjacent frontier admits the largest new mathematical advance this run can produce and defend, and what is that advance?
frontier: multiple fronts; each candidate project records its own frontier line with citations in FRONTIER_MAP.md before work starts
proposed_attack: portfolio search: parallel literature mapping, 30+ scored candidate projects, escalating tiers of computation and proof, adversarial destruction before any promotion
dead_routes:
  - re-deriving the frontier_math retention chain (that is hunts/frontier_math/ prior art, not this hunt)
  - direct numerical verification of RH to a new height as a headline (compute-bound, no new mathematics)
  - heuristic GUE analogies promoted without a theorem or an enclosure
required_oracles:
  - exact rational or integer arithmetic checked by an independent implementation
  - ball or interval enclosures via zeta.rigor with both backends where feasible
  - the Lean 4 kernel with zero sorrys and standard axioms
  - mpmath reference routines (zetazero, siegelz, nzeros) as numerical cross-checks
  - located primary literature quoted with theorem numbers
kill_conditions:
  - a claimed improvement fails an independent recomputation
  - the novelty search finds the statement in prior art
  - the effect does not survive increased precision or an enclosure
  - a structure-matched rival (Davenport-Heilbronn via zeta.epstein.battery) satisfies the same claimed criterion
  - the derivation is found to secretly assume RH or an unproved hypothesis without saying so
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

## Scope

May write: `hunts/rogue_frontier/**`, `figures/` if a figure earns it, and at
most one `docs/NN-*.md` at the end if a result earns one (next free number
taken from the tree at write time, never guessed). May not touch `zeta/`,
`ontology/`, `harness/`, or other hunts except to read them. The Lean arm
under `lean/` may gain new files only for a claim that has already survived
the destruction stages, in its own module, without touching existing proofs.

## Grading

Claims here use the repository ladder: measured, hardened, kernel-checked.
The word owned by `zeta/rigor.py` is not used in this directory at all, per
`tests/test_hunt_probe_discipline.py`. A composite claim takes the grade of
its weakest step. Ledger files:

- `FRONTIER_MAP.md` state of the art with primary citations
- `IDEA_PORTFOLIO.md` candidate directions and scores
- `RESULTS_LEDGER.md` active, dead, promoted, refuted claims
- `NOVELTY_LEDGER.md` searches performed, closest prior art
- `FAILURE_LEDGER.md` dead ends and why they died
- `REPRODUCE.md` exact reproduction steps for anything promoted
