# MISSION: controls for the F1 discovery engine (`docs/15`)

`docs/15-the-f1-discovery-engine.md` writes up seven exploratory prototypes
(`ontology/01_f1_geometry.py` … `07_the_imposter_gauntlet.py`) and closes with
a Reality Check that dials the rhetoric back. The Reality Check is the good
part of that document. It is also the untested part: five critiques recorded
as prose, none of them pinned by anything in `tests/`, one of them stating a
closed-form arithmetic law and one of them making a claim about a prototype
that is itself inaccurate.

This hunt turns that prose into measurements. It does not extend the
prototypes: `AGENTS.md` freezes `ontology/0*` as historical exploratory work,
so every instrument here lives in this directory and reads those files
without modifying them.

## What this hunt is allowed to touch

- Its own directory, `hunts/f1_engine_controls/`.
- One new test file, `tests/test_f1_engine_controls.py`, pinning what it
  measures.
- Correction notices in `docs/15-the-f1-discovery-engine.md`, which is the
  document whose claims are under test, and a stale-path repair in
  `docs/09-new-ontologies.md`.

Not `zeta/`, not `ontology/`, not `harness/`, not `README.md`, not
`ROADMAP.md`.

## The three questions

1. **The ln 2 multiplicity.** The Reality Check attributes the degenerate
   eigenvalue at ln 2 in `04_transcendental_matrix.py` to a boundary effect
   "with multiplicity `pi(N/2) - pi(N/3) - 1`". Is that the law?
2. **The density failure.** The same page says the prototype's frequencies
   "crawl" and that "we have dozens of frequencies below 17.7, where zeta
   only has one zero". What is the number, and which way does it move when
   the truncation is refined?
3. **The gauntlet.** `07_the_imposter_gauntlet.py` concludes that the
   geometry "structurally REJECTS the imposter" and is "IMMUNE to false
   positives"; the Reality Check answers that the gauntlet is vacuous because
   "the construction never actually consults zeta". Both statements are
   testable, and they cannot both be right.

```huntspec
id: f1_engine_controls
question: Which of the five Reality Check critiques in docs/15 survive being measured?
frontier: none of the five is pinned by a test; the ln 2 multiplicity is quoted as pi(N/2) - pi(N/3) - 1 and never checked
proposed_attack: read the prototypes without modifying them, compute the quantities the critiques assert, and pin whatever survives
dead_routes:
  - extending the prototypes themselves, which AGENTS.md freezes as historical exploratory work
  - rebuilding the Euler-product rival set, which zeta.epstein.battery already owns
required_oracles:
  - exact linear algebra on the incidence matrix, checked against the eigenvalue count of the built matrix
  - the standing rival battery in zeta.epstein
  - mpmath zero ordinates and zeta.zeros.N_of_T for the density comparison
kill_conditions:
  - the proposed multiplicity law disagrees with the eigenvalue count at any N in the scanned range
  - the density gap closes as the truncation is refined
  - the coefficient predicate turns out not to discriminate on the standing battery
agents_may:
  - read the prototypes
  - derive
  - code
  - attack
  - measure
agents_may_not:
  - modify the prototypes
  - declare novelty
  - declare theorem status
  - promote their own claim
```
