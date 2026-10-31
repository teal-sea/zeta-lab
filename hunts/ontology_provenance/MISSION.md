# MISSION: the Requirement A gate, mechanized

**Scope:** `hunts/ontology_provenance/` for the scanner, plus the case-log line,
the methods-index entry `hunts/README.md` requires, and the diagnosis note
under `hunts/factorization_vs_position/`. No edits to `zeta/`, `ontology/`,
or `harness/`.

## Why this hunt

`docs/09-new-ontologies.md` §5.1 states the positive target any candidate ontology
must hit, and splits it into three requirements. It then says of the first one:

> **Requirement A is mechanically checkable** (provenance scans of a construction's
> definition, the same technology as the `discovery/` seam tests).

That sentence is a claim about this repository that nothing in this repository
currently implements. There is no scan that takes a proposed construction and
answers "does it import the zeros?". Gate 4 has a number (`factorization_defect`),
Gate 3 has an executable battery (`zeta.epstein.battery`), Gate 2 has
`zeta.weil`. Gate 1 is prose. Requirement A has a sentence and no tool.

So a candidate frame can be written, run, produce plausible numbers, and pass
review without anyone checking the one property that decides whether it explains
anything: whether it was built from prime-power data or from the answer.

## The target

Given a Python module or function that claims to define an object, decide:

- **clean**: every name it reaches traces back to prime-power or archimedean data,
  and to no zero-derived quantity;
- **tainted**: at least one zero-derived quantity is reachable, with the importing
  path named;
- **undecided**: the module defeats static reading (dynamic import, `exec`,
  `importlib`, unparseable source). Reported, never counted as clean.

Tiers, because the difference matters to a reader:

1. **direct**: the defining module itself names a banned quantity;
2. **reachable**: it imports a laboratory module that does, proven as a path
   through the repository's own import graph.

## Kill conditions

- If the scan flags a module whose definition provably never touches the zeros
  (a false positive on the calibration set), the rule set is wrong and gets fixed
  before any verdict is reported.
- If a planted violation passes, the scanner is broken, not the violation
  lenient. The lesion test is the acceptance check, not the table.
- If the verdict for a module depends on which unrelated module was scanned
  first, the graph walk is order-dependent and is wrong.

## Honest scope, stated up front

This is a lexical and import-graph analysis, not a semantic proof. It can be
evaded by `getattr`, indirection through data files, or arithmetic that
reconstructs ordinates from a formula. It is a floor of the same kind as
`scripts/check_secrets.py`: it catches the ordinary case, which is the case that
actually occurs, and it must never be described as establishing Requirement A.
A clean verdict means "nothing zero-derived is reachable by name", not "this
construction is prime-derived".

## What is deliberately out of scope

- Requirements B and C. B is an identity to be measured on the test algebra, C is
  partly a judgment. This hunt does one of the three.
- Any judgement about whether a clean frame is correct. Provenance is orthogonal
  to truth: a prime-derived construction can still be wrong, and that is what the
  battery and the doors are for.

## Done

A scanner, a lesion suite that goes red on planted violations, and a table over
the laboratory's existing candidate frames stating tier and witness for each.
No claim beyond that table.

```huntspec
id: ontology_provenance
question: Does a proposed frame reach a zero-derived name, by a static read of its source?
frontier: docs/09 section 5.1 says Requirement A is mechanically checkable; before this hunt that sentence had no scan
proposed_attack: parse the file, classify banned names, and follow from-imports at symbol granularity
dead_routes:
  - treating a module-level import of a coefficient function as use of every name in that module
  - reading lexical reachability as definitional use of the zeros
required_oracles:
  - the lesion suite in test_provenance.py, which must go red on planted violations
  - a reading of each flagged frame against its source, not against the scanner headline
kill_conditions:
  - a flagged module whose definition never touches the zeros is a false positive and the rule set is wrong
  - a planted violation passes
  - a verdict depends on which unrelated module was scanned first
agents_may:
  - parse
  - classify names
  - report a tier and a witness
agents_may_not:
  - declare a clean frame prime-derived
  - promote a lexical hit to a definitional rejection
  - assign theorem status
```

