# Hunt r-414eed — how much power does `make_context.py --check` actually have?

`harness/departments/guard_ledger.py` carries the guard
`scripts/make_context.py --check` with `fired=None`, `known_misses=()` and
`scope="undetermined until demonstrated"`. The ledger's own rule is that an
outcome costs a demonstration, so the entry is currently a *worklist item*, not
a claim — `tests/test_guard_ledger.py::test_the_worklist_surfaces_the_undemonstrated_entries`
asserts exactly that it is still open.

The ledger names the smallest mutant: **one added public symbol with
`CONTEXT.md` left unregenerated.** This hunt builds it, runs it past the guard,
and records the outcome — plus enough siblings to say where the guard's
sensitivity stops.

## What this hunt may touch

`hunts/r_414eed/` only. In particular it does **not** edit the guard ledger,
`tests/test_guard_ledger.py`, or `hunts/README.md`; the mutants are applied to a
throwaway copy of the tree in `/tmp`, never to the repository. Consequences for
the ledger are reported, not applied — see `HANDBACK.json`.

## Method in one paragraph

`scripts/make_context.py` is a pure-`ast`, stdlib-only script whose `ROOT` is
derived from `__file__`, so it can be pointed at a copy of the tree. `probe.py`
copies the seven directories `build()` reads plus `CONTEXT.md` into a temporary
sandbox, checks that the copy reproduces the committed `CONTEXT.md` byte for
byte (control 1), applies one mutant, runs the guard, undoes the mutant, and
checks the guard is quiet again before the next one (control 2). Beyond the exit
code it also regenerates `CONTEXT.md` and diffs it, so a catch can be attributed
to the mutant's *symbol* reaching the index rather than merely to the
per-module line count moving.

## Nothing here bears on RH

This hunt measures a repository hygiene script. It touches no mathematics and is
not evidence for or against anything about ζ (`docs/08`).

```huntspec
id: r_414eed
question: Does scripts/make_context.py --check detect its declared smallest mutant, and where does its sensitivity stop?
frontier: guard ledger entry records fired=None, known_misses=(), scope "undetermined until demonstrated" — zero mutants ever run
proposed_attack: apply 24 smallest-edit mutants to a throwaway copy of the tree and read the guard's exit code, with a CONTEXT.md diff to attribute each catch to a mechanism
dead_routes:
  - editing the live tree to test the guard, which would make the mutation indistinguishable from ordinary work in progress
  - running the guard without a byte-exact baseline control, which would make every catch an artefact of the copy
required_oracles:
  - the guard's own process exit code under subprocess
  - byte comparison of the regenerated CONTEXT.md against the committed one
  - a same-sandbox undo check after every mutant
kill_conditions:
  - the unmutated sandbox fails the guard, so no catch can be attributed to a mutant
  - an undo leaves the sandbox dirty, so rows are contaminated by their predecessors
  - the declared smallest mutant passes the guard, in which case the ledger entry becomes fired=False and the guard is dead
agents_may:
  - copy the tree into a sandbox and mutate the copy
  - run the guard and record exit codes and diffs
  - report a proposed ledger amendment
agents_may_not:
  - edit harness/departments/guard_ledger.py or tests/test_guard_ledger.py
  - record an outcome in the guard ledger on their own authority
  - promote a boundary miss to a defect without stating the edit that reaches it
```
