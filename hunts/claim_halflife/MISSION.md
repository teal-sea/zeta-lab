# MISSION: `claim_halflife` — what happens to a claim after it is recorded

This laboratory publishes its working record, corrections included. That is a
policy, and a policy is a claim about behaviour. Nobody had measured the
behaviour.

The question is not whether the record is honest. It is narrower and
answerable: **once a claim is written into the case log, what happens to it?**
How often is it revised, how fast, by what, and how much of the record has
anything mechanical standing behind it.

The unit is one entry in `hunts/README.md`'s case log, because that is the
granularity at which this tree decides what it believes. There are 95 of them.

## Why this is worth a session

Three reasons, in descending order of how uncomfortable they are.

1. **The tree's own doctrine says every correction should leave a guard.**
   Every `HANDOFF.md` record carries a `Now caught by:` field. Whether that
   field is usually filled is a fact about the laboratory, and it is checkable
   from git.
2. **Survival is not the same as being checked.** A claim nobody revisited
   looks identical, from outside, to a claim that withstood scrutiny. The
   denominator has to separate them or the record flatters itself by
   construction.
3. **A pin is not a guard.** `harness/VERDICT.md` and the operating playbook
   both say a check that has never fired has no power. The presence of a test
   naming a hunt is presence, not power, and the difference is measurable by
   planting faults.

## What this hunt is not

It is not a mathematical result and nothing in it bears on RH (`docs/08`). It
is not an audit of whether any particular claim is true. It measures the
*process*, and a tidy process measurement is worth nothing on its own: the
standing rule in `meta/README.md` is that a session with no mathematics and a
neat ledger produced nothing.

```huntspec
id: claim_halflife
question: Once a claim is recorded in this laboratory's case log, how often is it later revised, how fast, and what fraction of the record has a guard that would actually fire if it stopped being true?
frontier: unmeasured; meta/interventions.jsonl records interventions by hand and has no denominator, and no measurement of the case log's correction rate or guard power exists in the tree
proposed_attack: parse the 95 case-log entries, attach each to the commits touching its own claim files, classify later commits as revisions at three declared strictness levels, then plant faults in the artifacts the pinning tests read and record which mutations go red
dead_routes:
  - counting corrections from commit-message keywords alone, which measures house style rather than corrections
  - treating a test added alongside a fix as evidence that a test caught the fix
  - running the measurement on the default checkout, which is a shallow clone and hides most of the history
required_oracles:
  - full git history, with shallowness checked before any count is taken
  - a stratified blind hand audit of the classifier over positives and negatives, scored against a withheld key
  - planted faults in the artifacts the pinning tests read, with a byte-identical rewrite as the null rung
  - null corpora with no research claims in them, classified by the identical rules
kill_conditions:
  - the classifier fires at the same rate on the null corpora as on claim files, which would show it reads commit habit rather than corrections
  - the blind audit finds the classifier's precision below chance on the positive arm
  - the planted-fault ladder cannot be run without leaving the working tree dirty
agents_may:
  - build the corpus, the classifier and the ladder under hunts/claim_halflife/
  - plant faults and revert them, asserting the tree is clean between targets
  - report rates with their denominators stated
agents_may_not:
  - edit any file outside hunts/claim_halflife/ to make a number come out better
  - describe an unrevisited claim as one that survived scrutiny
  - promote any of this to a statement about the mathematics
```
