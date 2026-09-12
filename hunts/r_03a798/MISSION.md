# Hunt R-03A798: what the hunt lexical guard actually reads

## The question

`tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word`
is the guard that keeps `hunts/` from claiming the word `zeta/rigor.py` owns.
The attention item that opened this hunt asserted a gap:

> the guard does not detect synonyms, *verified*, *confirmed*, *definitively*,
> *proves* are separately banned **but by other checks**; a hunt overclaiming
> in fresh vocabulary passes this guard

Two claims are bundled there, and they have different truth values. The first
is about the guard's reach. The second, "by other checks", is about whether
enforcement exists *somewhere*. This hunt measures both, plus the question
neither of them asks: whether the guard is even airtight on the one word it
does own.

## Scope

Writes only inside `hunts/r_03a798/`. Runs the real guard source unmodified
against a sandbox repo root in a tempdir; plants nothing in the live tree.
Nothing here is mathematics and nothing here is evidence for or against RH.

## Prior art

`hunts/wide_search/HANDOFF.md` §"the lexical ban" already records, as a
session note, that *verified / confirmed / definitively / proves* are "banned
by documentation but not by a test". That hunt got there first and this one
does not claim the observation. What is added here is the measurement: which
checks exist, what the guard's own boundary is on the word it does own, and
whether the documented-only ban is already being crossed in the live tree.

```huntspec
id: r_03a798
question: Does the hunts/ reserved-word guard detect overclaim synonyms, and do the "other checks" said to ban them exist?
frontier: one whole-tree lexical guard exists (test_no_hunt_claims_the_reserved_word); the four synonym bans are stated in hunts/README.md and CLAUDE.md with no located enforcement
proposed_attack: run the unmodified guard source in a sandbox repo root against a specimen battery spanning reserved word, its morphology, typographic evasions, the four documented bans, fresh overclaim vocabulary, and sanctioned vocabulary
dead_routes:
  - grepping the guard source and reasoning about what it would match, without running it, which cannot see collection or skip rules
  - planting specimens in the live hunts/ tree, which mutates a shared area other sessions may be running against
required_oracles:
  - pytest executing the unmodified guard source, exit status as the verdict
  - exhaustive enumeration of tests/*.py that both address hunts/ and read file text
  - literal substring occurrence counts over the committed hunts/ tree
kill_conditions:
  - the sandbox baseline with an empty specimen is not green, so per-specimen verdicts measure the sandbox rather than the specimen
  - a test enforcing any of the four documented bans is located, making the premise's "other checks" real
  - sanctioned vocabulary trips the guard, making the guard's failures noise rather than gaps
agents_may:
  - read any file in the repository
  - run the existing test suite
  - build a sandbox repo root in a tempdir and run the real guard against it
  - report a gap and name the smallest check that would close it
agents_may_not:
  - modify tests/, zeta/, harness/, meta/, lean/ or any root markdown file
  - modify hunts/README.md, including to add this hunt's case-log entry
  - write a new guard into the suite on its own authority
  - describe a documented-only rule as enforced, or a measured gap as a proven absence
```
