# `harness/` — the referee, factored out of the laboratory

This package answers one question, and it is the question that decides whether
a body of work is a department at all:

> **What could show this claim is not about its subject?**

It is deliberately *not* about ζ. `ontology/` already established the pattern —
a domain-agnostic core plus subject-coupled plugins, with the seam enforced by
tests rather than by good intentions. `harness/` applies that pattern to the
part of the repository that was previously hardwired: the instruments that kill
claims.

## The admission rule

**No department without a battery — and no battery without a measured
referee.**

A body of work whose claims nothing in this tree can falsify is not a
department. It is a probe, and probes belong where nobody will mistake one
for a result. `validate_battery` enforces this structurally: it refuses a
battery with no rival, a battery with neither decoy nor surrogate, and a
battery with no lesion. `validate_department` further refuses a department
with no declared **detector** (lesions without a detector staked on
noticing them are power theater — `compiler/FINDINGS.md` §8 measured that
gap) and no declared **scope** (a pass that means an unstated amount gets
read as meaning more than it does).

This is the repository's honest-scope rule turned into architecture.

## The four instrument roles

A claim can fail to be about its subject in exactly four ways a machine can
check without knowing whether the claim is true.

| Role | The question | Fails when |
|---|---|---|
| **Rival** | does the claim also hold for something that shares the structure and lacks the property? | it holds — so the structure is not why the property holds |
| **Decoy** | does the measurement move when the substantive input is swapped out? | it does not move — it was never reading the input |
| **Surrogate** | does a null model with no substantive input reproduce the observation? | it does — the observation is a property of the model class |
| **Lesion** | does the detector notice a violation planted on purpose? | it does not — the detector is blind, and its silence measures that |

The rival is the sharpest: no threshold, no statistics, just modus tollens.

## Both directions, or it is not calibrated

A battery that returns the same answer for everything is useless in a way no
single run reveals: one that never distinguishes looks exactly like a strict
referee. So a department must declare **reference claims** — at least one its
battery is expected to kill, and at least one it is expected to pass — and
`tests/test_department_conformance.py` re-runs them and re-derives the verdicts
rather than trusting the labels.

## The integrity layer — the referee, refereed

Structural validity is not verification: the sham battery commit `431cc74`
replaced was structurally complete, validated, passed the conformance suite
of its day, and could never have killed anything. `harness/integrity.py` is
that incident turned into architecture. It runs sixteen named checks against
a department and grades the battery `CALIBRATED` / `DETECTOR_INADEQUATE` /
`UNMEASURED` / `CONTAMINATED` / `HOLLOW` — no scalar score — and
`ClaimReport` pairs every claim outcome with that grade, incapable of
stating one without the other. A green claim from a hollow battery renders
as dangerous, because it is.

The audit's own power is measured the way it measures everyone else's:
`harness/shams.py` plants known corruptions in batteries (constant
detectors, target-as-rival, inert lesions, leaked labels), and
`tests/test_harness_integrity.py` asserts each catchable sham mode is
caught by its named check — while the two modes no mechanical check can
catch (a value-encoded label leak, co-designed calibration) are **pinned as
blind**, with their countermeasure (independent authorship, declared in
`harness/provenance.py`, attested rather than proven). The catalog is
`integrity.SHAM_MODES`, and every report prints the blind rows. Department
#5 (`referee`) makes all of this a subject under the same conformance audit
as everything else; `docs/20-verification-integrity.md` is the full record,
including where the recursion bottoms out.

## The seam

`harness/protocol.py` imports nothing from any laboratory package, names no
quantity any laboratory computes, and would work unchanged for a chemistry lab
or a compiler-optimisation search. `tests/test_harness_protocol.py` enforces
that three ways: an AST import scan, a subprocess that asserts no laboratory
module enters `sys.modules`, and a lexical scan of the source for
subject-matter vocabulary.

The whole file runs in about a tenth of a second, which is itself the check
working: if it needed the laboratory to run, the seam would already be broken.

Subject matter lives in `harness/departments/`, which may import whatever it
likes.

## Adding a department

Start from the scaffold, which generates questions rather than placeholder
instruments (a scaffold that generated runnable placeholders would be a
sham-battery generator):

```bash
.venv/bin/python -m harness.new_department my_domain
```

Then: build the four roles out of whatever the subject already has (do not
invent instruments for the occasion — if nothing in the tree can currently
kill a claim in this area, that is the finding, and the department is not
ready); declare detectors with a clean probe, a scope, a provenance record
and both reference claims; and **list it in `KNOWN_DEPARTMENTS` last** —
that line is what turns the conformance audit and the integrity audit on:

```bash
.venv/bin/python -m pytest -q -o addopts='' tests/test_department_conformance.py
```

There is no step where someone reviews it by hand. That is the point:
a department cannot be added quietly, and cannot be added without a referee
whose own power has been measured.

To watch all of it run end to end — every department, then the machinery
turned on itself:

```bash
.venv/bin/python -m harness.demo
```

## What this is not

It is not evidence machinery. A claim that survives every instrument here is a
**candidate for where a real argument must live** — nothing more. Per
`docs/08`, nothing computed in this repository is evidence for RH, and the
harness adjudicates only the weaker, decidable question of whether a
demonstration is about its subject at all.
