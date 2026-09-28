# `harness/`: the validation framework

This package answers one question about an empirical claim:

> **What could show this claim is not about its subject?**

It is deliberately not about ζ. `ontology/` established the pattern, a
domain-agnostic core plus subject-coupled plugins, with the seam enforced by
tests, and `harness/` applies it to the validation instruments that were
previously hardwired to the zeta code.

## The admission rule

**No department without a battery**, a subject is registered here (as a
*department*) only together with a battery of controls that could actually
fail. `validate_battery` enforces this structurally: it refuses a battery
with no rival (structure-matched negative control), a battery with neither
decoy (ablation) nor surrogate (null model), and a battery with no lesion
(planted fault). `validate_department` further refuses a department with no
declared **detector** (planted faults without a detector staked on noticing
them leave detector power unmeasured, `compiler/FINDINGS.md` §8 measured
that gap) and no declared **scope** (a pass that means an unstated amount
gets read as meaning more than it does).

This is the repository's honest-scope rule expressed as validation code.

## The four control roles

This framework tests four classes of failure, chosen because a machine can
check each without knowing whether the claim is true. (Four is a design
decision, not a theorem; a fifth checkable class would earn a fifth role.)

| Role | Conventional name | The question | Fails when |
|---|---|---|---|
| **Rival** | structure-matched negative control | does the claim also hold for something that shares the structure and lacks the property? | it holds, so the structure is not why the property holds |
| **Decoy** | ablation | does the measurement move when the substantive input is swapped out? | it does not move, it was never reading the input |
| **Surrogate** | null model | does a null model with no substantive input reproduce the observation? | it does, the observation is a property of the model class |
| **Lesion** | planted fault | does the detector notice a violation planted on purpose? | it does not, the detector's silence measures its blindness, not the world |

The rival is the sharpest: no threshold, no statistics, a plain
modus tollens.

## Calibration in both directions

A battery that returns the same answer for everything is useless in a way no
single run reveals: one that never distinguishes looks exactly like a strict
one. So a department must declare **reference claims**, at least one its
battery is expected to reject, and at least one it is expected to pass, and
`tests/test_department_conformance.py` re-runs them and re-derives the
verdicts rather than trusting the labels.

## The integrity layer: auditing the audit

Structural validity is not verification: the placeholder battery that commit
`431cc74` replaced was structurally complete, validated, passed the
conformance suite of its day, and could never have rejected anything.
`harness/integrity.py` is that incident converted into checks. It runs
sixteen named checks against a department and grades the battery
`CALIBRATED` / `DETECTOR_INADEQUATE` / `UNMEASURED` / `CONTAMINATED` /
`HOLLOW`, no scalar score, and `ClaimReport` pairs every claim outcome
with that grade, and cannot state one without the other. A passing claim
from a hollow battery is rendered as untrustworthy, because it is.

The audit's own power is measured the same way it measures everything else:
`harness/shams.py` plants known corruptions in batteries (constant
detectors, target-as-rival, inert planted faults, leaked labels), and
`tests/test_harness_integrity.py` asserts each catchable corruption mode is
caught by its named check, while the two modes no mechanical check can
catch (a value-encoded label leak, co-designed calibration) are pinned as
blind spots, with their countermeasure (independent authorship, declared in
`harness/provenance.py`, attested rather than proven). The catalog is
`integrity.SHAM_MODES`, and every report prints the blind rows. Department
#5 (`referee`) registers this verification machinery as a subject under the
same conformance audit as everything else;
`docs/20-verification-integrity.md` is the full record, including where the
recursion bottoms out.

## The seam

`harness/protocol.py` imports nothing from any laboratory package, names no
quantity any laboratory computes, and would work unchanged for a chemistry
lab or a compiler-optimisation search. `tests/test_harness_protocol.py`
enforces that three ways: an AST import scan, a subprocess that asserts no
laboratory module enters `sys.modules`, and a lexical scan of the source for
subject-matter vocabulary.

The whole file runs in about a tenth of a second, which is itself the check
working: if it needed the laboratory to run, the seam would already be
broken.

Subject matter lives in `harness/departments/`, which may import whatever it
likes.

## Adding a department

Start from the scaffold, which generates questions rather than placeholder
instruments (a scaffold that generated runnable placeholders would be a
generator of hollow batteries):

```bash
.venv/bin/python -m harness.new_department my_domain
```

Then: build the four roles out of whatever the subject already has (do not
invent instruments for the occasion, if nothing in the tree can currently
refute a claim in this area, that is the finding, and the department is not
ready); declare detectors with a clean probe, a scope, a provenance record
and both reference claims; and **list it in `KNOWN_DEPARTMENTS` last**,
that line is what turns the conformance audit and the integrity audit on:

```bash
.venv/bin/python -m pytest -q -o addopts='' tests/test_department_conformance.py
```

There is no step where someone reviews it by hand, which means a department
cannot be added quietly, and cannot be added without controls whose own
power has been measured.

### Your decoys and lesions get poked with payloads you did not write

`decoys-move-their-probe` and `lesions-plant-something` check that an
instrument is not an identity function, and to do that they have to hand it
*something*. In order, they try: an optional `probe` attribute on the
instrument itself, your department's own target payload, and a historical
fallback shape. Your instrument has to change **one** of those. Raising on the
others is fine, a decoy that only understands its own department's records is
doing its job, not failing.

This is written down because it was not, and the cost was measured
(`docs/23` §8.6): four independent parties asked to build *honest* departments
all wrote instruments faithful to their own payloads, two of them were graded
`HOLLOW` for raising on a foreign probe, and the only way to find out was to
read audit source they had been told not to read. Declaring a `probe` on a
decoy or lesion is optional and is the cheapest way to say exactly what your
instrument expects.

To run all of it end to end, every department, then the machinery applied
to itself:

```bash
.venv/bin/python -m harness.demo
```

## What this is not

It is not evidence machinery. A claim that survives every control here is a
candidate for where a real argument must live, nothing more. Per
`docs/08`, nothing computed in this repository is evidence for RH, and the
harness adjudicates only the weaker, decidable question of whether a
demonstration is about its subject at all.
