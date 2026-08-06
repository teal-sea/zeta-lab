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

**No department without a battery.**

A body of work whose claims nothing in this tree can falsify is not a
department. It is a probe, and probes belong where nobody will mistake one for
a result. `validate_battery` enforces this structurally: it refuses a battery
with no rival, a battery with neither decoy nor surrogate, and a battery with
no lesion.

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

## Adding department #2

Four steps. `harness/departments/zeta_department.py` is the worked example.

1. **Write the module.** Build the four roles out of whatever the subject
   already has. Do not invent instruments for the occasion — if nothing in the
   tree can currently kill a claim in this area, that is the finding, and the
   department is not ready.
2. **Declare the department** with a `door` pointing at a real page under
   `docs/doors/`, the `modules` it owns, and at least two `reference_claims`
   with known verdicts. Call `register_department` at import time.
3. **List it** in `KNOWN_DEPARTMENTS` in `harness/departments/__init__.py`.
4. **Run the conformance suite.** It is parametrized over that dict, so step 3
   is what turns the audit on:

   ```bash
   .venv/bin/python -m pytest -q -o addopts='' tests/test_department_conformance.py
   ```

There is no fifth step where someone reviews it by hand. That is the point:
a department cannot be added quietly, and cannot be added without a referee.

## What this is not

It is not evidence machinery. A claim that survives every instrument here is a
**candidate for where a real argument must live** — nothing more. Per
`docs/08`, nothing computed in this repository is evidence for RH, and the
harness adjudicates only the weaker, decidable question of whether a
demonstration is about its subject at all.
