# 32 — The Palomar arm: what an outside mechanical check adds, and what it does not

**21 August 2026.** On 18 August 2026 the Lean FRO and ICARM opened
[Palomar](https://palomar-registry.org/), a registry of Lean-verified
mathematics, described by its own documentation as the analogue of a preprint
server for Lean proofs. Three days later this laboratory submitted one result to
it. This document records what was submitted, what the check does and does not
establish, how the submission surface is built, and one measured observation
about the service itself.

The short version: the laboratory's Lean arm was already sorry-free and
axiom-clean, and that had been true for days. What changed is that somebody
other than us rebuilt it and agreed, and that a gap no in-tree test can close
was closed by a third party.

---

## 1. What was submitted

The **source-admissible strong closure**, three declarations, from
`teal-sea/zeta-lab` at commit `8a28a4faa3fb0fe68649f4f22faba7efe4bc3406`:

| Declaration | Statement |
| --- | --- |
| `ZetaLean.Palomar.pub1_strong_closure` | `sup ⟨1,v⟩²/⟨Av,v⟩ = c*` over the compactly supported monotone admissible class |
| `ZetaLean.Palomar.pub1_strong_closure_reciprocal` | the matching `inf ⟨Av,v⟩/⟨1,v⟩² = 1/c*` |
| `ZetaLean.Palomar.pub1_strong_closure_exists` | the same, existentially quantified over the profile and both uniform constants, so it carries no hypothesis at all |

These mirror `ZetaLean.Pub1.*` in the development. The three are the ones the
companion informal note names in its formal-verification section.

**Outcome.** Mechanical verification returned `status: pass` with zero errors
and zero warnings; the editorial review returned "No problems were identified"
across presentation, statement alignment, definitions, literature account, and
research interest. Each declaration depends on exactly `propext`,
`Classical.choice` and `Quot.sound`. The advertised statement surface imports
Mathlib alone, which the report records as `trust_level: high` with
`untrusted_sources: []`.

Public evidence, both naming the commit:
[verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/32448082170),
[registration](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/32451268512).

## 2. What the check establishes, and the one thing that is genuinely new

Palomar fetched a pinned commit, rebuilt the whole development on its own
hardware inside a sandbox, exported the proofs, and replayed them through Lean's
kernel **and** the independent NanoDa kernel. So Lean's own kernel is not the
single point of trust.

That is worth having, but it is not the interesting part. The interesting part
is **statement alignment**.

Nothing in this repository can check that the theorem we advertise is the
theorem we proved. A test suite runs the code we wrote against the claims we
wrote; if a docstring oversells a lemma, every test still passes. That failure
mode is where formalization projects lose credibility, and it is structurally
invisible from the inside.

The Challenge/Solution split is the mechanism that closes it. `Challenge.lean`
is a small statement-only surface that may import Lean core, Mathlib and Tau
Ceti and nothing else, so a reader can audit the claim without reading the
proof. `Solution.lean` proves the same declarations from the full development.
Comparator checks that the two agree. An outside party therefore certifies
neither more nor less than this: *the advertised statement is the proved one,
and its proof uses only the permitted axioms.*

**Where this sits on the certainty ladder: nowhere new.** `AGENTS.md` ends the
ladder at kernel-checked and says outside review is not ours to award. Palomar
is an automated check, not a person, and its own report says so in as many
words: "No person read it." It does not promote a result to a fourth rung. What
it does is *independently confirm* rung 3 and close the alignment gap. A
published claim still carries *pending external verification* until a qualified
human reader has walked the chain.

## 3. How the submission surface is built

Five files in `lean/`, and `lean/PALOMAR.md` is the operating guide:
`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`, and
`PALOMAR.md` itself. Three design points are not obvious and cost time to
rediscover.

**The Challenge carries one deliberate `sorry` per advertised statement.** That
is what the format requires of a statement surface. It is not an uncertified
step in the Lean arm, the proof development remains sorry-free, and it must not
be "fixed". The lakefile carries a comment saying so.

**`Solution.lean` does not import `Challenge.lean`.** Under this layout the two
modules independently declare the same names, so importing one into the other
collides. The definition block is instead duplicated byte for byte, which is
checkable mechanically and is checked before every submission.

**A structure declared twice is two distinct inductive types.** The bridges from
the `ZetaLean.Palomar` copies to `ZetaLean.Pub1` are `rfl` for every definition
except `SourceWindow`, where `sourceAdmissible_eq` transports the ten fields in
both directions. Whether Comparator would accept that shape was the one thing
that could not be tested locally, because Comparator needs Linux Landlock. It
accepted it.

**`definition_names` stays empty.** Palomar's CONTRIBUTING restricts that field
to definitions whose value is left *unspecified* in the Challenge. Ours are
concrete, so they are not holes, and naming them would invite scrutiny for a
feature the submission does not use.

`scripts/palomar_precheck.py` runs the mechanical gate locally before a
submission. Its docstring records its two limits: it covers the mechanical gate
only and not the editorial floor, and it is a reimplementation from published
policy rather than a copy of the authoritative `submission_contract.py`.

## 4. The editorial floor is a real gate, and description writing is part of it

`rubric.json` sets `minimum_score: 4` with
`mandatory_reject_below_minimum: ["notability"]`. A submission can be
mechanically perfect and still be rejected outright for failing to establish
that any mathematician would care.

This bit, and it is worth recording why. The first draft of
`project.description` stated the identity and stopped. Read cold, `sup
⟨1,v⟩²/⟨Av,v⟩ = ⟨1,A⁻¹1⟩` is a one-line Rayleigh quotient fact for any positive
definite operator, and an editor would be right to score it as routine. The
content is not the identity but the **reverse inequality over the constrained
class**: that imposing evenness, radial monotonicity, exact compact support, an
amplitude ceiling and uniform L¹ bounds on second derivatives does not lower the
supremum, proved by an explicit endpoint-tapered family inside the class. The
abstract has to say which half is classical and which half is the work.

The general lesson: the registry abstract is not a summary of the theorem, it is
an argument that the theorem is worth a reader's time, and the two are written
differently.

## 5. Scope, stated once

The submitted result is a statement about a Fredholm operator on an interval and
a class of test profiles. It says nothing about the zeros of the zeta function,
nothing about the Riemann Hypothesis, and it asserts no numerical value for `c*`
itself. `status.scope` in the published `formalization.yaml` says this in the
registry record, and `README.md` and this document repeat it rather than
softening it.

Originality is claimed and novelty is not. The `sources` block declares the
result `original-proof`, which is a claim about provenance, and states outright
that no literature search for prior art on the identity has been run. The cited
paper supplies the setting that is analyzed, namely the form factor, the
admissible window class and the induced scalar profile, and does not state or
prove this identity.

## 6. One measured observation about the service

Registration and publication are separate steps, and on 21 August 2026 the
second one stalled.

Palomar's own architecture, from its `docs/specification.md`, is that the public
website and data service are **views**: the private `PalomarDatabase` repository
is the canonical ledger, and `data.palomar-registry.org` is a Cloudflare Worker
serving a filtered projection of it. Registration triggers a public render run,
after which `PalomarReviewer` prepares a registration pull request, merges it on
clean checks, and finalizes.

Measured that day: nine render runs, all succeeding, from five distinct GitHub
accounts (`ehrlich-b`, `lennrt`, `mbaccaro-dev`, `teal-sea`, `Paul-Lez`).
Eleven hours after the first, **none** of the five repositories had appeared in
the public projection, whose newest entry was still `PALOMAR-2026-08-20-000003`
from the previous day. Entries from 17 to 20 August were unaffected.

The inference that this is a service-side stall rather than a per-submission
fault is safe, because the fault is common to five unrelated accounts while
older entries are intact. *Where* it stalls is not observable from outside,
since both `PalomarDatabase` and `PalomarSubmissionState` are private. The
laboratory's own record is unaffected either way: the mechanical and editorial
outcomes are recorded and the verification runs are public and permanent.

## 7. A defect found in Palomar's own contract

Filed as [PalomarPolicy issue #87](https://github.com/PalomarRegistry/PalomarPolicy/issues/87).
`CONTRIBUTING.md` and `docs/specification.md` describe `sources[].type` as a
closed vocabulary, under a heading named "Mechanical requirements". The intake
code accepts any nonempty string up to 200 characters, the template documents
the field as free text, and the upstream v0.4 schema defines it as a plain
string whose description lists values absent from the policy list. Two separate
components ship tests whose names state that the field is bounded free text.

Recorded here because the sequence is the point rather than the outcome. The
claim was first believed on a confident reading of the policy document, then
checked against the code that enforces it, and the check reversed the
conclusion. A spec and its implementation are two different artifacts and the
implementation is the one that runs.

## 8. What is next

A second submission is prepared for the Davenport-Heilbronn arm: two
minimum-modulus zero-existence criteria and the analytic half, at
`lean/comparator-dh.json` with metadata at `lean/palomar-dh/formalization.yaml`.
None of its advertised statements contains the off-line-zero conjunct, so none
of them can be read as the Davenport-Heilbronn theorem, and both its Challenge
documentation and its `status.scope` say so.
