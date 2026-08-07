# 19 — Research dossiers: an experiment in AI-native mathematical state

*A side project, and a probe rather than a department — see §6, which is the
most useful part of this document because it is the part that says no.*

## 1. The question

Can mathematical research state — intent, definitions, provenance, evidence,
failed attempts, proof obligations and verification status — be represented in
a structured form that helps an agent perform and **resume** rigorous
mathematical work?

Not "can we build a platform". One schema, one worked example, one CLI, and an
honest account of what it did and did not buy.

## 2. Why this repository is a fair test bed

Because the failure mode is already documented here, in `AGENTS.md`, under the
heading *The naming trap: three different "theta"s*. Three unrelated functions
share a name; `zeta.explicit.li` is the logarithmic integral while `zeta/li.py`
is Li's criterion, and importing one shadows the other.

A person escapes those by rereading a docstring. An agent resuming cold has no
such reflex — and the expensive version of the error is not a wrong import. It
is a definition that is **formally impeccable and denotes the wrong object**.

Hardy's Z is the sharpest available example, and it is why the worked example
is Hardy Z and not something more impressive:

| candidate | real on the line? | same zeros? | usable? |
| --- | --- | --- | --- |
| `Z(t) = e^{iϑ(t)}ζ(½+it)` | yes | yes | **yes** |
| `\|ζ(½+it)\|` | yes | yes | **no** — never negative, so no sign change to bisect |

The rejected candidate passes every obvious check. It is real, it is even, it
vanishes at exactly the right points, and it is useless, because the entire
purpose of Z is that it *changes sign*. A schema that cannot express "the
purpose is the sign change" cannot catch it.

## 3. The two load-bearing ideas

### 3.1 Intent is data

`dossier.schema.Intent` carries, in prose and before any formula, what the
object is *for* — plus `distinguishes_from`, the list of things it is most
likely to be confused with. A definition can be checked against a formula; the
intent can only be stated, and stating it is what makes a later mismatch
visible.

The Hardy Z dossier's `distinguishes_from` has five entries, four of which are
name collisions already documented in `AGENTS.md`. That is the field earning
its keep: it moves a naming trap from a paragraph a human might read into a
field an agent must read.

### 3.2 "Verified" is four different things

`dossier/status.py` carries four independent axes and refuses to reduce them:

| axis | what it means | how it fails |
| --- | --- | --- |
| `numeric` | a computation agreed at the sample points | agreement to forty digits is compatible with falsity — `docs/08` |
| `certified` | every step carried an enclosure | proves something about a *finite* computation only |
| `literature` | the published record | the citation may be about a different object |
| `formal` | a proof kernel accepted it | the Lean statement may not be the statement meant |

There is no `is_verified`, no score, and no ordering. `Support.__bool__`
**raises**, so `if support:` is a runtime error rather than a silent collapse.
`tests/test_dossier_schema.py::test_support_has_no_truth_value` is the test
that keeps it that way.

The axes are not decoration. In the Hardy Z dossier they read
`agrees-to-tolerance / not-attempted / standard / not-attempted` — one strong,
one absent, one strong, one absent. Any aggregate would have to invent a
weighting nobody can defend.

## 4. What the schema refuses

`dossier_reasons` reports every problem at once and refuses:

- a dossier with **no intent** — a formula with no way to tell if it is the right formula;
- a dossier with **no discriminating obligation** — an obligation nothing plausible fails is a tautology dressed as a check;
- an axis **asserting support with no artifact** — an assertion nobody can re-derive is decoration;
- a **rejected alternative with no reason**, and an **open question with no `what_would_settle_it`** — both are what an agent resuming cannot act on.

`RejectedAlternative` is the field a human would never write unprompted and the
one an agent most needs: without it the next pass re-derives the same dead end
and, worse, may adopt it, because a rejected alternative usually looks
reasonable.

## 5. What was actually measured

Not asserted — run, in `tests/test_dossier_hardy_z.py`:

- The two definitions in this tree agree. `e^{iϑ(t)}ζ(½+it)` versus
  `Λ(½+it) / (π^{-¼}·|Γ(¼+it/2)|)` — the route the Lean draft takes — agree to
  **3.4e-31** at dps = 30 across seven ordinates.
- A **convention question got settled by that check.** The Lean draft's
  docstring says it uses the completed zeta "to avoid needing a continuous
  branch of log Γ". That is right, and the dossier now records *why*: dividing
  by the positive real `π^{-¼}|Γ|` leaves `(Γ/|Γ|)·π^{-it/2}·ζ`, and `Γ/|Γ|` is
  an honest complex number that required no branch to form. The branch is
  needed only when ϑ is wanted as a real, continuous phase counter — for Gram
  points and N(T). Defining Z and counting zeros are different requirements,
  and only the second one needs the branch.
- The rejected alternative was **run alongside** the accepted one and shown to
  pass every obligation except the discriminating one.

That third item is the experiment's thesis in executable form.

## 6. The finding that matters: this is a probe, not a department

`harness/README.md` states the admission rule — **no department without a
battery** — and `validate_battery` enforces it structurally. The honest
question is whether this work can meet it. It cannot yet, and the reason is
worth more than the code.

A battery needs rivals: things that **share the claimed structure and lack the
property**. Ask what a rival to a *dossier* is, and two answers appear, both
unsatisfactory:

1. **A rival dossier** — e.g. one built for `|ζ(½+it)|` with Hardy Z's intent.
   This is a genuine modus tollens and it works; the essence of it is already
   in `test_Z_changes_sign_but_the_rejected_alternative_does_not`. But the
   thing being killed is a claim about **ζ**, adjudicated by **the zeta
   department's** subject matter. The dossier layer contributed the bookkeeping,
   not the refutation.
2. **A malformed dossier** — one with no discriminating obligation, or
   asserting support with no artifact. `dossier_reasons` catches all of those.
   But that is a unit test of a validator wearing a battery's clothes. Decoys,
   surrogates and lesions built this way would all be testing *my own code*
   rather than a subject.

Which exposes the real problem, and it is structural rather than a matter of
effort:

> **A dossier department would have no subject of its own.** Its rivals are
> borrowed from whatever department the dossier is about. A department whose
> battery is another department's battery is not a department.

So `dossier/` is registered nowhere, has no door in `docs/doors/`, and appears
in no department table. It is a probe, and it is labelled one in every file.

**What would make it a department.** The subject would have to become
*representations of research state* rather than the mathematics being
represented — and then a rival is a competing representation that carries the
same fields and loses something the dossier claims to preserve. Concretely: a
flat "notes.md" and a `verified: bool` record, run through the same resumption
task, where the dossier is claimed to preserve what they drop. That is a
measurable claim with a real rival, and it needs at least two more worked
examples and a resumption task with a scoreable outcome before it means
anything. Until then, the rule stands and this stays a probe.

## 7. Before extracting this into its own project

Not a roadmap — a list of things that would have to be *demonstrated*, since
right now the honest summary is "one schema, one example, no evidence it
helps":

1. **A second and third dossier**, at least one for an object where the intent
   is genuinely contested rather than textbook. One example proves a schema can
   be filled in, not that it is the right schema.
2. **A resumption experiment with an outcome.** Two agents, cold, one given the
   dossier and one given the source and docstrings, on the same task. If the
   dossier does not change what they produce, the schema is bookkeeping.
3. **One axis moved by machine.** Every status here was set by hand. The design
   is only worth anything if `certified` can be flipped by actually running an
   enclosure and `formal` by actually building the Lean file. Until then the
   four axes are an honest vocabulary, not an honest measurement.
4. **A dossier that catches a real error.** The Hardy Z example is
   retrospective: nobody was about to define Z as `|ζ|`. The schema earns its
   place the first time an obligation fails against a definition somebody
   actually intended to use.
5. **A rival representation to beat**, per §6.

Items 2 and 4 are the load-bearing ones. Everything else is scaffolding.

## 8. Scope

This document describes bookkeeping about a textbook function. Nothing in
`dossier/` is evidence for RH, none of it is a proof of anything, and Hardy's Z
locating zeros on the critical line says nothing whatever about zeros off it.
Per `docs/08`, that is the permanent situation and not a limitation of this
experiment.
