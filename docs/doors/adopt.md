# Door: take the referee for a subject that is not ζ

**For you if** you care less about the Riemann Hypothesis than about the
problem it forced this repository to solve: when plausible ideas cost minutes
to generate, the scarce resource is **reliable rejection** — and a rejector
nobody tests is just another claim.

**First command** — watch the referee referee itself:

```bash
.venv/bin/python -m pytest -q -o addopts='' tests/test_harness_protocol.py tests/test_department_conformance.py
```

(59 tests, about two minutes — the protocol half runs in a tenth of a second,
which is itself the seam working; the rest is department #1's rivals actually
being evaluated.)

The first file checks the protocol against stand-ins, including the seam that
keeps it subject-free. The second re-audits every registered department: door
on disk, rivals that answer, decoys that actually substitute, lesions planted
at more than one magnitude, and every reference claim re-run with its verdict
re-derived rather than trusted.

## The loop, and why the rejector is tested

The operating loop is *generate → attack → measure → discard → retain the
evidence* — as opposed to *generate → make a convincing explanation →
publish*. The attack step is four instrument roles, each a way a claim can
fail to be about its subject that a machine can check without knowing whether
the claim is true:

| Role | The question it asks |
|---|---|
| **Rival** | does the claim also hold for something that shares the structure and lacks the property? |
| **Decoy** | does the measurement move when the substantive input is swapped out? |
| **Surrogate** | does a null model with no substantive input reproduce the observation? |
| **Lesion** | does the detector notice a violation planted on purpose? |

The part most easily missed, and the part most worth taking: **the battery is
itself under test, in both directions.** A department must declare at least
one reference claim its battery kills and one it passes, and the conformance
suite re-derives both verdicts — because a referee that only ever says "no"
looks exactly like a strict one until you hand it something known to be
sound. The lesions close the loop on the other side: a detector that has
never been shown to notice a planted violation has a power of exactly
"assumed".

The same discipline is applied to language. *Certified* is a reserved word
with a single owner (`zeta/rigor.py`, every step enclosure-carrying);
everything else is at best *accurate*. Governing the vocabulary is the same
move as governing the code: no claim gets to promote itself.

## What transfers, and what is honestly untested

`harness/protocol.py` names no quantity any laboratory computes and imports
nothing from `zeta` — enforced by an AST scan, a `sys.modules` check, and a
lexical scan for subject-matter vocabulary. It would run unchanged for a
chemistry lab or a compiler-optimisation search.

But there is one department. The four roles are, today, a generalisation of
exactly one case, and whether they carve a *second* subject well is unknown
until someone builds one (`ROADMAP.md`, known gaps). That is the standing
invitation of this door: the admission procedure is four steps in
[`harness/README.md`](../../harness/README.md) §"Adding department #2", and
there is deliberately no fifth step where a human waves it through.

## The pattern outside a mathematics repository

Nothing in the protocol knows it is about mathematics. The same shape recurs
wherever generation got cheap before verification did: an agent's tool calls
need ground truth, an A/B test needs a stopping rule declared before the
data, a research assistant needs a counterexample battery, a detector needs
planted violations. What this repository adds to that observation is an
existence proof with tests: one subject, fully instrumented, where the
verdict cost collapsed to the claim cost
([`docs/17`](../17-the-falsification-harness.md) §4) — and where the referee
would fail the suite the day it stopped being able to say "yes".

A department keeps its own doors, its own docs and its own fun —
[learn.md](learn.md) and the heat-equation story exist because department #1
enjoys itself. The spine asks only one thing: **no department without a
battery.**

Related: [refute.md](refute.md) to bring a claim to department #1's battery;
[`docs/17`](../17-the-falsification-harness.md) for the day the instruments
earned this door.
