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
"assumed" — and since the 2026-08-09 build the detector is part of the
admission contract, its specificity is measured alongside its power (a
detector that fires on the clean probe carries no information, whatever its
lesion record says), and the battery as a whole receives an **integrity
grade** that travels with every claim outcome it produces. Batteries can
fail. There is a department whose subject is exactly that
([referee.md](referee.md), [`docs/20`](../20-verification-integrity.md)).

The same discipline is applied to language. *Certified* is a reserved word
with a single owner (`zeta/rigor.py`, every step enclosure-carrying);
everything else is at best *accurate*. Governing the vocabulary is the same
move as governing the code: no claim gets to promote itself.

## What transfers, and what is honestly untested

`harness/protocol.py` names no quantity any laboratory computes and imports
nothing from `zeta` — enforced by an AST scan, a `sys.modules` check, and a
lexical scan for subject-matter vocabulary. It would run unchanged for a
chemistry lab or a compiler-optimisation search.

Six departments now run under it: the mathematics, a decidable-property
subject (curves over F_p), a foreign-vocabulary subject (LLVM IR rewrites),
a foreign-*born* subject (croniter, battery content authored independently
and blind), a distributional subject (statistical model evaluation, which
forced `run_null_band` into the protocol), and the referee itself. Across
all six, `protocol.py` changed once — deliberately, to strengthen admission
— and the shared audit needed exactly two generalisations, both the same
mistake (payload-shape guessing; `ROADMAP.md`, known gap #1). What remains
honestly untested is adoption by an outside team: every department was
still orchestrated by this repository's own process. That is the standing
invitation of this door — start from
`python -m harness.new_department <name>`, whose scaffold generates
questions rather than placeholder instruments, and note that there is
deliberately no final step where a human waves the result through.

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
