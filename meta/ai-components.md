# Where the machine belongs, and where it does not

**Nothing here is a mathematical result.** This is evidence about the
laboratory, in the sense of `meta/README.md`: an attempt to name missing
capabilities, because you cannot automate what you cannot state.

## The question

The laboratory currently uses models in one role: the experimenter. Agents run
hunts, write instruments, compute. Almost everything else is mechanical,
the funnel's generators, the battery, the integrity audit, the promotion gate.
The obvious question is why, and the obvious answer is "no reason, we should
do more of it". That answer is too fast.

## The sorting principle (a hypothesis, and it is testable)

> **A model belongs wherever its output is checked against an oracle that is not
> a model. It does not belong where the only check is another model's
> agreement.**

The reason is the laboratory's own standing rule, applied to itself: *a
cross-check bounds only what is actually duplicated*, and *a repetition across
instruments is evidence about the instruments before it is evidence about the
subject*. Two agents drawn from the same weights are not two instruments. They
share priors, they share failure modes, and their agreement is close to free.

**The evidence for it is a session, 2026-08-11.** Three "independent"
derivations of the same functional were commissioned by three different routes,
with the generator of a claim never judging it. All three agreed. That agreement
was worth much less than it looked, because all three were the same model.
What actually carried the result was external and non-model:

- four constants published in the source paper, reproduced to every printed
  digit;
- a coefficient table from a 2008 thesis, reproduced by exact rational equality,
  written sixteen years before the paper;
- an exact Dirichlet convolution over 1260 integers;
- a control that reproduced a *known* theorem to ten digits before the
  instrument was pointed at anything unknown.

Every one of those is an oracle no model could flatter. Remove them and three
agreeing agents would have produced a confident, unfalsifiable, possibly wrong
number.

## Where it belongs (ranked)

**1. The literature backend. Build this first.** The socket already exists and
is deliberately empty: `ontology/knownness.py` carries an
`OfflineLiteratureBackend` that returns `UNKNOWN` forever, alongside
`WOULD_QUERY = ("OEIS", "arXiv", "MathSciNet", "zbMATH", "LMFDB")`, written down
so the hole is legible rather than hidden. The module's own docstring concedes
it can never establish that anything is new, and `establishes_novelty` is
hard-coded `False`.

That gap is load-bearing, and the same session measured it. A novelty claim was
about to be made for an object whose prior art sits in an unpublished 2008 PhD
thesis: not on arXiv, not in the arXiv full-text index, roughly one citation in
the literature. No mechanical check finds that. A model reading primary sources
did, and the claim survived only because the search happened before the writing.

The oracle here is external by construction: a source either contains the
statement or it does not, and the URL is checkable by a human in a minute.

**2. Formal codegen.** `HANDOFF.md` records that rung 3's remaining work is
"codegen, not mathematics". The kernel is the oracle, it is unbribable, and the
acceptance criterion is already binary and already enforced: it compiles with
zero `sorry`, or it does not count. There is no room for a model to be
persuasive here, which is exactly what makes it a good target.

**3. Standing adversarial review.** The director run's skeptics found six real
defects in recorded claims, two of them in controls that could not fire. That
worked, and it is currently a one-off event rather than a standing process. The
oracle is partial, a skeptic can be wrong, but every defect it proposes is
independently reproducible before it is written down, which is the discipline
that made the original run count.

## Where it does not belong

**Judging whether a battery is hollow.** This is the tempting one, and it is
where the laboratory is most exposed: six of six independently briefed authors
reached `CALIBRATED` with batteries that measure nothing, the audit catches two
of six, and the promotion gate waves through a held-out hollow battery's claim
with an empty reason list. Adding a model judge there *feels* like the repair.
It is a second instrument sharing the first one's blind spots, and the failure
is silent. `docs/23` already records that the surviving sham mode is one the
obvious mechanical fix inverts on honest departments; a model judge does not
obviously escape that, and nothing currently measures whether it does.

**Volume conjecture generation.** Dead twice, on the record. Programme P4 was
retired by its own pre-registered falsification test (fewer than 3 of 60
candidates surviving a five-minute attack). The same mistake was repeated on
2026-08-11, a fan-out generating several hundred candidate propositions across
fourteen territories, abandoned as the wrong altitude before it finished, on
operator instruction. The failure mode is specific: models generate
plausible-*shaped* statements, and plausible-shaped is exactly what the funnel
exists to reject. Volume raises the cost of triage without raising the yield.

**The authority layer.** `meta/operator-functions.md` records this as
permanently open by design, and the load-bearing guard is that the system may
not resolve a disagreement it is party to. That is not a capability gap waiting
to be filled.

## The experiment that would test the principle itself

The sorting principle above is a hypothesis stated by the same kind of system it
is about, which is precisely the situation the ledger is built to distrust.

`meta/asymmetry-experiment.md` already pre-registers the design, and its
cheapest informative slice is about an afternoon: have a model that has seen
neither the audit nor the authors' reasoning identify which of the six blind
batteries measure nothing, then compare against the audit's two of six.

- If it also gets two of six, independence is not the variable, the whole
  factorial is premature, and the "bad targets" list above is stronger than
  argued.
- If it gets materially more, then a model judge *does* see something the
  mechanical audit cannot, and the second section of this page is wrong and
  should be rewritten rather than defended.

Either outcome is worth more than the argument. Nothing here should be treated
as settled until it runs.

## Status

Proposal, not a decision. Written 2026-08-11 from a session that produced one
small mathematical result and three usable observations about how it was
produced. No capability claimed, no ledger entry: an `automated` claim costs a
named artifact, and none of the above has one yet.
