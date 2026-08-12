# Decision Memo: Zeta Lab's Next Phase

> Transcribed from `Zeta Roots - Core.pdf` (10 pages, received 2026-08-11).
> Mathematical typography restored where PDF extraction garbled it; content
> otherwise unaltered. This is an outside recommendation, not a result — see
> `docs/reviews/README.md` for the directory contract and `ROADMAP.md`
> ("The outside memos, triaged") for what was adopted from it.

## Recommendation

Zeta Lab should evolve from a zeta-specific research repository into a
research operating system built around its validation harness.

The next phase should not prioritize generating more conjectures or adding
agents everywhere. It should prioritize making the existing research loop:

> persistent, adversarial, inspectable, and increasingly autonomous wherever
> a non-model oracle exists.

The governing principle should be:

> **No agent without an oracle.**

Agents may generate ideas, search literature, write code, attempt proofs,
attack results, and explore branches. They should not be allowed to assign
epistemic status to their own outputs.

That authority should remain with exact computation, independent numerical
checks, primary sources, Lean or another proof kernel, explicit adversarial
controls, and — where necessary — human judgment.

## Why this is the right direction

The existing roadmap correctly identifies the validation harness — not the
zeta-specific mathematics — as Zeta Lab's most reusable asset. Its rivals,
decoys, surrogates, lesions, conjecture funnel, and self-auditing integrity
layer are what distinguish the project from systems optimized primarily for
discovery volume.

The roadmap also correctly identifies an automation gap: much of the pipeline
already has the right staged architecture, but execution, persistence, and
supervisory control remain partially manual.

I recommend closing that gap — but without converting Zeta Lab into an
autonomous conjecture factory.

The recent research behavior of the lab suggests that its strongest capability
is not merely producing plausible discoveries. It is producing hypotheses,
attacking them, killing some of its most exciting apparent results, preserving
those failures, and occasionally isolating narrower claims that survive.

Automation should amplify that behavior.

## Architecture

Zeta Lab should be organized conceptually into three layers.

### 1. Epistemic Kernel

This is the trusted core. It contains:

- harness controls;
- rivals, decoys, surrogates, and lesions;
- exact and interval arithmetic;
- Lean/kernel verification;
- preregistrations;
- provenance;
- claim history;
- regression tests for killed claims;
- source-backed literature evidence.

This layer should remain deterministic wherever possible and independent of
whichever frontier model is currently fashionable.

### 2. Agentic Research Layer

Agents operate above the kernel in specialized roles:

- literature scout;
- experimental mathematician;
- code/derivation agent;
- proof formalization agent;
- blind adversarial reviewer;
- white-box adversarial reviewer;
- research summarizer.

The existing roadmap already identifies literature search and automated
adversarial review as particularly high-leverage additions.

The important change is that these agents should produce **artifacts for
verification, not verdicts**.

### 3. Research Control Layer

A web interface should expose:

- active hunts;
- frontier maps;
- proof/dependency graphs;
- conjecture provenance;
- live agent branches;
- verification status;
- killed results;
- unresolved human decisions;
- start/pause/terminate controls.

The roadmap's proposed monitor, conjecture explorer, proof viewer, and control
surface are therefore worth building.

But the interface should emphasize research state, not agent activity. The
headline metric should not be "agents ran 8,000 experiments." It should be:

> What do we know now that we did not know before, and why are we entitled to
> believe it?

## First new primitive: HuntSpec

Before adding heavy orchestration, every autonomous investigation should
receive an explicit machine-readable research contract.

Example:

```yaml
hunt:
  id: realizability_gap
  question:
    Does ordered configuration realizability improve
    the current bandwidth-one lower bound?
  current_frontier:
    lower: 0.6725007037
    upper: 0.6818286875
  known_dead_routes:
    - scalar multi-window optimization
    - measure-only positivity
    - multiplicity-only constraints
  proposed_attack:
    triangle_consistency
  required_oracles:
    - exact small-N enumeration
    - rational LP certificate
    - independent implementation
    - Lean if a symbolic theorem emerges
  kill_conditions:
    - null model does not recover baseline
    - result deteriorates under refinement
    - realizable counterexample violates candidate inequality
  agents_may:
    - search
    - derive
    - code
    - attack
    - formalize
  agents_may_not:
    - declare novelty
    - declare theorem status
    - approve external release
```

This should become the unit of autonomous research. It gives the lab a durable
definition of:

> question → permitted search space → verification regime → falsification
> conditions → escalation rules.

## Highest-priority integrations

### 1. Literature Scout

Upgrade `knownness.py` with an AI-assisted literature retrieval layer.

The output should never be "NOVEL." It should instead return:

- databases searched;
- primary sources inspected;
- candidate equivalent results;
- adjacent results;
- exact passages/equations;
- unresolved ambiguity;
- "no matching result located" when appropriate.

The distinction matters because failure to find prior art is not proof of
novelty.

This is a very strong use of AI because its output can collide with
primary-source documents rather than another model.

### 2. Standing Adversarial Reviewer

Make red teaming continuous rather than occasional.

Every promising result should automatically generate two attacks:

- **Blind attacker**: sees the claim, assumptions, code and controls, but not
  the author's reasoning.
- **White-box attacker**: sees everything and searches specifically for
  correlated assumptions, shared preprocessing, normalization mismatches,
  hidden approximations and non-independent "independent" checks.

The goal is not merely to find counterexamples. It is to ask:

> What modification of the world would preserve the appearance of this result
> while making its interpretation false?

This is arguably the automation most aligned with Zeta Lab's identity.

### 3. Independence Graph

Every verification path should expose its dependency structure. For example:

```
                     input
                       │
                  conversion
                       │
            ┌──────────┴──────────┐
            │                     │
       Arb backend          interval backend
            │                     │
            └──────────┬──────────┘
                       │
                    agreement
```

Two implementations that share a faulty conversion layer are not fully
independent.

The lab should therefore measure **verification independence**, not merely
verification count. This should become visible both in machine-readable claim
metadata and in the UI.

### 4. Proof-Agent Adapter

External proof agents should be integrated only as proof generators. The
contract is:

```
agent
  ↓
generated Lean
  ↓
local repository
  ↓
lake build
  ↓
Lean kernel
  ↓
zero sorry
  ↓
verified proof artifact
```

This is almost an ideal AI integration because the model cannot persuade the
verifier.

The roadmap's suggestion to use proof-oriented systems for bounded
formalization tasks is directionally correct.

## Do not automate indiscriminate conjecture generation

I would explicitly reject "run the discovery funnel continuously and generate
as much as possible" as the default strategy.

Instead, use directed fungal exploration. The lab maintains a frontier map:

```
KNOWN
│
├── exhausted routes
├── blocked routes
├── unresolved assumptions
└── OPEN TERRITORY
       ├── experiment A
       ├── experiment B
       ├── adversarial construction
       └── literature probe
```

Agents should grow outward from identified open boundaries. This preserves
exploration while dramatically reducing triage debt.

The objective is not maximum candidate count. The objective is: legitimate
information gained per unit of human judgment consumed.

## The UI should celebrate killed results

One of Zeta Lab's most differentiating artifacts should be a first-class
graveyard. For every withdrawn result:

```
0.672529 candidate
STATUS               WITHDRAWN
WHY                  algebraic mismatch
CAUGHT BY            explicit counterexample
REGRESSION TEST      YES
FORMAL OBSTRUCTION   YES
CAN THIS FAILURE RECUR?   guard installed
```

That communicates more scientific credibility than a page containing fifty
"discoveries."

The product should show:

> Alive → Under attack → Certified → Killed → Why → Permanent guard

as normal research states.

## Orchestration

Use LangGraph, Claude Agent SDK, or another orchestration layer if useful, but
do not allow the orchestration framework to become the canonical repository of
scientific truth.

Workflow state may live there. Evidence should not.

The canonical research record should remain in durable Zeta Lab artifacts:

- hunt specifications;
- claims;
- computations;
- source records;
- proof artifacts;
- failure records;
- verification reports;
- git history.

That keeps orchestration replaceable.

## Recommended build order

I would authorize work in this sequence:

1. HuntSpec and run manifests
2. Literature scout
3. Standing adversarial reviewer
4. Verification-independence graph
5. Proof-agent adapter
6. Durable orchestration
7. Read-only research UI
8. Human-attention queue
9. Start/pause/steer controls
10. Run a highly targeted autonomous frontier hunt
11. Only then expand aggressively into additional domains

The roadmap proposes broadening into OEIS, L-functions, random-matrix
ensembles, LLM evaluation auditing and other areas. Those are promising, but
Zeta Lab currently has a rare opportunity to harden its research architecture
against live mathematical work before increasing scope. I would exploit that
first.

## What success should look like

Six months from now, a successful Zeta Lab should be able to accept:

> "Investigate whether configuration realizability creates a strict
> improvement over the current pair-correlation relaxation."

and autonomously:

1. create a preregistered hunt;
2. map known results and dead routes;
3. search prior literature;
4. generate several mathematically distinct attacks;
5. execute exact/numerical experiments;
6. generate its own adversarial controls;
7. kill failed branches;
8. preserve those failures permanently;
9. isolate surviving claims;
10. formalize bounded components where possible;
11. stop when real human mathematical judgment is required;
12. present the decision-maker with a compact evidence package.

The human should then see something like:

> One claim survived. 14 branches were killed. 3 independent non-model checks
> support the survivor. One unresolved lemma remains. Two papers may contain
> relevant prior art. Estimated human decision required: "Is this lemma worth
> pursuing?"

That is what useful research autonomy looks like.

## Decision requested

Approve Zeta Lab's next phase under the following charter:

> **Build an autonomous research system around the validation harness, not an
> autonomous conjecture generator around an LLM.**

Prioritize literature retrieval, adversarial review, formal verification,
provenance, durable hunt state, and the human-attention interface.

Do not permit model agreement to substitute for independent evidence. Do not
optimize for discovery count. And adopt the architectural rule:

> **No agent without an oracle.**

If Zeta Lab can preserve that principle while making the discovery loop
persistent and increasingly autonomous, the result could be substantially more
interesting than another AI mathematics agent.

It becomes an experiment in how to make machine-generated research trustworthy
enough to matter.
