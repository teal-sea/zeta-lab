# ROADMAP.md: what was built, why, and what is next

Current project decisions belong here. Detailed dated history is preserved in
[the pre-clarification roadmap](history/research-guidance-2026-09-12/ROADMAP.md),
unchanged from commit `4cb2230b0ba9f2e73121d0794ae81e08da84d3f5`.
`README.md` is the front door; `AGENTS.md` is the shared operating context;
[ALIGNMENT.md](ALIGNMENT.md) is the current research mandate and evidence discipline.

## Decision: constructive research is the objective (2026-09-12)

**Pursue original mathematics toward RH and useful intermediate results.**
Direct proof attempts, new bounds, counterexamples to candidate statements,
structural lemmas, computational discovery and formalization of new mathematics
are permitted within the assigned mission and authorized resources.

This owner-directed decision supersedes the old blanket non-goal of proving RH
or any part of it. It also supersedes the claims that an apparent discovery
must be a bug, that formal work may concern only known theorems, or that every
existing technique has a proved ceiling below RH. None is a standing research
veto. A proof attempt is permitted; its success is not presumed.

Numerical agreement, a passing model review or a rewritten equivalent
criterion is not a uniform theorem. Preserve the actual target, assumptions,
error terms, finite ranges and proof dependencies. Neither ambition nor a
negative verdict changes the required evidence. The distinction between an
original result and an established novelty claim remains in force.

## Decision: build on the quasi-Riemann theorem (2026-10-08)

The owner directed the laboratory to use OpenAI's zero-free half-plane
(every Dirichlet L-function, zeta included, has no zero with Re s > 7/8;
preprint of 2026-09-30) as an input and build on it, rather than only read or
replay it. Its Lean statements were rebuilt here and accepted by Lean's kernel
and the independent NanoDa kernel (`docs/38` section 7); its argument has not
been reviewed by any person. Results that use it are stated as "proved, given
OpenAI's Theorem 1.1", carry that hypothesis in every sentence, and take the
grade of the weakest step. The first four are in `docs/39`. If the theorem is
withdrawn or refuted, they revert to conditional statements and are marked so;
nothing here makes the half-plane a theorem of this laboratory beyond the
kernel grade of its formal statements.

## Decision: build on the Alpoge theorem (2026-11-21)

The owner directed the laboratory to use Levent Alpoge's theorem (posted
2026-11-20 as a Lean 4 archive: Mathlib's `RiemannHypothesis`, and GRH for
Dirichlet L-functions, so that every Dirichlet L-function is zero-free for
Re s > 1/2, the trivial character at s = 1 excepted) as an input and build
on it.
The verification was done outside this laboratory and was read here in two
sources. The joint statement of the Lean and Mathlib communities, endorsed by
the Lean FRO and the Mathlib Initiative and dated 2026-11-21, says: "We
hereby certify that both the statement and the proof of the Riemann
Hypothesis are correct." Andrew Sutherland's verification page, as updated
2026-11-21 12:55 UTC, records that all 175,187 modules compile, that the five
theorems of `Main.lean` rest on `propext`, `Classical.choice` and
`Quot.sound` only, that every module was replayed through the Lean kernel,
that two independently written kernels accept the full export, and that all
five statements, the three about Dirichlet L-functions included, match a
challenge file that imports only Mathlib; the same page listed some kernel
runs as still in progress. This laboratory's own replay (hunt #159, on
another branch) had not produced its verdict when this was written, so the
kernel grade is the outside checkers', not this laboratory's.

Results that use it are stated as "proved, given the Alpoge theorem", carry
that hypothesis in every sentence, and take the grade of the weakest step,
which is usually the laboratory's own unreviewed argument; the theorem's
kernel grade here is the outside checkers', and any bridge from Mathlib's
definitions to the classical objects (for example from
`DirichletCharacter.LFunction` to a classical L(s, chi)) is a step of its
own that must be written and graded. The scope is Dirichlet L-functions, all moduli and all characters;
nothing here extends it to Dedekind zeta functions or Hecke L-functions. If
the theorem is withdrawn or refuted, the results revert to conditional
statements and are marked so. This departs from the 2026-10-08 precedent,
which built only after this laboratory's own rebuild was accepted by two
kernels, and from recommendation 2 of the regrade board; the owner chose to
build on the outside verification. If hunt #159's replay fails or disagrees
with the outside checks, every result stated "given the Alpoge theorem" is
marked conditional again until the disagreement is resolved. The record page
is `docs/49`.

The decision "constructive research is the objective" (2026-09-12) named RH
as the target. That target is now settled by a theorem proved outside this
laboratory. **No successor target has been chosen.** The candidates are in
`docs/reviews/2026-11-20-rh-claim-regrade-board.md` section (b); choosing one
is an open owner decision, recorded here as open. Until it is made, this
decision authorizes building on the theorem within existing missions and
names no new objective.

## Decision: a failed attempt does not close a method

Use the four dispositions in `ALIGNMENT.md` section 5: candidate refuted,
restricted class obstructed, attempt unresolved, or paused by allocation.
A theorem excluding a construction in a specified information class still
applies to that class. A failed estimate, a limited search or an exhausted
allowance does not establish a universal no-go.

Apply the same standards of proof and review to consequential route-closure
claims as to claimed improvements. A proposed estimate implying RH is a
potential route to RH, not a requirement to assume RH first. A counterexample
must satisfy the candidate's complete hypotheses before it refutes the
candidate. Shared intermediate lemmas need not distinguish the target from
every rival by themselves.

## Decision: breadth before automatic commitment

Within a mission that permits comparison, examine distinct mathematical
mechanisms cheaply, then develop credible constructions. A candidate may
produce a useful lemma before a complete RH argument exists. Immediate
contradictions can stop a trial; otherwise challenge the actual construction,
not merely its technique's name.

The newest hunt's next door has no automatic priority over every other route.
Revisit that choice when the complete argument or available inputs change.
A compact reformulation is not automatically a more tractable problem, and a
conditional side theorem is not automatically an improvement to the fixed
unconditional target. Preserve unused leads without silently launching them.

No new campaign, fixed portfolio allocation, worker count or budget is adopted
by this clarification. Specific scientific priorities and any expansion of a
mission remain the owner's decisions, with routine choices delegated only
within the authorized scope.

## What is already built

The existing workbench includes numerical zeta evaluation, zeros and explicit
formulas; statistics and heat flow; Weil and Davenport-Heilbronn controls;
interval arithmetic, Li/Jensen and other criteria; finite-field examples;
exploratory hunts; and the Lean arm. Use `CONTEXT.md` for the generated API,
document and script index rather than treating an old table as live state.

This decision changes no mathematical implementation, theorem statement,
certificate, experimental data or formal proof. The existing code, tests and
research branches are retained.

## Existing operating decisions remain

- Keep new exploratory work in its scoped hunt. Do not modify an occupied
  checkout or another worker's artifacts. Read current branch instructions
  and available ownership records before acting.
- Preserve the generalized harness's demotion and its recorded experiments.
  Its live bookkeeping is distinct from its frozen framework. This change
  does not authorize a new framework, scheduler or department system.
- Keep scientific reproducibility material with the public science and
  private operational allocation with its owning repository. Existing
  visibility, release, account and spending permissions do not expand here.
- Keep rigorous arithmetic, exact-input handling, independent checks,
  no-sorry requirements and the weakest-link rule for composite claims.
  A finite computation proves only what its verified reduction and range cover.
- Keep resource limits, process ownership, secret controls and safe release
  procedures. This document authorizes no hosted CI experiment, new service,
  recurring job or deployment.
- Preserve the public record of corrections and failed attempts. The site and
  generated indexes remain documentation surfaces, not automatic proof grades
  or publication permission for a new private artifact.

## Historical decisions and scientific state

The [historical roadmap](history/research-guidance-2026-09-12/ROADMAP.md)
retains the full phase table, harness experiments, probe results, field
reports and earlier decisions byte for byte. Its old research prohibitions
are superseded above; its raw observations and scoped mathematical findings
are not erased or silently regraded. This change is not a fresh literature
review or a re-audit of every historical result.

`HANDOFF.md` and each hunt's own records describe dated checkpoints. Resolve
the relevant current branch and evidence before using a checkpoint as live
state. A main-branch introduction need not include a later research-branch
result. Preserve both the original record and a precise correction when they
conflict; do not convert an old summary into authority over newer evidence.
