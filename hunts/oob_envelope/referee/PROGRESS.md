QUESTION: Supervisor, approve the five Modal-only referee units in RUNS.md, profile teal-sea, one unit per single-use container, 600 seconds and 1792 MiB maximum per unit, with a $0.15 batch allowance and per-unit durable outputs? No numerical run has started.

# Referee progress, 2026-09-27

**Status: analytic review recorded; independent numerical execution blocked
on explicit supervisor approval.** No local numerical test, smoke verifier,
reducer, sweep, build, or Python import was run. No push or publication.

The written review starts with five graded verdicts. Core support lemma and
the finite-cosine split survive ordinary analytic review. The full L=0.8
numerical enclosure remains UNRESOLVED pending independent execution.

## Findings requiring the authors' attention

1. The exact full-space `1.158e-17` endpoint in numerics RESULTS is not supplied
   by the displayed leading shift plus two-block accounting: subtract the
   nonzero coupling error or enclose an additional leading-block margin.
   `1.1579e-17` is a candidate safe rounded endpoint, conditional on the
   author's enclosures. This is not a claim that the true minimum is lower.
2. Theory's all-N cosine estimate uses its correlation inequality beyond the
   proved range. N=1, m=8 makes that intermediate inequality read `1 <= 0`.
   Restrict the cosine estimate or use the shift-norm quadratic bound.
   The limiting duality identity survives this identified repair.
3. Finite-measure H alone does not justify the analytic-strip quadrature
   argument. The actual finite-cosine witness does satisfy that hypothesis.
4. The latest numerics discussion cannot bracket the L=1.19 floor between
   upper bounds at L=1.1 and L=1.2. Monotonicity gives only one of those
   directions. Stage A supplies no support-2.38 positivity result.

Other scoped caveats, the source threshold slip, pole budget, tail factor,
extended-value definitions and theory's later self-review are in REVIEW.md.

## Exact readback

- Requested theory snapshot `e62cac5`; RESULTS changes through `9f5bbc3`;
  final progress/caveat readback `fa6f450`.
- Requested numerics interim RESULTS `ed52a32`; original rational witness
  and initial result at base `57ef234`; final RESULTS/PROGRESS update `b9a25ba`.
- Zhu v2 primary-source reduction and quadrature/tail sections read.
- No author implementation read or imported. Frozen rational data copied
  as input, preserving source metadata.
- Git fetch and current sibling-worktree/Orca-terminal listing performed.
  The advertised research `list_sessions` tool is unavailable here.

## Concrete implementation ready for the approval gate

`independent.py` implements an independent two-atom envelope proof, exact
frozen coefficients, Clenshaw-Curtis assembly on the same 96-mode space,
series-bounded transforms and poles, explicit quadrature radius, alternative
tail/coupling bounds, and shifted interval LDL. K1 is applied to the
full-space lower bound. K3 has both overlap and frequency-integral checks,
with explicit analytic tail formulas. The three lesions target their
broken invariants. DH K2 is independently reconstructed from its defining
coefficients and conductor, at two resolutions, measured grade.

`run_modal.py` dispatches one approved unit and commits each unit's outputs
to volume `oob-envelope-referee`. All numerical work, including eigenanalysis,
stays inside the unit container. Five units are specified in RUNS.md.
The source has only been read as text: it is unexecuted and may require a
bounded repair after its first approved runtime check.

No new report is evidence of a completed run. No JSON execution result is
present. The frozen input JSON is author data, not a referee result.

## Supervisor's Stage A update

Accepted as reported: original app stopped; nine durable units and a reducer
artifact exist on `oob-envelope-stages`. N=360, L=1.19, T=500 midpoint
`5.775648793894534e-48`; interval LDL `n_neg=null`, `undecided=306`; no
quadrature/tail/coupling bounds. Grade: measured and inconclusive. The newer
numerics record adds midpoint inertia only, not an enclosure of that sign.

The newer numerical lane also reports a completed K2 gate-rejection control.
This does not clear this referee's independent K2 task.

## Stopping point

Local activity was limited to reading, writing, source retrieval, git and
static text inspection. No test suite or context generator ran, in accordance
with the compute rule and referee-only edit scope. No external issue,
message, PR, push, or publication was created. Await the supervisor's answer
to QUESTION before any numerical execution.
