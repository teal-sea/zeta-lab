# Referee progress, 2026-09-27

**Status: four units PASS; final DH resolution pending.**
The degree-160/192 CC errors have conservative operator bounds below
`2e-49`/`2e-61`; actual Arb budgets will be saved before matrix assembly.
The safe endpoint is `1.1579e-17`, with coupling subtracted. Numerics has
adopted this correction at `3132b7d`; theory repairs at `b447f0d` pass ordinary
analytic readback. Independent K1 passes in both leading units. The first K2
resolution passes at measured grade: DH Q is about -0.3163 and R about
-0.7314, with scalar/matrix agreement. Its higher-resolution repeat is the
only remaining execution obligation in this approved batch.
No local numerical test, smoke verifier,
reducer, sweep, build, or Python import was run. No push or publication.

The written review starts with five graded verdicts. Core support lemma and
the finite-cosine split survive ordinary analytic review. The full L=0.8
numerical enclosure now passes the two independent-quadrature resolutions,
conditional on the explicitly reviewed analytic budgets, on the even sector.

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
Items 1 to 3 have now been repaired in the author prose and reviewed;
item 4 remains in numerics `3132b7d`.

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
- Repair readback: theory `b447f0d`, numerics `3132b7d`, prose only.

## Concrete implementation authorized for remote execution

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
The source was reviewed statically before launch. Controls and both leading
units have now executed only on Modal, without a source repair or rerun.

Source/approval commit `c65c66e` is the fixed run revision. `controls` completed
in app `ap-NhsIKRPPAvEgmNaQlKQZDY`: independent S, K3 and three lesions pass
at measured grade. App stopped with zero tasks; manifest/result downloaded
from volume and result hash matched. `leading160` completed in app
`ap-SQrnl1WJoJuZpHOMPUXByS`: both shifted LDL gates, K1 and safe endpoint pass.
All five output hashes, including the exact-dyadic matrix, match the volume
readback; app stopped with zero tasks. Degree 192 then launched in
`ap-9f0IwvcUOng9xbvYkzLnaU`, and completed with the same passed gates.
All leading192 output hashes match volume readback; its app is stopped with
zero tasks. `dh512` completed in `ap-btXCifdZX2A2S973lxR5jA`, app stopped,
zero tasks; both witness/result hashes match volume readback. RUNS.md records
four successes, no failures or inconclusive units, and no active referee app
before the final authorized `dh768` dispatch.

## Supervisor's Stage A update

Accepted as reported: original app stopped; nine durable units and a reducer
artifact exist on `oob-envelope-stages`. N=360, L=1.19, T=500 midpoint
`5.775648793894534e-48`; interval LDL `n_neg=null`, `undecided=306`; no
quadrature/tail/coupling bounds. Grade: measured and inconclusive. The newer
numerics record adds midpoint inertia only, not an enclosure of that sign.

The newer numerical lane also reports a completed K2 gate-rejection control.
This does not clear this referee's independent K2 task.

## Execution boundary

Local activity was limited to reading, writing, source retrieval, git and
static text inspection. No test suite or context generator ran, in accordance
with the compute rule and referee-only edit scope. No external issue,
message, PR, push, or publication was created. The supervisor approved the
five-unit batch with the conditions in RUNS.md. Commit the prelaunch record,
then run sequentially and stop on the first failure or inconclusive gate.
