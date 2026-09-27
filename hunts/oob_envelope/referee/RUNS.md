# Referee approved run record, 2026-09-27

**APPROVED by the supervisor on 2026-09-27; not yet launched.** Authorization
is for these exact five units, sequentially, profile `teal-sea`, under
20 core-hours and a $0.15 allowance. Stop on the first failure or inconclusive
gate. Commit scoped source, brief and run record and review exact names and
safety before launch. This does not authorize the L=1.19 campaign or reruns.

## Proposed units

| unit | work | anticipated time, estimate only | hard input timeout |
|---|---|---|---|
| `controls` | independent per-prime constants, K3 overlaps and frequency integrals with tails, three lesions | 30–180 s | 600 s |
| `leading160` | 96-mode L=4/5 block, CC degree 160, 512 bits; explicit quadrature/series/tail/coupling budgets; two shifted LDL decisions; K1 | 180–570 s | 600 s |
| `leading192` | same frozen form and subspace, CC degree 192, 640 bits and deeper series seeds | 240–570 s | 600 s |
| `dh512` | 65-mode DH negative witness, H=0 reduction, time-domain and frequency-domain evaluation | 20–120 s | 600 s |
| `dh768` | independent resolution repeat of DH control | 30–180 s | 600 s |

These are unmeasured engineering estimates, not timing claims. The authors'
L=0.8 run reports about 25 seconds for its different implementation; that is
not a calibration of this new code. The first `controls` unit includes the
initial runtime/API check. Any implementation failure or timeout stops the
batch for inspection; no automatic retuning or repeat is authorized.

Each input gets a new, single-use container with one physical CPU core as
both request and hard limit; memory request 1024 MiB, hard limit 1792 MiB.
One container is active at a time. Each unit has a 570-second work alarm and
a 600-second Modal input limit. C-library calls can defer the Python alarm;
the Modal limit remains the outer limit. Startup has its own 600-second
limit. The reviewer must own and monitor every invocation to a terminal
state. No unattended job is proposed.

## Cost estimate

The maximum requested input runtime is 3000 core-seconds, or 5/6 core-hour,
with at most 1.75 GiB per container. At the retrieved standard Function
rates, CPU is `$0.0000131/core-second` and memory is
`$0.00000222/GiB-second`. Thus the input execution estimate at every hard
limit is `$0.050955`, rounded to **$0.06**. Rates were checked against the
[official Modal pricing page](https://modal.com/pricing) on 2026-09-27.

Approved **$0.15 batch allowance**, including initial image work and
incidental storage/startup. This is an operational spending allowance,
not a provider-enforced dollar cap. Image-build cost and provider-level
infrastructure retries are not bounded by the five function timeouts.
No manual reruns are included. Stop and report if the initial unit fails
or monitoring shows the allowance is at risk.

## Durable outputs and provenance

Profile: `teal-sea`. New volume: `oob-envelope-referee`. Each unit writes
under `<revision>/<unit>-<uuid>/`, independently of all other units.

Every unit writes a manifest before numerical work, then its own result or
error, environment versions, code/witness hashes and elapsed time. The zeta
units write the enclosed lower triangle as exact dyadic midpoint/radius
pairs before LDL and eigenanalysis, and a separate LDL record before the
measured eigenvalue calculation. Progress commits occur every 20 panels.
The DH units preserve their witness vector before the reduced-form check.

Every write is renamed atomically and followed by a Modal volume commit.
A hard kill can leave the manifest at `running`, which must be reconciled
with Modal's terminal state; it is never counted as a completed result.
No local matrix reduction is needed. The local entrypoint writes only the
returned receipt. Any later comparison/reducer that needs arithmetic must
also run on Modal and be separately budgeted if these outputs do not suffice.

The API settings follow [Modal's Function configuration](https://modal.com/docs/sdk/py/latest/App)
and [volume commit documentation](https://modal.com/docs/guide/volumes).
Neither the application, image, nor volume has been created by this review.

## Approved dispatch

From the repository root, use the referee commit hash as REVISION. Dispatch
one unit at a time, inspect its returned terminal status, and stop on any
failed or inconclusive gate. Each actual dispatch is recorded below:

```sh
MODAL_PROFILE=teal-sea modal run hunts/oob_envelope/referee/run_modal.py \
  --unit controls --revision REVISION --approved
```

Subsequent unit names, within the same explicit approval: `leading160`,
`leading192`, `dh512`, `dh768`. No GH Actions, local Python, smoke test,
reducer or build is part of this plan.

## Acceptance contract

- Controls: all three mutants trigger their relevant broken invariant;
  endpoint/out-of-band correlations vanish and the in-band defect agrees
  with its exact overlap formula. Finite checks remain measured.
- Both zeta units: the frozen envelope passes an Arb decomposition; LDL
  passes at `1.158e-17` and finds a negative pivot at `1.1585e-17`; full
  tail/coupling subtraction leaves the outward-safe `1.1579e-17` endpoint
  and remains below K1. Both raw matrices and all error terms must exist.
- Both DH units: negative time-domain and reduced-form Rayleigh values,
  with the independent scalar quadrature agreeing on the reduced witness.
  A missing runtime result, resource refusal, or a wrong target form is not
  a pass. This first DH control is measured, not an enclosure of its integrals.
- Reproduction of the theorem's conclusion does not independently reproduce
  the author's tighter quoted error constants or validate their code.

## Static prelaunch review and degree budget

The source and initial request were committed as `1249b94`; BRIEF.md was
already tracked on the base. The final prelaunch revision also records this
approval, the following degree calculation, a cheap in-container budget gate,
and an explicit `inconclusive` terminal status for false acceptance flags.
Exact dispatch names are `controls`, `leading160`, `leading192`, `dh512`,
`dh768`. They match both allowlist and dispatcher. No author code is imported.
The local entrypoint imports only the Modal orchestration API and writes a
receipt; all mathematics and acceptance checks execute in the remote unit.
Retries are zero; single-use containers, one CPU, resource limits, profile
guard, per-unit paths and volume commits were inspected as text.

Ordinary analytic budget, to be checked with Arb inside each leading unit:
there are 29 frozen high coefficients, each of absolute value below 2;
their frequencies are below 18. The comb coefficient sum is below 3,
`|beta|<2`, `log(pi)<2`, and `cosh(18/4)<46`. Consequently the strip symbol
majorant is below 4000 and the entry majorant
`2L(4N-3) exp(2L/4) M_symbol` is below `5e6`.
With `rho=1+sqrt(2)`, the per-entry error is
`400 M_entry/[pi (rho-1) rho^q] < 2e9/rho^q`.
Since `rho^4=17+12sqrt(2)>33` and `33^2>1000`, degree 160 gives an entry
error below `2e-51`, and degree 192 below `2e-63`. Multiplication by 96
gives operator errors below `2e-49` and `2e-61`, respectively. Both are far
below the target `1e-17` scale and the `1e-21` safe-rounding margin.
These are conservative derivations, not local numerical test results.
`budget.json` will record the actual enclosed errors before assembly.
Arithmetic propagation and LDL can still be inconclusive and must pass.

The author endpoint `1.158e-17` must lose `eps_B` in the two-block proof.
The acceptance target is **1.1579e-17** after subtracting the independently
bounded coupling. Numerics has adopted that correction in its latest RESULTS;
this referee still requires its own completed enclosure before promotion.

No local parsing, import, smoke test, Python execution or numerical reduction
was performed. Static review cannot substitute for the first remote check.

## Execution ledger

No app IDs or terminal results yet. Counts: 0 launched, 0 successful,
0 failed, 0 inconclusive, 5 pending. Volume readback pending.
