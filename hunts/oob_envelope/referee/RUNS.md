# Referee approved run record, 2026-09-27

**APPROVED batch completed: 5 successes, 0 failures, 0 inconclusive.** Authorization
is for these exact five units, sequentially, profile `teal-sea`, under
20 core-hours and a $0.15 allowance. Stop on the first failure or inconclusive
gate. Commit scoped source, brief and run record and review exact names and
safety before launch. This does not authorize the L=1.19 campaign or reruns.

## Approved units and original estimate

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
The application, image and volume were created by the approved first unit.

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
`budget.json` records the actual enclosed errors saved before assembly.
Arithmetic propagation and LDL passed in both leading units.

The author endpoint `1.158e-17` must lose `eps_B` in the two-block proof.
The acceptance target is **1.1579e-17** after subtracting the independently
bounded coupling. Numerics has adopted that correction in its latest RESULTS;
this referee's two completed enclosures now support that corrected endpoint.

No local numerical parsing/import, smoke test, Python computation or reduction
was performed. The local Modal CLI imported orchestration code only.

## Execution ledger

Fixed source revision: `c65c66efc3c8773c5af33cb0e0657262e34bf84b`.
Source files are retained unchanged, including their prelaunch "unrun"
annotations; the subsequent execution status is recorded here and in manifests.
Initial image `im-NmG98aqP2NRUXZ7Dt7P8Ov` built in a reported 12.85 seconds.

| unit | app ID | terminal/active state | durable unit directory |
|---|---|---|---|
| controls | `ap-NhsIKRPPAvEgmNaQlKQZDY` | completed, gate true; app stopped, zero tasks | `controls-a4feaac8775d4162b67d7b8aa6007804` |
| leading160 | `ap-SQrnl1WJoJuZpHOMPUXByS` | completed, gate true; app stopped, zero tasks | `leading160-ef68634f3c3b48afa25b622dd08eec87` |
| leading192 | `ap-9f0IwvcUOng9xbvYkzLnaU` | completed, gate true; app stopped, zero tasks | `leading192-ab7bc85aac7d460c9cb4c0345fcaab93` |
| dh512 | `ap-btXCifdZX2A2S973lxR5jA` | completed, gate true; app stopped, zero tasks | `dh512-0e120161c03047efb3d0555d704884bf` |
| dh768 | `ap-abCKDTvqdbI4OWIGmJ52fP` | completed, gate true; app stopped, zero tasks | `dh768-b5ac0f96eec044c18033fb24f7943230` |

Final counts: **5 launched, 5 successful, 0 failed, 0 inconclusive,
0 running, 0 not launched, 0 retries**. Each input had its own container;
apps were reconciled to stopped with zero tasks before the next launch.

All directories sit under the fixed revision on volume `oob-envelope-referee`.
Controls manifest reports 5.646634578704834 seconds of unit work; all three
lesions and K3 pass, measured grade. `S_ideal` begins
`1.5552528267195543951568233271330596615`; exact `S_frozen` matches the input.
The result SHA-256 is
`769a1e536737082ea44704e712c7a94f2274ac29870465443e744d325d7fad26`.
Its downloaded file matches that durable manifest hash. Source and witness
SHA-256 values also match the current scoped files. Readback is stored in
`outputs/controls-a4feaac8775d4162b67d7b8aa6007804/volume/`.

The first directory download to a nonexistent local destination produced a
malformed local concatenation; it is retained as `directory-download-attempt.txt`.
Downloading manifest and result individually fixed this file-I/O problem.
No numerical unit was repeated and no numerical reducer was run locally.

`leading160` completed in 93.07853555679321 seconds. The unit returned
`acceptance_gate=true`, positive LDL at `1.158e-17`, and a negative pivot
at `1.1585e-17` (index 36). The measured Ritz minimum begins
`1.1583402660085778616489630627792930825e-17` and lies in the author bracket.
The independent per-entry quadrature budget is approximately `1.186e-54`,
tail budget `2.256e-95`, and coupling budget `1.621e-46`. K1 and the
coupling-subtracted safe `1.1579e-17` endpoint pass. These rounded summaries
are not endpoint enclosures; full balls are in result/budget JSON.

All six durable files were downloaded under
`outputs/leading160-ef68634f3c3b48afa25b622dd08eec87/volume/leading160-ef68634f3c3b48afa25b622dd08eec87/`.
The manifest's hashes match all five output files, including the exact-dyadic
matrix and LDL record. Matrix SHA-256:
`4164ccbfe6ba8c96652274c2c0ac9224a74eaa69702b733347ff874fa3888640`;
result SHA-256:
`c51cc835b5238bbab5caad8e404de083a55bf48e9615268859f8ebe5c7b653b2`.
Modal app metadata confirms stopped at 14:18:45 America/Bogota, zero tasks.

Sequencing disclosure: degree 192 was launched only after reading the
leading160 completed receipt, checking all durable output hashes, and seeing
the app stopped. The supervisor's subsequent request to update this ledger
before the next launch arrived just after that launch. This ledger had still
shown leading160 running at that instant. It is corrected here; before any
DH launch, both terminal reconciliation and this written ledger will be
updated. No failure or inconclusive result was ignored, and no unit reran.

`leading192` completed in 115.78645706176758 seconds with gate true. It
reproduces both shifted LDL decisions, K1 and the safe `1.1579e-17` endpoint.
Its measured Ritz minimum has the same stored 85-digit string as leading160;
this textual agreement is not an extra error enclosure. Its independent
per-entry quadrature error is about `6.685e-67`; the tail and coupling balls
have the same leading digits as leading160. All six files were downloaded
under `outputs/leading192-ab7bc85aac7d460c9cb4c0345fcaab93/volume/leading192-ab7bc85aac7d460c9cb4c0345fcaab93/`.
All five output hashes match the durable manifest. Matrix SHA-256:
`a5b58509745a7327f9ac9c1913f54288348780eddadca52fa6a0e8007518dfab`;
result SHA-256:
`b55b5137714be31decd243bd43b08664b0a6c131b4507a5acb4798823a73fde6`.
The app is stopped, zero tasks, at 14:21:47 America/Bogota. This record was
written after readback and before dispatch of `dh512`.

`dh512` completed in 6.50263786315918 seconds with gate true, measured grade.
On its unit-norm DH witness, `Q=-0.31630285307629097`,
`R=-0.7314173097418135`; the independent adaptive scalar evaluation gives
`R=-0.7314173097417971`. The H=0 reduction and negative-witness gates pass;
`beta=-21.22492167124564`, so the essential floor also refuses positivity.
This is a negative-control result, not an enclosure of the DH integrals.
The witness, result and manifest were downloaded under
`outputs/dh512-0e120161c03047efb3d0555d704884bf/volume/dh512-0e120161c03047efb3d0555d704884bf/`.
Both output hashes match the manifest. Result SHA-256:
`6f32ca6f2a288cdfe27d0c9c58a681c8cb34b8dda4e0231fe4a793372c1c00ec`.
The app stopped at 14:23:22 America/Bogota with zero tasks. This written
reconciliation precedes the final approved unit, `dh768`.

`dh768` completed in 8.452404975891113 seconds with gate true, measured grade.
It gives `Q=-0.31630285307558303`, `R=-0.7314173097420369`, and scalar
adaptive `R=-0.7314173097419605`. The negative witness, domination and
scalar/matrix agreement gates pass again. The three durable files are under
`outputs/dh768-b5ac0f96eec044c18033fb24f7943230/volume/dh768-b5ac0f96eec044c18033fb24f7943230/`.
Both output hashes match the manifest. Result SHA-256:
`39b3d1994a16e3627f20ac8bbbf28561d7c5e716c15eb2b70ec1725381c31db4`.
The app stopped at 14:24:57 America/Bogota with zero tasks.

Final Modal app metadata for all five stopped apps is saved in
`outputs/modal_terminal_apps.json`. Every unit has a receipt, durable
manifest, result and volume readback; both leading units also have matrix,
budget, progress and LDL artifacts, and both DH units have witness vectors.
All 15 output-file hashes match their respective downloaded manifests.
No numerical reducer or comparison script ran on Ghost.

Resource closeout: each manifest's elapsed time is below its 570-second
work alarm; the sum is below 230 seconds at one allocated core, hence below
0.064 core-hour of input work. Applying the quoted CPU rate and full 1.75 GiB
memory cap to that work gives a function-work estimate below $0.004.
This excludes startup, the reported 12.85-second image build and storage;
it is not a billing statement. No rerun or allowance increase was needed.
The original $0.15 allowance and <20 core-hour ceiling were retained.

Scientific closeout: both independent leading units support the corrected
`1.1579e-17` lower bound on the even sector, subject to the explicit ordinary
analytic budgets. K1 passes; K2, K3 and lesions pass at measured grade.
No L=1.19 unit was authorized or run. Stage B remains a separate supervisor
decision, with its quadrature/tail/coupling and interval-sign obligations open.

# L = 1.19 independent run, 2026-09-28

Thomas authorized this referee task and four core-hours total. The older
L=4/5 batch is closed; its no-new-run language does not apply to this task.
Plan: L119_PLAN.md. First measured unit is panels 990 through 999, CC-192,
1024 bits, N=500. Unmeasured planning range: 60 to 600 seconds, hard limit
900 seconds, one CPU, 1792 MiB. No numerical work runs locally. Before
remaining units launch, record measured runtime and multiply by 100 with
explicit allowance for the reducer and startup. Stop if four core-hours
cannot cover the work. Every unit commits its own evidence to the volume.

Remote session-listing tool with research status is unavailable. The exposed
Honcho list_sessions is a memory API, not the research-session tool. Fetch
completed; git worktree listing identifies the two author branches. Orca
initially reported no runtime; its read-only terminal check is retried after
starting the app. No other lane receives messages or writes.

Pilot 1, source 41ff24f: app `ap-rLGrvMGdAOqdVOOTZOS39n`, **failed safely**
after 5.43 core-seconds at the transform-width guard, before any completed
panel. App list confirms stopped, zero tasks. The 1024-bit recurrence at
x near 595 did not meet the requested 1e-65 radius. Error and receipt saved
under outputs_L119/41ff24f. This is an arithmetic-width failure, not a sign
result. No remaining unit was dispatched. Repair: 1280 bits and series tail
threshold 2^(-precision+64), with unchanged quadrature and target. The next
pilot has the same ten panels and 900-second hard limit. It remains inside
the task's four-core-hour authorization; its measured cost still gates the
full dispatch. No automatic retry is enabled.

Pilot 2, numerical source 548f9a4: app `ap-rqh9FPUy7RU4JTYWllgrfl`,
**completed**, 71.383 core-seconds including serialization/checkpoints.
App list confirms stopped, zero tasks. Ten panels at the largest t pass,
with arithmetic row-radius <1.005e-125. Envelope slacks are positive for
all four primes. Independent bounds are eps_Q <1.697e-64 per entry,
eps_D <1.490e-184 and eps_B <1.553e-90. Downloaded manifest, budget and
result are in outputs_L119/548f9a4; the matrix remains on the volume.

**Measured estimate recorded before full dispatch:** 100 times the measured
71.383 seconds is 7138.3 core-seconds, under 1.983 core-hours. Reserve 30%
for slower containers (2142 seconds), 900 seconds for reduction/controls,
600 seconds for startup and image overhead, and the 5.43-second failed pilot.
Total planning allowance <10800 core-seconds, **under three core-hours**,
leaving at least one hour below the authorized four-core-hour ceiling.
The remaining 99 units run with ten containers maximum, one core each,
one unit per container and no retries. The ten-pilot-panel checkpoint is
reused, never recomputed. All matrices are per-unit volume checkpoints;
no local reducer. Stop the app if accumulated work threatens the ceiling.
Numerical source and all assembly parameters stay pinned to 548f9a4.
