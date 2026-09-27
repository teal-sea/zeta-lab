# Referee progress, 2026-09-27

**COMPLETE: all five approved Modal units PASS.** The corrected bound
`Q(f) >= 1.1579e-17 ||f||^2` survives independent review for real even f
supported on `[-4/5,4/5]`. Grade: independently reviewed ordinary reduction
plus an enclosure-carrying numerical step. It is not kernel-checked.

K1 passes in both leading units. K2 at two resolutions, K3 and all three
planted lesions pass at measured grade. The five-line graded verdict and
proof/error-budget details are in REVIEW.md. No support-2.38 positivity
result follows: the L=1.19 interval-sign and remainder obligations stay open.

## Completed independent implementation

No author implementation was read or imported. The exact rational witness
was taken as input; its two-atom sine-kernel construction was independently
rederived. The 96-mode space was retained so that the target Ritz problem
stayed identical, while quadrature changed to Clenshaw-Curtis and transforms
were evaluated with series-enclosed downward recurrence.

Both CC degrees 160 and 192 pass shifted interval LDL at `1.158e-17` and
have a negative pivot at `1.1585e-17`. The measured leading minimum begins
`1.1583402660085778616489630627792930825e-17`. Quadrature operator errors
are below `1.139e-52` and `6.418e-65`; tail deviation is below `2.256e-95`
and coupling below `1.621e-46`. The coupling-subtracted interval comparison
proves the outward-safe `1.1579e-17` endpoint on the full even sector.
These are rounded-up bounds from the stored balls, not midpoint substitutes.

The controls independently reconstruct S and detect the in-band, one-prime
sign and dropped-power lesions. K3 checks complex and odd functions, including
the boundary frequency. DH H=0 negative witnesses give Q about -0.3163 and
R about -0.7314 at both resolutions, agreeing with independent scalar
quadrature. Those controls retain measured grade.

## Accepted repairs and exact readback

- Theory RESULTS was read from requested `e62cac5`, through `9f5bbc3` and
  caveats `fa6f450`, then repaired `b447f0d`. The all-N quadratic bound,
  analytic-strip scope, threshold expansion, pole budget, bounded-symbol
  definitions and even-sector argument pass ordinary analytic readback.
- Numerics RESULTS was read from `ed52a32`, with the exact witness/results
  at base `57ef234`, and updates `b9a25ba`, `3132b7d`, `f779b27`.
  The coupling-subtracted endpoint is corrected to `1.1579e-17`; the false
  L=1.19 two-sided bracket from upper bounds has been withdrawn.
- Zhu v2 primary-source reduction and quadrature/tail sections were read.
  Prior-art verification limits remain explicit in REVIEW.md.
- Final git fetch completed; author heads read back as theory `b447f0d`
  and numerics `f779b27`. Research `list_sessions` is unavailable; the earlier
  read-only Orca terminal/worktree listing identified the sibling lanes.

## Run reconciliation and durable evidence

RUNS.md records authorization, cost estimate, prelaunch static review, exact
unit names, app IDs, every terminal state, file hashes and volume readback.
The frozen source/approval revision is `c65c66e`. Every unit used profile
`teal-sea`, its own single-use container, one CPU, no retries, and a separate
committed output directory on volume `oob-envelope-referee`.

Final counts: **5 launched, 5 successful, 0 failed, 0 inconclusive, 0 active,
0 retries**. All five apps are stopped with zero tasks. All 15 output-file
hashes match the downloaded manifests. Both raw interval matrices, budgets
and LDL records, plus both DH witnesses, are preserved under `outputs/`.
The app-state readback is `outputs/modal_terminal_apps.json`.

Each input stayed below its time limit; combined manifest work is below
230 seconds at one core. The function-work estimate is below $0.004 at the
quoted rates and maximum memory; startup/build/storage are extra and no
provider billing statement was obtained. The approved $0.15 allowance and
<20 core-hour limit were retained without reruns or expansion.

The supervisor's request to update RUNS.md before the next launch arrived
just after degree 192 was dispatched. Degree 160 had already passed terminal
and hash reconciliation; its written ledger was then brought current.
The ledger was updated and committed before either subsequent DH dispatch.
This timing is disclosed in RUNS.md; no failed/inconclusive gate was skipped.

## Remaining limits and execution boundary

No blocker remains for this referee batch. The author's unseen Gauss-rule
code and exact quoted quadrature constant were not audited; the corrected
scientific result is independently supported by the CC implementation.
There is no independent odd-sector numerical bound here, no kernel-checked
proof, and no L=1.19 positivity result. Stage B remains a separate supervisor
approval decision, with no new paid unit requested in this review.

All numerical work ran on Modal. Local work was reading/writing, source
retrieval, git, static text inspection, hashes, and Modal orchestration/file
I/O only. No local numerical Python, test, smoke verifier, reducer, sweep or
build ran. No Actions, external message, issue, PR, push or publication was
created. All edits and durable readbacks are confined to referee/.
