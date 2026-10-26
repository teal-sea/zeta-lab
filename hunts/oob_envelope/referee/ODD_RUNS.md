# Odd referee execution ledger

Authorized: ODD_BRIEF.md and Thomas's execution request. Incremental Modal
input compute cap: 14400 core-seconds. Profile teal-sea, one CPU per input,
at most ten concurrent inputs, no detached app, no push. The present agent
watches every owned app to a terminal state. Local work is limited to edits,
reads, compilation and tiny sanity checks. Existing referee files are read-only.

Preflight: clean branch teal-sea/oob-odd-referee at 06fdc801. Fetched remote
refs without integrating. The Orca worktree listing was used because the
requested project list_sessions tool is not exposed in this session. Other
visible oob lanes were done. Existing shared venv is linked locally and
reports python-flint with both expected backends; the pre-push hook is installed.
The full fast suite is not run on this host, per the brief's compute constraint.

## Estimate before the pilot

The previous even referee measured 71.383 core-seconds for ten high-frequency
500-mode panels. This is a planning input, not a measurement of the odd code.
First run one odd unit on panels 990 through 999 at the frozen main settings.
Allow 180 seconds, one core, with a 165-second internal alarm, no retries.
Measure it and replace the provisional extrapolation before any main batch.
There are 100 main ten-panel units and 30 Zhu ten-panel units. The latter
have 200 modes and lower precision. Reserve 1200 seconds for Zhu,
900 seconds for reduction and controls, 600 seconds for startup/verification,
and a 30% reserve on the main extrapolation. Provisional total is
100*71.383*1.3+1200+900+600=11979.79 core-seconds, below the cap.
Stop before the main launch if measured extrapolation exceeds the cap.
Every unit checkpoints a manifest, budget, progress and exact-dyadic matrix.
Quota refusal is a terminal blocker, not a mathematical failure.

## Pilot and measured dispatch estimate

Source freeze commit 3ce6ab9. App ap-F5KLwbmFxNF1jLkY7PfYBU completed the
main high-frequency pilot, panels 990 through 999. Manifest runtime:
72.40257549285889 core-seconds, including serialization and checkpoints;
assembly progress at panel ten was 60.388236847 seconds. No numerical gate
failed. No quota block was encountered.

Recorded before any full main dispatch: 100*72.40257549285889*1.3 plus
1200 for Zhu, 900 for reducers/controls and 600 for startup/verification is
12112.334814071656 core-seconds, or less than 3.365 core-hours. This includes
the successful pilot. Proceed with Zhu's 30 units and reduction first, then
the remaining 99 main units if observed runtime still fits the cap.

Local tiny hygiene run: 29 passed, five deselected, 3.84 seconds. The
context index is current. Contribution structure check fails on existing
hunt-level omissions: MISSION lacks a huntspec block, and hunt-level RUNS
and RESULTS do not exist. None was changed by this review. The narrower
referee documents and evidence remain within the authorized write scope.

## Zhu validation completed; main dispatch

App ap-XXYjuxO0XEJyrQxtC3FKhQ: all 30 Zhu assembly units completed,
651.6811525821686 core-seconds. App ap-FRG5XG7ywfOtMwX6OlcjI9: reducer
completed in 42.71830892562866 core-seconds, passing the positive endpoint,
quadrature moments, pole normalization, matrix hashes and tail gates.
Both local entrypoints exited zero. Total recorded work including pilot is
766.8020370006561 core-seconds. The original planning allowance still covers
all remaining work. Before main launch, an updated conservative estimate is
766.8020370006561+99*72.40257549285889*1.3+900+600
=11585.013502931595 core-seconds, below 3.219 core-hours. Launch the 99
remaining main units with the byte-identical source and exact inputs.

## Main assembly completed

App ap-oyXeqoiRrDLKIDCKlkzXlj completed all 99 remaining main units. Together
with the pilot, all 100 main blocks are present. The client emitted one
heartbeat deadline warning, but continued returning successful units and
exited zero; no input failed or was retried. Total recorded work through
all assemblies and Zhu reduction is 8197.112294197083 core-seconds.
One main reducer has at most 900 input seconds available, leaving the total
below 9098 core-seconds before conservative app-occupancy accounting.

## Final result, counts, and terminal states

Main reducer app ap-MDXpk3KteZl2PtytdCXKFA completed in
255.8151834011078 core-seconds. The safe endpoint 2.99e-44, the actual
pole-sign mutation and the negative-operator control all passed. Independent
artifacts were frozen locally in `cefd6363` before reading
three worker comparison artifacts at 08ff0491. No worker Python was read.
The measured reduced-form value agrees at the worker's displayed precision;
the independent lower shift remains the one fixed before execution.

| app | task | terminal state | maximum allocated cores |
|---|---|---|---|
| ap-F5KLwbmFxNF1jLkY7PfYBU | main pilot | stopped, zero tasks | 1 |
| ap-XXYjuxO0XEJyrQxtC3FKhQ | Zhu assembly | stopped, zero tasks | 10 |
| ap-FRG5XG7ywfOtMwX6OlcjI9 | Zhu reduction | stopped, zero tasks | 1 |
| ap-oyXeqoiRrDLKIDCKlkzXlj | main assembly | stopped, zero tasks | 10 |
| ap-MDXpk3KteZl2PtytdCXKFA | main reduction and controls | stopped, zero tasks | 1 |

Counts: 132 completed inputs, zero failed inputs, zero inconclusive inputs,
zero retries. These comprise 130 assemblies and two reducers, 1300 panels,
250900 CC node evaluations including repeated endpoints. Two positive
factor proposals and one expected negative-control refusal. Two controls
passed. No quota block. One early read requested a not-yet-written result
and returned file-not-found; it was a read, not a numerical input or failure.

Recorded input work totals 8452.92747759819 core-seconds, 2.348035410443942
core-hours. Manifest elapsed time is recorded before the final manifest
commit. For a separate conservative occupancy bound, the complete app
lifetimes times maximum cores sum to 78+91*10+50+838*10+262=9680 core-seconds,
less than 2.689 core-hours. Both are below the 14400-second authorization.
All states, durations and package versions are saved in execution_summary.json
and modal_terminal_apps.json. Container Python image series is 3.12, with
python-flint 0.9.0, mpmath 1.3.0 and gmpy2 2.2.1. The container Python patch
version was not logged. Modal client is 1.5.5; local Python is 3.13.14.

Seventeen deciding artifacts were downloaded. Their compressed and
uncompressed hashes, plus every numerical source/input hash, match the
unit manifests. The final head/factor and all source and exact inputs are
local; intermediate panel matrices remain at the named volume paths and
are covered by locally saved unit manifests. No heavy local numerical run,
GitHub Actions, push, PR or publication occurred.

## Final local checks

The affected fast hygiene selection passed again: 29 passed, five slow
checks deselected, 4.44 seconds. Python compilation and git diff --check
pass; CONTEXT.md is current. Nine reported outward error bounds were checked
against their saved printed balls with directed decimal arithmetic. Exact
rational comparison confirms the chosen independent endpoint lies strictly
below the worker's exact endpoint, and both displayed Rayleigh comparisons
agree. The composite arithmetic and ordinary-proof grades are unchanged.

The initial secret-scanner call omitted the required ref argument. A second
call incorrectly supplied a directory instead of a ref and is not counted
as a valid scan. The final check uses the real committed range
06fdc801..HEAD; its output is final_secret_check.log. These CLI invocation
mistakes did not execute any numerical inputs. No out-of-scope repair to
repo tooling was attempted.
