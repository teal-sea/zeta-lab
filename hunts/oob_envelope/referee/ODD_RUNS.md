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
=11585.013502836228 core-seconds, below 3.219 core-hours. Launch the 99
remaining main units with the byte-identical source and exact inputs.
