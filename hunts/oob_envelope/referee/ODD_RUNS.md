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
