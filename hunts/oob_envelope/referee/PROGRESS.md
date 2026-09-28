# Referee progress, 2026-09-28

**ACTIVE: all 100 L=1.19 blocks complete; final reducer is next.**
Assembly source 548f9a4, CC-192, 1280 bits, 500 even modes. First precision
pilot failed safely; one full-batch preemption caused cancellation of nine
units. Their byte-identical recovery passed. All four apps so far are stopped
with zero tasks. RUNS.md contains the full reconciliation and compute.

Volume oob-envelope-referee: l119/548f9a4 has 91 complete blocks and nine
interrupted attempts; l119/recovery548 has the nine replacements. All raw
matrices remain preserved. Reducer source 119280a, unit reduce_548f9a4,
will use only completed manifests and enforce exact coverage and hashes.
It checks fixed shift 5.718e-48, outward lower endpoint 5.7179e-48,
Rayleigh upper endpoint 5.776e-48, and the -1e-47 I lesion. Positivity
remains UNRESOLVED until that unit completes.

Successful assembly work: 8680.695 core-seconds. Interrupted work: 530.324;
failed precision pilot: 5.428. A conservative app-occupancy bound through
recovery is 9996 core-seconds, below 2.777 hours. Final reducer allowance
900 seconds plus startup fits the four-core-hour ceiling.

Next: run reducer, watch to stopped, retrieve and verify its artifacts,
update REVIEW.md's five verdict lines, run scoped lexical/whitespace checks,
and commit. No push, PR or publication. No author code read. All numerical
work is on Modal and all repository writes remain under referee/.
