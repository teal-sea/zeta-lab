# RUNS: estimates written before launch, actuals after

Machine: the shared swarm box (32 vCPU, 115 GiB), 1-minute load average 58 to
216 during these runs (other workflows), MemAvailable above 77 GiB throughout.
Every run is one single-threaded process, under 1 GB, checkpointed per window
c into `units/<variant>_<kind>.json` (a rerun skips finished windows). At most
seven of these processes ran at once, within the cap of eight. All times are
wall-clock on that loaded box: measured, not pinned by any test, and only good
for the next estimate.

| run | unit timed first | estimate written before launch | actual (per window, then total) |
|---|---|---|---|
| `ghost.py arb dh` (primary, 7 c) | c = 29 in the scratchpad probe: 6.5 s ground state, under 3 s counting | about 30 s per c, 4 min | 22 to 37 s, 206 s (after one void launch, below) |
| `ghost.py arb zeta` (7 c) | c = 30: 5 s at 900 bits, plus the 3200-bit LDL steps | about 1.5 min per c, 10 min | 52 to 90 s, 497 s |
| `ghost.py windows`, first version (Z_epstein scan) | one Z_epstein evaluation: about 10 s on the loaded box | 450 evaluations: over an hour | stopped after about 12 min; replaced (RESULTS s0) |
| `ghost.py windows`, PARI version | lfunzeros: 0.01 s; confirmations 10 s per Z_epstein evaluation | about 10 min | 117 s (Epstein), 544 s in all |
| `ghost.py arb dh --variant=q1`, `sham`, `scan`, `scanfine` | as primary | 30 s per c, 12 min for all four | 16 to 29 s, 162 s; 19 to 28 s, 163 s; 15 to 23 s, 116 s; 17 to 24 s, 61 s |
| `ghost.py float dh` (dps 60) | its first window, c = 29 | written after that unit: 3 min per c, 21 min | 138 to 180 s, 1088 s |
| `ghost.py float zeta` (dps 320) | scaled from float dh by the cost of dps 320 arithmetic (about 3x) | 9 to 15 min per c, 1 to 1.75 hours for 7 c | 301 to 464 s per c |
| `ghost.py arb epstein`, `dedekind` (primary and prec2) | scaled from the stored Epstein scan (4 s per cell at N = 128) plus the counter | 1 min per c, 30 min for the four runs | 19 to 28 s, 12 to 22 s, 27 to 42 s, 18 to 26 s; 698 s in all |
| `ghost.py float epstein`, `dedekind` (dps 60) | as float dh | 3 min per c | 127 to 212 s; 79 to 145 s per c |
| `ghost.py arb * --variant=prec2` (dh, zeta) | as primary at 1.6x the precision | 1.5x primary | 25 to 37 s, 203 s; 66 to 75 s, 482 s |
| `ghost.py arb dh 29 31 47 --variant=N64`, `N192`, `N256` | N = 64 first | N^3 scaling from N = 128: 5 s, 1 min, 3 min per c | 7 to 15 s; 39 to 56 s; 76 to 180 s |
| `ghost.py gap2`, `s2`, `resolution` | reuse of the primary ground states | under 1 min per c | 7 to 17 s per c (gap2); resolution 1 to 3 min per diagnostic |

**Void launch, kept on record.** The first `ghost.py arb dh` launch produced
two void units (c = 31 and 63/2): the residual of the shifted inverse
iteration reached rounding level, its ball contained 0, `sqrt` of the
residual's dot product returned NaN, the eigenvector radius eta became NaN,
and every sign and every segment of those units was undecided (the unit
printed "ghost = False" with no sign change at all). Fixed by
`ghost.residual_upper` (square root of the sum of squared upper bounds) plus
a finiteness guard; the two units were discarded and the whole DH run
repeated; `test_ghost.py` pins the fix.

**Stop and resume, kept on record.** The campaign's workflows were stopped at
the usage limit at 18:10Z on 2026-10-21, after the last float unit
(`float_epstein`, c = 47) had been written but before `ghost.py summary` had
merged the float units. The lane was resumed at about 21:20Z by a second agent
in the same worktree, after checking that no process was still writing it (no
file had changed since 18:03Z). No unit was recomputed; `summary` was rerun,
which completed S7, and the prose was revised against the merged table. The
resume ran only the summary and the lane's tests (single process, under a
minute of compute besides the tests).

**Failed launch, kept on record.** The first `ghost.py float epstein` and
`float dedekind` launches stopped at their first window with a TypeError:
`zeta.epstein.log_derivative_coefficients` takes a callable, and was handed
a list. Fixed in `_float_epstein`; both runs repeated from their first window.
