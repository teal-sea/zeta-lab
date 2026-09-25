# Brief: numerics worker

Read first: `hunts/weil_propagation/MISSION.md`, `AGENTS.md` (hard rules,
certainty ladder, compute discipline), then
`hunts/rogue_frontier/weil_trunc/RESULTS.md` sections 2, 4, 8 and
`THEOREM_FEASIBILITY.md`. The Galerkin assembly lives in
`hunts/rogue_frontier/weil_trunc/galerkin.py` (float/mpmath) and
`enclosures.py` (Arb). Import them; do not rewrite them.

Python: `/Users/thomas/zeta-lab/.venv/bin/python` with
`PYTHONPATH=<this worktree root>`. python-flint is installed there.

## Question

How does the ground state of the truncated Weil form at window L = log c
relate to the ground state at L' = log c' with c' slightly larger? We want a
transport relation that could carry positivity forward, and we want to see
it break for Davenport-Heilbronn exactly where DH turns negative.

## Tasks, in order

1. Reproduce, cheaply, lambda_min and ground vector v(c) for zeta and DH at a
   few (c, N) cells already in the record (e.g. c = 13, 29, 30, 31 at modest
   N). Match the recorded values before going further.
2. Build a common function-space picture across c: map ground states at
   different c into one space (for example the entire transforms F_v(z) on
   the real line, or the functions on [0, L] extended by zero). Measure
   overlap, energy of v(c) under the form at c', and the Rayleigh quotient
   of the transported vector, on a fine c-grid (non-integer c allowed).
3. Decompose the change of the form from c to c' into: archimedean change,
   new prime-power terms entering (n in (c, c']), and the rescaling of the
   basis. Report which term drives the ground-state energy up or down, for
   zeta and for DH, especially across DH's c = 30 -> 31 crossing.
4. State any candidate monotonicity or transport inequality you observe, with
   its range and grade. Test it on DH. If it holds for DH it is refuted.

## Output

Write only in `hunts/weil_propagation/numerics/`: scripts, JSON with every
number, and `RESULTS.md` with measured or hardened grades stated per claim.
Commit to this branch in small commits. Do not push.

## Limits

Local runs under 10 minutes each and a few GB of memory. Record estimates in
`hunts/weil_propagation/numerics/RUNS.md` before any run over a minute. If a
larger run is needed, stop and write the proposed CI job in RESULTS.md
instead of running it. No `lake build`.

Finish by running `tests/test_hunt_probe_discipline.py` and writing a
five-line summary at the top of RESULTS.md: what was found, grade, what
refutes it, next step.
