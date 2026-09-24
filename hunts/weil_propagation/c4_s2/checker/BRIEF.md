# Brief: checker/, independent verification and the kill-controls

You own `hunts/weil_propagation/c4_s2/checker/` and write nowhere else.

## Independence rule (read this twice)

**Do not open, import or read anything in `kernel/` or `two_adic/`,
including their `INTERFACE.md`, until the coordinator sends you their
output.** Write your tests first, from theory RESULTS §0 and §7, the
mission's interface contract, and the primary sources. Commit them, then
send a status message "phase 1 committed <hash>". The coordinator routes
kernel/ and two_adic/ output only after that commit is in `git log`.
Afterwards you may adapt the call glue to their real signatures, but not the
properties your tests assert. If a property turns out wrong, say so in
`RESULTS.md` and keep the original commit in history.

## Phase 1 (time box 1.5 hours)

1. **Your own Q.** `checker/` implements Q on the shared basis for
   c ∈ [2, 3) from theory §0, independently. Calibrate it against
   `zeta.weil.weil_functional` on at least two unrelated test-function
   families (for example the Fejér pair and a smooth bump), and against the
   CCM matrix of `hunts/rogue_frontier/weil_trunc/galerkin.py` on the same
   basis. Take the x → 0 limit of A(f) analytically or by a stated series,
   not a finite difference. Tolerances come from the measured deviation at a
   stated dps. (The rejected prior attempt,
   at the path in your task spec, failed on both
   points; you may read it, do not copy it.)
2. **Tests of R_S = Q − T_S**, written as properties any correct
   construction must satisfy, derived from the sources. Examples, not a
   ceiling: T_S Hermitian and positive semidefinite (the unitarity
   argument of §7.1); switching the place 2 off gives the S = {∞} term; the
   S = {∞} statement of Connes-Consani arXiv:2006.13771 Thm 6.11 at
   c ∈ {1.5, 1.9}; the inertia of R_S stable in N (N = 8, 16, 32), which is
   the operational content of "bounded rank"; precision response (dps 40
   against 60); Q itself positive on the cells (Zhu arXiv:2608.24827,
   support ≤ 1.6). State the grade of each property's derivation.
3. **The (U-S) gate** (mission kill-control 1), in exact arithmetic for
   n ≤ 200, as your own implementation. Only after it passes, compare it
   with theory `checks.py` check K and numerics `us_check.py` (read via
   `git show`).
4. Commit, then the status message. **Milestone 1.**

## Phase 2 (after routing)

5. Run your tests against kernel/ and two_adic/. Report each failure to the
   coordinator in a status message naming the owning folder, the test, and
   the exact numbers; the coordinator routes it to the owner. Do not fix
   their code.
6. Kill-controls 2, 3 and 4 of the mission. For the positive control, if
   kernel/ or two_adic/ do not accept Dedekind's data, record "positive
   control not exercised" and why. **Milestone 2.**

## Phase 3

7. R_S on every cell c ∈ {2.2, 2.5, 2.9}, N ∈ {8, 16, 32}, full space and
   function class: inertia, the three lowest eigenvalues, their N- and
   precision response. JSON in your folder, each number pinned by a test.
8. `RESULTS.md`, including a table of which kill-control ran and how it came
   out. Stay available for re-runs until the coordinator says you are done.

## Standing rules (identical in all four briefs)

- **Read first:** `hunts/weil_propagation/c4_s2/MISSION.md` (scope, shared
  basis and cells, interface contract, kill-controls, done),
  `hunts/weil_propagation/MISSION.md`, `AGENTS.md` (hard rules, certainty
  ladder, original vs novel), `ALIGNMENT.md` sections 4 and 5, and theory
  `hunts/weil_propagation/theory/RESULTS.md` sections 0, 7, 7.1, 7.3, 8.
- **Python**, from the worktree root:
  `PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python`. The
  `.venv/bin/python` named in `AGENTS.md` does not exist in this worktree.
  Tests: `PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 <your folder> tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py`
  (`testpaths` is `tests`, so name your folder explicitly).
- **Compute:** four workers share a 16 GB laptop. Every local run under 10
  minutes and a few GB; N ≤ 32 and dps ≤ 60 unless you state why; pytest
  `-n 2` at most. Anything larger goes in your `RESULTS.md` as a CI proposal
  with a measured per-unit estimate. No `lake build`.
- **Git (shared worktree, shared branch `teal-sea/weil-c4-s2`):** commit only
  your own folder:
  `git add hunts/weil_propagation/c4_s2/<folder>/` then
  `git commit -m "<msg>" -- hunts/weil_propagation/c4_s2/<folder>/`.
  Never `git commit -a`, `git add -A` or `.`, `git stash`, `reset`,
  `rebase`, `checkout` of files you do not own, or `push`. Files outside your
  folder in `git status` belong to peers: leave them. On an `index.lock`
  error wait a few seconds and retry. Small commits; end each message with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- **Read-only inputs** from the sibling branch:
  `git show teal-sea/weil-propagation:hunts/weil_propagation/numerics/<file>`.
  Source PDFs go in your session scratchpad, never in the repository.
- **Lexical ban:** `tests/test_hunt_probe_discipline.py` fails if the past
  participle of "certify" appears anywhere under `hunts/` in a `.py`, `.md`
  or `.json` file, case-insensitive, including inside a longer word and
  inside a sentence disclaiming it. Do not write it. Never dump a raw
  `zeta.rigor` result dict to JSON (it carries that key); rename keys.
  House style: no em dashes in prose you write.
- **Provers: AXLE only** (`axle` on PATH, runs remotely: `axle check`,
  `verify-proof`, `disprove`, `repair-proofs`). No Leanstral, no Aristotle,
  and no escalation about their keys (operator's decision). Prover output is
  input, not evidence: it counts only after zero-sorry checking, and is
  graded kernel-checked for exactly that lemma and nothing wider.
- **Grades:** the `AGENTS.md` ladder; a composite claim takes the grade of
  its weakest step. Every number in your `RESULTS.md` is pinned by a test in
  your folder. Tolerances come from a measured deviation at a stated dps,
  never asserted. A search you did not run is "not searched".
- **Orca:** every `--from` and `--terminal` you pass is **your own** handle
  from your preamble, never the coordinator's. Check your inbox at each
  checkpoint (before starting a new file, after a test run) and immediately
  before `worker_done`. Blocking questions go through your preamble's `ask`
  command. Send a `status` message to the coordinator at each milestone
  named below. Anything outside the mission, irreversible, or costing money:
  ask, do not do.
- **Finish:** `RESULTS.md` in your folder whose first five lines say what was
  built, the key numbers with their grades, and what is open; an ALIGNMENT
  s5 status (refuted, obstructed in a restricted class, unresolved, or paused
  by allocation). An exact statement of where the construction is stuck is a
  complete result; a fabricated number is not. Then `worker_done` once, with
  `--outcome succeeded` or `--outcome failed`, `--files-modified` and
  `--report-path`.
