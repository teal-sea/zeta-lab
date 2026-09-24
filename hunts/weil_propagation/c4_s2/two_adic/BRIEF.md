# Brief: two_adic/, gap (b), P_2 through E_S and the assembly of T_S

You own `hunts/weil_propagation/c4_s2/two_adic/` and write nowhere else.
Time box: **3 hours** of work from your start. At the box, write
`RESULTS.md` with what stands and stop.

## The gap

The action of the 2-adic projection P_2 on window functions through the map
E_S is not given in a form that yields matrix entries. You build it, and you
own the assembly of T_S(f) = Tr(ϑ_S(f) Π_S ϑ_S(f)*) for S = {∞, 2} with the
product-ball projection Π_S = S_∞ ⊗ P_2 + 1 ⊗ (1 − P_2).

## Inputs

- Connes arXiv:math/9811068 s VII (Thm 4, the semilocal trace formula,
  L²(X_S), the map E_S and the quotient by S-units).
- Connes-Consani arXiv:2006.13771 (the S = {∞} construction you extend).
- Connes arXiv:2602.04022 s7.2-7.4, eq. (22) (the semilocal form of the
  Weil functional).
- Theory RESULTS §7.1-7.3, especially §7.3 item 2 (1_{ℤ_2} is self-dual, so
  time and frequency limiting to ℤ_2 coincide; graded there as a
  derivation, unreviewed: recheck it).
- The rejected prior attempt, read and do not trust:
  `remainder.py` and `RESULTS.md`, at the path in your task spec.

## Tasks, in order

1. Fix the objects exactly from the sources, for S = {∞, 2}: X_S, the
   scaling action ϑ_S, E_S and the S-unit quotient, the product-ball cutoff,
   P_2. Recheck the factorization of Π_S. **Milestone 1: status message.**
2. The action of P_2 through E_S on window functions, as matrix entries on
   the shared basis. Start with the 1 ⊗ (1 − P_2) piece, which needs no
   archimedean data.
3. `T_S_matrix(c, N, dps, local_data, arch_type)` on the mission cells.
   `local_data` is the tower at 2 given as Satake parameters α_{j,2}
   (degree d); ζ is (1,), Dedekind ζ_{Q(√−23)} is (1, 1). The builder must
   **refuse** non-unitary parameters (|α| ≠ 1) and a tower s_k(2) that is not
   of the form Σ_j α_j^k with unitary α_j (mission kill-control 2: W_a and
   Epstein (1,1,6) must be refused; returning a trace term for them is a
   defect). Report the inertia of T_S at each cell (unitarity says it is
   positive semidefinite; measure it, do not assume it), and check that
   switching the place 2 off reproduces kernel/'s `T_inf_matrix`.
   **Milestone 2: status message with the cell numbers.**
4. S_∞ comes from kernel/. The coordinator routes kernel/`INTERFACE.md` to
   you when it exists. Until then build against a stub with the interface
   the mission names, and do not edit kernel/. If the representation kernel/
   delivers does not fit, say what you need through `ask`; do not build a
   second S_∞.
5. `INTERFACE.md` in your folder: functions, conventions, JSON keys.

cutoff/ works on the product-ball versus global-module question and may read
your folder. You use the product-ball cutoff.

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

## Follow-up, 2026-09-24: grade the Modal accuracy run (s7b)

*Added by the coordinator.* The operator approved running your s7b compute
proposal on Modal. `modal/` ran it; its outputs are in
`hunts/weil_propagation/c4_s2/modal/out/gram_<nvec>_<S>.json`, one per
(nvec, S), in the shape `ta_gram_probe.py` writes for one run: nvec 140, 160,
180, 200 at S = 4800 and 160 at S = 9600, plus the calibration run 80 at
S = 4800, which matches your committed `ta_gram_probe.json` entry to 8.2e−15.
Provenance (tree 284eff6, versions, wall and CPU seconds, cost) is in
`modal/RUNS.md`. Everything above in this brief still applies.

Your task: **grade it, in this folder only.**

1. Merge the new runs into `ta_gram_probe.json` in its existing shape, each
   marked with its source (`modal/out/...`, tree 284eff6, platform). Read
   `modal/` files; never edit them.
2. Apply the criterion your script's docstring fixed before the S = 4800 runs
   were read (s7b): the nvec response at S = 4800, the S response at 160
   modes (4800 against 9600), and the probe. State whether ΔT's band on
   c = 2.2, N = 8 now falls below Q's lowest eigenvalue there (2.5738e−4), at
   which nvec, or that it does not. Your s7b extrapolation (the 0.36 ratio per
   20 modes) was a prediction: say whether the new runs confirm or refute it.
   Do not move the criterion after reading the numbers.
3. Update RESULTS s7b, and your first five lines where they change (line 1's
   band, line 5's open item), with grades: measured (float64, one route)
   unless something is independently checked.
4. Pin every new number with a test in this folder that reads
   `ta_gram_probe.json` (and, for the merge, the `modal/out/` files).

Constraints for this follow-up:
- **Do not edit any file in T_S's import closure**: `ta_ts.py`,
  `ta_prolate.py`, `ta_mellin.py`, `ta_data.py` (nor kernel/). checker/'s
  snapshot guard keys on their blobs, and checker/ is merging new N = 32 rows
  under the current digest right now. If a code change looks necessary, ask.
- Nothing heavy locally (a few minutes at most); no new Modal runs. If the
  grade needs another run, say which one and its estimate, and ask.
- Commit with pathspecs, your folder only. No push. No em dashes.
- Run your folder's tests plus `tests/test_hunt_probe_discipline.py` and
  `tests/test_docs_numbering.py` before `worker_done`.

## Follow-up 2, 2026-09-24: your citations of checker/ went stale

*Added by the coordinator.* checker/ re-graded R_S at N = 32 after you
finished (8d66d09, 3dc0a74; its RESULTS lines 1 to 3 and s7.7). Two tests in
`test_ta_checker_citations.py` now fail against `checker/checker_ts_cells.json`
(`test_n_minus_of_R_S_below_band`: c = 2.2 reads 4, 4, 0, not 4, 4, 3;
`test_N8_refinement`: `refinement_response["32"]` is no longer None), and
your RESULTS line 5 and line 589 still quote the old N = 32 counts
(4, 4, 3 / 4, 9, 20 / 4, 10, 20).

Task: bring your citations of checker/ up to date, in this folder only.
Read checker/'s RESULTS lines 1 to 3 and s7.7 and its JSON; cite what it now
says (the N = 8 and 16 counts are unchanged; at N = 32 the count is
undecided on that route in float64, with the reasons checker/ gives), and
update the two tests to pin the current checker/ values. Change no
mathematical statement of your own. Same constraints as the first
follow-up: no edits to T_S's import closure, no runs beyond the tests, your
folder only, pathspec commits, no push, no em dashes.
