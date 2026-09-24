# Brief: kernel/, gap (a), the archimedean Sonin projection S_∞ on windows

You own `hunts/weil_propagation/c4_s2/kernel/` and write nowhere else.
Time box: **3 hours** of work from your start. At the box, write
`RESULTS.md` with what stands and stop.

## The gap

S_∞, the archimedean Sonin projection, has no closed kernel on these
windows. Connes-Consani arXiv:2006.13771 s6 proves the S = {∞} case with
numerically identified prolate data. Your job is to make S_∞ computable on
window functions in the shared CCM basis of the mission, so that two_adic/
can compose it with P_2 and checker/ can measure R_S.

## Inputs

- Connes-Consani arXiv:2006.13771: Intro, s3 (Cor 3.8, Rem 3.9), s4, s6,
  Thm 6.11, the trace remainder δ(ρ) (their eqs. (8), (10)).
- Connes arXiv:math/9811068 s VII; CCM arXiv:2511.22755 (prolate
  functions, s7-8); theory RESULTS §7.3 item 2 (the factorization
  Π_S = S_∞ ⊗ P_2 + 1 ⊗ (1 − P_2); graded there as a derivation, unreviewed).
- The rejected prior attempt, read and do not trust:
  `remainder.py` and the review, at the path in your task spec. Its split Q = Q_∞ − √2 log 2 · g(log 2) is sound in
  substance. Its two defects, not to be repeated: a claimed 1e-25 tolerance
  that was never achieved (tolerances come from a measured deviation), and
  the x → 0 limit of A(f) taken by a hard-coded 1e-6 finite difference (do
  it analytically or by a stated series).
- `hunts/rogue_frontier/weil_trunc/galerkin.py` and `SOURCE.md` for the
  basis and the archimedean entries.

## Tasks, in order

1. Fix the S = {∞} objects exactly from the source, with section and
   equation numbers: the Sonin space and S_∞, the representation ϑ(f), the
   trace term Tr(ϑ(f) S_∞ ϑ(f)*), the function class of Thm 6.11 (which
   vanishing conditions on the transform are imposed), and δ(ρ). Translate
   into the mission's notation (our f is their g). **Milestone 1: status
   message.**
2. Make S_∞ Galerkin-computable on windows: a closed kernel if one exists,
   otherwise numerically identified prolate data as in their s6, with a
   convergence study (basis size and precision response). State which, and
   grade it.
3. `T_inf_matrix(c, N, dps)`: the S = {∞} trace term as a Hermitian matrix
   on the shared basis. Calibrate at c ∈ {1.5, 1.9} against the statement of
   Thm 6.11 (the inertia and lowest eigenvalues of Q_∞ − T_∞ at
   N = 8, 16, 32, on the full space and on the function class), and report
   the precision response (dps 40 against 60). **Milestone 2: status
   message with the calibration numbers.**
4. If feasible within the box, support the Γ_ℂ archimedean type
   (Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1), the archimedean data of Dedekind ζ_{Q(√−23)})
   so the positive control can run. If not, say so plainly in
   `INTERFACE.md` and `RESULTS.md`.
5. `INTERFACE.md`: the functions, their conventions, the JSON keys, and the
   exact representation of S_∞ that two_adic/ consumes (for example a matrix
   on a stated basis of L²(ℝ), or a kernel function with its quadrature
   rule). The coordinator routes it to two_adic/ and checker/.

Values for the mission cells c ∈ {2.2, 2.5, 2.9} go to a JSON in your folder.

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
