# Brief: cutoff/, gap (c), product-ball cutoff against the global module cutoff

You own `hunts/weil_propagation/c4_s2/cutoff/` and write nowhere else.
Time box: **2 hours** of work from your start. This is proof work and can
run indefinitely; at the box, write `RESULTS.md` with the exact state and
stop.

## The gap

The factorization Π_S = S_∞ ⊗ P_2 + 1 ⊗ (1 − P_2) (theory §7.3 item 2) holds
for product cutoffs. Connes' semilocal formula (arXiv:2602.04022 eq. (22))
cuts off by the global module |x|_S, which does not factor. The passage from
the product-ball cutoff to the module cutoff is unproved. two_adic/ builds
T_S with the product-ball cutoff; your result decides what that T_S says
about the formula as Connes states it.

## Inputs

- Connes arXiv:2602.04022 s7 and eq. (22); Connes arXiv:math/9811068 s VII;
  Connes-Consani arXiv:2006.13771.
- Theory RESULTS §7.3 item 2 and its caveat.
- two_adic/ (read-only, when it exists).

## Tasks, in order

1. State both cutoffs exactly for S = {∞, 2} on windows c ∈ [2, 3), and the
   trace term each one defines. **Milestone 1: status message.**
2. Prove that the two give the same T_S on these windows, or bound the
   difference (operator norm, or trace, on the window space), or state the
   gap exactly: which term fails to transfer, and why.
3. If a matrix comparison is cheap, compute the difference on the mission
   cells in the shared basis, reusing two_adic/'s functions read-only through
   imports, never by editing their files. If it is not cheap, say what it
   would cost.
4. If a clean lemma comes out, you may state it in Lean and check it with
   AXLE; grade it kernel-checked for exactly that lemma.

Your `RESULTS.md` must say which of prove / bound / gap you reached, with
its grade.

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
