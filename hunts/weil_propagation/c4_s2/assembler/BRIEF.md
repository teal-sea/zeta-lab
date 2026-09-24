# Brief: assembler/, combine the bounds, recount by exact inertia, write delta_t_bound/RESULTS.md

You own `hunts/weil_propagation/c4_s2/assembler/` and
`hunts/weil_propagation/c4_s2/delta_t_bound/` (create it), and write nowhere
else. Time box: **3 hours of work**, not counting time waiting for the
bounds to be routed to you. At the box, write what stands, commit, and
finish.

## Your job

Phase 1 starts now, before any ε exists. Phase 2 starts when the
coordinator routes `bound_trunc/` and `bound_quad/` results to you.

**Phase 1: pre-register, then build the harness.** Commit before any ε
arrives (the commit must be in `git log` before you read either bound
folder):

1. `assembler/PREREG.md`: (a) the composition
   ε = eps_trunc + eps_quad + e_Q + e_T∞ per build (triangle inequality), with
   e_Q and e_T∞ taken from checker/ and kernel/ at their stated sizes and
   grades (read their RESULTS; do not re-derive them; include the float64
   rounding of Q and T_∞ into the stored R); (b) the count: exact rational
   inertia n_−(R + εI) on the stored R of each build, formed as
   `checker/run_checker_inertia.py` forms it (import read-only; reuse its two
   exact routes), at c = 2.9, 2.5 and 2.2, on the full space and on the C4
   class subspace V_4 as s7.9 does; (c) the decision rule that separates the
   four outcomes of this brief, in particular outcome 2 (growth absent, ε
   resolves it) from outcome 3 (ε swamps the spectrum), fixed before any ε is
   seen; (d) the wording of each outcome for `c4_s2/RESULTS.md` line 2, per
   the operator's ruling.
2. `assembler/assemble.py` and `test_assembler.py`: the harness, run against
   synthetic ε values (for example the stored band, 2 × band, 0), which must
   reproduce checker/ s7.9's counts at ε = band.

**Phase 2: the recount.** When routed: read both bound folders, compose ε
per build, run the recount, and write `delta_t_bound/RESULTS.md`. Its first
five lines: (1) ε per cell at c = 2.9 and what it is made of; (2) the count
below −ε at N = 8, 16, 32 on every c = 2.9 build, and at 2.5 and 2.2; (3)
which outcome this is, by the pre-registered rule; (4) the grade, weakest
step named; (5) what is open. Every number pinned by a test in
`delta_t_bound/` or `assembler/`. Then send the coordinator the proposed
text for `c4_s2/RESULTS.md` line 2 (the coordinator writes that file, not
you). referee/ reviews your pre-registration and your final counts.

## The question (shared by all four folders)

R_S = Q − T_S with T_S = T_∞ + ΔT (two_adic/ RESULTS s5 item 2, s5b, s7b,
s10). ΔT is the whole 2-adic part of T_S,
ΔT(g) = Tr(ϑ(g)(Q_∞ − Q_S)ϑ(g)^*), computed by two_adic/ in float64 from a
finite family of prolate modes (`ta_prolate.py`, `ta_mellin.py`, ρ by QR
since c3dca00). At c = 2.9 the stored R_S has 4, 10, 20 eigenvalues below
−band at N = 8, 16, 32 (checker/ s7.9, exact rational inertia of the stored
float64 matrices, `checker/checker_inertia.json`). The band (8.2e−3 at
c = 2.9, N = 32) is a response, not a bound, and 14 of the 20 at N = 32 lie
between −2·band and −band.

**Goal of this follow-up:** a proven bound ε ≥ ‖ΔT_exact − ΔT_stored‖,
spectral norm on the (2N+1)-dimensional space spanned by U_n, n = −N … N
(MISSION.md interface contract), for each stored build, carried by arb
enclosures; then the count of eigenvalues of the stored R_S strictly below
−ε, by exact inertia. By Weyl, each such eigenvalue gives a negative
eigenvalue of the Galerkin compression of the exact R_S, provided the errors
of Q and T_∞ are inside ε too.

**Stored builds** (nvec | S | N; Kmax = `two_adic.ta_prolate.kmax_for(nvec)`):
N = 8: 80|1200. N = 16: 80|1200, 80|1600, 120|1200, 120|1600, 160|1600.
N = 32: 200|2400, 240|2400, 280|2266, 319|2633, 364|3060. The matrices are
in `checker/checker_ts_snapshot.json` (key `T_S`, `units`) and
`modal/out_rho/checker_*.json`; `checker/run_checker_inertia.py` shows how R
is formed from them. Measured responses to compare against:
two_adic/ s7b (nvec 80 → 200 at S = 4800, c = 2.2, N = 8) and checker/ s7.2,
s7.3a, s7.8 (80 → 120 → 160 at N = 16, 200 → 364 at N = 32).

**Error sources of ΔT_stored and their owners:**

| source | owner |
|---|---|
| prolate modes beyond nvec omitted from Q_∞ and Q_S | bound_trunc/ |
| s cutoff S of the Mellin and Gram integrals, including the order-1/S tails | bound_quad/ |
| w quadrature: Gauss panels on [1, 2^Kmax], the dyadic truncation at Kmax, the asymptotic 1/w tail series (its term count) | bound_quad/ |
| mode data: η_n and ζ_n evaluated in float64 (scipy spherical Bessel) | bound_quad/ |
| the Gram step, QR of the Gram factor in `ta_mellin.rho` | bound_quad/ |
| float64 rounding in the assembly of the stored matrix | bound_quad/ |
| Q (checker/, mpmath dps 40, rounded to float64) and T_∞ (kernel/, dps 40) | assembler/ states their size and grade; nobody re-derives them |

**The bound interface (fixed now, so the referee can test against it before
it exists).** Each bound folder exposes a Python function and a JSON file:

- `bound_trunc/eps_trunc.py`: `eps_trunc(c, N, nvec, S, Kmax) -> flint.arb`;
  `bound_trunc/eps_trunc.json`: a list of entries
  `{"c", "N", "nvec", "S", "Kmax", "eps_upper", "grade", "assumptions"}`.
- `bound_quad/eps_quad.py`: `eps_quad(c, N, nvec, S, Kmax) -> flint.arb`;
  `bound_quad/eps_quad.json`: same keys.

`eps_upper` is a decimal string that is an upper bound on the error (the
upper end of the arb ball, rounded up), for every stored build at every c in
{2.2, 2.5, 2.9}. `assumptions` lists the numbered assumptions of the
folder's derivation that the number depends on. If a bound does not exist
for a build, the entry says `"eps_upper": null` and why.

## Outcomes (all acceptable; the numbers decide which)

1. **Growth below −ε**: the count at c = 2.9 still grows over N = 8, 16, 32.
   Wording, per the operator's ruling (2026-09-24): C4 fixes no rank bound,
   so no finite N refutes bounded rank. Say: n_−(R_S) ≥ k_N at N = 8, 16, 32
   on this construction (lower bounds), which rules out any remainder of rank
   below k_32 here and is evidence against bounded rank; not a refutation.
2. **Growth absent below −ε, with ε small enough to resolve it**: C4
   survives this test; say so plainly.
3. **The bound closes but ε swamps the spectrum**: counts collapse because ε
   is large, not because the negatives are gone. This is "not resolved at ε",
   and it is **not** outcome 2.
4. **No usable bound**: say precisely which step would not close. That is
   itself a result.

**Grade ceiling.** The tail and quadrature bounds are ordinary arguments.
With arb carrying every numerical step and referee/ having reviewed the
derivation, the best grade is "enclosure-carrying numerics on a derivation
reviewed internally (unreviewed externally)". Only a statement AXLE checks
in Lean with zero sorry is kernel-checked, and only for exactly that
statement. A composite takes its weakest step.

## Rules (all four folders)

- Read first: the repo `AGENTS.md` (hard rules, certainty ladder, lexical
  bans), `hunts/weil_propagation/c4_s2/MISSION.md` (including the follow-up
  sections at the end) and lines 1 to 5 of `c4_s2/RESULTS.md`.
- Worktree `/Users/thomas/orca/workspaces/zeta-lab/weil-c4-s2`, branch
  `teal-sea/weil-c4-s2`. **Never push.** Three other workers commit to the
  same branch in the same tree at the same time: commit only your own paths,
  `git add <your paths> && git commit -m "..." -- <your paths>`; never
  `git add -A`, `git commit -a`, `git stash`, `git reset` or `git checkout`
  of anything outside your folder. If `.git/index.lock` exists, wait a few
  seconds and retry. Commit messages start `hunts(weil_propagation/c4_s2/<folder>):`.
- Write only in your own folder (and the files this brief names). Read
  anything. Do not touch `zeta/`, `ontology/`, `harness/`, another c4_s2
  folder, `MISSION.md` or `c4_s2/RESULTS.md`. Import other folders'
  modules read-only.
- Python: `PYTHONPATH=/Users/thomas/orca/workspaces/zeta-lab/weil-c4-s2 /Users/thomas/zeta-lab/.venv/bin/python`.
  python-flint 0.9.0 (arb, fmpq) is installed there. `pytest -n 2` at most.
- Compute: nothing over about 10 minutes or 3 GB locally; four workers share
  a 16 GB laptop. Heavier units go to Modal (`modal`, profile teal-sea):
  ask the coordinator first, then estimate one unit and append the estimate
  to `c4_s2/modal/RUNS.md` under a new section headed with your folder name
  **before** the batch (the only file outside your folder you may touch, and
  only by appending). Checkpoint per unit. `modal app stop` your apps when
  done. No GitHub Actions, no `lake build`.
- Provers: AXLE only (`axle check`, `verify-proof`, `disprove`,
  `repair-proofs`; it runs remotely). No Leanstral, no Aristotle.
- Grades: the AGENTS.md ladder, weakest step governs. Every number stated in
  your RESULTS.md is pinned by a test in your folder.
- Lexical: under `hunts/` the reserved word that AGENTS.md keeps for
  `zeta/rigor.py` and the Lean arm is banned in every form, including inside
  a sentence disclaiming it (`tests/test_hunt_probe_discipline.py` reads the
  bytes). Say "enclosure-carrying" or "proven (ordinary argument)". No em
  dashes in prose you write.
- Coordination: questions go through the `ask` command in your preamble;
  send a short status message at each milestone. Before `worker_done`, run
  your folder's tests plus `tests/test_hunt_probe_discipline.py` and
  `tests/test_docs_numbering.py`. Finish with `worker_done` and an explicit
  `--outcome`.
