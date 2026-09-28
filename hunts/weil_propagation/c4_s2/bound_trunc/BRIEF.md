# Brief: bound_trunc/, the prolate-mode truncation tail of ΔT

You own `hunts/weil_propagation/c4_s2/bound_trunc/` and write nowhere else
(except appending to `c4_s2/modal/RUNS.md` if you use Modal). Time box:
**3 hours** from your start. At the box, write `RESULTS.md` with what stands,
commit, and finish.

## Your job

Prove a bound on the error of ΔT from omitting the prolate modes beyond
nvec, the binding error (two_adic/ s7b: 80 → 120 modes moved T_S by up to
7.8e−2 at N = 16; per-20-mode responses at c = 2.2, N = 8 fall slowly,
ratios 0.53 to 0.80). Derivation with numbered, stated assumptions, then
arb code that evaluates it on every stored build.

Two facts to take seriously before you start: two_adic/ s6 shows P F_S P is
bounded but not Hilbert-Schmidt (no super-exponential eigenvalue decay for
the semilocal problem), and the measured response decays slowly. What the
count needs is only the compression of the error to the (2N+1)-dimensional
window space on the U_n basis, in spectral norm, not a bound on the
operator. Do not bound more than that.

## Milestones

1. **Feasibility, within 45 minutes.** Write `DERIVATION.md` section 1:
   (a) exactly what ΔT_exact is, as a limit over modes, from two_adic/ s5
   and the sources it cites (CCM arXiv:2310.18423 Thm 4.6, Connes-Consani
   arXiv:2006.13771); (b) whether that limit is proven to exist, in which
   norm, and on what argument; (c) whether a tail bound for the omitted modes
   is derivable, and which inputs it needs (prolate eigenvalue decay on these
   windows, the dilation series of |Θ|^{−1}, the ρ step's dependence on the
   mode count). Commit, and send the coordinator a status message with the
   verdict. If no bound is derivable, say exactly which step does not close:
   that is outcome 4 for your part and is a result; then look for a weaker
   statement that still serves the count, and stop at the box either way.
2. **Derivation.** `DERIVATION.md`, every assumption numbered, every constant
   either closed form or an arb enclosure. Commit and tell the coordinator:
   it goes to referee/ for review.
3. **Enclosure code.** `eps_trunc.py` and `eps_trunc.json` in the interface
   below, for every stored build at c ∈ {2.2, 2.5, 2.9}; `INTERFACE.md`;
   tests in `test_bound_trunc.py`. A test must show the bound dominates the
   measured mode responses listed above (necessary, not sufficient; state
   the inequality you test, with the triangle inequality made explicit).
4. **RESULTS.md**, first five lines: the bound, its assumptions, its values
   on the c = 2.9 builds, its grade, what is open.

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
