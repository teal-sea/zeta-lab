# ACTIVE-CLAIMS — live coordination between concurrent sessions

**Read this before launching an agent, a prover submission, or a build
in `hunts/frontier_math/`.** `HANDOFF.md` is the serial channel (session
to session, across time). This file is the *parallel* one: two or more
sessions have worked this directory simultaneously all of 2026-08-12,
coordinating only through git, and that produced three avoidable
collisions — a near-duplicated bridge, an artifact landed with unrewritten
imports that the other session's test caught, and a formalisation target
each side approached from a different end without knowing.

## The protocol, in three lines

1. **Before starting**: `git fetch origin main && git log --oneline -15 origin/main`,
   then read the CLAIMS table below.
2. **When you start something that will run longer than a few minutes**:
   add a row. Push it immediately, before the work.
3. **When you finish or abandon it**: mark the row and push. A stale claim
   is worse than no claim.

Claims are advisory, not locks. If you need something another session
holds, take it and say so in the row — but take it knowingly.

## CLAIMS

| Session | Holding | Files it will write | Status |
|---|---|---|---|
| codex-counting-lattice | re-audit the large-k budget floor after re-optimising the critical-lattice spacing at every k; derive the `2*pi` lattice limit | `counting_lemma.py`, `test_counting_lemma.py`, `PROOF-LEDGER.md` | **DONE** — fixed-spacing `6.3e-3` floor falsified; exact Poisson limit `c2(0) - A^2 = 0.00517169408367867955` landed with the re-optimised ladder and lesion control |
| transplant-lemma (Fable) | the negative-margin question: does the multi-pair verdict survive at theta = 995/1000 for large clusters at the resonance spacing | `negative_margin_probe.py`, `test_negative_margin_probe.py` | **ACTIVE** — refinement running |
| transplant-lemma (Fable) | adversarial extremum search over configurations | `adversary_evolution.py`, `test_adversary_evolution.py` | **PAUSED** — module complete, agent lost to a container restart, not yet re-run |
| transplant-lemma (Fable) | prover submissions on the E-form family | `zeta23ext/Zeta23Ext/EForm2/`, `TruncEst/` | **LANDED** |
| (other session) | the extension package's assembly, module ports to the upstream pin, `Bridge.lean` | `zeta23ext/` build files, `BRIDGE-SPEC.md`, `PIPELINE.md` | inferred from commits, not self-declared |
| transplant-lemma (Fable) | the near-coincident closure campaign: four parallel angles on the last quantifier | `repulsion_trade.py`, `near_coincident.py`, `cluster_sdp.py`, `exact_gap_attack.py`, `verify_lemma_c_independent.py`, `RETENTION-PROBLEM.md` (+ tests) | **SINGLE-PAIR (k=1) RETENTION CLOSED at hardened grade**, no separation hypothesis — four routes agree, exact-rational certificate, coordinator reproduction. **Multi-pair k>=2 (blocker 2 proper) still OPEN.** Ledger 2026-08-13: defect #19 was labelling the first as the second; defect #20 then over-corrected by relaying `cluster_sdp`'s factor 1.99 as an obstruction to the k>=2 STATEMENT — it obstructs only that ACCOUNTING, whose two sides are maximised by different configurations. Measured worst relative margin at k<=6 is **+0.343**, no downward trend in k |
| lab-rejection-philosophy | O9 cost estimate + work order for the nine-window damage table | `o9_scoping.py`, `test_o9_scoping.py` (18 pins), `O9-SCOPING.md`, `O9-BRIEF.md` | **LANDED** 2026-08-13 — measures only, lands nothing in `zeta23ext`. Headline: the recorded `c_k` are attained suprema, so O9 as written has zero margin and cannot close under enclosures; §7 absorbs up to a **1.3945x** cap inflation, and at 1.20x inflation + `1/200` window widening the whole object is **389 leaves, depth 16**, about an eighth of `BandCert/Data.lean`. Size was never the obstacle. The widening is capped at **0.00695** by O3's `|u| <= 1` radius — `Kpair(1.01) = 0.77943 < 39/50` — which a first draft of the brief broke; now asserted in code and pinned |
| o9-first-build (Opus 5) | standing the Lean arm up and building it for the first time; the 2-D O9 table | `o9_leaf2d.py`, `test_o9_leaf2d.py`, `O9-2D-STATUS.md`, one import line in `EForm3/O9Check.lean` | **DONE** — pushed as `claude/o9-first-build`. Read `O9-2D-STATUS.md` §0 **before** trusting any leaf-table cell count: `decide +kernel` refutes 7 of the 9 chunks of the 1-D table, and the 2-D table shares the leaf layer that caused it. |
| o9-first-build (Opus 5) | clearing the 13 orphaned O9 modules: deleting the refuted 1-D table, wiring the soundness chain into the default build | `EForm3/O9Data.lean`, `O9Check.lean`, `O9Damage.lean` (deletions), `O9PhiCmp.lean`, new `O9Audit.lean`, `EForm3/Main.lean` | **DONE** — 0 orphans, `O9Audit` builds, 48 theorems all on the three standard axioms. Note `Retention.margin_identity` currently reports **`sorryAx`**, not from a written `sorry` (there are none) but because Mathlib drift broke `RetentionWired.lean:44`; drift can silently un-sorry-free a development and only the axiom audit shows it |
| higher_xi arm | cross-arm transfer proposal (k=2 reduction) | `hunts/higher_xi/CROSS-ARM-TRANSFER.md` | **ANSWERED** in `CROSS-ARM-REPLY.md` - transfer does not survive; their scan window excluded the binding family |
| (other session) | **Road A obligation #8**: the k=1 reduction algebra (`margin_eq`, `energy_sub_card`), submitted to Aristotle as project `281fd3e5-8077-44c4-8497-a51b613092a0`, stated over abstract reals with `retention_gap`/`energy_F` as hypotheses | `lean/ARISTOTLE-RUNS.md` Batch 4 | **SUBMITTED, not landed** - self-declared in their own record; this session is NOT touching it |
| transplant-lemma (Fable) | **Road A obligation #10**: the 196-cell window table + the wiring lemma `ghat(z) = Phi2(-i z)`, and **Road B**: the counting lemma for `k >= 2` | `window_table.py`, `arm_identification.py`, `mean_damage.py`, `kpair_identity.py`, `ROADMAP-OPTIONS.md` (+ tests, + `data_window_table.json`) | **ACTIVE** - O9 generated as a leaf file: **344 cells** in the kernel's own fixed-point arithmetic (`o9_leaf.py`), 0 undecided. The earlier `196` was an Arb-grade estimate and is 43% low. Staged in `zeta23ext/Zeta23Ext/EForm3/O9{Data,Check,Damage}.lean` and **deliberately NOT imported by `Zeta23Ext.lean`** — uncompiled here, so wiring it would risk the other session's build. Road B: shared-R measured, counting lemma done; `k >= 2` still open |
| two-species (Fable) | the two-species restatement of blocker 2; the k=2 equal-depth case; the depth-extended (depth <= 1) damage landscape | `two_species.py`, `k2_closure.py`, `test_two_species.py`, `test_k2_closure.py`, `K2-TWO-SPECIES.md` | **LANDED 2026-08-15** — `D(0,tau) = -Kpair(tau)` splits `Psi` and the k-pair slack becomes a two-species system (identity residual 1.1e-14); **k=2 EQUAL DEPTHS CLOSES at measured grade** over a 6601-cell tau-table, 0 nonpositive in both cap modes (worst +0.0529 signed / +0.0033 unsigned), closed form beyond tau = 114.2, v-convexity for all y in (0,1/2]. Depth-1 corrections: no-damage radius 5.3984 < 28/5, far constant 0.6636 > 637/1000. **k >= 3 and unequal depths remain OPEN** (grid-measured >= 0; obligations named). Quantifier discipline: this is the first multi-pair case, NOT blocker 2 |
| o9-leaf-fix (Fable) | applying run R-2926E4's recorded fix: o9_leaf.py leaves() to kernel arithmetic, N_CELLS_KERNEL 344 -> 476, LEAF CAVEAT rewritten, dependent pins | `o9_leaf.py`, `test_o9_leaf.py`, `test_o9_leaf2d.py` (pin only), `window_table.py` (comment only) | **LANDED 2026-08-15** — every number from `hunts/r_2926e4/probe.py`, reproduced before landing (476 cells, depth 22, 0 undecided, min margin 3.12e8 ulp; baseline recheck 0 of 476 fail). Four pre-existing test failures on main (`test_o9_is_staged_but_not_wired_into_the_package`, three in `test_o9_leaf2d.py`) are unchanged by this and left for their owners |
| lattice-extremality (Opus 5) | is the uniform 2*pi lattice the centre-gas extremum over CONFIGURATIONS? adversarial search over periodic configurations at the correct one-sided convention | `lattice_extremality.py`, `test_lattice_extremality.py`, `K2-TWO-SPECIES.md` (T1 section only) | **DONE** 2026-08-20 — follows the closed form landed in 084f326. G4's withdrawal removed the only recorded counterexample without supplying a proof, so lattice extremality was believed and unestablished. Attacked over periodic configurations (m = 2..6, 300 restarts) and three structured families: **NO COUNTEREXAMPLE FOUND**, every search returned to the uniform lattice, detector power measured at 1e-2 against 1e-6 optimiser resolution. Still unproved; T1 not discharged. Wrote nothing in `zeta23ext/`. |
| lp-route (Opus 5) | turn the lattice-extremality search into an argument: structure-factor / Cohn-Elkies route | `lattice_extremality.py`, `test_lattice_extremality.py`, `LATTICE-EXTREMALITY-ROUTE.md`, `K2-TWO-SPECIES.md` (T1 only) | **DONE** 2026-08-20 — the identity is verified off-lattice, the sign conditions on `kappa_hat` are proved rather than measured, and uniqueness follows from Newton's identities. Closes `rho >= 1/(2*pi)` with the rectification idle. Gaps A (sparse side) and B (the clip, reduced to a majorant problem) remain; T1 NOT discharged. Wrote nothing in `zeta23ext/`. |
| gap-b (Opus 5) | close the rectification gap in the lattice-extremality route with an explicit majorant | `lattice_extremality.py`, `test_lattice_extremality.py`, `LATTICE-EXTREMALITY-ROUTE.md`, `K2-TWO-SPECIES.md` (T1 only) | **DONE** 2026-08-20 — `v = K_1(0)*(sin(x/2)/(x/2))^2` satisfies all four constraints with margin 0.558, so hypothesis H2 is gone and the bound holds for every configuration at `rho >= 1/(2*pi)`. Gap A (sparse side) is the only one left; T1 still NOT discharged. Next: enclose the two inequalities with `rigor.py`. Wrote nothing in `zeta23ext/`. |

## Standing notes for whoever holds `zeta23ext/`

- Artifacts arriving from the prover carry `import RequestProject.*` lines.
  **Rewrite them to the package namespace before committing**;
  `tests/test_zeta23ext_imports.py` catches this, and it caught it once.
- A prover summary's caveats are not the decision procedure; the local
  kernel check is. (That rule came from the other session and is right.)
- Never pipe a gate command whose exit status the next step depends on —
  `pytest ... | tail` masks the failure and the `&&` chain proceeds.
- **A submission's project directory must contain every artifact its brief
  tells the prover to reuse.** Naming a file is not shipping it. This has
  cost two full rebuilds (the band certificate, then eform3).
- **A function and its autocorrelation have different decay.** `c2 = g⋆g`
  is continuous and gives 1/s²; `g` itself jumps at the support edge and
  gives only 1/s. Conflating them has caused two defects in this hunt.

## Practice adopted from the other session (2026-08-13)

Their Batch 4 submission did two things worth copying on every future
prover submission:

- **State the lemma over abstract objects, with the tree's own theorems as
  HYPOTHESES rather than facts to reprove.** Their `margin_eq` takes
  `retention_gap` and `energy_F` as hypotheses, so the file is
  self-contained against Mathlib alone. That sidesteps the empty-directory
  defect (#16) entirely — there is nothing to ship — and the artifact is
  reusable outside this package.
- **Numerically check the STATEMENT before submitting it** (they used 2000
  random instances per lemma). A wrong statement costs a multi-hour round
  trip, and this ledger already records one submission the prover refuted
  for a missing hypothesis.

## Landing note, 2026-08-16

`two-species` and `o9-leaf-fix` were developed on separate branches and
landed together. Both appended a row to the table above at the same
anchor, which conflicted; the resolution kept **both** rows — the claims
are independent (one is the k=2 restatement, the other applies run
R-2926E4's recorded o9_leaf fix) and neither supersedes the other.

Landed onto `main` in this order, each verified before the next:
`hunt/r-3c1cbb-05c755d3` (Mertens I+II, fast-forward), then
`claude/o9-leaf-kernel-476`, then `claude/k2-two-species`.

Pre-existing failures on `main` at the time of landing, verified present
on the untouched trunk and therefore NOT introduced here:
`test_o9_leaf.py::test_o9_is_staged_but_not_wired_into_the_package`,
three tests in `test_o9_leaf2d.py`, `test_huntspec.py::
test_every_mission_huntspec_block_in_the_tree_validates`, and
`test_lab_state.py::test_the_view_renders_every_section`. They belong to
other sessions' work and were left untouched.
