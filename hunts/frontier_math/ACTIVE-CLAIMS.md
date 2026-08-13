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
| transplant-lemma (Fable) | the negative-margin question: does the multi-pair verdict survive at theta = 995/1000 for large clusters at the resonance spacing | `negative_margin_probe.py`, `test_negative_margin_probe.py` | **ACTIVE** — refinement running |
| transplant-lemma (Fable) | adversarial extremum search over configurations | `adversary_evolution.py`, `test_adversary_evolution.py` | **PAUSED** — module complete, agent lost to a container restart, not yet re-run |
| transplant-lemma (Fable) | prover submissions on the E-form family | `zeta23ext/Zeta23Ext/EForm2/`, `TruncEst/` | **LANDED** |
| (other session) | the extension package's assembly, module ports to the upstream pin, `Bridge.lean` | `zeta23ext/` build files, `BRIDGE-SPEC.md`, `PIPELINE.md` | inferred from commits, not self-declared |
| transplant-lemma (Fable) | the near-coincident closure campaign: four parallel angles on the last quantifier | `repulsion_trade.py`, `near_coincident.py`, `cluster_sdp.py`, `exact_gap_attack.py`, `verify_lemma_c_independent.py`, `RETENTION-PROBLEM.md` (+ tests) | **SINGLE-PAIR (k=1) RETENTION CLOSED at hardened grade**, no separation hypothesis — four routes agree, exact-rational certificate, coordinator reproduction. **Multi-pair k>=2 (blocker 2 proper) still OPEN**: short by 1.99x on the budget side. Ledger 2026-08-13; coordinator defect #19 was labelling the first as the second |
| higher_xi arm | cross-arm transfer proposal (k=2 reduction) | `hunts/higher_xi/CROSS-ARM-TRANSFER.md` | **ANSWERED** in `CROSS-ARM-REPLY.md` - transfer does not survive; their scan window excluded the binding family |
| (other session) | **Road A obligation #8**: the k=1 reduction algebra (`margin_eq`, `energy_sub_card`), submitted to Aristotle as project `281fd3e5-8077-44c4-8497-a51b613092a0`, stated over abstract reals with `retention_gap`/`energy_F` as hypotheses | `lean/ARISTOTLE-RUNS.md` Batch 4 | **SUBMITTED, not landed** - self-declared in their own record; this session is NOT touching it |
| transplant-lemma (Fable) | **Road A obligation #10**: the 196-cell window table + the wiring lemma `ghat(z) = Phi2(-i z)`, and **Road B**: the counting lemma for `k >= 2` | `window_table.py`, `arm_identification.py`, `mean_damage.py`, `kpair_identity.py`, `ROADMAP-OPTIONS.md` (+ tests, + `data_window_table.json`) | **ACTIVE** - table sized at 196 cells (inside BandCert's 62-248), both roads' first task landed; the counting lemma is the only thing left before `k >= 2` |

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
