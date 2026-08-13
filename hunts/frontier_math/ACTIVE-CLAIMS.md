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
| higher_xi arm | cross-arm transfer proposal (k=2 reduction) | `hunts/higher_xi/CROSS-ARM-TRANSFER.md` | **ANSWERED** in `CROSS-ARM-REPLY.md` - transfer does not survive; their scan window excluded the binding family |

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
