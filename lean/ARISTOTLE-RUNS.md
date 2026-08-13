# Aristotle runs — submissions, ids, and collection state

The proof-agent adapter's durable ledger (`lean/proof_adapter.py`; contract
in `docs/26` §4). Every submission is recorded here with its project id so
any later session can collect. The rule stands: whatever comes back is
input — it counts only after the static refusal scan and a zero-`sorry`
`lake build` on this repository's toolchain. Aristotle's own verification
claims are never copied into this file.

Collect with:

```bash
source ~/.zshrc   # ARISTOTLE_API_KEY
.venv-tools/bin/python -c "
import sys; sys.path.insert(0, '.')
from lean.proof_adapter import collect_from_aristotle
print(collect_from_aristotle('<project_id>', destination='/tmp/aristotle'))"
# then, for each returned .lean file:
.venv/bin/python lean/proof_adapter.py check <file.lean> <ModuleName>
```

## Batch 1 — Sturm-track calibration (submitted 2026-08-12T00:08-0500)

Four bounded lemmas in Mathlib vocabulary, graded easy → hard, chosen from
the Mathlib upstream track (`ROADMAP.md`, "The upstream track": Sturm is
the contribution target). Purpose: calibrate what Aristotle-hours buy at
each difficulty grade before spending them on the real chain. Prompts
pinned in the table; every prompt required zero `sorry`/`admit`/`axiom`/
`native_decide` and forbade weakening the statement.

| id | project | statement (target theorem) | status |
| --- | --- | --- | --- |
| sturm-A-poly-ivt | `ad115f79-69be-4cfa-90da-594f91709dd7` | `p.eval a * p.eval b < 0 → ∃ x ∈ (a,b), p.IsRoot x` (polynomial IVT) | collected — accepted |
| sturm-B-eval-mul-deriv-pos | `631981c2-0e06-44e6-bce4-0a2f63851e9b` | right of any root of `p ≠ 0`: `0 < p.eval y * p'.eval y` on some `(x, x+ε)` | collected — accepted |
| sturm-C-coprime-simple-roots | `bc1f63ca-f6a6-4147-b3c6-2ff3594fe8d0` | `IsCoprime p p' →` roots of `p` are not roots of `p'` | collected — accepted |
| sturm-D-odd-multiplicity-sign-change | `f8281972-1c81-440f-8b35-8f6c0197b504` | odd `rootMultiplicity x` ⟺-direction: eval changes sign across `x` | collected — accepted |

Expected turnaround: hours (the Grasshopper case study measured ~8 for a
hard problem; A and C should be far faster). Update the status column at
collection: `collected — accepted`, `collected — refused (<reason>)`, or
`no output`. A refused artifact's reason belongs here verbatim; do not
resubmit the same statement without changing something and saying what.

Note: a fifth project (`0701719a-…`, description "lean", created
2026-08-12T04:55Z) predates this ledger — it is the operator's own
dashboard test, not adapter-submitted, and is not tracked here.

## Batch 2 — the zeta23ext port (submitted 2026-08-12T15:01-0500)

Purpose: make `zeta23ext` assemble. The package's modules were proved
service-side against an older Mathlib and had never been built against the
pin they must integrate under. Measured here first, module by module,
against the already-compiled Mathlib `v4.33.0-rc2` in `lean/` (drop the
module in as a scratch target, build, delete) rather than buying a
round-trip to find out. That measurement is what the prompts carry.

**Result of the local survey, which is the reason this batch is three
projects and not four:**

| module | verdict under `v4.33.0-rc2` |
| --- | --- |
| `Composition.lean` | **builds clean** — zero `sorry`, axioms `[propext, Classical.choice, Quot.sound]`. No port needed, nothing submitted. |
| `GridIncidence.lean` | 2 failures (lines 109, 290) |
| `FloorCert.lean` | 1 failure (line 82) |
| `BandCert/Leaves.lean` | 1 failure (line 144); blocks the 6 modules downstream of it (the imports are a single chain Iv → Leaves → Phi → Check → Cap → Data → Verify → Main) |

| id | project | task | status |
| --- | --- | --- | --- |
| port-A-gridincidence | `bbd1c2a0-2eea-4507-b061-15594381a402` | `rw [MeasureTheory.L2.inner_def]` (109) and `rw [Complex.real_smul]` (290) both fail with "did not find an occurrence of the pattern"; `simp only` makes no progress either. Both lemmas exist unchanged, so the drift is in the goal shape upstream of each site. | submitted |
| port-B-floorcert | `f4d78035-5d82-4375-bf39-50b127268b74` | line 82 `ring_nf` made no progress on the goal | submitted |
| port-C-bandcert-leaves | `d0703744-f625-4a39-8234-a9f44465feda` | line 144 type mismatch after simplification; prompt also carries the import-path correction below | submitted |

Prompts pinned at `~/.claude/jobs/8633dae1/tmp/prompts/` for this session;
each required zero `sorry`/`admit`/`axiom`/`native_decide` and forbade
weakening or restating any theorem, proof bodies only.

**A defect found by the survey, independent of the port.** All eight
`BandCert/` modules as committed carry `import RequestProject.X` — the
proving service's own project-local module namespace — while
`Zeta23Ext.lean` imports `Zeta23Ext.BandCert.Main`. The package therefore
could not have assembled at any pin: the first `lake build` dies on an
unknown module, before any mathematics is reached. Nothing about the proofs
is wrong; the artifacts were landed without their import paths rewritten,
and no local assembly had ever been attempted to notice. The rewrite is
mechanical (`RequestProject.` → `Zeta23Ext.BandCert.`) and is folded into
port-C's prompt rather than done blind here, so one artifact carries both.

### Batch 2 collection (2026-08-12, same day)

All three returned within hours. **Two accepted, one refused and repaired
locally**; the split is the reason the local kernel check exists.

| id | outcome |
| --- | --- |
| port-A-gridincidence | **collected — accepted.** Builds under `v4.33.0-rc2`; all 18 declarations report `[propext, Classical.choice, Quot.sound]`; declaration lines byte-identical to the original, changes confined to proof bodies. It set up a real v4.33.0-rc2 environment, reproduced both failures, and found the **root cause both sites share**: `convert … using 1` on a `HasSum` goal now leaves an `AddCommMonoid` instance-equality goal first, so the following `rw` has nothing to act on. Replaced with explicit `have key : … ; rw [key]; exact h`. |
| port-B-floorcert | **collected — refused, then repaired here.** Its own summary carried the honest caveat that it could only build against v4.28.0. The local check under `v4.33.0-rc2` failed at a site it never saw: `ring` (reporting as `ring_nf`) after `convert h using 1` in `geom_hasSum` — *the same root cause port-A had already isolated*. It had fixed a different `mul_pow`/`ring_nf` site instead. Repaired here with `simpa [mul_comm] using h`, isolated in a 6-line scratch file first to iterate in seconds. Now builds; `theoremA`, `B1`–`B4`, `corollary` all report the three standard axioms. |
| port-C-bandcert-leaves | **collected — accepted.** Import path corrected as asked and the line-144 mismatch replaced with a normal-form-independent `rw`/`ring` argument. |

**`Phi.lean` was repaired locally, not submitted.** With `Leaves` ported, the
chain's next module failed at 13 sites, all one shape: projection-through-
definition (`(a.add b).1` vs `a.1.add b.1`) that the newer `simp` no longer
unfolds. A uniform fix — naming the `CIv` operation in each `simpa` set, plus
three `ofR`/`AIV` sites — cleared all 13. Cheaper to do than to describe in a
prompt.

**The whole `BandCert` chain now builds under `v4.33.0-rc2`**: 8 modules,
8704 jobs, `Verify` alone taking 1513 s. Zero `sorryAx` anywhere in the log;
`cap_le_slack` and `f_nonpos_off_bands` report only the three standard axioms.

**What this cost, and the lesson.** Two of three service artifacts were
correct as delivered; the third was confidently wrong in a way its own
verification could not have detected, because its environment could not build
the target. The refusal scan plus a local kernel check on this machine is what
separated them, exactly as `proof_adapter.py` was built to do. Aristotle's
self-report was *honest about its limitation* and still shipped a
non-building artifact — that is the failure mode to keep expecting.

## Batch 3 — Bridge and the last assembly blocker (submitted 2026-08-12, sprint 3)

| id | project | task | status |
| --- | --- | --- | --- |
| bridge-A-algebra | `d54aea65-6679-46f9-9c7d-b64f154cf9a1` | the three Bridge identities (Hermitian expansion, Gram identity, and `D = R + 2 tr(PQ) + ‖Q‖²_F`), self-contained over Mathlib with upstream's definitions carried verbatim | **collected — accepted** |
| port-D-pairenergy | `f7dc3271-da10-4b1d-97cf-8fdb4a77d96a` | `PairEnergy.lean`, the last assembly blocker: `Matrix.posSemidef_iff_eq_conjTranspose_mul_self` does not exist under this Mathlib (lines 87, 230), plus a brittle `<;>` simp chain at 314 | submitted |

**bridge-A accepted, and note what its acceptance did NOT rest on.** Its summary
carried the same caveat that produced a refusal in batch 2 — it could only build
against v4.28.0, not the target pin. The local check under `v4.33.0-rc2` passed
this time: all three theorems build, each reporting only
`[propext, Classical.choice, Quot.sound]`. Same caveat, opposite outcome, which
is exactly why the caveat is not the decision procedure and the local kernel
check is.

One structural change it made and flagged: the definition block is wrapped in a
`noncomputable section`, because `Real.sqrt` has no executable code and `Wmat`
would otherwise be rejected by the compiler IR check. Definition texts are
unchanged; no statement weakened.

**What is still owed on Bridge.** It is landed as `Zeta23Ext/Bridge.lean`
carrying its own copies of `rtrace`, `frobSq`, `Wmat`, `Pmat`, `xsq` — that is
what made it provable without the dependency. The point of the module is to sit
on *upstream's* objects, so replacing those local copies with `import Zeta23`
and re-checking is an outstanding step, not a finished one. `BRIDGE-SPEC.md` §1
lists each definition against its upstream source line for exactly that swap.

## Batch 4 — the k=1 retention reduction (submitted 2026-08-12/13)

The 2026-08-12 closure (`f39dc49`, corrected to k=1 only by `7df6ed8`,
defect #19) states its reduction is "algebra on two sorry-free theorems
already in the tree". This submits exactly that algebra, so the step moves
from hardened grade to kernel-checked.

| id | project | task | status |
| --- | --- | --- | --- |
| retention-algebra | `281fd3e5-8077-44c4-8497-a51b613092a0` | `margin_eq` (the exact retention margin from the gap identity) and `energy_sub_card` (`E[F] − n` equals twice the strictly-upper-triangular repulsion sum, from the energy identity plus the diagonal normalisation) | submitted |

**Stated over abstract reals on purpose.** Aristotle does not have this
package's `EForm3` modules, and the reduction needs none of them: both
`retention_gap` and `energy_F` enter as *hypotheses* of the submitted lemmas
rather than as facts to be reproved. That makes the file self-contained
against Mathlib alone, and it makes the artifact reusable — the analysis is
already sorry-free in the tree, and only the algebra was ever missing.

Composing the two gives the closure's own formula,

    margin = (4/A²)·[ Shq(y)/2 − Σ_j D_j + (1/400)·Σ_{j<k} φ_r(x_j−x_k)² ]

which is the statement that the repulsion term is not optional: the weaker
route discards it by using `n ≤ E[F]` in place of the identity, and that route's
hypothesis is arithmetically false from n = 8.

**Both statements were checked numerically before submission** (2000 random
instances each, `margin_eq` and `energy_sub_card` both exact), because a wrong
statement costs a multi-hour round trip and the ledger already records one
submission refuted by the prover for a missing hypothesis.
