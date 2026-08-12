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
| `BandCert/Leaves.lean` | 1 failure (line 144); blocks the 4 modules downstream of it |

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
