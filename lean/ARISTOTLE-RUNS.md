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
| sturm-A-poly-ivt | `ad115f79-69be-4cfa-90da-594f91709dd7` | `p.eval a * p.eval b < 0 → ∃ x ∈ (a,b), p.IsRoot x` (polynomial IVT) | submitted |
| sturm-B-eval-mul-deriv-pos | `631981c2-0e06-44e6-bce4-0a2f63851e9b` | right of any root of `p ≠ 0`: `0 < p.eval y * p'.eval y` on some `(x, x+ε)` | submitted |
| sturm-C-coprime-simple-roots | `bc1f63ca-f6a6-4147-b3c6-2ff3594fe8d0` | `IsCoprime p p' →` roots of `p` are not roots of `p'` | submitted |
| sturm-D-odd-multiplicity-sign-change | `f8281972-1c81-440f-8b35-8f6c0197b504` | odd `rootMultiplicity x` ⟺-direction: eval changes sign across `x` | submitted |

Expected turnaround: hours (the Grasshopper case study measured ~8 for a
hard problem; A and C should be far faster). Update the status column at
collection: `collected — accepted`, `collected — refused (<reason>)`, or
`no output`. A refused artifact's reason belongs here verbatim; do not
resubmit the same statement without changing something and saying what.

Note: a fifth project (`0701719a-…`, description "lean", created
2026-08-12T04:55Z) predates this ledger — it is the operator's own
dashboard test, not adapter-submitted, and is not tracked here.
