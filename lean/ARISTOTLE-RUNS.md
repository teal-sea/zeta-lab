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

### Batch 4 collection

**collected — accepted.** Both theorems build here under `v4.33.0-rc2`,
statements byte-identical to the submission, each reporting only
`[propext, Classical.choice, Quot.sound]`. Static scan clean. Landed as
`Zeta23Ext/RetentionAlgebra.lean`.

`energy_sub_card` rests on one `private` helper, `sum_sq_split`, which splits
the double sum by trichotomy into strictly-upper, strictly-lower and diagonal
parts and identifies the two off-diagonal halves through the symmetry
hypothesis; the diagonal then collapses under the normalisation.

Its summary carried the same "built against v4.28.0, not the target pin"
caveat that preceded a refusal in batch 2 and a clean pass in batch 3. Third
occurrence, and the caveat remains uninformative in both directions — which is
the argument for the local kernel check being the gate rather than the
service's own report.

**What this does and does not move.** The k=1 retention reduction's *algebra*
is now kernel-checked. The analysis it composes (`retention_gap`, `energy_F`)
was already sorry-free in the tree, so the k=1 layer's chain is closed end to
end at kernel grade. What is untouched: the multi-pair statement of blocker 2
(k blocks at different depths and centres) is still open, per the correction in
`7df6ed8` (defect #19). The lemmas here are stated over abstract reals, so
wiring them to `EForm3`'s objects — discharging the two hypotheses from the
tree's own theorems — is a remaining step, not a finished one.

## Batch 5 — the EForm3 port (submitted 2026-08-13)

Found by trying to make batch 4 load-bearing. `RetentionWired.lean` discharges
`RetentionAlgebra`'s four abstract hypotheses from the tree's own
`retention_gap`, `energy_F`, `Qre_zero_even` and `Qre_zero_zero`. It cannot be
checked yet, because **`EForm3` itself does not build at the target pin** —
the fourth module set in this package landed without ever being built there.

| id | project | task | status |
| --- | --- | --- | --- |
| eform3-A-taylor | `24b0a7ad-f71f-4b7e-b4be-c54178785c6f` | `Taylor.lean`: type mismatches after simplification at 42, 57, 85, 104; `ring_nf` no progress at 63, 109 | submitted |
| eform3-B-closedform | `e3753571-74c1-4efd-abb1-034021025dc2` | `ClosedForm.lean`: `field_simp` no progress at 74, 104 | submitted |

Both prompts carry the two failure classes this package's port has already
taught us — `convert … using 1` leaving an instance-equality goal first, and
projection-through-definition no longer unfolded by `simp` — since a prompt
that names the drift gets a normal-form-independent repair rather than another
brittle one.

**The pattern is now worth stating as a pattern.** Four separate module sets
(`BandCert/`, `EForm/`, `PairEnergy`, `EForm3/`) have been landed into this
package without a build at the pin they must integrate under. Each time the
proofs were fine and the port was a handful of tactic sites. The cost is not
the repair, it is that nothing downstream can be verified until it is done:
`RetentionWired` is written and unverifiable purely because of this.
`assemble.sh` exists to make that check one command; it only helps if it runs
before landing rather than after.

### Batch 5 collection, and batch 6

| id | outcome |
| --- | --- |
| eform3-A-taylor | **collected — accepted.** Builds under `v4.33.0-rc2`, declarations byte-identical, scan clean. |
| eform3-B-closedform | **collected — accepted.** Same, and it repaired two further sites carrying the identical fragile pattern that had not been reported as failing. |
| eform3-C-numerics | `c272510e-da2d-427c-8e57-433cb95bc866` — the last blocker in the chain (lines 95, 138, 143). Submitted. |

**Both repairs removed the dependence rather than patching the symptom**, which
is why each fixed several reported sites at once. `Taylor` replaced every
`simpa`-built `HasDerivAt` and every `convert … using 1; ring` with an
explicitly ascribed term corrected by `HasDerivAt.congr_deriv`, so the side
goals are plain real identities. `ClosedForm` replaced
`convert h using 1; field_simp; ring` with
`refine h.congr_deriv ?_; rw [div_eq_iff hne]; ring`, using the nonvanishing
hypothesis explicitly instead of letting `field_simp` pick a normal form.
Batch 6's prompt carries both patterns verbatim, since a prompt that names the
drift gets a durable repair rather than another brittle one.

**Fixing a layer reveals the next.** Taylor and ClosedForm landing exposed
`Numerics`, which the earlier survey could not see because the build stopped
above it. That is the expected shape of a port and not a new defect — but it
does mean "the survey found N sites" is a lower bound until the chain builds
end to end.

## Batches 5-7 — Pub 1 source-admissible strong closure (submitted 2026-08-16)

Twelve bounded lemmas supporting the Lean formalization of
`hunts/wide_search/RESULTS-xiprime-admissible-closure.md` (PR #45).  Every
prompt fixed the target toolchain (`v4.33.0-rc2`, Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`), required the statement
character-for-character, and forbade `sorry`/`admit`/`axiom`/`native_decide`.
Landed files are `lean/ZetaLean/Pub1/Aristotle/<tag>.lean`, each wrapped in a
namespace `Aristotle<tag>` so they can coexist.

Every artifact was collected, statically scanned, and built here before use.
The service's own verification claim is not recorded and was not relied on.

| tag | project | statement | status |
| --- | --- | --- | --- |
| A | `891558c0-e08b-4dc1-82fe-6ccfb293fec2` | `ContDiff ℝ 3 eta` for the degree-7 smoothstep glued by `0`/`1` | collected — accepted, ported unchanged |
| B | `a3324dee-ca6d-4156-a6f3-ec4072112ce9` | Schur test for the quadratic form of a nonnegative symmetric continuous kernel on `I` | collected — accepted, ported unchanged |
| C | `bc93ed8f-703c-4d9b-b2a5-a9fd5ca34e88` | solvability of `w + Tw = 1` by Banach fixed point on `ℝ →ᵇ ℝ` | collected — accepted after 1 local repair (uncurry continuity) |
| D | `8199d0e7-3da2-4778-ab3a-c9f550907300` | `∫₀¹ η'² = 700/429`, `∫₀¹\|η''\| = 35/8` | collected — accepted after local repair (both endings rewritten with explicit antiderivatives) |
| E1 | `3a469262-610b-4d77-aefe-bcacf9ad72fd` | `F₁` summable/nonneg/even on `[-1,1]`, `∫₀¹F₁ ≤ 4/9` | collected — accepted after 1 local repair |
| E2 | `eb98c4b7-e2c1-49ad-9e46-ad0c36ca1833` | `F₁` continuous; row bound `∫_I F₁(s-t)dt ≤ 4/9` for `\|s\| ≤ 1/2` | collected — accepted after 1 local repair |
| F | `26c4943d-f20c-4b68-b956-234fda2bd876` | `F₁` summable and nonnegative globally (the series is entire) | collected — accepted, ported unchanged |
| H | `a4a867ab-2525-43e7-8f30-0382cf588620` | `1/5 ≤ w ≤ 1` and evenness, difference-kernel form | collected — accepted, ported unchanged; superseded by H2 |
| H2 | `0de51d62-89b9-4df7-a632-d616e9c496ad` | same, for a two-variable kernel, plus uniqueness | collected — accepted, ported unchanged |
| J | `24421b6b-73dd-438b-ac64-331bb7270687` | `η(L/2-\|u\|) ∈ C²`; the taper `√(w(u/L))·η(L/2-\|u\|) ∈ C²` | collected — accepted after 1 local repair |
| K | `0171902b-9d64-4dd6-a3da-c4ee01dedc84` | form symmetry, energy Cauchy-Schwarz, and `⟨Aw,v⟩ = ⟨1,v⟩` | collected — accepted, ported unchanged |
| M | `05973d17-6d83-4795-8631-a7cbecb9d40f` | mass and form bounds turning `L²` convergence into quotient convergence | collected — accepted, ported unchanged |

**Measured turnaround:** batch 5 (A, B, C, D) returned in roughly 35 minutes;
E1 and E2, the two series-analysis targets, took about an hour.  This is the
first batch with wall-clock actually observed rather than estimated.

**The recurring port defect, worth naming.** Five of the twelve failed here for
the same two reasons, both version drift rather than mathematics:
`norm_num` with the interval-integral simp set no longer evaluates a polynomial
definite integral (fixed by an explicit antiderivative plus
`intervalIntegral.integral_eq_sub_of_hasDerivAt`), and `simpa` normalizes a
lambda into `Pi.mul`/`Function.comp` form that then fails to unify. Prompts for
future batches should ask for `HasDerivAt.congr_deriv` and explicit `.mpr`
applications in preference to `simpa`/`convert`.

Prompts are pinned in the private operating repo at
`fulcrum/records/aristotle-prompts/pub1/` (the prompt corpus is the private side
of the boundary; the statements themselves are public, in the .lean files).
