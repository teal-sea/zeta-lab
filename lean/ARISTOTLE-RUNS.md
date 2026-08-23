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

**Measured turnaround.**  Submit-to-collect, per project.  These are upper
bounds: collection was polled, not instantaneous, so the true service time is at
most the figure shown.

| batch | submitted | collected | elapsed |
| --- | --- | --- | --- |
| A, B, C, D | 01:19 | 01:38 | <= 19 min |
| E1, E2 | 01:19 | 01:50 | <= 31 min |
| F, H, J | 02:02 | 02:18 | <= 16 min |
| K | 02:14 | 02:33 | <= 19 min |
| M | 02:14 | 02:43 | <= 29 min |
| H2 | 02:25 | 02:43 | <= 18 min |

All twelve landed inside about 1h25m of wall clock across three overlapping
batches.  This is the first entry in this ledger with wall-clock actually
observed rather than estimated, and it revises the standing "hours" figure down
by roughly an order of magnitude: the Grasshopper case study's ~8 h is not what
these bounded lemmas cost.

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

## Batch 8 — Pub 1 analytic obligations (submitted 2026-08-16, later same day)

Seven further bounded lemmas aimed at removing the four analytic assumptions
recorded in `lean/ZetaLean/Pub1/OBLIGATIONS.md`.  Same rules as batches 5-7, and
the prompts now carry the porting notes distilled from those batches (explicit
antiderivatives instead of `norm_num` on interval integrals; `congr_deriv`
instead of `convert`; no `simpa` on lambdas).  That guidance paid: all seven
ported unchanged, against seven of twelve in the previous round.

| tag | project | statement | status |
| --- | --- | --- | --- |
| N | `ef6f7ba0-bb8f-4a90-a5b5-98b7457c6e09` | second derivative of a convolution against a kernel with a `\|x\|` kink, via splitting at `t = s`; the two moving endpoints produce `2 f'(0) v(s)` | collected — accepted, ported unchanged |
| O | `8a0369d6-ee00-4962-bbf4-3e7625d9b9ff` | `∫_I \|s-t\|^m t^n dt` in closed form | collected — accepted, ported unchanged |
| R | `bf7c9cd9-68b7-49b1-8e87-ae61ae9a5183` | the two resolvent estimates `‖z‖ ≤ (9/5)‖g‖` in `L^∞` and `L²` | collected — accepted, ported unchanged |
| S | `f6285416-5ef5-471b-8aeb-8b906917dbe2` | the half-line form factor is entire; `f 0 = 0`, `f'(0) = 1`, `f'' = q` | collected — accepted, ported unchanged |
| T | `34c103b7-ec61-4128-bd19-771f462dcc69` | uniform `L¹` bound on `φ_L''` for `L ≥ 8` | collected — accepted, ported unchanged |
| U | `d0e0056a-4800-4385-8f1d-7e82197de3ea` | the same for `(φ_L²)''` | submitted |

**What N bought, and why it matters.** The informal chain says
`F₁'' = 2δ₀ + q`, and Mathlib has no convenient distributional-derivative API for
this kernel. Rather than build one, N differentiates the split integral twice and
recovers the delta mass as the sum of two moving-endpoint boundary terms. The
coefficient `2` is then a theorem, not a convention: it is `2 f'(0)` with
`f'(0) = 1` proved separately in S. This is the cheaper route by a wide margin
and it is the one the operator prompt suggested.

**Measured turnaround** (submit to collect, upper bounds; collection was polled):
N, O ~55 min and ~20 min; R ~35 min; S ~65 min; T ~75 min; U ~85 min. The two
series-analysis targets (S) and the product-rule/`L¹` target (T) were the slow
ones, consistent with batch 5-7 where the series work also ran longest.

Prompts are pinned in the private operating repo at
`fulcrum/records/aristotle-prompts/pub1/`.

## Batch 9 — Pub 1 analytic closure, second pass (submitted 2026-08-16)

Six lemmas aimed at the two remaining critical paths.  Prompts carried the
porting notes from batches 5-8.

| tag | project | statement | status |
| --- | --- | --- | --- |
| J2 | `099e164b-5b45-4d06-8748-0dfb3b95f214` | taper `C²` and `√w` `C²` with bounds, from `C²` on the OPEN interval only | collected — accepted, ported unchanged |
| TU2 | `b9af4feb-04f1-4a99-8af6-ce88319c664d` | the two uniform `L¹` bounds under the same weakened hypothesis | collected — accepted after 5 local repairs |
| V | `5bc0bd6f-ab37-4140-a44a-581d4dffa7cc` | geometric tails `∑_{k≥20} a_k`, `∑_{k≥20} d_k`, and `Summable dCoef` | collected — accepted, ported unchanged |
| W | `a4602e1b-0eef-4d1d-9f74-1435d2c9de00` | pointwise derivatives ⟹ `ContDiffOn ℝ 2` on an open set; boundedness on the closed one | collected — accepted, ported unchanged |

**Why J2 and TU2 exist at all.**  Batch 8's `J`, `T`, `U` asked for `C²` on a
*neighbourhood* of the closed interval.  That hypothesis is unsatisfiable: `w''`
jumps by `2w(±1/2) ≥ 2/5` at the endpoints, because the delta mass contributes
inside `I` and not outside.  The theorems were true and uninstantiable.  Restated
over the open interval with bounded derivatives, they instantiate.  The lesson
for prompt-writing is to ask for the weakest hypothesis the downstream argument
actually consumes, not the most convenient one to state.

**Turnaround** (submit to collect, upper bounds; polled): V ~40 min, W ~40 min,
TU2 ~95 min, J2 ~2 h.  Four of four accepted; one needed repair.

## Batch 10 — Pub 1 assembly closure (submitted 2026-08-16)

| tag | project | statement | status |
| --- | --- | --- | --- |
| Y | `d17ee0f9-cd6a-4aad-a6d4-ed1519c86640` | the `L^∞` resolvent estimate by a maximum principle | collected — accepted, ported unchanged |

One project, and it is the one that mattered: batch 8's `R` form of the same
estimate asked for a *minimal* bound `Bz`, which would have needed the sup built
as an `sInf`.  Restated as "`|z|` attains its max on the compact interval, and at
that point the equation gives the bound directly", it is a short proof and drops
straight in.  Same lesson as `J2`/`TU2`: ask for the form the downstream argument
can actually feed.

This batch completed the development.  `pub1_strong_closure` and
`pub1_strong_closure_reciprocal` are now unconditional.

Prompts are pinned in the private operating repo at
`fulcrum/records/aristotle-prompts/pub1/`.

## Batch 11 (not opened): S2, the stability rank-trace lemma (2026-08-23)

**No project was created and no API call was made.** The entry exists because the
ledger's job is to let a later session find out what happened, and "nothing was
sent" is a thing that happened.

The formal-native probe of `hunts/ainta_seven_point/ARISTOTLE-PROBE.md` was
authorised to send three bounded variants of Ainta's S2 (the scalar lemma alone,
the full theorem, the theorem with the scalar lemma as a hypothesis) under the
handoff's rule that *only what remains* goes to the service. After the local pass
nothing remained: the full theorem builds with zero `sorry`s and standard axioms
only, in `hunts/frontier_math/zeta23ext/Zeta23Ext/StableRankTrace.lean`, and the
scalar lemma turned out to be an existing upstream theorem
(`Zeta23.ZeroSide.RankTraceMult.sq_sub_ge_gc`).

| tag | project | statement | status |
| --- | --- | --- | --- |
| S2-scalar | none | `(p - n)^2 + 4n >= 2p - 1 + Psi p` for `p, n >= 0` | not sent: already upstream as `sq_sub_ge_gc` |
| S2-full | none | `stable_rank_trace` (trust map form) | not sent: proved locally before a residual existed |
| S2-hyp | none | the same with the scalar lemma as a hypothesis | not sent: weaker variant of a closed target |

**A calibration project the operator may want, and the reason it was not opened
here.** The interesting unasked question is whether the service searches the
ambient library rather than reproving from scratch. Hand it
`stable_rank_trace_sharp` cold, with `Zeta23` importable and with no mention of
`rank_trace_mult`, `gc` or `sum_eigenvalues_comm` in the prompt, and measure
whether it finds the four-line corollary route or reinvents the fifty-line
skeleton. Ground truth is now known exactly, which is the only reason the
measurement would be worth anything. It is a measurement about the tool, so it is
an allocation call and not this pursuit's to make.

## Batch 12 (not opened): the Ainta bridge, S6-S9 and S11-S16 (2026-08-23)

**No project was created and no API call was made by any of the five agents.**
Five agents worked the bridge of `hunts/ainta_seven_point/TRUST-MAP.md` in
parallel from the branch `bridge/skeleton`, each under a cap of 3 submissions,
each keeping its own ledger under `hunts/ainta_seven_point/bridge/`. The five
ledgers are merged here; the per-group files stay in place as the provenance
record. Total used: **0 of 15.** Every obligation closed by direct proof under
the pinned toolchain (`leanprover/lean4:v4.33.0-rc2`, mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`, `Zeta23` at
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`) before a residual existed, and the
standing rule (`ARISTOTLE-PROBE.md` section 7, Batch 11 above) is that a closed
target is not sent: that buys a comparison about the tool, which is an
allocation call for the owner.

| group | branch | ledger | obligations | used | status |
| --- | --- | --- | --- | --- | --- |
| skeleton | `bridge/skeleton` | `hunts/ainta_seven_point/bridge/ARISTOTLE-skeleton.md` | the whole bridge typechecks end to end with 11 named `sorry` lemmas; S7 and S16 proved outright | 0 of 3 | done |
| finite | `bridge/finite` | `hunts/ainta_seven_point/bridge/ARISTOTLE-finite.md` | S6 `regroup_posIndex`, S7 `count_defect`, S11 `block_energy`, S12 `block_defect`, S13 `block_bound`, S15 `offset_average` and `span_retained_le` | 0 of 3 | all PROVED |
| pinching | `bridge/pinching` | `hunts/ainta_seven_point/bridge/ARISTOTLE-pinching.md` | S14 `pinching_partition`, `pinching_submatrix` | 0 of 3 | both PROVED |
| S8 | `bridge/S8` | `hunts/ainta_seven_point/bridge/ARISTOTLE-S8.md` | S8 `tail_passage` | 0 of 3 | PROVED |
| S9 | `bridge/S9` | `hunts/ainta_seven_point/bridge/ARISTOTLE-S9.md` | S9 `kernel_limit`, `deleted_strips` | 0 of 3 | both PROVED |

Integration (branch `bridge/integrate`, same day): the five branches merge
cleanly (disjoint files by construction), `lake build Zeta23Ext.Bridge.Main`
from deleted Bridge oleans completes in 44 s wall (8854 jobs), zero `sorry`
warnings, and every `#print axioms` line in the tree, `seven_point_bound` and
`seven_point_bound_paper` included, reports `[propext, Classical.choice,
Quot.sound]`. The record of what was proved and what remains a hypothesis is
`hunts/ainta_seven_point/BRIDGE.md`.

What was not sent, and why it would still be a measurement rather than a
result: the same calibration project Batch 11 describes, now with sixteen
ground-truth proofs instead of one. The candidates with the most to teach are
S9 `kernel_limit` (808 lines of helper, the proof that the trust map graded
LARGE and that turned out to reuse `[L23]`'s `PrimeSide.rho` and the sharp
window comparison) and S14 `pinching_partition` (the one library fact the map
called MISSING, proved in 321 lines from the row-stochastic mixture of the
spectrum of a principal submatrix). Not opened here; the owner's call.
