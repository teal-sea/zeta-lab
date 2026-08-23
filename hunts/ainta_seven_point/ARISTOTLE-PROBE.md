# ARISTOTLE-PROBE: S2, the stability rank–trace lemma

Formal-native research probe, run 2026-08-23. One obligation, not a formalization of a
paper. The success criterion set for it was *did formal feedback change the mathematical
understanding*, with a returned proof counted as a bonus rather than the criterion.

## Verdict, in one line

The theorem is proved and builds with zero `sorry`s on this repository's pinned
toolchain, and **no Aristotle project was opened**, because after the local pass there
was no residual to send. Two findings came out, and neither is the proof.

**The first, and the one the probe exists for:**

> **S2, as stated in the trust map's vocabulary, is an instance of a theorem that is
> already kernel-checked inside `anthropics/zeta-23-lean` itself**:
> `Zeta23.ZeroSide.RankTraceMult.rank_trace_mult`, at `c = 2`, evaluated at the
> eigenbasis presentation of `P = V Vᴴ`. Ainta's `Psi` is that development's own `gc 2`
> shifted by one.

That is a correction to §4 of `TRUST-MAP.md`, which named S2 "the smallest step that is
both **new to Ainta** and load-bearing", and pointed the proof at `RankTrace.lean:52-56`.
The "load-bearing" half stands. The "new" half does not. And the map is not guilty of a
missed search: it had already found `RankTraceMult.lean` and filed its defect term as
*"a different one"*. §11 is about why that reading was wrong, and it is a more useful
finding than a missed grep would have been.

**The second, found by doing what the handoff said to do first:** the vendored package
`hunts/frontier_math/zeta23ext` **does not assemble on `main`**. Three modules fail, none
of them mine, one of them dragging a `sorryAx` into a declaration. §1b.

## 1. What was proved

File: `hunts/frontier_math/zeta23ext/Zeta23Ext/StableRankTrace.lean` (new; no upstream
file was edited). Namespace `Zeta23Ext.StableRankTrace`.

The trust map's statement, transcribed without alteration:

```lean
theorem stable_rank_trace (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q)
```

with `Psi t = if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3`, exactly as written at
`TRUST-MAP.md` ~line 520.

Also proved, and stronger:

```lean
theorem stable_rank_trace_sharp (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q)
```

**The sharp form needs no hypothesis on `V` at all.** No column-norm bound, no rank
bound. See §6.

Axiom audit. Eleven `#print axioms` lines are **in the module**, following the idiom of
`Zeta23Ext/TruncEst/Axioms.lean`, so the audit re-runs on every `lake build` rather than
living in a document that can drift from the tree. All eleven report

```
[propext, Classical.choice, Quot.sound]
```

for `Psi_eq_gc_two_add_one`, `Psi_attained`, `two_mul_sub_one_add_Psi_le`, `pmat_eigCols`,
`xsq_eigCols`, `rtrace_specMap_Psi`, `stable_rank_trace_sharp`, `stable_rank_trace`,
`stable_rank_trace_no_defect`, `stable_rank_trace_collapse`, `sharp_le_stable`.

Standard axioms only, no `sorry`, no `native_decide`.

## 1b. Second finding: `zeta23ext` does not assemble on `main`

The handoff said to build the vendored package once on the untouched tree first, and
that a failure there is itself a finding. It failed.

```
$ bash hunts/frontier_math/zeta23ext/assemble.sh <worktree>
Some required targets logged failures:
- Zeta23Ext.RetentionWired
- Zeta23Ext.EForm2.Bridge
- Zeta23Ext.TruncEst.Kernel
error: build failed

DOES NOT ASSEMBLE (lake exit 1), do not land Lean on top of this
```

At `36c6070` (`main`), pinned toolchain `leanprover/lean4:v4.33.0-rc2`, against the
prebuilt store the script itself selects.

| module | failure |
| --- | --- |
| `Zeta23Ext/RetentionWired.lean` | `:44:45` `ring_nf` made no progress; `:44:2` type mismatch. As a consequence `Retention.margin_identity` reports `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `Zeta23Ext/EForm2/Bridge.lean` | `:84:6`, `:96:6`, `:160:6` `simp` made no progress |
| `Zeta23Ext/TruncEst/Kernel.lean` | five: `:65:14` function expected, `:60:33` unsolved goals, `:189:4` type mismatch after simplification, `:192:9` `unfold` failed on `d1c2`, `:217:4` `apply @funext` could not unify |

Three things worth stating precisely, because the easy misreadings are all wrong:

- **It is not the dependency store.** The mathlib rev in
  `hunts/frontier_math/zeta23ext/lake-manifest.json` and in `lean/lake-manifest.json` are
  the same, `51e6992efd06126df61a496bebf8f49482a4e129`, and that is the rev actually
  checked out in the store the script symlinks. `batteries` matches too
  (`76e1c118b0700b4ceafe99532e887d6431625e1a`).
- **It is not the `Zeta23` dependency.** None of the three failing modules imports
  `Zeta23`. `TruncEst/Kernel.lean` imports `Mathlib` and nothing else.
- **It is not this branch.** The failing build was launched against the untouched tree,
  before `StableRankTrace.lean` existed or was imported anywhere.

The failure shapes (`simp`/`ring_nf` made no progress, an `unfold` that no longer
unfolds, an instance goal `instAddCommGroup = normedAddCommGroup.toAddCommGroup`) are the
signature of module text written against a different Mathlib than the one it is now
pinned to. This is the fourth occurrence of the class of defect `assemble.sh` was written
for, and its own header records the first three.

**The new module is unaffected and was verified two independent ways**, since the package
verdict cannot carry it:

- `lake build Zeta23Ext.StableRankTrace` from a deleted olean: *Build completed
  successfully (2782 jobs)*, 4.8 s, all eleven `#print axioms` lines clean, no warning
  from the file.
- a direct `lean` invocation on the source against the same `LEAN_PATH`: exit 0, no
  diagnostics.

**This document does not claim that `zeta23ext` assembles.** It claims that
`Zeta23Ext.StableRankTrace` builds, which is the weaker and true statement.

Recorded as issue #101. Not fixed here: it is outside this probe's mission, and the
likely repair is a port pass per module rather than one root cause.

## 2. The identification, which is the finding

Upstream defines, in `Zeta23/ZeroSide/RankTraceMult.lean`:

```lean
def gc (c x : ℝ) : ℝ := x ^ 2 - c * x - (max (x - c) 0) ^ 2
```

`gc 2 x = x² − 2x` for `x ≤ 2` and `2x − 4` for `x ≥ 2`. Ainta's profile is

```
Psi x = (x − 1)² = x² − 2x + 1   for x ≤ 2,
Psi x = 2x − 3   = 2x − 4 + 1    for x > 2,
```

so `Psi = gc 2 + 1` identically. That is `Psi_eq_gc_two_add_one`, kernel-checked.

The additive `1` is `Psi 0`, and it is not decoration: it is precisely the bookkeeping
that converts a defect summed over the **nonzero** spectrum against a **rank** count into
a defect summed over **all of `r`** against `Fintype.card r`. The two adjustments cancel
exactly. Writing `ρ = rank(V Vᴴ)`, `d = card n`, `s = card r`, and `S` for the sum of
`gc 2` over the nonzero spectrum:

```
rtrace Psi(VᴴV) = S + (s − ρ)·Psi 0 = S + s − ρ,     hence     − s + rtrace Psi(VᴴV) = S − ρ.
```

Read the right-hand side: Ainta's `card r` bookkeeping is `[L23]`'s **unrelaxed** rank
bookkeeping `− ρ`, plus the honest defect `S`. That is the precise sense in which the
enhancement is an enhancement, and also the precise sense in which the two are the same
accounting: the `Psi 0 = 1` shift and the switch from `rank P` to `Fintype.card r` cancel
term for term, and what is left over is `S`. `[L23]`'s `rank_trace_ineq` then relaxes
`− ρ` to `− r` using `rank P ≤ r`; nothing in the enhanced passage needs that step, so
the rank hypothesis disappears. That is the structural gain, and it is what makes the
sharp form hypothesis-free.

The full chain, all four steps upstream except the last:

1. `rank_trace_mult` (upstream) at `c = 2`, applied to `P = Pmat m v`:
   `2·tr P + Σⱼ gc 2 (mⱼ xⱼ) + 4·tr Q − 4b ≤ ‖P + Q‖_F²`.
2. Evaluate it at the **eigenbasis presentation** `m = λ(P)`, `v = ` the eigenvector
   columns. Then `xⱼ = 1` (unitary columns) and the diagonal defect *is* the spectral
   defect: `Σⱼ gc 2 (λⱼ)`. This is the presentation at which upstream's own Schur–Jensen
   step `sum_gc_eigenvalues_ge` holds with equality, so nothing is lost.
3. `sum_eigenvalues_comm` (upstream) transfers it to the Gram side, because `gc 2 0 = 0`:
   `Σᵢ gc 2 (λᵢ(V Vᴴ)) = Σⱼ gc 2 (μⱼ(VᴴV))`.
4. `Psi = gc 2 + 1` turns that into `rtrace (specMap … Psi) − card r`.

Step 2 is the only part that was not already a named declaration. It is 25 lines
(`eigCols`, `wmat_eigCols`, `pmat_eigCols`, `xsq_eigCols`).

## 3. Handoff expectation versus what was found

| the handoff expected | what the tree actually holds |
| --- | --- |
| "`rank_trace_ineq`'s proof with ONE scalar estimate sharpened", copy the skeleton | no skeleton was copied; the theorem is a corollary of an exported upstream theorem |
| "prove the scalar lemma separately (`nlinarith` / case split on `t ≤ 2`)" | already upstream, `sq_sub_ge_gc`, in exactly that generality |
| ingredients named: `VonNeumann.lean:171`, `HermitianPosPart.lean:148-180`, `specMap`, `rtrace_specMap`, `specMap_posSemidef` | all present, and *none of them was needed directly*: they are consumed inside `rank_trace_mult`, one level down |
| unnamed anywhere, and load-bearing | `sum_eigenvalues_comm`, the `V Vᴴ` ↔ `VᴴV` spectral transfer (traces of powers + Lagrange interpolation), `RankTraceMult.lean:189` |
| named by the trust map at `:382`, but as a *contrast* ("a defect term, just a different one") rather than as the tool | `rank_trace_mult`, `RankTraceMult.lean:281`. It is the tool: the theorem is quantified over presentations, and the eigenbasis one gives the spectral defect. §11 |

The handoff's own non-vacuity test was the right one and it passed (§5). Its model of
*where the work was* was wrong: it pointed the proof at `Zeta23/LinAlg/`, which the
upstream README says was "written first as a self-contained development accompanying §3
of the paper, by the paper's authors, and is incorporated here unchanged". The
defect-carrying machinery is in `ZeroSide/`, which the README lists as "also proved here,
**beyond the statements of Theorems A-E**". The trust map had in fact already read
`ZeroSide/RankTraceMult.lean` and cited it; §11 is about why that did not change §4's
plan, and it is not a search failure.

## 4. The scalar lemma's status

**Already proved upstream**, as `Zeta23.ZeroSide.RankTraceMult.sq_sub_ge_gc`:

```lean
lemma sq_sub_ge_gc {c p n : ℝ} (hp : 0 ≤ p) (hn : 0 ≤ n) (hc : 0 ≤ c) :
    c * p + gc c p - 2 * c * n ≤ (p - n) ^ 2
```

At `c = 2` this is exactly Ainta's `(p − ν)² + 4ν ≥ 2p − 1 + Psi p`. Two things were
added here rather than reproved:

- `two_mul_sub_one_add_Psi_le`, the same estimate restated in Ainta's own notation, so
  the two forms are visibly the same statement and not two statements that agree.
- `Psi_attained`: the minimum is *attained*, at `ν = (p − 2)⁺`:
  `(p − (p−2)⁺)² + 4(p−2)⁺ = 2p − 1 + Psi p` identically. The trust map called the
  sharpened form "the exact minimum"; an inequality with no attainment claim does not pin
  that word, so it is pinned.

Upstream does not state the attainment in this pointwise form; it proves something
stronger and different, that the *assembled* Lemma R is tight (§8).

## 5. Non-vacuity: the `Psi = 0` collapse

The trust map's built-in test: *specialising `Psi` to the constant `0` must recover
`rank_trace_ineq_two`. If your statement does not reduce to the existing theorem at
`Psi = 0`, the statement is wrong, not the proof.*

Run in both directions, both kernel-checked:

- `stable_rank_trace_no_defect`, the `Psi := 0` shadow of the statement, proved
  **independently, from `RHLinalg.rank_trace_ineq_two`** (with `rank (V Vᴴ) = rank V ≤
  card r`). This is the test as written: the shadow really is the existing theorem.
- `stable_rank_trace_collapse`, the same conclusion, derived instead from
  `stable_rank_trace` plus `Psi_nonneg`. This is the other half, and it is the half that
  says the enhanced form is a *strengthening* of the existing theorem rather than a
  different inequality that happens to look like it.

The statement passes. It was not wrong.

## 6. What `hV` is actually for

The column bound `hV : ∀ j, ∑ i ‖V i j‖² ≤ 1` is used for exactly one inequality:

```
rtrace (V Vᴴ) = Σⱼ Σᵢ ‖V i j‖² ≤ Σⱼ 1 = card r.
```

That single step is the whole difference between the sharp form and the trust map's form:
`4·tr P − 3·card r ≤ 2·tr P − card r` iff `tr P ≤ card r`. Nothing else in the argument
consults `hV`. Pinned as `sharp_le_stable` and `rtrace_self_mul_conjTranspose`.

Two consequences worth carrying downstream, because S2 feeds fifteen other steps:

- The trust map's form is **strictly weaker** than what the same proof delivers, by
  `2·(card r − tr(V Vᴴ)) ≥ 0`. If a downstream step is tight, that slack is free and is
  currently being discarded.
- Any downstream use that cannot supply `hV` can still use `stable_rank_trace_sharp`.

## 7. Aristotle submissions

**None. No project was opened, and no `ARISTOTLE_API_KEY` call was made.**

| what the handoff authorised | disposition |
| --- | --- |
| the scalar lemma alone | not sent: already an upstream theorem (`sq_sub_ge_gc`) |
| the full theorem | not sent: proved locally, zero `sorry`, before any residual existed |
| the theorem with the scalar lemma as a hypothesis | not sent: the weaker variant of a target already closed |

The handoff's rule was *"only what remains goes to Aristotle"*. Nothing remained. Sending
a closed target would have bought a comparison, not a result, and that is an allocation
call the probe was not given. `lean/ARISTOTLE-RUNS.md` carries the non-submission entry
so a later session does not go looking for a project id that does not exist.

**A calibration submission the operator may want, stated concretely so the decision is
cheap.** The interesting unasked question is whether the service *searches the ambient
library*: hand it `stable_rank_trace_sharp` cold, with `Zeta23` importable but with no
mention of `rank_trace_mult`, `gc` or `sum_eigenvalues_comm` in the prompt, and see
whether it finds the four-line corollary route or reinvents the fifty-line skeleton. That
is a measurement about the tool, it costs one project, and the ground truth is now known
exactly, which is the only reason it would be worth anything. It is Core, not this
pursuit, so it is named here and not run.

## 8. Residual goals

**In the target: none.** Every goal closed. There is no residual to write down, which is
the outcome the handoff's step 5 did not budget for.

Genuinely open, and *not* pursued because the handoff forbids formalizing beyond this one
theorem:

- **S12**, which `TRUST-MAP.md` §4 names as the next-smallest:
  `tr Psi(G) ≥ min{1, 2 Σ |G_ij|²}`. Given §2, this is now a question about `gc 2` and
  should be re-scoped before anyone points a probe at it: the same reading that dissolved
  S2 may or may not dissolve S12, and nobody has looked.
- **Tightness.** Upstream proves `Zeta23.ZeroSide.TightMult.lemmaR_tight`: on integer
  multiplicities `1 ≤ mⱼ ≤ c` carried by **orthonormal** vectors plus `b` pair-blocks,
  Lemma R holds with *equality*. Orthonormal columns are exactly the regime where
  `xsq = 1`, which is the regime of step 2 above, so the same witness family should make
  `stable_rank_trace_sharp` an equality. That is now **measured** rather than read off
  (§9): over 400 random instances of that family the slack is zero to `1.07e-14`. So
  Ainta's sharpening sits *at* the known optimum of the device rather than beyond it,
  which bears on §1.4 of the trust map's ceiling arithmetic. Grade: *measured*, one
  route, float. It is **not** formalized in the Lean file, and the general statement
  (that the two attainment sets coincide) is proved nowhere here.

## 9. What the numbers say

`check_stable_rank_trace.py` in this directory. It is not evidence that the inequalities
hold, which the kernel already settled; it answers what a proof does not.

```
[0] max |Psi - (gc2 + 1)| over [-3, 8]:          7.105e-15
[1] 4000 random (hV-satisfying) instances
    min slack, sharp form:                       +0.129088
    min slack, trust-map form:                   +1.651277
[2] 4000 random instances with hV VIOLATED
    min slack, sharp form:                       +0.077948
[3] the TightMult family (orthonormal columns, m_j in {1,2}, c = 2)
    max |slack| over 400 instances:              1.066e-14
[4] gap between the two forms on the hV-satisfying draws
    2*(card r - tr P):  min 0.0409  mean 6.0504  max 15.2972
```

Read: `[0]` is the identification of §2 as a float check independent of the Lean proof.
`[2]` exercises the sharp form outside `hV`, where the trust map's form is not even
stated. `[3]` is the tightness measurement of §8: zero slack, so the sharp form is an
equality on the family upstream proves extremal for Lemma R. `[4]` sizes what the trust
map's transcription discards, and on unstructured draws it is not small: a mean of 6.05
against a `card r` that never exceeds 8.

Grade for everything in this section: *measured*. One route, float arithmetic, no
enclosures.

## 10. Did the formal state change the mathematical picture?

Yes, and not in the direction the probe was pointed. The question the probe was built to
answer was *how hard is the one new lemma*; the answer the formal state gave was *it is
not new relative to the development you chose to state it in*. Writing S2 in `[L23]`'s
Lean vocabulary is what forced the discovery, because the vocabulary is not neutral: the
moment `Psi` had to be a real function fed to `specMap`, the question "which real function
does this development already push through `specMap`" had an answer, and the answer was
`gc 2`, one shift away. A prose reading of the paper against the prose of `[L23]` §3 would
not have surfaced that. §3 of the paper genuinely does contain only the unenhanced
`lem:ranktrace`, and the enhanced form lives in a part of the Lean tree that has no
counterpart in the paper's numbered statements. Three specific things changed. The scalar
estimate is not the gap and never was, so a probe budgeted for "one sharpened scalar
estimate" was budgeted against the wrong object. The rank hypothesis is removable, which
was invisible in the trust map's form and is visible the moment the `Psi 0 = 1`
bookkeeping is written out. And the `hV` hypothesis is doing far less than its prominence
in the statement suggests, which means the trust map's transcription is lossy against the
lemma the same proof supports. What did **not** change: S2 is still one step of sixteen,
it is still load-bearing, and the two analytic bridges S8 and S9 are untouched by any of
this.

## 11. What the trust map actually said, and where the gap really is

An earlier draft of this document said the map "did not look in `Zeta23/ZeroSide/`".
**That is false and the correction is worth more than the claim was.** `TRUST-MAP.md:382`
says, in bold, *"`[L23]` already keeps a defect term, just a different one"*, and cites
`RankTraceMult.lean:281` for `rank_trace_mult`, `TightMult.lean:93` for `lemmaR_tight`,
and `RankTraceMult.lean:119` for `sum_gc_diag_le_sum_gc_eigenvalues`. It names `gc` by
its definition. It even tells a formalizer to *"read `lemmaR_tight` first to know what
they are not allowed to gain"*, which is exactly the right instruction and is what §8
and §9 above act on.

So the map searched the right file and read it. The gap is one step further in, and it
is a more interesting kind of gap than a missed grep.

**The map treated the two defects as different objects.** Its words: *"Ainta's `tr
Psi(M)` is a spectral defect on the Gram matrix rather than a per-zero one, and the
tightness result does not forbid it."* That reads `rank_trace_mult` as a theorem about
one fixed presentation of `P`, the per-zero one. It is not. `rank_trace_mult` is
universally quantified over presentations `(m, v)` with `P = Pmat m v`, and **at the
eigenbasis presentation its per-zero defect is the spectral defect**. Upstream's own
`sum_gc_eigenvalues_ge` says as much in one direction (diagonal ≤ spectrum, by
Schur-Jensen), and the eigenbasis is where that inequality is an equality. Ainta's `tr
Psi(M)` is therefore not a different defect. It is the same defect read at the
presentation that maximises it.

**And `Psi` was never matched to `gc 2`.** §4 of the map says the new content is
"replacing the scalar estimate `min_{n≥0}((p−n)² + 4n) ≥ 2p − 1` by the exact value
`2p − 1 + Psi(p)`", and points the proof at `RankTrace.lean:52-56`, the `sq_ge_linear`
route. That exact estimate is `sq_sub_ge_gc` at `RankTraceMult.lean:81`, in the file the
map had already opened, because `Psi = gc 2 + 1`. Two sections of the same map hold the
two halves and never meet: §4 states the obligation as if `RankTraceMult` did not apply,
and §5's paragraph records `RankTraceMult` as a contrast rather than as the tool.

**The transferable rule is therefore not "search harder".** The map's search was fine.
It is this: **when a formalization already carries an object of the right shape, check
whether the target is an instance of it before recording it as a different object.** The
cheap test is the one that settled it here, and it is mechanical: write both profiles as
functions of one real variable and subtract. `Psi − gc 2 = 1` is visible in ten seconds
on a plot and is `Psi_eq_gc_two_add_one` in four lines of Lean. "A spectral defect rather
than a per-zero one" is a statement about *where the defect is evaluated*, and a theorem
quantified over presentations does not care.

What the map got right and should be credited with: it found the file, it found the
tightness theorem, it flagged the tightness theorem as the thing to read first, and its
non-vacuity test (`Psi := 0` must recover `rank_trace_ineq_two`) was the correct test and
passed. The obligation it named is real and load-bearing. Only "new" is wrong.

## 12. Palomar: the precheck, and a recommendation against a third entry

`scripts/palomar_precheck.py` was run against both documented surfaces of
`lean/PALOMAR.md`, from this worktree:

| surface | invocation | result |
| --- | --- | --- |
| Pub 1 | `. lean lean/comparator.json lean/formalization.yaml` | 64 pass, 1 warn, 0 FAIL |
| DH | `. lean lean/comparator-dh.json lean/palomar-dh/formalization.yaml` | 57 pass, 1 warn, 0 FAIL |

The single warn on each is the pre-existing one: `v4.33.0-rc2` is a release candidate
rather than a stable release, permitted by policy. Nothing in this branch disturbs either
surface, which is the regression the run was for.

**A third surface was not authored, and the recommendation is not to make one.** The
brief for this probe assumed a clean build would clear Palomar's notability floor on its
own. §2 removes that assumption. The registry's rubric carries
`mandatory_reject_below_minimum: ["notability"]`, and the honest description of this
result is *a bridging corollary between a paper's lemma and a theorem already
kernel-checked in a public Lean repository*. That is worth having in this tree. It is not
a registry entry, and submitting it as one would be rounding a rung upward for an
audience.

Recorded so the decision is the owner's and costs one reading, not one investigation:

- **What would be advertised.** `stable_rank_trace` and `stable_rank_trace_sharp`, with
  `Psi`, `rtrace`, `frobSq`, `posIndex` and `specMap` restated verbatim in a fresh
  namespace (all five are short; `specMap` needs only Mathlib's `conjStarAlgAut`).
- **Which project directory.** `hunts/frontier_math/zeta23ext`, not `lean/`. The theorem
  depends on `anthropics/zeta-23-lean`, which `lean/` does not require, and adding that
  dependency to the laboratory's own Lean package to serve a submission would be a change
  to core made for a registry's convenience.
- **What the replay would cost the registry.** A cold build of Zeta23 plus Mathlib. Both
  existing surfaces build against Mathlib alone.
- **The dependency is the whole problem, restated.** An entry whose Solution module is a
  four-line corollary of an imported theorem advertises the import, not the entry.

## 13. Scope, and what this does not claim

- This is one lemma. **The seven-point theorem is not verified**, and nothing here moves
  it. S2 is one step of sixteen; S8 and S9 remain the substantial analytic bridges and
  were not touched.
- Nothing here is evidence for RH.
- "Kernel-checked" here means Lean 4 + Mathlib at the pin in
  `hunts/frontier_math/zeta23ext/lean-toolchain` (`leanprover/lean4:v4.33.0-rc2`), zero
  `sorry`s, standard axioms only, built on this repository's own toolchain. Upstream's
  own verification claims are not copied; the build was run here.
- The claim "S2 is an instance of an existing upstream theorem" is a claim about
  `anthropics/zeta-23-lean` at rev `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, the rev
  pinned by `hunts/frontier_math/zeta23ext/lakefile.toml`. It is **not** a claim about
  what Ainta's note knew, cited, or should have cited; the note's own text was not
  available to this session and was not consulted. Relative to the *paper* `[L23]` §2–§3,
  the lemma may well be new. Relative to the *Lean development* the trust map chose as
  its vocabulary, it is not.
- The tightness reading in §8 is read off upstream statements and is not re-derived here.
