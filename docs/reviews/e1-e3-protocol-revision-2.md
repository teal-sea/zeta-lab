# E1–E3 Protocol — Revision 2 (response to the five objections)

*Planning only. Nothing implemented. This document supersedes the affected sections of `e1-e3-experiment-protocol.md`; everything not revised here stands as written there.*

---

## 1. Judgment on each objection

**Objection 1 (v0 may not promote itself) — ACCEPTED, fully.** This was a genuine hole, and it is exactly the failure the tree's own history warns about: the ninth moment increment was withdrawn because its gates were "chosen after seeing those values" and therefore had "no falsification weight" (ROADMAP.md:785-792). A v0 that both estimates the variance *and* issues the promotion is the same contamination one level up. The rule you propose is also the repo's central rule applied to the experiment about the repo: the probe may propose, it may not promote. One asymmetry is retained and should be stated: **kill-on-v0 is legitimate** even though promote-on-v0 is not, for the same reason the funnel makes `refuted` terminal while `survives` is the most expensive state to enter — a friendly exploratory run that cannot show the effect is strong evidence of absence, while a friendly run that shows it is only a lead with a `proof_gap`.

**Objection 2 (semantic equivalence across A/C/D) — ACCEPTED, with one recorded scope consequence.** The audit below confirms the confound: as designed, L1 was undetectable-in-principle under A/C (the support assertion lived only in the removed dossier), and L4 was explicitly information-absent in A. That measured information *presence*, not representation. The correction — same underlying facts, only encoding varies — is right for the primary experiment. The consequence to record honestly: equalizing facts deliberately stops measuring the *other* half of the original thesis, that the discipline causes facts to be recorded at all (the withdrawal exists because the case-log convention exists). A null result in revised E2 therefore does not touch "the discipline generates the record"; that half is observational and belongs to E1, not to this benchmark, because any benchmark version of it requires us to author the sloppy condition and the strawman risk is unbounded. Condition A is accordingly renamed: it is no longer "casual notes" (a realism claim) but **flat representation** (a controlled encoding). This also surfaces a confound in the other direction, kept and reported rather than removed: C/D carry large volumes of non-lesion-relevant prose, A is compact — so structure must beat not only absence of structure but the noise floor of its own verbosity. That is a fair property of representations to measure.

**Objection 3 (split representation lesions from competence controls) — ACCEPTED.** The audit classifies L3, L7, L8 as controls: their material (module code, draft notes, docstrings) sits in the stable layer, identical across conditions, so condition differences on them would be noise. They are retained for two purposes: competence floor (a model detecting zero controls is below the benchmark's floor; its runs are flagged) and ceiling reference. One consequence the audit exposed, worth stating because it is a finding about the machinery rather than the protocol: **under fact-parity, only lesions touching dossier-recorded state can move D above C** — the typed machinery covers a thin slice of the tree. The original set had effectively one such lesion (L1). Two were added (L9, L10, below) so the D-vs-C contrast rests on four lesions rather than one. If D-vs-C is null, part of the explanation may simply be coverage, and the report must say which.

**Objection 4 (E3-B needs an information-equivalent rival) — ACCEPTED.** T vs B alone confounds typing with information destruction; the three-arm design isolates it. One honest limitation added to the design: in a prompt setting, T's runtime coercion guard (`Support.__bool__` raising) cannot fire — agents see rendered text, so E3-B tests the *representation format*, not the guard. The guard's distinct value (protecting code consumers, not prose consumers) is out of scope for v0 and noted as such, so a T ≈ F result is not over-read as "the type system does nothing."

**Objection 5 (freeze the answer key; behavioral falsity check) — ACCEPTED.** The amendment rule I wrote was a contamination hole: amending a key after observing outputs is fitting the instrument to the data, however uniformly applied. Frozen key, frozen boundaries, exclusion-not-amendment, repair-only-for-v1 — adopted verbatim. The E3-A correction is also right and is the stronger check: a grep proves absent code paths; a state hash proves absent *effect*. Both are kept, with the hash as the requirement and the grep demoted to a supporting scan.

**Objections I think are wrong: none.** All five are corrections the tree's own discipline demands. The only pushbacks are the two scope notes above (kill-asymmetry under objection 1; the retired information-generation hypothesis under objection 2), and neither changes what you proposed — they change what the results may be claimed to mean.

---

## 2. Revised E2 condition design

**Two-layer construction.** Every snapshot is built from one frozen HEAD as two layers:

- **Stable layer — byte-identical in all conditions:** all package code (`zeta/`, `ontology/`, `harness/`, `lean/`, `compiler/`), all scientific tests, package-level READMEs (`harness/README.md`, `ontology/README.md`, `hunts/README.md`'s rule section), the `docs/` reading course, scripts, data. Exception rule: a docs/ file that *describes removed machinery* is removed with it (docs/19 goes wherever `dossier/` goes).
- **Varying layer — authored per condition from the frozen fact list:** root governance documents (README front matter, AGENTS/CLAUDE.md, HANDOFF.md, ROADMAP.md, the hunts case log), `dossier/` and its coupled tests, and NOTES.md (condition A only).

**Conditions:**

- **A — flat representation:** varying layer replaced by one NOTES.md containing every underlying fact from the frozen fact list, one casual line per fact, shuffled order, no headings beyond a date. No dossier, no discipline tests.
- **C — disciplined prose:** the real governance documents (which already contain the underlying facts, since the fact list is drawn from real recorded history), verified against the fact list at freeze; no dossier, no dossier tests.
- **D — typed machinery:** the full tree.

**Fact-parity rule (the load-bearing addition):** for every primary lesion, the *underlying fact statement* is written first and frozen; every proposition required for a 2-score diagnosis must be derivable in every condition; only the encoding varies. D may additionally carry mechanical tripwires — that is the machinery under test — but D may not possess a fact A and C never received. **The consultant audits the condition × lesion manifest for fact parity before the freeze**; the manifest is part of the pre-registration.

Plants (the invalidations/baits themselves) live in the stable layer wherever possible, byte-identical; where a plant must live in the varying layer (L2, L6), it is authored per condition from the same frozen plant statement.

Everything else from the v0 design stands: private fork, no `.git`, no internet, identical tools including pytest, frozen task wording (diagnose / plan / handoff), 3 runs × 2 model families, familiarity probe.

---

## 3. Revised lesion classification + condition × lesion manifest

**Primary representation lesions (7): L1, L2, L4, L5, L6, L9, L10.**
**Control / competence lesions (3): L3, L7, L8.**
Per-lesion contrast annotation: which comparison it can inform (D-vs-C requires the fact to be dossier-representable; C-vs-A requires only prose-vs-flat).

| # | Underlying fact (frozen first) | A — flat | C — prose | D — typed | Plant (identical across conditions) | Contrast | Class |
|---|---|---|---|---|---|---|---|
| L1 | Hardy Z lemmas were proved in Lean; formal support recorded with artifact + observation date | NOTES line: "Hardy Z lemmas proved in Lean (ZetaLean/HardyZ.lean), checked 8/7" | HANDOFF prose: same assertion, artifact, date | Dossier record: formal axis `PROVED`, artifact, dated observation — plus the tripwire test | a `sorry` introduced into HardyZ.lean (stable layer) | **D-vs-C** and C-vs-A | PRIMARY |
| L2 | A hunt claimed an off-line-zero correlation; the claim was withdrawn for three recorded reasons; the withdrawal is on record | NOTES: earlier line asserting the claim, later line "didn't hold up (incomplete zero list; test set was the rival set)" | HANDOFF restored paragraph + case-log withdrawal with the three reasons | same as C, plus hunt-discipline vocabulary test in the tree | the withdrawn claim re-asserted as current in the varying layer, authored per condition from one frozen plant statement | **D-vs-C** (weakly) and **C-vs-A** | PRIMARY |
| L4 | python-flint absent ⇒ rigor cross-check silently off; suite shows "5 skipped"; this hazard is on record | NOTES line: "need python-flint or the rigor cross-check silently skips (suite looks green)" | AGENTS.md Setup warning, full prose | same as C (no typed representation of backend state exists at freeze) | requirements edited so flint is absent (stable layer) | **C-vs-A**; D≈C expected | PRIMARY |
| L5 | The matrix/existence-route class of attacks is closed, with the gate-#3 reason recorded | NOTES line: "existence-of-operator attacks closed — detector can't see off-line zeros, distinguishes nothing" | ROADMAP closure section with reasons | same as C (no typed Decision object exists — deliberately unbuilt) | a TODO draft in the stable layer proposing a Wu–Sprung-style attack as "promising next step" | **C-vs-A**; D≈C expected | PRIMARY |
| L6 | The project scope is "workbench, not proof; nothing here advances RH", stated in docs/00 (stable) and the governance layer | NOTES scope line contradicting planted claim | README/HANDOFF scope prose | same as C | a "proof by construction" sentence planted in the varying-layer doc per condition, contradicting stable docs/00 | **C-vs-A**; D≈C expected | PRIMARY |
| L9 | `\|ζ(½+it)\|` was considered as a Z definition and rejected — real, even, same zeros, but never negative, so no sign to bisect | NOTES line: "use Z, not \|zeta\| — \|zeta\| never changes sign" | prose paragraph (HANDOFF/ROADMAP) with the reason | typed `RejectedAlternative` with `why_rejected`, plus the discriminating obligation | a scratch draft in the stable layer adopting \|ζ(½+it)\| as "a simpler Z" for a proposed scan | **D-vs-C** and C-vs-A | PRIMARY |
| L10 | The R-vs-C Lean definition question was asked and is resolved, with the resolution recorded | NOTES line: question + "settled: keep both APIs, realness from the completed-zeta route" | prose Q&A in HANDOFF | typed `OpenQuestion` with non-blank `resolution` | a task note in the stable layer asking the next session to "settle" the already-settled question | **D-vs-C** and C-vs-A | PRIMARY |
| L3 | (control) a staged department candidate whose instruments are placeholders | — module code identical in all conditions (stable layer); admission discipline in harness/README, also stable — | | | the staged sham module itself | none expected | CONTROL |
| L7 | (control) a draft note promoting `distinguishes=True` to "structure explains the property" | — draft note and the corrective harness/README both stable — | | | the draft note | none expected | CONTROL |
| L8 | (control) hunt results whose scan never calls the completeness gate; caveat in the detector docstring | — hunt directory and docstring both stable — | | | the hunt directory | none expected | CONTROL |

**Scoring split.** Primary detection score reported as two pre-registered sub-scores: **D-set** = {L1, L2, L9, L10} (max 8) for the D-vs-C contrast; **C-set** = {L2, L4, L5, L6} (max 8) for the C-vs-A contrast (L2 appears in both by design and is annotated as shared). Controls {L3, L7, L8} are reported separately: a run detecting 0 controls is below the competence floor and is flagged; ceiling on controls across all conditions is expected and unremarkable.

Fairness note carried into pre-registration: the D-set is small because the typed machinery genuinely covers little of the tree; a null D-vs-C result must be reported with that coverage caveat rather than as a clean kill of typing.

---

## 4. Revised E3-B design (three-arm)

Hypothesis unchanged; arms revised:

- **T — typed:** the `Support.render()` four-axis block, statuses from the closed vocabularies.
- **F — flat, information-equivalent:** the *same four facts* as unstructured prose sentences, no axis names, no enumerated statuses, no ordering convention (e.g. "a computation agreed at the points tried; nobody ran enclosures; a paper discusses this; the Lean file holds complete-looking proofs nobody watched compile").
- **B — boolean:** `verified: true/false`, the naive collapse (true iff any axis asserts).

Fact-parity rule applies between T and F for every profile; B is deliberately destructive. 8 profiles × 3 formats × 2 models × 3 runs = 144 single-prompt trials (still cheap). Task wording and flattening definition unchanged.

**Pre-registered interpretation table (verbatim from the objection, adopted):**

| Result | Reading |
|---|---|
| T > B | rich representation beats one-bit collapse |
| F > B | preserving evidence facts beats one-bit collapse |
| T > F | typed semantic boundaries add protection beyond information preservation |
| T ≈ F > B | the value is information preservation, not the type system |
| T ≈ F ≈ B | our representation isn't affecting downstream behavior at all |

Recorded limitation: the coercion guard cannot fire in prompt trials; a T ≈ F result says nothing about the guard's value to code consumers, and the report may not claim otherwise in either direction.

---

## 5. Revised pre-registration / promotion rule

Replaces §7.6–7.8 of the v0 protocol; all other prereg items stand, with these additions:

- **The condition × lesion manifest (§3 above) is part of the frozen pre-registration**, consultant-audited for fact parity before any snapshot is built.
- **Answer key freeze:** lesion definitions, answer key, and 0/1/2 boundaries are frozen before the first run. After outputs exist: scorer disagreement is recorded; if the frozen rubric cannot resolve it, the lesion is **excluded from primary v0 analysis** (reported); the key may be repaired **only for v1**. The key is never altered using information from the outputs it scores.
- **v0 outcome vocabulary — v0 may kill or calibrate, never promote:**
  - **KILL** — in either model family, median D ≤ median A on the combined primary set, with controls above floor (the machinery adds nothing over flat facts). Terminal for the product-semantics hypothesis.
  - **BENCHMARK-BROKEN** — controls at floor in any condition (models below competence), or scorer exclusions remove more than ⅓ of a primary sub-score's lesions, or a fact-parity breach is discovered post hoc. The result is void; only the benchmark may be repaired.
  - **CANDIDATE-POSITIVE** — apparent D > C on the D-set and/or C > A on the C-set. This is a *lead with a proof gap*, not a result. It authorizes exactly one thing: designing confirmatory v1.
  - **AMBIGUOUS** — anything else. One design revision permitted; then v1 or stop, owner's call.
- **Confirmatory v1 (the only path to E4):** fresh lesion *instances* of the same classes (new surface text, new plants, same underlying-fact discipline, consultant again audits parity and again authors two); scoring rubric frozen from v0's repaired version before any v1 data; **numeric thresholds chosen from v0's observed spread and signed before the first v1 run**; same or stricter controls; both model families. Only v1 meeting its signed thresholds earns E4. v0 numbers may never be pooled with v1 numbers.
- **E3-A falsity check, strengthened:** before invalidation, hash every durable record file (dossier subjects, status-bearing records) in the scratch worktree; plant the invalidation; run the suite; hash again. Required result: tripwire test fails **and** the record hashes are byte-identical — the machinery refused, nothing rewrote. The source grep for status-writing code paths is retained as a supporting scan, not the proof.

---

## 6. Revised decision tree

| Observed result | Next action |
|---|---|
| E1: ≥⅔ interventions judgment-only/owner-authority, low artifact-legibility | **Stop** the product line; keep the log as documentation; the operator is the method |
| E2 v0: KILL | **Stop**; disposition to ROADMAP; E3-A tripwires kept only where they stand as ordinary lab tests |
| E2 v0: BENCHMARK-BROKEN | Repair the benchmark only; no inference in either direction; one repair cycle, then run or abandon |
| E2 v0: C > A but D ≈ C (calibration reading) | v1 optional and only if the D-set coverage caveat plausibly explains the null; otherwise **keep as documentation** — the transferable asset is prose discipline |
| E2 v0: CANDIDATE-POSITIVE on D-set | **Design and run confirmatory v1** (fresh instances, pre-signed thresholds). No E4, no sibling anything, no admission attempt on v0 numbers |
| E2 v1: meets its signed thresholds in both families | **Run E4** (outside-team test); dossier department admission attempt per docs/19 §6 becomes legitimate |
| E2 v1: fails its signed thresholds | **Stop**; the candidate positive did not confirm; disposition recorded; no v2 |
| E3-A works, E2 shows nothing | **Tiny internal tool** at most: tripwires as ordinary tests; nothing more |
| E3-B: T ≈ F > B | Product constraint reframed: the asset is information preservation, not typing; typed-schema product claims die; prose/flat-preserving formats suffice — record it |
| E3-B: T ≈ F ≈ B | Kill the no-flattening product constraint for prompt consumers; note the code-consumer guard remains untested |
| E3-B: T > F > B | The typing claim survives for downstream language; feeds v1/E4 framing |
| Results vary primarily by model family, not condition | **Stop**: state carriage is dominated by model capability; record in ROADMAP |
| E1 procedural share high AND v1 confirms AND E3 favorable | E4, then and only then sibling probe; customer discovery stays gated behind E4 |

No path reaches E4 from v0. No path reaches customer discovery except through E4.

---

## 7. Implementation-sequence deltas

The v0 sequence stands with three changes: (a) item 5 (lesion planting) is preceded by a new item — **freeze the underlying-fact list and the condition × lesion manifest, consultant parity-audit, then sign** — and the answer key is written and frozen in the same step; (b) item 4's snapshot script now builds the two-layer construction (stable layer copy + per-condition varying layer from the fact list); (c) item 8's E3-A work adds the hash-before/hash-after harness (small, scratch-branch only, deletable — the tripwire tests themselves remain the non-deletable survivors).

---

# PROPOSED EXPERIMENT CONTRACT (rev. 2)

**Question.** Is a meaningful part of this laboratory's operating discipline carried by transferable artifacts and machinery, or mainly by the operator's unstated judgment? Sub-questions: (E1) what the operator contributes and how much is legible from artifacts alone; (E2) whether, **holding underlying facts semantically equivalent across conditions**, disciplined prose beats flat representation (C vs A) and typed machinery beats disciplined prose (D vs C) on resumption under planted failures; (E3-A) whether artifact→status couplings mechanically demand reevaluation with **provably zero automatic status rewrites** (state-hash check); (E3-B) whether typed support reduces downstream flattening beyond what **information-equivalent flat support** (three-arm: typed / flat / boolean) already provides.

**Will be built.** The intervention log (JSONL + schema doc + validator) in the private ledger repo; a private fork with a two-layer snapshot script, three condition snapshots of one frozen HEAD, ten history-derived lesions (7 primary under a consultant-audited fact-parity manifest, 3 competence controls; two lesions consultant-authored), a frozen answer key, one prompt template, one scoring rubric; 8–10 staleness tripwire tests in the public tree plus a scratch-branch hash-comparison harness; 8 × 3 support-profile prompt sets.

**Will not be built.** No CLI, no runner beyond a script and checklist, no dashboards, no typed Session/Decision/Intervention/Artifact/Warrant objects, no dependency graph, no battery versioning, no sibling repository, no product code. Building any of these before results exist is contamination.

**Primary measurements.** E1: intervention rate and mechanizability distribution, double-classified. E2: median lesion detection reported as two pre-registered sub-scores — D-set {L1, L2, L9, L10} for D-vs-C, C-set {L2, L4, L5, L6} for C-vs-A — controls reported separately as a competence floor. E3-A: tripwire detection with byte-identical durable-record hashes across invalidation. E3-B: flattening rate across T / F / B.

**What counts as success.** E2 v0 has no success state that promotes: its best outcome is CANDIDATE-POSITIVE, which authorizes only the design of confirmatory v1 (fresh lesion instances, thresholds signed from v0's spread before v1 data, frozen scoring). Success = **v1** meeting its signed thresholds in both model families, plus E3-A full detection with zero rewrites, plus E3-B showing T > F (not merely T > B). E1 is informative regardless of direction with ≥15 events.

**What counts as failure.** v0 KILL (D ≤ A in either family with controls above floor); v1 failing its signed thresholds (terminal — no v2); E3-B showing T ≈ F (typing claim dies; information-preservation claim survives only if F > B); E1 showing ≥⅔ judgment-only with low artifact-legibility. BENCHMARK-BROKEN voids inference and permits one repair cycle only.

**Frozen before first run.** The underlying-fact list; the condition × lesion manifest (consultant-audited for fact parity); lesion definitions, answer key, and scoring boundaries; the task prompt; the settled-dead-ends list; the outcome vocabulary above. After outputs exist, the key is never amended — unresolvable scorer disagreement excludes the lesion from primary v0 analysis, and repairs apply only to v1.

**Forbidden until results exist.** E4 on v0 numbers (v0 may kill or calibrate, never promote); sibling repository; customer discovery; dossier department admission; commercial framing in the public tree; implementing any typed governance object; changing `zeta/`, `ontology/`, `harness/`, `dossier/` for experiment-only reasons; altering thresholds, the fact list, or the answer key after data exists; pooling v0 with v1.

**Authority.** The owner signs this contract and the pre-registration, holds all go/no-go decisions, and adjudicates under the frozen rules only. The consultant audits the fact-parity manifest, authors two lesions per round, and may serve as second scorer; neither the consultant nor any coding agent may promote a result, alter frozen materials, or initiate a forbidden action. The laboratory's scientific objective is unchanged; conflicts between the experiment and normal lab work resolve in the lab's favor, up to aborting the probe.
