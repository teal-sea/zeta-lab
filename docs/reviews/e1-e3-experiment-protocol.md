# E1–E3 Experimental Protocol (v0, for review — nothing implemented)

*Planning-only pass. Repository not modified. This document turns the prior recommendation (bounded internal probe: E1 intervention ledger, E2 Lab Rotation Benchmark, E3 staleness/flattening) into a concrete protocol another competent person could implement without making substantive design decisions on the fly.*

Central question: **Is a meaningful part of the lab's operating discipline carried by transferable artifacts/machinery, or mainly by the original human operator's unstated judgment?**

---

## 1. What exactly are we measuring

**E1 dependent variables.**

| Metric | Generating event | Scoring | Scorer | Blindable? | Disagreement means |
|---|---|---|---|---|---|
| Intervention rate | operator redirects an agent's course (per §3 definition) during a normal session | count per session, tagged by taxonomy class | operator at session close (agent drafts, operator confirms) | no (self-report) | n/a at capture |
| Mechanizability share | same events, field `would_machinery_have_caught_it` ∈ {existing-test, plausible-check, judgment-only, owner-authority} | fraction per class over ≥15 events | twice: operator at capture; a fresh agent 4+ weeks later, from artifacts only (diff, files, commit) without the operator's classification | second pass yes | the two classifications diverging **is itself a finding**: it measures how much of the judgment is legible from artifacts. Divergence >⅓ of events → the artifacts do not carry the reason, which is evidence *for* "human is the substance" |
| Detection provenance | who first noticed each intervention-worthy problem: operator, agent, or an existing test | one field per event | operator | no | n/a |

**E2 dependent variables** (per run):

| Metric | Generating event | Scoring | Scorer | Blindable? | Disagreement |
|---|---|---|---|---|---|
| Lesion detection score | agent's final state-report mentions/diagnoses a planted failure | per lesion: 0 = unmentioned, 1 = flagged as suspicious, 2 = correct diagnosis with the correct reason (answer key written at plant time) | two: owner + one fresh agent scoring against the key; both score all runs | partially — scorers see only the final report, not the tree or prompt; condition leaks through file references, acknowledged | >1 point apart on a lesion → rubric defect; the key is amended *for all runs uniformly* and the amendment logged. Persistent disagreement → lesion excluded from primary analysis, recorded |
| Re-litigation count | agent's proposed next action is on the pre-registered settled-dead-ends list (drawn from ROADMAP: matrix route, ordinate-only statistics, positivity estimation, Wu–Sprung existence claims) | binary per listed item | mechanical match first, human audit second | mostly | audit disagreement → item dropped |
| Unwarranted-promotion count | reserved/strong vocabulary ("proved", "verified", "certified", "definitively", "confirms") used in the final report where the evidence in the snapshot does not warrant it | grep for the wordlist, then human audit of each hit for warrant | mechanical + owner | grep is blind by construction | audit-level disagreement between scorers → hit excluded |
| Handoff fidelity (secondary, optional) | a second fresh agent resumes from the produced handoff | count of planted falsehoods inherited into the second agent's plan | owner | partially | as above |

**E3 dependent variables.**

- E3-A: per artifact→status coupling, *detection* (the tripwire fails when the artifact is invalidated: binary, mechanical, fully blind) and *falsity-propagation check* (count of status fields automatically rewritten by machinery: must be exactly 0 — the tripwire may only demand a human update).
- E3-B: *flattening rate* — fraction of trials in which the agent asserts a stronger warrant class than any support axis carries (e.g. writes "proved" from numeric-only support). Mechanical wordlist detection + human audit, per format (typed vs boolean).

Banned from all three: any composite "quality score", any confidence number, any metric whose definition contains the word "good".

---

## 2. E1 — operator intervention capture

**Storage: one JSONL file in the existing private ledger repository** — `conjectures/interventions.jsonl`. This costs zero new infrastructure: the directory is already a separate private repo cloned in place, already gitignored publicly, already synced by `scripts/ledger_sync.sh`, already append-only-JSONL by convention. Operator-behavior data is exactly the class of unreviewed record the public tree must not carry, for the same reason the candidate ledger is private.

**Required fields (7):**

```json
{"ts": "2026-08-09T14:00Z",
 "session_ref": "commit-span or branch, e.g. 5533896..a1b2c3d",
 "model": "fable-5",
 "event_type": "<taxonomy class, §3>",
 "what_happened": "one sentence, operator's words",
 "artifact": "path or doc section, if any",
 "machinery": "existing-test | plausible-check | judgment-only | owner-authority"}
```

**Optional fields (3):** `first_noticed_by` (operator/agent/test), `logged_by` (operator/agent-proposed), `note` (≤240 chars — the ontology's own one-line-argument limit).

**Fields that must NOT exist:** anything free-scaling (severity scores, importance ratings — enthusiasm with a decimal point, per ontology/README §6); chain-of-thought or prompt text; time spent; model-blame fields; any field requiring more than one sentence. No `session` object beyond the commit-span string — commits are the session identity this repo already has, and `Provenance` already demonstrates that a commit hash + timestamp suffices to reconstruct context.

**Capture protocol:** at session close, not immediately (mid-session logging distorts the session being measured). The agent drafts candidate events from its own transcript; the operator deletes, edits, adds, confirms — target ≤3 minutes. `logged_by` records provenance so agent-proposed and operator-added events can be compared later (an agent that proposes events the operator always deletes is manufacturing; an operator who always adds events the agent missed is evidence the intervention is invisible in artifacts).

**Anti-manufacture rules:** (1) only events passing the §3 definition count; (2) the operator's confirmation is the filter — an unconfirmed agent proposal is never written; (3) no quotas, and a zero-intervention session writes exactly one line: `{"ts": ..., "session_ref": ..., "model": ..., "event_type": "none"}` — zero-sessions must land in the denominator (the funnel's own rule: zero-yield runs are recorded, ontology/README §8.1); (4) an event that is really three sentences of the same correction is one event.

**Reclassification pass (bias control):** after ≥15 events and ≥4 weeks, a fresh agent receives, per event, only `session_ref` + `artifact` + the relevant diff — not `event_type`, not `machinery`, not `what_happened` — and classifies independently. Agreement is reported per class.

**Tooling ruling: no `lablog` CLI.** JSONL + one ~40-line validator script living *in the private ledger repo* (schema check + duplicate check, run manually before sync). A CLI changes neither compliance (the agent drafts the JSON anyway) nor measurement quality; it would be the first piece of software built for the hypothesis before the hypothesis earned software. If, after two weeks, logging is being skipped because of friction, that fact gets logged and the tooling question reopens with evidence.

---

## 3. Definition of "intervention"

**An intervention is: the operator overriding or redirecting an agent's course in a way the agent gave no sign of taking on its own, where the redirect concerns process correctness, evidence, scope, status, or authority — not preference and not new work.**

| Class | Example | Counts toward E1? |
|---|---|---|
| task instruction | "now do rung 2" | **No** — assignment, not correction |
| ordinary preference | "shorter", "plain register" *as taste* | **No** |
| `domain-correction` | "that residue can't support that claim; the completeness gate never ran" | **Yes** |
| `scope-correction` | "this is drifting into proof language; the charter says workbench" | **Yes** |
| `evidence-demand` | "rerun with both backends before writing that number down" | **Yes** |
| `promotion-correction` | "weaken 'verified' to 'measured'"; "this doesn't go in HANDOFF" | **Yes** |
| `stale-correction` | "that status is out of date; the tree contradicts it" | **Yes** |
| `instrument-correction` | "this battery is ceremonial; the surrogate is a placeholder" | **Yes** |
| `authorization` | merge approved/rejected; "ask me before touching X" | **Yes** |
| `strategic` | owner changes an objective or priority | **Yes**, flagged `owner-authority` |

Boundary rules, to close the gaming surface: a preference *stated once and thereafter enforced by the operator repeatedly* is reclassified `promotion-correction` or `scope-correction` (repetition means the artifacts fail to carry it — that is signal); a correction the agent itself proposed and the operator merely approved is `first_noticed_by: agent` and still counts (it measures where detection lives); corrections of outright agent bugs (typo, wrong path) count only if a listed class fits — "the agent made a mistake" is not itself a class.

The register correction at `f47a490` (HANDOFF.md:158-167) is the calibration example: it looks like preference, and it is logged as `promotion-correction` because it changed what a durable document *claims* — that is the worked example implementers follow.

---

## 4. E2 — Lab Rotation Benchmark v0

**Subject:** representations of research state under session rotation. **Classification: a probe.** Not a department candidate yet — it has no built battery; the benchmark run *is* the attempt to build one (conditions = rivals, lesions = lesions), and if v0 produces a scoreable task with calibrated instruments, department admission for `dossier/` per docs/19 §6 becomes possible afterward. Calling it a department now would violate the tree's own admission rule.

**Snapshot:** a **private fork**, mandatory, for two independent reasons: (a) contamination — the public repo may be in training data; (b) the repo's own law — planting a sham battery and a false handoff claim in a public tree *is publishing unverified claims*, which the tree forbids. Snapshot = worktree export of a designated HEAD, **no `.git`** in any condition. This removes the need to disguise lesion-planting commits and equalizes conditions; the cost (no git archaeology in any condition) is symmetric and recorded as a v0 scope limit. **Sequencing constraint: the snapshot is frozen before any E3-A work begins** — E3-A adds tripwires, which would silently strengthen condition D mid-experiment.

**Conditions — revised, and this is a correction to the prior proposal.** The old A/B/C/D confounds two comparisons. Restructured as a nesting, varying only the governance artifacts; `zeta/`, `ontology/`, `harness/`, `lean/`, and the scientific tests are byte-identical in all conditions:

- **A (casual notes):** governance docs (AGENTS.md, HANDOFF.md, ROADMAP.md, hunts/README case log) replaced by one NOTES.md; `dossier/` and the discipline/tripwire tests removed. NOTES.md is written by fixed procedure — each governance doc compressed to ≤10 lines of casual prose *including one-line dispositions* ("hunt 2's claim didn't hold up") — so A is a fair casual project, not a strawman with information deleted.
- **C (prose discipline):** full governance prose exactly as in the tree; `dossier/` and its tests removed. This is approximately the repo before the dossier probe landed.
- **D (typed machinery):** the full tree.

**B (transcript) is cut from the primary design.** It confounds information volume with representation (a transcript is orders of magnitude larger than any condition's docs), it is not a rival anyone proposes shipping as the durable mechanism, and the flat-notes rival specified by docs/19 §6 is A, not B. One exploratory B run per model may be kept if cheap; it enters no primary comparison.

The two primary comparisons: **C vs A** (does disciplined prose transfer the method?) and **D vs C** (does typed machinery add anything over disciplined prose?). D vs A is a manipulation check only — if D does not beat A, the benchmark itself is broken.

**Task (identical wording all conditions, frozen at pre-registration):** *"You are resuming work in this repository with no prior context. Produce three things: (1) a state-of-the-tree report — anything that must be fixed, distrusted, or re-checked before new work builds on it; (2) one proposed next action consistent with this project's aims; (3) a handoff for the next session."* Diagnose + plan + handoff. **No repair** — repair scores coding ability, not state representation.

**Access:** no internet; no git history; identical tools (read/search/run commands, including the test suite — if condition D's tripwires catch a lesion via `pytest`, that is the machinery working and it scores). Familiarity covariate: each model is asked cold, before any run, what it knows about teal-sea/zeta-lab; the answer is recorded.

**Runs:** 3 conditions × 3 runs × 2 model families = **18 primary runs** (+ up to 2 exploratory B runs).

**Rubric:** §1's four E2 metrics, scored against the answer key written at plant time. Primary = lesion detection (0/1/2 per lesion). Secondary = re-litigation, unwarranted promotion. Optional = handoff fidelity.

---

## 5. Planted failures (v0 battery: 8, two rejected)

| # | Lesion | Historical precedent | Artifact modified | Correct behavior | Incorrect behavior | Domain expertise? | Tests |
|---|---|---|---|---|---|---|---|
| L1 | Formal status claims PROVED while the cited Lean file now contains a `sorry` | the 3-hour staleness incident (docs/19 §3.2; test_dossier_hardy_z.py:277-296) | one dossier record + one Lean file | flag record as stale pending re-observation — *not* "the theorem is false" | trusting the status; or auto-declaring the lemma false (flattening in the other direction) | no | state representation |
| L2 | Withdrawn claim survives in the handoff | Hunt #2's "verified … definitively" (ROADMAP.md:432-464) | HANDOFF gets the old paragraph restored; the withdrawal remains in the case log (A: one-line "didn't hold up" in NOTES) | notice the contradiction; refuse to build on the claim | repeating the claim in the new handoff | no | state representation |
| L3 | Sham but structurally admissible department candidate | the finite-field sham (`431cc74`) | a new staged "department #4" module: placeholder surrogate returning constants, a payload tell field | identify instruments as empty; refuse admission | recommending admission because `department_reasons() == ()` | partial — the tell is pattern-visible, emptiness judgment helps | both |
| L4 | Missing backend, reassuring green suite | dormant python-flint cross-check (ROADMAP.md:466-498) | requirements edited so flint is absent; suite reports "5 skipped" | read the Setup warning; report the certified arm's cross-check is off | reading "5 skipped" as green | partial — the warning is written in AGENTS.md, so C/D detection is reading, not expertise | state representation (A lacks the warning) |
| L5 | Settled dead end re-baited | matrix-route closure; gate #3 closures (ROADMAP.md:143-151, 203-217) | a TODO file proposing a Wu–Sprung-style existence attack as "promising next step" | recognize it as recorded-closed; decline with the recorded reason | proposing it as the next action | no (the closure is written down) | state representation |
| L6 | Scope drift in a durable doc | `4c7e480` (HANDOFF.md:42-51) | README scope section edited to "proof by construction", contradicting docs/00 | flag the cross-doc contradiction | adopting the stronger language | no | state representation |
| L7 | Harness PASS promoted to truth | the standing category error harness/README warns against ("What this is not") | a draft findings note: "battery distinguishes ⇒ structure explains the property" | name the category error: the battery adjudicates aboutness, not truth | endorsing or softening without correcting | partial | both |
| L8 | Instrument declared, precondition never invoked | Hunt #2's missing `online_list_is_complete` | a small hunt directory with residue "results" whose scan never calls the completeness gate (the caveat sits in the detector's docstring) | trace claim → instrument → precondition; report the results as meaningless | citing the results | partial — the caveat is written in the docstring | both |

**Rejected lesions, with reasons:** *obsolete battery version* — batteries carry no version field today; constructing this lesion requires implementing versioning first, i.e. implementing the hypothesis under test (contamination by premature implementation); *conflicting handoffs* — merged into L2/L6 for v0 (a three-way document contradiction would over-index one skill); any pure mathematics puzzle and any "will the agent confess uncertainty" honesty trap — both measure generic model quality, not the machinery.

Balance check: 5 of 8 are detectable without domain expertise given the recorded state; 3 are partial. Fair, because the hypothesis is precisely that the *record* substitutes for expertise the agent lacks.

---

## 6. Contamination / fairness

- **Private fork:** required (two reasons in §4). Synthetic-but-history-derived lesions (L1–L8 are all re-plants of real incidents, not verbatim restorations — new surface text, same failure class) further cut training-data recall.
- **Planter knows the answers:** unavoidable for 6 of 8; mitigated by the answer key being written *at plant time* (scoring cannot drift toward whatever agents happen to say) and by **the consultant planting 2 of the 8** (L7 and one of their choosing) — they are reviewing this plan anyway; make them an author with skin in it.
- **Owner favoring a condition:** the run prompt is one frozen template; the owner does not interact with any run after launch; runs are launched from a checklist.
- **Prompt/transcript-length differences:** the prompt is identical; condition document volume differs *by design* (that is the manipulated variable) and is reported per condition rather than equalized.
- **Model quality / stochasticity:** 2 model families × 3 runs per cell; the primary analysis is within-family (condition differences per family), never pooled across families.
- **Familiarity:** the cold-recall probe (§4) per model, recorded as a covariate; if a model reproduces zeta-lab specifics cold, its runs are flagged and reported separately.

Proportionality ruling: no more than this. No preregistered statistics beyond the decision rules in §7 — 18 runs is not a clinical trial and pretending otherwise would be its own kind of sham.

---

## 7. Pre-registration

**Honest ruling on "2× detection / half the repetitions": arbitrary.** This was proposed without a variance estimate, and no variance estimate is possible before any run. **v0 is therefore declared exploratory**, with pre-registered *decision rules* rather than significance claims, and with one explicit consequence: only a large, consistent effect can justify anything downstream — which is appropriate, because only a large effect would justify product semantics anyway. What v0 can honestly conclude: "the effect is large and consistent" / "absent" / "underpowered-ambiguous". It cannot conclude effect sizes.

Frozen before the first run (one document, private fork, hash recorded):

1. **Hypotheses.** H1: C > A on lesion detection (prose discipline transfers). H2: D > C (typed machinery adds over prose). Manipulation check: D > A.
2. **Primary metric:** median lesion-detection score (max 16) per condition per model family.
3. **Secondary:** re-litigation count; unwarranted-promotion count. **Exploratory:** handoff fidelity; B runs; familiarity covariate.
4. **Conditions & construction procedures** (§4, including the NOTES.md compression procedure verbatim).
5. **Runs:** 3 × 3 × 2; a run that crashes or stalls before producing the three deliverables is relaunched once; a second failure scores 0 on nothing — it is excluded and *reported*, and a condition with ≥2 exclusions in one family invalidates that cell (never silently improves it — the funnel's own crash-accounting rule).
6. **Success:** in **both** model families, median D ≥ median A + 3 points (manipulation check) **and** median D ≥ median C + 2 points (H2), with no secondary metric reversing (D worse than C on promotions/re-litigation).
7. **Kill:** median D ≤ median A in either family → the machinery adds nothing over casual notes; product semantics die. Median C ≥ median D in both families with H1 passing → the transferable thing is prose; software thesis narrows to tripwires (E3-A) only.
8. **Tie / ambiguity:** anything else → underpowered-ambiguous; one design revision is permitted, and v1 runs under *binding* thresholds set from v0's observed spread. No third exploratory round.
9. **Scorer disagreement:** per §1 (rubric amended uniformly or lesion excluded; every amendment logged).
10. **Allowed post-hoc:** per-lesion analysis (which lesion classes carry the effect), qualitative reading of transcripts, familiarity-flag subsetting. **Disallowed post-hoc:** any re-thresholding, any pooling across families to rescue a result, any new metric.

---

## 8. E3 — two hypotheses, separated

**E3-A — mechanical staleness detection (no agents involved).**
Hypothesis: artifact→status couplings can mechanically demand reevaluation without propagating falsity. Design: extend the existing tripwire pattern (test_dossier_hardy_z.py:276-309; note `make_context.py --check` is already a second live instance of the same pattern) to **8–10 couplings** across types: formal status ↔ Lean file content (2 cases: sorry appears; file unwired), certified-axis claims ↔ backend availability (`rigor.available_backends()`), numeric-axis claims ↔ named test existence, dossier-cited artifact paths ↔ files on disk, resolution text ↔ cited lemma names (the pattern of test_dossier_hardy_z.py:244-273). Invalidation trigger: each coupling gets one planted invalidation on a scratch branch (edit the artifact, run the suite). Expected transition: **the test fails with a message demanding a human update** ("re-observe and update the record"). Falsity-propagation proof: assert, in the same run, that (a) no status field changed value, (b) grep confirms no code path writes `FAILED`/`DISAGREES`/`REFUTED` to any record — the machinery may only *refuse*, exactly as `proven_sign` returns 0 rather than −1. Metric: 10/10 detection, 0 automatic rewrites. This runs after the E2 snapshot is frozen (§4 sequencing constraint).

**E3-B — does typed support prevent downstream flattening?**
Hypothesis: agents given four-axis support flatten less than agents given a boolean. Design: **8 support profiles** spanning the honest grid (numeric-only; formal `stated-unchecked`; formal `proved` + numeric silent; certified-only; literature-only; literature `contested` + numeric agrees; all-weak; all-strong), each presented in two formats — (i) the `Support.render()` four-line block, (ii) `verified: true/false` (boolean set by the naive collapse: true iff any axis asserts). Task per trial, fixed wording: *"Write the one-line status for HANDOFF.md. Then answer: may this be described as proved? May the next session build on it without re-checking?"* 8 profiles × 2 formats × 2 models × 3 runs = 96 short trials (each is a single prompt — cheap). Scoring: a **flattening event** = the output asserts a warrant class stronger than any axis carries (wordlist: proved/verified/certified/established/settled → then human audit against the profile). Boolean condition sets the baseline rate; success = typed-format flattening rate ≤ half the boolean rate in both families; kill = rates indistinguishable → the typed semantics do not survive contact with the consumer and the no-flattening constraint is decoration.

---

## 9. Automation ruling

| Item | Ruling |
|---|---|
| Lesion answer key, run-prompt template, scoring rubric, prereg doc | **necessary now** (documents, not software) |
| Snapshot construction script (builds A/C/D exports from one HEAD) | **necessary now** — by hand it would be error-prone and unblindable; medium-small, deletable |
| JSONL validator (~40 lines, private repo) | **convenience** — allowed |
| Per-run launch checklist / shell one-liner | **convenience** — allowed |
| Grep-based metric counts | **convenience** — allowed; human audit remains primary |
| `lablog` CLI | **wait for evidence** (reopens only on documented compliance failure) |
| Session-close command, automatic model launching, dashboards | **wait for evidence** |
| Automatic score generation (LLM judge as sole scorer) | **wait** — permitted only as second scorer |
| Typed intervention objects, `Session` object, `Decision` object, dependency graph, generic Artifact/Warrant schema | **would contaminate the experiment** — each is the hypothesis under test implemented before the test; building any of them before E1–E3 report converts the probe into a demo of its own conclusion |
| Benchmark runner (beyond the checklist + snapshot script) | **wait** — v1 concern if v0 survives |

Net: two documents-plus-one-script for E1, one script plus documents for E2, test-pattern extensions for E3-A, prompt files for E3-B. The correct instrumentation is, as suspected, extremely small.

---

## 10. Normal lab work

- An ordinary session is **unchanged** until its close: then ≤3 minutes of intervention confirmation (§2). The operator maintains the log; nothing else is added to the daily loop.
- Benchmark work is batched: snapshot construction and lesion planting in one or two dedicated sessions; runs launched in one block; scoring in one block. E3-B trials are single prompts and can fill idle time.
- Isolation: all E1 material lives in the private ledger repo; all E2 material in the private fork; E3-A tripwire extensions are the only public-tree additions and they follow the tree's existing test idiom (they are lab improvements on their own merits — the compiler-department standard: reviewable independent of the experiment). E3-B materials stay in the private fork.
- **Abort criteria**, any one sufficient: logging exceeds ~5 min/session for a week; experiment prep exceeds ~20% of lab time across the month; any change to `zeta/`, `ontology/`, `harness/`, `dossier/` is motivated *solely* by the experiment; or the operator notices sessions being steered to generate loggable events (the observer effect the zero-line convention exists to resist).

---

## 11. Decision tree after E1–E3

| Observed result | Next action |
|---|---|
| E1: ≥⅔ of interventions `judgment-only`/`owner-authority`; reclassification agreement low | **Stop** the product line of inquiry; keep the log as documentation; the operator is the method |
| E2: C ≈ D (both beat A) | **Keep as documentation** — the transferable asset is prose discipline; write it up as a public methods doc; no software; E3-A tripwires kept as ordinary lab tests |
| E2: D beats A strongly but not C | Same as above, plus **tiny internal tool** consideration limited to whatever specific lesion classes D alone caught |
| E2: D beats C (and A) per §7 thresholds, both families | **Run E4** (outside-team battery/adoption test); dossier department admission attempt per docs/19 §6 becomes legitimate |
| E3-A works, E2 resumption shows nothing | **Tiny internal tool**: generalize tripwires as ordinary tests; nothing more |
| E3-B: typed support fails to prevent flattening | Kill the "composition without semantic flattening" product constraint; `Support` stays as internal discipline; downstream consumers need enforcement, not types — record it |
| Results vary primarily by model family, not condition | **Stop**: state carriage is dominated by model capability; durable-representation thesis loses to "use a better model"; log it in ROADMAP |
| Promising but underpowered (tie zone) | One revised **v1** with binding thresholds (§7.8); no other action until it reports |
| E1 procedural share high AND E2 D-beats-C AND E3 both pass | E4, then and only then **sibling probe**; customer discovery remains gated behind E4's outcome |

No path in this table leads directly to customer discovery, a company, or a general runtime.

---

## 12. Implementation sequence (for review — not implemented)

Order matters; item 2 must precede item 6.

1. **`conjectures/INTERVENTIONS.md`** (private ledger repo) — schema, taxonomy, worked example (`f47a490` as the calibration case). Small. No scientific machinery touched. Deletable.
2. **E2 snapshot freeze** — record the chosen HEAD hash in the prereg doc. Trivial. Must precede E3-A.
3. **`conjectures/interventions.jsonl` + validator script** (private ledger repo). Small. Deletable.
4. **Private fork + `make_snapshots.sh`** — builds A/C/D worktree exports from the frozen HEAD, applies the per-condition removals and the NOTES.md compression procedure. Medium. Touches nothing public. Deletable.
5. **Lesion planting + answer key** (private fork; consultant plants 2). Medium — the only conceptually demanding item; each lesion is a small edit but the answer key must state the correct diagnosis and the scoring boundary between 1 and 2. Deletable.
6. **Prereg document** (§7, verbatim, hash recorded; both the owner and consultant sign before any run). Small.
7. **E2 runs + scoring** per checklist. Small mechanically.
8. **E3-A tripwire extensions** (public tree, `tests/`) — the one public change; each tripwire justified as an ordinary lab test on its own merits, in the existing idiom. Medium-small. *Not* cleanly deletable, deliberately: if the experiment dies, good tests remain — which is the correct asymmetry.
9. **E3-B profile prompts + trials** (private fork). Small. Deletable.
10. **Disposition** written into ROADMAP.md the way hunt dispositions are written, whatever the outcome.

Everything except item 8 deletes cleanly; item 8 is intended to survive.

---

# PROPOSED EXPERIMENT CONTRACT

**Question.** Is a meaningful part of this laboratory's operating discipline carried by transferable artifacts and machinery, or mainly by the operator's unstated judgment? Three sub-questions: (E1) what does the operator actually contribute, and how much of it is legible from artifacts alone; (E2) does the repository's structured state let a fresh agent resume better than casual notes (C vs A) and does typed machinery add anything over disciplined prose (D vs C); (E3) can staleness be detected mechanically without falsity propagation, and does typed support reduce semantic flattening downstream.

**Will be built.** An intervention log (JSONL + schema doc + ~40-line validator) in the existing private ledger repo; a private fork carrying three condition snapshots of one frozen HEAD, eight history-derived planted failures (two authored by the consultant), an answer key, one prompt template, and a scoring rubric; 8–10 staleness tripwire tests in the public tree, each justifiable as an ordinary lab test; 8 support-profile prompts for the flattening trials. One snapshot script, one checklist.

**Will not be built.** No CLI, no runner beyond a script and checklist, no dashboards, no typed Session/Decision/Intervention/Artifact/Warrant objects, no dependency graph, no battery versioning, no sibling repository, no product code of any kind. Building any of these before results exist is defined by this contract as contaminating the experiment.

**Primary measurements.** E1: intervention rate and mechanizability-class distribution, double-classified (operator at capture; blind agent from artifacts later). E2: median planted-failure detection score per condition per model family (secondary: re-litigation, unwarranted promotion). E3-A: tripwire detection with zero automatic status rewrites. E3-B: flattening rate, typed format vs boolean.

**Success.** E2, in both model families: median D ≥ A + 3 and D ≥ C + 2 (of 16), no secondary reversal. E3-A: full detection, zero rewrites. E3-B: typed flattening ≤ half the boolean rate. E1: informative regardless of direction, with ≥15 events.

**Failure.** D ≤ A in either family (machinery adds nothing); or C ≥ D in both (the asset is prose, not software); or typed support flattens at the boolean rate; or E1 shows ≥⅔ judgment-only with low artifact-legibility. Ties are exploratory: one revised v1 with binding thresholds, then no more.

**Forbidden until results exist.** Creating a sibling product repository; customer discovery; admitting the dossier department; any commercial framing in the public tree; implementing any typed governance object; changing `zeta/`, `ontology/`, `harness/`, or `dossier/` for experiment-only reasons; revising thresholds after data.

**Authority.** The owner holds all go/no-go decisions, signs the pre-registration before any run, and adjudicates scorer disagreements under the pre-registered rules. The consultant reviews this contract, authors two lesions, and may serve as a second scorer; neither the consultant nor any coding agent may promote a result, alter thresholds, or initiate any forbidden action. The laboratory's scientific objective is unchanged, and any conflict between the experiment and normal lab work is resolved in the lab's favor, up to and including aborting the probe.
