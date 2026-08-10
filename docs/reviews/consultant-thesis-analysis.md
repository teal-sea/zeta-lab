# Blind Analysis: Productization Thesis vs. zeta-lab (HEAD 5533896)

*Independent repo-side analysis, performed without seeing another model's prior evaluation. Grounded directly in git history and current file contents as of 2026-08-08.*

---

## A. Current-head facts

HEAD is `5533896` on `main`, clean except untracked scratch (`analysis.md`, `interactive_lab/`, `lean/Scratch*.lean`, `scratch/`). One untracked file, `analysis.md` (today, 14:48), may be the other model's evaluation; per the blind-analysis instruction I did not open it. 136 commits on `main`. The sibling repositories named in the thesis (four private repos of the operator's, names redacted) are **not locally present**; every cross-repo pattern below is flagged as unverified where it relies on them. One adjacent project *is* locally present: a private market-diligence repository of the operator's (path, name and document titles redacted), whose `CLAUDE.md` carries standing laws directly relevant to this thesis — I cite it where used.

**Implemented behavior (code, runs today):**

- **Battery/Department admission control.** `harness/protocol.py:381-433` (`battery_reasons`) refuses a battery with no rival, neither decoy nor surrogate, or no lesion; `department_reasons` (`protocol.py:502-535`) additionally requires reference claims in *both* directions. Three departments registered (`harness/departments/__init__.py:21-25`: `zeta`, `finitefield`, `compiler`). `tests/test_department_conformance.py` is parametrized over that dict; `test_a_claim_true_of_everything_distinguishes_nothing` (line 94) and `test_every_reference_claim_earns_its_declared_verdict` (line 123) re-derive verdicts rather than trusting labels.
- **Candidate lifecycle.** `ontology/`: five candidate kinds with decision procedures, six verdict states with enforced entry criteria (`survives` requires `checks_run ⊇ {known, trivial, refutation}`, `verified_effort > effort`, and a `proof_gap` — ontology/README.md §2), provenance sufficient for a stranger to re-derive (§3), append-only ledger, and a funnel that "will not promote anything to `survives` on its own authority" (§8.3).
- **Typed, non-collapsing verification.** `dossier/status.py`: four axes; `Support.__bool__` raises (`status.py:179-184`); `STATED_UNCHECKED` added when reality forced it (`status.py:100-117`). Assertion-with-no-artifact is refused (`support_reasons`, `status.py:205-227`).
- **Typed staleness, micro-scale.** `tests/test_dossier_hardy_z.py:276-309` is a working staleness tripwire: a `stated-unchecked` formal record contradicted by a wired root build fails a test that "reads text files only, so no missing toolchain can switch it off." `OpenQuestion.resolution` (`dossier/schema.py:176-201`) is the same mechanism one level up, added after a real 3-hour staleness incident.
- **Errors as data, not passes.** `run_battery` records a raising rival in `errors` and refuses to count a crash as a refutation (`protocol.py:594-618`), which caught a real over-promotion on day one (ROADMAP.md:269-277).

**Structurally enforced behavior:** the seam (AST scan + `sys.modules` subprocess + lexical scan) on `harness/protocol.py`, `ontology/*`, `dossier/*`; department audits turned on by listing; hunt vocabulary pinned by `tests/test_hunt_probe_discipline.py`.

**Documented protocol (convention, not code):** "a hunt may propose a candidate … may not promote its own claim" (hunts/README.md, may/may-not table); the reserved word *certified*; ROADMAP.md as the decision ledger ("stated so they are not re-litigated"); HANDOFF.md as the session handoff; MISSION.md per hunt/worktree (`hunts/*/MISSION.md`); the review flywheel (ROADMAP.md:359-367).

**Observed human workflow (recorded in prose, not typed anywhere):** Hunt #2's "verified" headline reached HANDOFF.md and was withdrawn *by review* (ROADMAP.md:432-464); the sham finite-field battery was staged for admission and caught *by review*, explicitly because "the structural audit catches missing instruments, not empty ones" (ROADMAP.md:514-521; commit `431cc74`); the scope-drift commit ("proof by construction") entered the tree and was reconciled later at the owner's direction (HANDOFF.md:42-51, 158-167); a register correction came from the owner (`f47a490`); a probe's own instruction was overridden on review ("renamed, not deleted", ROADMAP.md:586-589). ROADMAP.md:384 states outright: *"the operator loop plus the recorded decisions in this file are the adaptive component."*

**Projections / consultant vocabulary with no in-tree counterpart:** `Investigation`, `Session`, `Decision` (as typed objects), `Typed Warrant` (as a portable object — the dossier's `Support` is the nearest thing and is deliberately not portable), authorization/approval semantics (zero occurrences in `harness/`, `ontology/`, `dossier/` code; "owner" appears 4 times in prose repo-wide), an intervention ledger (does not exist — see D), and everything commercial. **One inaccuracy to correct:** the consultant's examples treat "promotion" as one problem; this tree separates at least three admissions with different mechanisms (see D), and its ledger (`conjectures/ledger.jsonl`) records candidates and runs, not operator interventions — I verified the actual JSONL contents.

---

## B. Strongest case for

The repository-grounded case, without the phrase "AI institution":

1. **The promotion rule already exists three times in independent forms, which is what convergence looks like.** The funnel refuses self-promotion to `survives` (ontology/README.md §8.3). Hunts may propose and may not promote (hunts/README.md). The vocabulary is governed (*certified* has one owner). And that adjacent private repo states the identical rule for a completely different subject: "Agents that produced a finding never judge it" and proposals labeled `[OWNER]` vs `[CLAUDE — PROPOSAL]` (its own `CLAUDE.md`, research standard + standing law 3). The same operator independently reinvented "agents may propose anything; they may not promote their own proposals" for mathematics research and for market diligence. A rule that recurs across two unrelated subjects under one operator is at least a candidate for extraction.

2. **The referee-under-test discipline is genuinely unusual and already domain-transplanted twice — measured, within one repo.** Eval harnesses test the subject; this tree tests the *tester*: both-direction reference claims re-derived (`test_department_conformance.py:123-150`), lesions with magnitudes so blindness is a number not an assumption (compiler FINDINGS §5: `blind_to = ('nsw_flag_on_a_wrapping_shift',)`, magnitude 0.5), and shams caught (`431cc74`). The protocol survived a decidable-property subject and a foreign-vocabulary subject with zero changes to `protocol.py` (ROADMAP.md:592-606) — and the one shared-audit change it forced was a *strengthening* (the `probe` convention catching identity lesions, compiler FINDINGS §13.2).

3. **The failure the product would prevent has already haappened here, twice, with cost.** Hunt #2's unsupported "verified … definitively" reached the authoritative handoff; the certified arm's cross-check was silently off for the repo's whole life until 2026-08-07 (ROADMAP.md:466-498). Both are exactly the consultant's GATE examples ("an agent closes an incident using an unreplicated theory"; "a structurally passing but substantively empty evaluation"), instantiated in a repository *purpose-built to prevent them*. If it happens here, it happens everywhere.

4. **The benchmark the consultant proposes is the repo's own recorded next step.** docs/19 §6 already specifies what would make dossier a department: subject = *representations of research state*, rival = "a flat notes file plus a `verified: bool`", "measured on a resumption task the dossier claims to do better" — that *is* the Lab Rotation Benchmark, written down here before the consultant proposed it. Convergent design from inside and outside is the strongest available signal that the object is real.

5. **The typed-warrant idea has an existence proof with a earned scar.** `STATED_UNCHECKED` exists because a single `verified` boolean could not honestly describe a real situation (docs/19 §5b.1); the staleness tripwire exists because a record actually went stale for 3 hours (test_dossier_hardy_z.py:277-296). These aren't speculative semantics; each was forced by an incident.

---

## C. Strongest case against

1. **The human is the substance, and the tree says so in its own voice.** Every consequential catch in the record was made by review, not machinery: the sham battery ("emptiness was caught here by review", ROADMAP.md:520-521), Hunt #2's withdrawal, the renamed-not-deleted test, the conformance change "reviewed on its own merits rather than because a candidate needs it" (compiler FINDINGS §11.2). ROADMAP.md:384 names the operator loop as the adaptive component. The layer the consultant most wants to sell — admission of *substantive* promotions — is exactly the layer this repo has measured to resist mechanization: structural audits pass hollow instruments; a hollow instrument is caught only by someone who understands the subject. Compiler FINDINGS §8 states it as a standing fact: "admissible" and "has a working detector" are independent, and only the first is enforced.

2. **Batteries are bespoke and expensive, and the three existing ones prove it rather than refute it.** The zeta battery took a mathematics laboratory; the finite-field battery required knowing Hasse's theorem quantizes lesion magnitude (ROADMAP.md:528-535); the compiler battery required building a poison-aware interpreter and cross-checking it against compiled output (FINDINGS §13.1). The consultant concedes this (Battery Foundry), but then the "product" is a services business with a thin runtime — ~700 lines of `protocol.py` plus conventions. The moat candidate is methodology, and methodology leaks.

3. **All three departments were authored "in the same repository by the same process against the same protocol" — the repo's own known gap #1 (ROADMAP.md:592-606).** There is zero evidence of outside adoption. `docs/doors/adopt.md` exists and has, as far as this tree records, never been walked through by anyone but the author. Transplantation — the whole product question — is exactly the untested axis.

4. **Adjacent categories cover pieces.** Eval platforms cover "does the check run and pass"; workflow/CI covers "no merge without the check"; agent-memory products cover persistence; governance products cover approvals. The residue this tree adds — referee calibration, typed non-collapse, staleness-not-falsity — is real but narrow, and the burden is on the thesis to show that residue carries purchase decisions rather than admiration.

5. **Paperwork risk is real and the tree has felt it.** The dossier's own known gap: "one example and no evidence that it helps … nobody was about to define Z as `|zeta(1/2+it)|`" (ROADMAP.md:607-612). The honest current summary of the flagship state-representation experiment is "one schema, one example, no evidence it helps" (docs/19 §7). A product built now would ship the unproven part.

6. **Domain favorability.** Mathematics, finite fields, and an 8-bit compiler subset are unusually verifiable: exact oracles, cheap exhaustive enumeration, a literature. The consultant's GATE customers (customer service, incident response, experiments) have noisy oracles, contested ground truth, and organizational politics. Nothing in this tree bears on that regime.

7. **The whole thing may reduce to an unusually disciplined operator plus Git.** HANDOFF.md and ROADMAP.md are prose; they work; the recorded failures (Hunt #2, scope drift) were failures *of the prose channel* that were also *repaired through the prose channel*. Perhaps the fix is "write better handoffs," cost zero.

---

## D. Reusable primitive

**The Battery protocol is not the complete primitive.** It adjudicates one question — *is this demonstration about its subject at all?* (harness/README.md, "What this is not") — and deliberately not truth, not promotion, not authority. It contains no staleness, no session, no approval, no warrant portability (verified: zero matches for authorization/session concepts in the three packages).

**The tree contains three distinct admissions, and the rival hypothesis ("it's all already covered") is true for two of them and false for the third:**

1. *Candidate admission* (funnel) — **covered**, thoroughly (ontology).
2. *Department/battery admission* — **covered structurally**, with the measured caveat that structure catches missing, not empty; emptiness is human (`431cc74`).
3. *Institutional state-transition admission* — claims entering HANDOFF.md/ROADMAP.md/README.md, merges, scope changes, handoff integrity — **not covered by machinery.** It is covered by convention plus review, and the two worst recorded incidents (Hunt #2's headline; the scope-drift commit `4c7e480`) were both failures on exactly this layer. The consultant's mismatch begins precisely here.

**Direct answers to the six questions:**

- *Is the existing Battery protocol the complete primitive?* No — one component: the referee-calibration component.
- *Is it one component of a wider primitive?* Yes. If the wider primitive deserves a name, it is **calibrated promotion discipline**: no claim, instrument, or status change promotes itself; every promoter must be shown able to fail (both directions, lesions); support types never collapse; upstream change makes support stale, not false. Parts exist in code, parts only in convention.
- *Is the wider primitive consultant-invented abstraction?* Partially. `Warrant` ≈ `Support` (exists). Typed staleness — exists at micro scale with one incident justifying it; missing at repo scale. `Handoff` — exists as prose with one recorded integrity failure (a datum *for* typing it). `Decision` — ROADMAP.md in prose, works, no demonstrated loss yet. `Session`, `Investigation`, authorization — no counterpart, no demonstrated need; unearned until the benchmark shows prose loses something.
- *Does `conjectures/ledger.jsonl` represent operator interventions?* **No.** I read it: candidate and run records only (`{"kind": "constant", "claim": {...}, "provenance": {...}}`). Operator interventions exist solely as narrative in ROADMAP.md/HANDOFF.md/commit messages. The consultant's intervention ledger is not a duplicate of anything.
- *Would a Lab Rotation Benchmark honestly qualify as a Department today?* Not today — no built instruments, no scoreable task. But it is the one proposed department that would *not* violate "a department whose battery is another department's battery is not a department," because its subject would be representations of research state, with rivals (flat notes + `verified: bool`), decoys (shuffled/emptied dossier fields), surrogates (generic boilerplate handoffs), and lesions (planted stale statuses, conflicting handoffs — several already exist as real history to replant). The repo designed exactly this in docs/19 §6 and ROADMAP.md:314-318. It is the legitimate admission path.
- *Are Decision, Session, authorization, typed staleness genuinely missing or bureaucracy?* Typed staleness: genuinely missing at repo scale, with a working micro-mechanism to generalize and a measured incident as baseline. Handoff integrity: genuinely missing, one incident. Authorization: missing but low-frequency here (one operator); machinery now would be paperwork ahead of evidence. Session/Decision objects: bureaucracy until a scoreable resumption test shows prose loses something specific.

What this does that eval/fact-check/memory/governance products do not: it tests the referee (both directions, quantified blindness), forbids semantic flattening structurally (`Support.__bool__` raises — a *runtime error* for the careless consumer, not a guideline), and treats invalidated upstream artifacts as staleness rather than falsity. That distinction is defensible. Whether it is *purchasable* is undetermined by anything in this tree.

---

## E. Human-operator extraction

Proposed event schema — one JSONL record per intervention, written at session end (the review-flywheel pattern, ROADMAP.md:359-367, extended to the operator). Fields for every event: `event_type`, `session_ref` (branch/commit span; commit hashes are the session objects this repo already has), `model`, `what_prompted_it` (one sentence), `artifact_touched` (path), `would_machinery_have_caught_it` (`existing-test` / `plausible-check` / `judgment-only` — the load-bearing field), `outcome`. **Not recorded:** chain-of-thought, prompts, anything about the mathematics itself, anything that takes >2 minutes to write — if logging costs more than the intervention, the log dies and deserves to.

Event types, classified from the interventions already visible in this tree's history:

| Event | Precedent in tree | Classification |
|---|---|---|
| claim language weakened / promotion denied | Hunt #2 withdrawal; `f47a490` register fix | **assistable** (vocabulary scans automate the detection; the verdict is human) |
| battery rejected as ceremonial | sham battery, `431cc74` | **domain-expert-only** (the measured finding: structure can't see emptiness) |
| stale artifact noticed | 3-hour dossier incident | **automatable** (the tripwire pattern already works) |
| handoff corrected / conflicting handoffs | HANDOFF.md addendum correcting §1 | **assistable** |
| scope change disguised as continuation | `4c7e480` | **assistable** (diff-against-charter checks are plausible); final call **owner-authority-only** |
| rejected approach re-attempted | ROADMAP "not re-litigated" sections | **automatable** in detection (settled-decision index), human in adjudication |
| stronger backend demanded | python-flint pin (ROADMAP.md:466-498) | **automatable** (backend checks are already code) |
| missing evidence requested / fact-vs-inference split demanded | pervasive | **assistable** |
| merge approve/reject, owner decision required | PR #1, adjacent-repo laws | **owner-authority-only** |
| "instrument was never invoked" noticed | `online_list_is_complete` absent from hunts/ | **automatable** (call-site scan) |

Avoid manufacturing process: log only interventions that actually occurred; no quotas; a session with zero interventions logs nothing. **Dataset size:** ~20–30 real sessions — this repo has run roughly that many since 2026-08-01 (136 commits, multiple sessions/day), so one month of continued work suffices. **Evidence the repository carries the method:** a fresh agent, different model, no prior conversation, detects planted failures at a rate comparable to the operator's recorded rate, using only the tree (condition C/D of the benchmark). **Evidence the human carries it:** interventions cluster in `judgment-only`; detection collapses whenever the operator's session framing is withheld; different models produce wildly different intervention rates on identical states.

---

## F. Product wedge

My call modifies the consultant's trio: **kill GATE as the first build, accept a narrowed Battery Foundry as the eventual wedge, treat BENCH as internal research until the benchmark reports.**

GATE-first fails on this tree's own evidence: its value is the battery's substance, batteries are bespoke (three worked examples, all expensive), and the substance-check resists mechanization (§C.1). Shipping GATE without Foundry ships an empty pipe.

The narrowed wedge, if commercialization is ever tested: **forward-deployed referee engineering for teams whose agents modify code**, because that is the one domain where this tree proves batteries are constructible against an executable oracle at low cost — department #3 was built in two sessions with *no LLVM tooling installed* (compiler FINDINGS §1). First buyer: a platform-engineering lead already burned by an agent-merged regression — the budget exists as "AI code review / CI spend," the failure is costly and already digital (diffs, test logs, CI records), and the minimum workflow is: we build the rival/decoy/surrogate/lesion set for their merge gate, calibrate it in both directions, and hand them the conformance suite that re-derives its verdicts in CI. The human stays as the promotion authority; the machinery only refuses and reports. Value measure: prevented regressions caught by the battery that their existing suite missed, and — the differentiated number — *measured detector blindness* ("your review process is blind to lesion class X at magnitude Y"). Continued payment: batteries rot (lesion classes drift with their codebase); the conformance suite re-run is the subscription. Why not custom eval consulting: an eval measures the agent; this instruments and calibrates *their referee*, and ships the audit that keeps it honest. **Do not build first:** any universal `/verify` endpoint, any confidence score, any cross-domain schema, any autonomous steward.

Stated plainly: nothing in this repository evidences willingness to pay. The wedge above is the most defensible shape *if* the internal experiments survive; it is not a recommendation to start selling.

---

## G. Minimum product probe

The smallest build testing the thesis is **not a runtime**. Two artifacts:

1. **The Lab Rotation Benchmark harness** (inside zeta-lab, as the dossier department's admission attempt): a frozen tree state; 6–10 planted failures taken from *real history* (the 3-hour stale formal status; Hunt #2's withdrawn claim left in an old HANDOFF revision; the sham battery restored; the missing python-flint backend with its green-looking "5 skipped"; a settled dead end from ROADMAP re-baited; a scope drift like `4c7e480`; two conflicting handoff addenda — the tree has already produced every one of these organically); fresh agents under conditions A–D; a scoring script. Reuses: `dossier/` as condition D's machinery, `harness/protocol.py` unchanged as the battery frame, hunts/MISSION.md as the session frame. Manual: authoring the frozen state and adjudicating scores. Logged: per-condition detection, repetition, promotion-language violations, interventions needed. Output: one scorecard per condition.
2. **The intervention ledger** (schema per §E), running alongside normal lab work.

Domain-specific and staying that way: the planted failures. Human approvals: the owner freezes the state and approves the scoring rubric before any run (pre-registration — the ninth-increment contamination, ROADMAP.md:785-792, is this repo's own lesson on choosing gates after seeing values). Success after three "deployments" (three benchmark rounds across ≥2 models): condition D beats condition A on planted-failure detection and non-repetition by a pre-registered margin, and the intervention ledger shows ≥⅓ of interventions in `automatable`/`assistable`. **What would reveal no reusable software core:** condition C (conventions alone, prose) ties condition D — meaning the discipline transplants as *documents*, and the product is a methodology pamphlet, not software.

---

## H. Objective experiments

Ordered cheapest → most expensive. All thresholds to be pre-registered with the owner before first data (non-negotiable given ROADMAP.md:785-792).

**E1 — Intervention ledger.** *Hypothesis:* ≥⅓ of operator interventions are procedural (automatable/assistable), not domain judgment. *Setup:* §E schema, 20–30 sessions, written at session close. *Baseline:* none needed — this is instrumentation. *Metric:* distribution over the classification field. *Pass:* ≥⅓ procedural with ≥15 events total. *Kill/narrow:* if ≥⅔ land `judgment-only` or `owner-authority-only`, BENCH narrows to a checklist and the steward vision dies. *Confounders:* self-report bias (the operator classifies their own interventions); mitigate by having a later fresh agent re-classify from the artifacts alone. *Exercises:* the review flywheel. *Location:* inside zeta-lab (a probe directory; touches no core package).

**E2 — Lab Rotation Benchmark v0.** *Hypothesis:* structured state (D) materially beats flat notes (A) on resumption. *Setup:* §G. *Rival:* conditions A (NOTES.md), B (transcript), C (conventions/prose). *Metrics:* planted-failure detection rate; rejected-work repetition; unsupported promotions in output language; cross-model resumability. *Pass:* D > A by pre-registered margin (suggest: ≥2× detection, ≥half the repetitions) on ≥2 models. *Kill:* D ≤ A → product semantics die; D ≈ C → the transplantable thing is prose discipline, software thesis narrows to the tripwire pattern only. *Confounders:* planted failures authored by whoever authored the machinery (an outside person should plant at least two); agent familiarity with this public repo from training data (use a private fork state). *Exercises:* dossier, HANDOFF conventions, hunt discipline. *Location:* inside zeta-lab — it is literally docs/19 §7 items 2+5.

**E3 — Typed staleness at repo scale + careless-consumer test.** *Hypothesis:* the tripwire pattern generalizes beyond one dossier, and typed support actually prevents flattening downstream. *Setup:* generalize the text-reading tripwire to ~10 artifact→status couplings; separately, hand agents a harness `distinguishes=True` verdict and a `Support` object and ask them to summarize. *Rival:* the same artifacts with a `verified: bool`. *Metric:* staleness detection latency vs the 3-hour incident baseline; rate at which summaries write "proved"/"verified" from non-formal support. *Pass:* tripwires catch planted invalidations in-session; flattening rate with typed support is measurably below the boolean rival's. *Kill:* if agents flatten typed support into "verified" at the same rate as the boolean — the semantics don't survive contact with the consumer, and the "composition without semantic flattening" constraint is decoration. *Exercises:* `dossier/status.py`, the tripwire tests. *Location:* zeta-lab.

**E4 — Outside battery authorship.** *Hypothesis:* someone who is not this operator can build an admissible, non-sham battery from `harness/README.md` + `docs/doors/adopt.md` alone. *Setup:* one external person, subject of their choosing, no help beyond the docs; then this side audits for emptiness (the sham test — the audit the structure can't do). *Rival:* the null outcome is forward-deployed help being required. *Metric:* admissible battery, zero protocol changes, sham-audit passed, wall-clock. *Pass:* admissible + non-sham within ~2 sessions of effort. *Kill/narrow:* if it takes forward-deployment, the software thesis narrows to Battery Foundry services; if their battery is a sham *they believe in*, the methodology does not transplant as documents at all. *Exercises:* known gap #1 (ROADMAP.md:592-606) — this is the exact experiment the gap calls for. *Location:* sibling probe (outside zeta-lab; zeta-lab only receives the resulting PR-shaped evidence).

**E5 — Customer pilot.** Only if E1–E4 survive. *Hypothesis:* a team pays for a calibrated referee on agent-produced code changes. *Setup:* §F wedge, one design partner. *Metric:* prevented failures their existing gate missed; renewal. *Pass:* one renewal at a price above delivery cost. *Kill:* prevented-failure count ≈ 0, or value attributed entirely to the humans we embedded. *Location:* entirely outside both repos.

---

## I. Kill conditions

- **No product exists:** E2's condition D ≤ A, and E3's flattening test fails. What remains is a well-run repo.
- **Only consulting exists:** E4 requires forward-deployment *and* E5 renews only with embedded humans.
- **Useful internal tool, no company:** E2 passes but E4 fails — the machinery helps this operator and transplants to no one.
- **Narrow product:** E2, E3 pass; E4 passes only in executable-oracle domains (code, math) → a referee-calibration product for agent code changes, nothing wider.
- **Broader platform might exist:** E4 passes in a *non*-executable-oracle domain — the one observation that would genuinely surprise me given this tree.
- **Kill the public/scientific knowledge vision:** if E2 shows cross-model resumability is dominated by model capability rather than repository state (condition B ≈ D across models), durable research packages add nothing over transcripts.
- **Kill the flywheel:** it is two hypotheses (enterprise pressure → rigor; rigor → enterprise value) with zero supporting observations in either repo today; it should not merely be killed on failure — it should be ignored until E5 exists, because no cheaper experiment bears on it.
- **The existing Battery protocol is sufficient:** if E1 shows interventions are dominated by "battery rejected as ceremonial"-type events and E2's planted failures are all caught by condition C — then convention + battery is the whole system and no new semantics are justified.
- **New product semantics justified:** E2 passes with the margin specifically attributable to typed state (D beats C, not just A), and E3's tripwires catch what prose missed.

---

## J. Scope and governance

**Recommended relationship: bounded internal probe (E1–E3) inside zeta-lab + one recorded strategic option; no sibling repo yet; no commercial motion.**

- **ROADMAP.md:** at most one short section, written by the owner or explicitly `[PROPOSAL]`-labeled, recording: the option exists, E1–E3 are the probes, and the dossier department's admission path (docs/19 §6) is the vehicle. E2 belongs in ROADMAP anyway — it was already promised there before any consultant appeared (ROADMAP.md:314-318).
- **Outside the repository:** all commercial material, customer conversations, E4, E5, and the flywheel speculation. Nothing about buyers enters this tree; the lab's public record should not carry an unverified business thesis for the same reason `conjectures/` is private.
- **Authority this coding agent does not have:** creating sibling repos, altering the Phase II objective, admitting the dossier department without the benchmark, adding product framing to public docs, or presenting any of this analysis as decided. (Nothing was modified during this analysis; this report is terminal-only.)
- **Owner's decision:** whether E1's logging overhead is acceptable; the pre-registered thresholds; whether E4's external person exists; whether anything commercial ever starts.
- **Scope-drift protection:** the probes enter as probes under the existing classification (hunts/dossier precedent); the standing rule "a probe that bypasses the battery has produced no result" (ROADMAP.md:459-464) applies to the product thesis itself. Dogfood inversion — the lab serving a product roadmap — is prevented by one test: any change to `zeta/`, `ontology/`, `harness/` justified *only* by product needs is refused. The compiler department's precedent is the model: the shared audit changed only when the change was a strengthening reviewable on its own merits.

---

## K. Final call

**Run a bounded internal probe: E1 (intervention ledger) + E2 (Lab Rotation Benchmark) + E3 (staleness/flattening), inside zeta-lab, pre-registered, 30–60 days. No sibling repo, no commercial motion, until E2 reports.**

- **Confidence:** 70%.
- **Strongest supporting fact:** the benchmark the thesis needs is the repo's own already-recorded plan (docs/19 §6, ROADMAP.md:314-318) — the probe costs almost nothing beyond work the lab already owed itself.
- **Strongest opposing fact:** every substantive catch in this tree's history was made by human review, and the tree says the operator loop is the adaptive component (ROADMAP.md:384, 520-521) — the probe may simply confirm the human is the product.
- **Fact that would reverse me:** an outsider (E4) building a non-sham battery from the docs alone in a non-code domain — that would justify jumping straight to a sibling product probe. Conversely, condition C tying condition D in E2 would downgrade my call to "record and observe only."
- **30-day sequence:** week 1 — owner approves/edits the intervention schema and pre-registers E2 thresholds; weeks 1–4 — log interventions during normal lab work; weeks 2–3 — freeze the benchmark state, plant failures (≥2 planted by someone other than the machinery's author), write the scorer; week 4 — run conditions A–D on two models, score, write the disposition into ROADMAP the way hunt dispositions are written.
- **First thing the owner should do:** pre-register the E2 pass/kill thresholds in writing before any benchmark data exists.
- **First thing the owner should not do:** create the sibling repo. A repo is a commitment device, and this thesis has not yet survived its own battery.

---

# REPLY TO EXTERNAL CONSULTANT

I ran your thesis through this repository's own method — grounded at HEAD `5533896`, files and history inspected directly, your framing deliberately not taken as authoritative. Here is where you are right, where you are wrong or premature, and what we will do.

**Where you are right.** Three things, each verifiable in-tree. First, your central rule — agents may propose, may not promote their own proposals — is not a product idea we lack; it is a rule this operator has now written independently at least three times: the funnel refuses self-promotion to `survives` (ontology/README.md §8.3), hunts may propose and may not promote (hunts/README.md), and a second repository of ours states "agents that produced a finding never judge it" for market diligence. That convergence is the best evidence in your favor. Second, you are right that institutional state-transition admission is a distinct layer and that it is where our machinery stops: our two worst recorded incidents — an unsupported "verified … definitively" reaching the authoritative handoff (Hunt #2), and a scope-drift commit rewriting the honest-scope rule — both happened on exactly that layer, and both were caught by human review, not by anything structural. Third, "staleness, not falsity" and "composition without semantic flattening" are not inventions of yours; they exist here at micro scale with scars to justify them (`Support.__bool__` raises; a formal-status record went stale for three hours and now has a text-reading tripwire test that would catch the recurrence).

**Where you are wrong, redundant, or premature.** Your redundancy worry is half right, so let me answer it precisely. Candidate admission and department admission are fully covered — `Candidate`/verdicts/ledger and `Battery`/`validate_battery`/conformance do what your Investigation/Claim/Challenge objects would do there, and better than a rename would. `conjectures/ledger.jsonl` does **not** represent operator interventions — I read it; it holds candidate and run records only — so your intervention ledger duplicates nothing. But your wider object model is mostly unearned: `Session`, `Investigation`, `Decision` as typed objects have no in-tree counterpart *and no demonstrated need* — our decision record is prose (ROADMAP.md) and it demonstrably works, including surviving disagreement and correction. `Warrant` already exists as the dossier's four-axis `Support`. Authorization semantics are premature for a one-operator lab. And your nearer commercial wedge, GATE, is upside down on our evidence: the value of any gate is its battery's substance, our three batteries were each expensive and bespoke, and the one failure mode structure cannot catch — a battery that is hollow rather than missing — was caught here only by domain review (the sham finite-field battery, commit `431cc74`). GATE without Foundry is an empty pipe; you concede this and then still rank GATE first. Rank it last.

**The decision.** Bounded internal probe; no sibling repo yet; nothing commercial. Specifically: (1) an intervention ledger over the next ~20–30 real sessions, with each event classified automatable / assistable / domain-judgment / owner-authority; (2) your Lab Rotation Benchmark, built — and here is the part you should find satisfying — as this repository had already specified before your proposal: docs/19 §6 defines the only honest path by which our dossier probe becomes a department, and it is your benchmark exactly: subject = representations of research state, rival = a flat notes file plus a `verified: bool`, scored on a resumption task, with planted failures drawn from our real history (the stale formal status, the withdrawn claim left in an old handoff, the sham battery, the silently-absent backend); (3) a flattening test — hand agents typed support and a boolean rival and measure who writes "proved."

**Ordered tests and kill conditions.** E1 ledger: if ≥⅔ of interventions are domain-judgment or owner-authority, your BENCH narrows to a checklist. E2 benchmark, thresholds pre-registered before data: if structured state does not beat flat notes by the registered margin on ≥2 models, the product semantics die; if it merely ties *prose conventions*, the transplantable thing is documents, not software. E3 flattening: if agents collapse typed support into "verified" at the boolean rate, your no-flattening constraint is decoration. E4, only after those: an outsider builds a battery from our docs alone, unassisted — if that needs forward deployment, you have a services business; if their battery is a sham they believe in, the methodology does not transplant at all. Willingness-to-pay is tested last and outside both repositories.

**Current reality versus direction, kept apart.** Today: one human operates rotating CLI sessions against a tree that carries an unusually calibrated referee for three subjects authored by that same human, with promotion discipline that is part code, part convention, part review. There is no autonomous steward here, no Igor, and the sessions are not the product. Direction: if the benchmark shows the tree — rather than the operator's unstated understanding — carries a measurable share of the method, a sibling probe with its own charter and kill conditions becomes justified, and its wedge is referee calibration for agent-produced code changes, where our compiler department proves batteries are cheap to build against executable oracles. If the benchmark shows otherwise, what you have found is a disciplined operator, and we will say so in the same ledger.
