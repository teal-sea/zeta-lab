# INSTITUTION-FUTURES.md

*Strategic cartography, 2026-08-13. Companion to `ARCHITECTURE-ARCHAEOLOGY.md`.
The archaeology asked "what is this?"; this asks "what is it trying to become?"
It designs nothing, implements nothing, renames nothing, and resolves no
ambiguity that the evidence leaves open.*

**Evidence discipline.** Every major claim is tagged `[E]` evidence (a file,
test, commit, or measured number), `[I]` inference (derived from evidence, could
be wrong), or `[S]` speculation (mine, unsupported). The archaeology's three
limits still bind: shallow clone (history starts 2026-08-07), four load-bearing
directories are gitignored and empty here, and no suite was run.

**One dependency is declared unresolved throughout.** The operator refers to a
*planned blinded / equal-budget harness evaluation*. **No such evaluation exists
under that name in this repository** `[E]` — I searched for "equal budget",
"equal-budget", "blinded evaluation", "harness evaluation", "matched budget" and
found only one unrelated hit. The nearest in-tree designs are E2/E4 in
`docs/reviews/consultant-thesis-analysis.md` §H and experiment 1 in `docs/20` §8.
I therefore treat the operator's evaluation as an **external, operator-held plan
(possibly in the off-repo futures map, `HANDOFF.md` §"Where the off-repo material
lives")**, mark every harness-dependent decision as gated on it, specify in §12
what it would have to contain to be decisive, and **assume nothing about its
outcome**.

---

## 1. Executive finding

**The three futures are not three destinations. They are one mission, one
hypothesis about that mission's byproduct, and one method for executing either
— and the tree's own records say so more clearly than its front page does.**

- **Future B (mathematics laboratory)** is the only one with a *stated
  objective* in the binding rules file: `CLAUDE.md` §honest-scope names
  "Phase II's explicit Research Objective … produce one externally verified
  mathematical statement that humanity didn't previously know" `[E]`. It is also
  the only one with a live external-facing deliverable (the frontier candidate)
  and the only one whose next action is scheduled (`HANDOFF.md` queue item 0–1).
- **Future A (subject-independent verification framework)** is a *hypothesis
  about a byproduct*: that the referee generalizes. The README leads with it
  `[E]`, and the tree has invested heavily in it — but §7 below shows, by the
  repository's own standards, that **the abstraction layer has never adjudicated
  a single live research claim of this laboratory**, and that the live research
  independently re-implemented the four roles by hand rather than importing them
  `[E]`.
- **Future C (agentic research operating system)** is not a destination at all
  on current evidence; it is an *operating method*, and the tree adopted its
  primitives while explicitly refusing its orchestration `[E: ROADMAP "The
  outside memos, triaged"; docs/26 §6 closing]`. It becomes a third destination
  only if someone decides to make it one, and nothing in the tree has.

**The tension is therefore not architectural. It is budgetary and reputational.**
Architecturally the three coexist without conflict — the seam tests guarantee A
cannot contaminate B, and C is additive. What they compete for is (i) the
operator's scarce judgment, (ii) frontier-model tokens, which `HANDOFF.md`
records as exhausted `[E]`, and (iii) **the front page** — which currently leads
with A's framing while the actual work, the actual queue, and the actual stated
objective are B's.

**The single most important unvalidated claim in the institution is not "the
harness generalizes." It is "the harness does anything."** §7 develops this
against the repository's own admission rule.

---

## 2. The three futures

| | **A — The Instrument Maker** | **B — The Mathematics Laboratory** | **C — The Research Operating System** |
|---|---|---|---|
| One sentence | A subject-independent way to test whether an empirical demonstration is about its subject at all, reusable by anyone. | A very small lab that produces mathematical statements strong enough to survive outside review. | A way of running research in which agents generate and non-model oracles decide. |
| Pulled by | `harness/`, `docs/doors/adopt.md`, 4 non-mathematical departments | `zeta/`, `lean/`, `hunts/frontier_math/`, the certainty ladder | `meta/`, `docs/reviews/`, the 2026-08-11 adopted builds, `automation/` |
| Stated objective in a binding file? | **no** | **yes** (`CLAUDE.md` Phase II) | **no** (charter *adopted as framing*, ROADMAP) |
| Live deliverable today | the 6-department demo | the 0.6725106958 candidate + `zeta23ext` | none |
| Next scheduled action | none | Mathlib Zulip question (HANDOFF queue 0–1) | none |
| Validation status | **unproven** (§7) | partially validated (kernel-checked steps; rung 4 unreached) | **unmeasured** (`docs/26`: "the first time any of them catches something real … is when this document gets its first follow-up section" — no such section exists) `[E]` |

---

## 3. Future A — The Instrument Maker

### 3.1 One plain sentence
A reusable, subject-independent framework that makes refuting a plausible claim
cost minutes instead of days, by forcing every subject to supply controls whose
own power has been measured.

### 3.2 Which subsystem pulls toward it
`harness/` — `protocol.py` (four roles, Battery, Department), `integrity.py`
(19 checks → 5 grades), `shams.py`, `provenance.py`, `independence.py`,
`guards.py`, `graveyard.py`, `review.py`, and the six-department registry.
Secondarily `ontology/`'s domain-agnostic core and `compiler/`.

### 3.3 Strongest evidence it is intentional `[E]`

| Evidence | What it shows |
|---|---|
| `README.md:1-5` — "plus a reusable validation framework for testing whether an empirical claim is about its subject at all" | it is the *third line of the front page* |
| `harness/README.md:7` — "It is deliberately not about ζ" | explicit intent |
| The seam, enforced three ways (AST import scan, `sys.modules` subprocess, lexical vocabulary scan) on `protocol.py` | intent made mechanical, not aspirational |
| `KNOWN_DEPARTMENTS` = 6, of which **4 have no mathematical content** (`compiler`, `croniter`, `referee`, `stateval`) | the tree paid real cost to test generality |
| `docs/doors/adopt.md` — a fifth door for readers who do not care about ζ | audience-level commitment |
| `harness/blind_authoring_2026_08_09/` — 10 independently authored departments, digest-pinned, with a scorer | a genuine adversarial experiment on the framework itself |
| ROADMAP 2026-08-06: "the laboratory extends by *department*, not by directory, and a department is defined by what can refute its claims" | the decision, dated |
| ROADMAP 2026-08-07: "the scarce resource is no longer ideas but **reliable rejection**" | the thesis behind it |
| `docs/reviews/consultant-thesis-analysis.md` §F — an outside-informed wedge ("forward-deployed referee engineering for teams whose agents modify code") | someone has already costed the product shape |

### 3.4 What the institution looks like if A dominates
The mathematics becomes department #1 among many and stops being the headline.
The unit of work is *admitting a subject*, not proving a theorem. The README
becomes a framework front page; `docs/doors/adopt.md` becomes the main door.
Success is measured in **outside adopters** and in **modes the audit catches**,
not in bounds. `zeta/` becomes a very good worked example and a regression
fixture. `lean/` becomes a niche appendix. The natural end states are a library,
a services practice, or a standard — all three of which require an audience that
does not exist yet `[E: known gap #1]`.

### 3.5 Reclassification under A
- **Core:** `harness/protocol.py`, `integrity.py`, `shams.py`, `provenance.py`, `independence.py`, `guards.py`, `graveyard.py`, `review.py`, `tests/test_department_conformance.py`, `tests/test_harness_*`, `harness/new_department.py`, `docs/17,20,21,22,23`, `docs/doors/`.
- **Supporting infrastructure:** `harness/departments/*` (as fixtures), `compiler/`, `harness/blind_authoring_2026_08_09/` (as the held-out corpus), `harness/demo.py`.
- **Experimental:** `promotion.py`/`preregistration.py` (already self-classified KEEP AS PROBE), `dossier/`, `meta/`.
- **Obsolete-ish:** nothing is obsolete, but `hunts/frontier_math/` (~110 files) and most of `lean/` become *content*, not architecture — kept as the worked example that earned the framework, at the cost of a very large repository for a framework whose runtime is ~700 lines `[E: consultant analysis §C.2]`.

### 3.6 What evidence exists that A is *useful*
1. **`docs/17` — five claims died in one day** using the four instruments, "verdict cost collapsed to claim cost." **The strongest piece of evidence in the entire institution for the four *roles*.** `[E]`
2. **The day-one catch:** `zeta.factorization.factorization_defect` would have been promoted to "the decision procedure for Gate 4"; `run_battery` recorded the rival's exception and left `distinguishes` False `[E: ROADMAP; docs/17 §5; pinned in tests/test_harness_zeta_department.py]`. **This is the one recorded instance of the protocol layer itself preventing an over-promotion.**
3. **`docs/22`** ranks RH-equivalent criteria by *measured detection strength* against the Davenport–Heilbronn rival (Li's criterion inert; Weil positivity tunable to −22.4; Mertens explosive) — real research output produced by the rival instrument `[E]`.
4. **Protocol stability across four foreign subjects** with zero `protocol.py` changes, then one deliberate strengthening `[E: ROADMAP known gap #1]`.
5. **`detector-claim-agreement` earns its keep**: catches its planted mutation, catches one blind-authored hollow battery nothing else catches, and catches `docs/21`'s hollow battery `[E: ROADMAP 2026-08-10]`.

### 3.7 What remains completely unvalidated
- **Outside adoption.** Zero. Every department was orchestrated by this process `[E: known gap #1; docs/20 §8 experiment 1, unrun]`.
- **That the *abstraction* adds anything over the concrete instruments.** See §7 — this is the sharp one.
- **That the audit constrains a motivated author.** Measured and **falsified at n=6**: six of six blind authors reached `CALIBRATED` with batteries that measure nothing `[E]`.
- **That a department's grade means anything outside this tree.** `compiler` and `referee` currently grade `DETECTOR_INADEQUATE` and are not exempted `[E]`.
- **Willingness to pay.** "Nothing in this repository evidences willingness to pay" `[E: consultant analysis §F]`.

### 3.8 Strongest argument against pursuing A
**The seam that makes it general is the same thing that caps what it can catch,
and the cap has been measured.** `docs/23`: rival *quality* is the choice that
decides whether a battery can reject anything, rival quality requires knowing
which differences are load-bearing, and that is domain knowledge the seam
forbids. The obvious mechanical fix inverts — it scores four real departments as
*more* separated than the sham `[E]`. So the framework can enforce *that* you
have rivals and never *that they are good rivals*, which is the only part that
matters. A framework that outsources its load-bearing judgment to the author,
and whose audit is defeated 6/6 by authors who try, is at serious risk of being
**ceremony with excellent documentation**.

Second-order: the batteries are bespoke and expensive (a mathematics lab; Hasse's
theorem; a poison-aware interpreter) — so the "framework" is ~700 lines plus a
services business `[E: consultant §C.2]`.

### 3.9 Smallest experiment that moves confidence materially
**A1 — the usage audit, extended forward (cost: near zero, one week of normal
work).** §7.3 establishes that today no live research claim routes through
`harness`. Declare, in advance, that the *next* two substantive claims produced
by any hunt will be run through `run_battery` + `audit_department` **in addition
to** whatever the hunt would have done. Record: did the battery change any
verdict, surface any caveat, or cost time for nothing? Two data points beats zero.

**A2 — the real E4 (cost: one outside person, weeks).** `docs/20` §8 experiment
1: an external team builds a department from the docs alone; this side then
audits for emptiness. This is the *only* experiment that can validate the
generality claim, and the tree has named it "the experiment most likely to hurt"
for a year of sessions without running it `[E]`.

### 3.10 What would falsify A as a *major* future
- E4 (or the operator's blinded/equal-budget evaluation) shows an outsider's
  battery is admissible-but-hollow, or requires forward deployment → the
  transplantable thing is a services practice or a pamphlet, not a framework.
- A1 shows the battery changes no verdict on live claims over ~5 claims → the
  abstraction is not doing the work; the concrete instruments are.
- A second, pinned-harness repeat of the blind-authoring exercise again reaches
  6/6 hollow-`CALIBRATED` → the grade carries no information about a motivated
  author, and everything built on the grade inherits that.

---

## 4. Future B — The Mathematics Laboratory

### 4.1 One plain sentence
A very small laboratory that produces at least one mathematical statement new to
humanity and strong enough that a qualified outsider signs off on it.

### 4.2 Which subsystem pulls toward it
`zeta/` (25 modules), `lean/` (58 files, 0 sorrys, 8739 kernel jobs),
`hunts/frontier_math/` (~110 files — the largest single working directory in the
repository), `hunts/higher_xi/`, the certainty ladder, `zeta/rigor.py`.

### 4.3 Strongest evidence it is intentional `[E]`

| Evidence | What it shows |
|---|---|
| `CLAUDE.md` §honest-scope: "Phase II's explicit Research Objective is to **produce one externally verified mathematical statement that humanity didn't previously know**" | **the only future with an objective in the binding rules file** |
| `README.md` lines 9–80: the front page's *first* section is the frontier candidate with a per-step grade table | the actual headline |
| `HANDOFF.md` queue item 1, and the next-session prompt: "One external acceptance is worth more to this project than another internal result" | the scheduled next action is B's |
| `hunts/frontier_math/` file count; `zeta23ext/` a Lean package pinned against the source paper's own formalization | where the work actually is |
| Commit history 2026-08-11→13: nearly every commit is frontier mathematics (`Batch 4 lands: the k=1 retention algebra is kernel-checked`, …) | where the tokens actually went |
| The certainty ladder's rung 4 ("externally reviewed") existing at all, and being marked unreached | the objective encoded as a grade |
| ROADMAP "Queued" lanes: higher-ξ hierarchy → CUE F_k → derivative zeros → corrected F₂ | a mathematics agenda, ordered |
| `lean/ARISTOTLE-RUNS.md`: 4 prover batches, Sturm batch accepted | external compute bought for B's benefit |

### 4.4 What the institution looks like if B dominates
It is a research group of one human plus rotating agents, whose output is
theorems, bounds, counterexamples, and negative results, and whose distinguishing
practice is that it publishes its failures alongside its results. Success is a
Mathlib merge, a paper acknowledged by the source authors, an accepted preprint.
The harness stays as *internal quality control* — the thing that keeps the group
from fooling itself — and stops being marketed. `docs/doors/adopt.md` becomes a
curiosity.

### 4.5 Reclassification under B
- **Core:** `zeta/`, `lean/`, `hunts/frontier_math/`, `hunts/higher_xi/`, `zeta/rigor.py`, the certainty ladder, `docs/00–16`, `docs/27`.
- **Supporting infrastructure:** `harness/` (internal QC), `ontology/` (lead triage), `lean/proof_adapter.py`, `ontology/scout*.py`, `data/`, `tests/`.
- **Experimental:** `meta/`, `dossier/`, `promotion.py`/`preregistration.py`, `hunts/HUNTSPEC.md`.
- **Obsolete:** `croniter` and `stateval` departments (they exist only to test A's generality); `compiler/` likewise; `interactive_lab/`; arguably `harness/blind_authoring_2026_08_09/`.

### 4.6 What evidence exists that B is *useful*
1. **Kernel-checked theorems that did not exist before**, sorry-free, on this
   repo's own toolchain: the composition inequality and its θ-corollary; the
   grid-incidence law (shipping with a counterexample showing evenness is
   necessary); the census floor by rational weak duality with no `native_decide`
   and no floats; the retention certificate arithmetic `[E: README front table]`.
2. **A candidate improvement to a published constant**, with every step graded
   and its weakest step named, plus an explicit "not numerically effective at any
   reachable height" caveat `[E]`.
3. **Eleven of its own defects caught and published**, including a route it
   proposed and then refuted with its own controls `[E]`.
4. **`PowerfulDecomposition.lean`** — a classical structure theorem with an API,
   kernel-checked, and Mathlib verifiably has no powerful-number machinery at all
   `[E: HANDOFF item 1, checked 2026-08-12]`. This is a concrete, near-term
   external-acceptance candidate.
5. **The director run found six real defects** in the repo's own claims,
   including a wrong `proven_sign` invisible to the two-backend cross-check `[E]`.
   B's self-correction machinery works.

### 4.7 What remains completely unvalidated
- **Rung 4 has never been reached.** No qualified outsider has walked any chain.
  "External review — none yet — invited, not required" `[E: README]`.
- **No upstream contribution has been accepted anywhere.** Zero.
- **The frontier candidate's last gap is open** (the many-pair case), and the
  lab's own proposed route for it was refuted `[E: docs/27 §4]`.
- **Rung 3 is blocked on a headroom re-plan** and the 215-site sweep sits at
  60/215 `[E]`.
- **Effectiveness:** the improvement's crossover sits near T ≈ 10^(1.7×10⁶) `[E]`
  — real as a liminf statement, unreachable in practice.

### 4.8 Strongest argument against pursuing B
**The base rate.** This is a one-operator laboratory attacking the neighbourhood
of the hardest open problem in mathematics, funded personally, with frontier
tokens exhausted `[E]`, whose flagship result is a +1.0×10⁻⁵ improvement to one
constant that is not effective at any computable height, whose last gap is open,
and which has never had an external reader. `docs/08` is a 
failure catalogue the lab wrote itself. The honest prior on "one externally
verified statement humanity didn't know" being achieved is low, and *everything
else in the repository would still exist and be interesting if it were not.*

Second-order: B's value is nearly binary and gated on other people's attention
(Mathlib maintainers, paper authors), which the lab does not control — and
`ROADMAP` records a Mathlib triage closing two PRs for inadequate AI-usage
disclosure `[E]`.

### 4.9 Smallest experiment that moves confidence materially
**B1 — post the Zulip question (cost: one message).** Already queued as HANDOFF
item 0–1: ask `#mathlib4 > Is there code for X?` whether the powerful-number
decomposition is wanted. A "yes" converts a cold PR into an invited one; a "no"
saves the entire effort. This is the cheapest high-information act available to
the whole institution and it has not been done.

**B2 — send the Remark 1.1 finding to the source paper's authors (cost: one
email).** `hunts/wide_search/RESULTS-pair-ceiling.md` already contains a
careful-reader finding useful to them, and reporting it needs no submission queue
`[E: HANDOFF]`. It tests "can this lab produce something an expert values?"
without a gatekeeper.

### 4.10 What would falsify B as a *major* future
- B1 and B2 both return silence or "already known" **and** the many-pair gap
  stays open for a sustained period → the lab is producing internally-valid work
  that no external party values, and the Phase II objective is not reachable at
  this budget.
- A Mathlib submission is rejected specifically on *quality* (not process) →ceiling reached.
- Someone else closes the many-pair gap first → the specific race is lost, though
  this would not falsify B in general.

---

## 5. Future C — The Research Operating System

### 5.1 One plain sentence
A persistent, adversarial, inspectable research loop in which agents generate,
search, code, attack and formalize, and only non-model oracles assign epistemic
status.

### 5.2 Which subsystem pulls toward it
`meta/` (ledger, operator-functions, ai-components, asymmetry-experiment),
`docs/reviews/` (the decision memo and portfolio), the 2026-08-11 adopted builds
(`independence.py`, `guards.py`, `HUNTSPEC.md`, `proof_adapter.py`,
`ontology/scout*.py`, `review.py`, `graveyard.py`, `scripts/70_lab_state.py`),
and the untracked `automation/` nightly rig.

### 5.3 Strongest evidence it is intentional `[E]`

| Evidence | What it shows |
|---|---|
| ROADMAP "The strategy memo's charter … is adopted as the phase framing: agents produce artifacts for verification, not verdicts; model agreement never substitutes for independent evidence" | **the charter was adopted**, in the decision file |
| `hunts/HUNTSPEC.md`: "The rule it encodes is the phase charter's: **no agent without an oracle**"; `required_oracles` lexically refuses any entry naming a model | the charter made mechanical |
| Nine builds landed in a single day on the strength of one decision record `[docs/26]` | genuine investment |
| `meta/README.md`: the question "how much legitimate research output can a very small human organisation produce when generation is cheap, skepticism is architectural, verification is systematic, and routine work can be delegated?" | C stated as *the* research question of the second laboratory |
| `docs/25`: nine investigators with conflicting mandates, isolated contexts, "the generator of a claim never also judged it" | C executed once, by hand |
| `lean/proof_adapter.py` + `external/README.md` (7 cloned outside systems) | C's integration surface exists |
| `automation/` — built, gitignored, "has run zero nights", "waiting on the operator's switch" | C's autonomous half is one switch away |

**And the counter-evidence, which is equally explicit:** ROADMAP *deferred*
"orchestration, the research UI, the attention queue, start/pause controls" with
the rule "**measure the loop before automating it**", and `docs/26` §6 closes
with the same refusal standing `[E]`. **The tree adopted C's epistemology and
refused C's machinery.**

### 5.4 What the institution looks like if C dominates
The unit of work becomes a *run*, not a claim. The operator states a question and
receives an evidence package: "One claim survived. 14 branches were killed. 3
independent non-model checks support the survivor. One unresolved lemma remains."
`[E: the memo's own success picture]`. The lab needs orchestration, a run
registry, cost accounting, an attention queue, and start/pause/steer controls —
i.e. exactly the operational layer the archaeology found missing. Mathematics
becomes the *first workload* rather than the point. `meta/` becomes core.

### 5.5 Reclassification under C
- **Core:** `meta/`, `hunts/HUNTSPEC.md`, `lean/proof_adapter.py`, `ontology/scout*.py`, `harness/review.py`, `harness/graveyard.py`, `harness/guards.py`, `harness/independence.py`, `scripts/70_lab_state.py`, `automation/`.
- **Supporting infrastructure:** `harness/protocol.py` + departments (as the oracle contract), `ontology/funnel.py`, `lean/`, `zeta/` (as oracles).
- **Experimental:** everything on probation — HuntSpec, run manifests, promotion gate.
- **Obsolete:** nothing yet; but the prose spine (`HANDOFF.md` as the coordination channel) would be replaced, which is the largest single behavioural change of any future.

### 5.6 What evidence exists that C is *useful*
1. **The director run** — role separation produced six real defects; "three of the
   run's four most useful outputs came from an agent whose only reward was
   destroying another agent's work" `[E: docs/25]`. This is the best evidence any
   future has that *organizational structure among agents* produces research value.
2. **The proof adapter has a real accepted batch** (four Sturm lemmas,
   `collected — accepted`), under a contract where the service's own verification
   claim is input, not evidence `[E: lean/ARISTOTLE-RUNS.md]`.
3. **The scout's networked half works with a verified `FOUND` path** (OEIS
   content-confirmed, A-number citable) and structurally cannot say NOVEL `[E]`.
4. **`meta/`'s baseline exists**: 14 interventions, architecture caught 3 of 14
   (21%), six of eight automatable gaps closed the same day `[E]`.

### 5.7 What remains completely unvalidated
- **Not one loop has been measured**, which is C's own stated precondition `[E]`.
- **The nightly rig has run zero nights** `[E]`.
- **HuntSpec and run manifests are defined, validated, and never used** — the
  only blocks in the tree are the templates inside `HUNTSPEC.md` `[E]`.
- **`docs/26` has no follow-up section**, which its own closing paragraph defines
  as the test of whether any of the nine builds caught something real `[E]`.
- **The meta-ledger cannot compute its ratio** — no numerator class is counted
  anywhere `[E: meta/ledger.py `ratio()` refuses]`.
- **The meta-ledger is co-designed measurement** by its own admission `[E]`.

### 5.8 Strongest argument against pursuing C
**The tree's own rule forbids it at this stage, and the rule is well-founded.**
"Measure the loop before automating it." Nothing measured. Worse: C's cost is
paid in exactly the resource that is exhausted (judgment/tokens), while its
benefit is speculative. And the second laboratory's own README states the trap:
*"a session that produced no mathematics and a tidy ledger produced nothing"*
`[E]`. C is the future with the highest ratio of infrastructure to output, in an
institution whose only stated objective belongs to B.

Third: C's most-cited justification is two **outside memos**, which the
directory's own contract says are not results `[E: docs/reviews/README.md]`.

### 5.9 Smallest experiment that moves confidence materially
**C1 — write one HuntSpec and one run manifest for the *next* hunt (cost: minutes).**
The primitive exists and is validated; it has zero users. One real use tells us
whether the fields are the right fields — and its own probation terms say it
earns promotion "the first time a kill condition fires mechanically" `[E]`.

**C2 — arm the nightly rig for exactly three nights**, with a HuntSpec, a kill
condition, and a run manifest per night. This is the memo's build-order item 10
and the only way to measure a loop `[E]`. Three nights is cheap and produces
either a measured loop or a named failure.

### 5.10 What would falsify C as a *major* future
- C1/C2 produce runs whose manifests are all "produced nothing" and whose kill
  conditions never fire → the primitives are decoration.
- `meta/`'s ledger, over 20–30 sessions, lands ≥⅔ in `domain-judgment` /
  `owner-authority` → the human is the substance, and the automatable share does
  not justify an OS `[E: this exact kill condition is pre-registered in
  `consultant-thesis-analysis.md` §H E1]`.
- The E2-class result already on the record repeats: typed/structured state does
  not beat disciplined prose `[E: ROADMAP 2026-08-09 — it already did not]`.

---

## 6. Compatibility / conflict analysis

**Answer: (C) different layers of the same institution, with one important
qualification and one real conflict — not (A) mutually exclusive, and only
partly (D).**

### 6.1 Are they mutually exclusive? **No.** `[E]`
There is no architectural conflict. The seam tests *guarantee* that A cannot
contaminate B (`protocol.py` imports nothing from any laboratory, verified three
ways). C is purely additive. Nothing in the tree forces a choice. Any claim that
one must die is a claim about budget, not about code.

### 6.2 Are they compatible but requiring hierarchy? **Yes, and the hierarchy is
already implied by the evidence** `[I]`
- **B is the mission** (only stated objective; only live deliverable; only
  scheduled action).
- **A is a hypothesis about B's byproduct** — and it *depends on B*: the audit's
  measured ceiling is that rival quality requires domain knowledge the seam
  forbids, so a good battery needs a real subject. A without B-like subjects is a
  framework with no way to know if its instruments are any good.
- **C is a method for running B (or A)** — the tree adopted its charter and
  refused its machinery, which is precisely the posture of a method, not a
  destination.

### 6.3 Are they different layers of the same institution? **Mostly yes.** `[I]`
Mapping onto the archaeology's L1/L2/L3: B = L1 (subject), A = L2 (referee),
C = L3+G (method and governance). The archaeology found these are *separable*,
and this analysis finds they are also *ordered*: L2 exists because L1 kept
fooling itself, and L3 exists because L1+L2 kept needing a human. **Each layer
was created by a failure of the layer beneath it.** `[E: §3.1 of the archaeology
— every abstraction traces to an incident]` That is a layer relationship, not a
competition.

### 6.4 Are they temporarily co-resident experiments? **Partly — and this part is
explicit.** `[E]`
`README.md`: "The non-zeta subjects (curves over F_p, LLVM IR rewrites, cron
schedule semantics, statistical model evaluation) **exist to test that the
framework generalizes**." Four of six departments are, by the README's own words,
experiments about A rather than subjects the lab cares about. Similarly `dossier/`
and `promotion.py` self-classify as probes. So a substantial fraction of what
looks like Future A is temporarily-resident *evidence-gathering*, not a
commitment.

### 6.5 The one real conflict
**Front-page identity is zero-sum and currently mismatched.** `[E + I]`
The README's opening line sells A. The README's first *section* is B's frontier
candidate. `CLAUDE.md`'s stated objective is B's. The queue is B's. The commits
are B's. A reader of the front page and a reader of the commit log form different
beliefs about what this is. That is a real cost — it affects who shows up, what
an outside reviewer expects, and what the operator feels obliged to maintain.
**This is the one thing in this document that is genuinely a decision rather than
an experiment.**

### 6.6 Something else worth naming
`[I]` There is a fourth latent identity nobody has named: **the institution as a
published record of how a small AI-assisted lab actually fails.** The graveyard,
the 11 published defects, `docs/21`'s and `docs/23`'s recorded failures, the
6/6 hollowing result, `docs/25`'s six defects, `meta/`'s 0-for-4 calibration —
this corpus is *unusual and externally interesting on its own*, requires no
future to be validated, and is already complete enough to be read. It is not a
future so much as an asset that all three futures currently under-claim.

---

## 7. The harness as an unproven hypothesis

*Treating "the harness is useful" as an unproven claim, and using the
repository's own admission rule against it.*

### 7.1 The repository's own standard, applied
`harness/README.md` demands of every subject: a rival that shares the structure
and lacks the property; a decoy; a surrogate; a lesion; and reference claims in
both directions. **Apply that to the harness itself.**

| Role | What it would be for the claim "the harness improves research reliability" | Does it exist? |
|---|---|---|
| **Rival** (shares structure, lacks the property) | *Independent replication + a pre-registered checklist + code review* — same "attack before believing" structure, no protocol layer | **No such rival has ever been run.** This is the central gap. |
| **Decoy** (ablation) | run the same research with the concrete instruments (`zeta.epstein.battery`, `zeta.surrogate`) but **without** `harness/protocol.py` | **This ablation is running right now, unintentionally — see §7.3** |
| **Surrogate** (null) | a null "framework" that produces grades from nothing | `NaiveGate` exists for the *promotion* layer only `[E]`; nothing for the battery layer |
| **Lesion** | planted hollow batteries | **Yes — `shams.py`, and the blind corpus. Well done and honest.** |
| Reference claim it must **reject** | a hollow battery | **Fails at n=6 for motivated authors** `[E]` |
| Reference claim it must **pass** | an honest battery | Initially **also failed** — 2 of 4 honest parties graded HOLLOW for fidelity `[E: docs/23 §8.6]`; fixed, now 4/4 |

**By its own admission rule, the harness-as-subject would not be admitted as a
department today: it has lesions and no rival.**

### 7.2 What evidence supports it, sorted by strength

**(a) Genuine empirical support — for the four ROLES:**
- `docs/17`: five independent claims of Riemann-zero structure, all refuted in
  one day, "verdict cost collapsed to claim cost" `[E]`.
- `docs/22`: measured detection strength of RH-equivalent criteria against the DH
  rival — a real research finding produced by the rival instrument `[E]`.
- `NULLCONTROLS.md` / `zeta/surrogate.py`: the moments concentration result was
  reclassified from candidate finding to "explained/generic" **because a matched
  null reproduced it** `[E: ROADMAP]`. This is the single cleanest case of a
  control changing a research conclusion in this repository.
- The Davenport–Heilbronn rival sitting at the 27th percentile of a matched null
  — a number that has retired several claims `[E]`.

**(b) Evidence that it functions as designed (necessary, not sufficient):**
- 19 conformance tests × 6 departments pass; `validate_battery` refuses malformed
  batteries; the seam tests pass in 0.1 s; `harness.demo` re-derives every verdict
  live. **All of this shows the code does what the code says.** None of it shows
  research got more reliable.

**(c) Evidence of actual improvement in research reliability — thin:**
- The `factorization_defect` day-one catch is the **one** clean case where the
  protocol layer prevented an over-promotion `[E]`.
- `detector-claim-agreement` catching `docs/21`'s hollow battery `[E]` — but that
  battery was authored by this tree's own process (`docs/23` §8.5 says so).

**(d) Circular / self-generated evidence — a large fraction:**
- Department #5 (`referee`) is the machinery graded by itself, with a rival this
  tree reconstructed.
- `shams.py`'s mutations are authored by the same process that wrote the checks.
  ROADMAP says it explicitly for the newest one: "The check was built from that
  battery, so that battery is not an independent test of it, and the catalog says
  so" `[E]`.
- `meta/`'s cohort was "authored by the agent whose behaviour it describes" `[E]`.
- The four non-mathematical departments were all authored inside this process
  `[E: known gap #1]`.

### 7.3 The sharpest finding: the abstraction has no live client

**Measured, not argued:** `[E]`

```
grep for run_battery | validate_battery | audit_department | ClaimReport
  → harness/ itself ......................... yes (incl. its own departments)
  → tests/ .................................. yes (15 files)
  → hunts/ .................................. ZERO
  → scripts/ ................................ ZERO
  → zeta/ ................................... ZERO
  → ontology/ ............................... ZERO
```

`scripts/70_lab_state.py` imports `harness` — but the **ledgers**
(`graveyard`, `guards`, `review`, `independence`), never `protocol`.

Meanwhile the concrete instruments *are* used by live research:
`zeta.epstein.battery` and `zeta.surrogate` are imported by `hunts/wide_search/`,
`hunts/flow_repair/`, `hunts/jensen_clock/`, `hunts/golden_control/`,
`hunts/local_positivity/`, and several `scripts/` `[E]`.

**And the decisive detail:** `hunts/wide_search/probe.py` implements the four
control roles **by hand** — `rival_check()` wrapping `zeta.epstein.battery`, a
hand-rolled `null_band()` (the same name as `harness.protocol.run_null_band`),
and lesion checks — rather than importing `harness` `[E]`. The live research
independently re-derived the harness's roles inside the same repository instead
of using the harness.

**And:** the `zeta` department's two reference claims are `functional_equation`
and `multiplicativity` — its own *calibration pair* `[E]`. **No live research
claim of this laboratory has ever been adjudicated by `harness/`.** The frontier
candidate's grades come from the certainty ladder, Lean, and `rigor.py` — not
from a battery.

`[I]` The honest reading: **the four roles are validated; the protocol layer is
not.** The roles earned their place in `docs/17` *before* `harness/protocol.py`
existed (docs/17 is dated 2026-08-05; the protocol is 2026-08-06 and appears in
that document as a **postscript**) `[E]`. Everything since has demonstrated that
the abstraction is *well-built*, not that it is *used*.

### 7.4 Component-by-component verdict

| Component | Individually demonstrated value? | Evidence |
|---|---|---|
| **Rival** (structure-matched negative control) | **YES — strongest in the tree** | docs/17 (5 kills), docs/22, gate #3, the DH 27th-percentile calibration |
| **Surrogate / null model** | **YES** | the moments concentration result reclassified as generic (`NULLCONTROLS.md`) |
| **Lesion / detector power** | **YES** | ε\* blindness floors; compiler's `blind_to` at magnitude 0.5; croniter's measured mutant magnitudes |
| **Decoy / ablation** | **Weak** | polarity differs per department and reading it wrong is a recorded mistake `[E: ROADMAP dept #2]`; no case where a decoy alone changed a conclusion |
| `validate_battery` / admission rule | **Partial** | it is a *forcing function on authors*, and forced 6 real batteries into existence; but it cannot see emptiness, by measurement |
| `Department` / `KNOWN_DEPARTMENTS` | **Not demonstrated** | zero live clients (§7.3); its value is that listing turns audits on — real, but internal to A |
| `integrity.py` grades | **Partial, with a measured ceiling** | catches mechanical emptiness; defeated 6/6 by motivated authors |
| `detector-claim-agreement` | **YES** (narrow) | catches three things nothing else catches |
| `rival-separator-abundance` | **NO — self-declared** | "ships and acts on nothing"; threshold sits above the whole calibrated range `[E]` |
| `promotion.py` / `preregistration.py` | **NO — self-classified KEEP AS PROBE** | mirror condition unreachable; inherits every blind spot below it |
| `independence.py` | **Promising, unproven** | one declared subject; the incident that motivated it is real and severe |
| `guards.py` | **Promising, unproven** | 5 records, 2 undemonstrated |
| `graveyard.py` / `review.py` | **Unproven** | 3 graves against dozens of prose kills; no review completed |
| `shams.py` + blind corpus | **YES as an instrument on the audit** | it is what produced the 6/6 result — i.e. its value is that it *falsified* the audit |

### 7.5 What equal-budget baseline should it beat

`[I]` The rival that has never been run. Concretely, the harness must beat **the
same research effort spent on:**

1. **Independent replication.** A second implementation of the claim's key
   computation by a party who sees the claim and not the code. *This is the
   baseline that most threatens the harness*, because `docs/25` records that the
   run's most useful outputs came from a **replicator** and **skeptics**, not
   from any battery `[E]`.
2. **A written pre-registered checklist** — `docs/17` §2's "one transferable
   checklist", which is prose and already exists.
3. **Ordinary code review by someone who knows the subject** — which is what
   caught the sham battery, Hunt #2, and the scope drift `[E]`.

**The prediction to test:** if the harness cannot beat "replication + checklist +
subject-matter review" at equal cost, then A is *mostly reducible to independent
replication with better bookkeeping* — which is a real but much smaller claim,
and would argue for keeping the four roles and the ledgers and shrinking
everything else.

**This is precisely where the operator's planned blinded/equal-budget evaluation
belongs, and it is unresolved.** §12 specifies what it must contain.

### 7.6 What would make us simplify or delete it

| Observation | Consequence |
|---|---|
| A1 (§3.9) shows the battery changes no verdict on ~5 live claims | delete `Department`/registry; keep the four roles as plain functions in `zeta/` and per-hunt |
| The equal-budget evaluation shows replication ≥ harness | reduce `harness/` to: the four roles + `shams.py` + the ledgers; delete `promotion.py`, `preregistration.py`, `rival-separator-abundance` |
| A pinned-harness repeat again yields 6/6 hollow-`CALIBRATED` | stop reporting grades as if they carry information about motivated authors; keep the audit as an author-assist checklist only |
| E4 shows an outsider needs forward deployment | A is a services practice or a document, not a framework; keep `docs/doors/adopt.md`, delete the generality claim from the README |
| The `DETECTOR_INADEQUATE` grades on `compiler`/`referee` are never answered | the grade vocabulary is not actionable; collapse five grades to "audited / not audited" |

**And what would make us expand it:** an outsider builds a non-sham battery in a
**non-executable-oracle domain** — "the one observation that would genuinely
surprise me given this tree" `[E: consultant analysis §I]`.

### 7.7 Fair statement of the counter-case
`[E]` Two things must be said against my own critique. First, the harness's most
damaging results were produced **by the harness's own instruments** — the 6/6
hollowing, the honest-controls finding, the promotion gate's empty reason list.
An architecture that funds the experiments that damage it is behaving better than
most. Second, **absence of live clients may be a scheduling fact, not a value
fact**: `harness/` is 4 days old relative to the frontier campaign that has
consumed nearly every commit since. `[I]` I do not think this fully explains it —
`hunts/wide_search` *re-implemented* the roles rather than importing them, which
is a signal about ergonomics or discoverability, not about scheduling — but it is
a real alternative explanation and A1 is the experiment that separates them.

---

## 8. Scientific architecture vs operational infrastructure vs public identity

Three questions the repository currently answers with one word ("Zeta Lab"). They
are independent, and today's implementation does not determine tomorrow's answer.

| | **Scientific architecture** (what the institution is entitled to believe) | **Operational infrastructure** (how work gets done) | **Public / organizational identity** (what outsiders think this is) |
|---|---|---|---|
| Today | certainty ladder · reserved word · `rigor.py` enclosures · Lean kernel · the four control roles · gate #3 · precision-response rule · honest-scope rule | one operator · rotating CLI sessions · git branches + worktrees · 3 prose files · no CI · no telemetry · `70_lab_state.py` unscheduled | "Zeta Lab: a computational and formal workbench … plus a reusable validation framework" — a public MIT repo with no external readers `[E]` |
| Authoritative source | `CLAUDE.md` + the tests | `HANDOFF.md` + git | `README.md` |
| Validated? | **partially** — Lean and `rigor.py` are self-evidently sound; the ladder's rung 4 is unreached | **no** — never measured | **no** — zero external engagement |
| Coupled to a future? | B and A both depend on it; C consumes it | **future-neutral** (§9) | **decision, not evidence** (§6.5) |

**The specific question the operator raised — what is the harness?** The evidence
supports **exactly one** of these answers today and leaves the rest open:

- **Scientific core?** `[E]` **No.** No live research claim routes through it
  (§7.3); the frontier's grades come from Lean, `rigor.py` and the ladder. The
  scientific core is the *certainty ladder plus the two certified regimes plus
  the four control roles* — three of which live in `zeta/`, not `harness/`.
- **One experimental research project?** `[E]` **Yes, today.** Four of six
  departments exist "to test that the framework generalizes" (README's words),
  and `docs/20` §8 lists the experiments that would damage it. This is the
  description the tree's own text supports.
- **Internal infrastructure?** `[I]` **Aspirationally, but not yet in fact** —
  infrastructure has users, and it has none outside its own tests.
- **A product/library?** `[E]` **Undetermined and explicitly not started.**
  "Nothing in this repository evidences willingness to pay"; the recorded
  decision is "no sibling repo, no commercial motion, until E2 reports."

`[I]` **The important consequence:** because the harness is currently *an
experiment*, not the scientific core, **modifying, shrinking, or even removing it
would not endanger the institution's scientific standing.** The things that would
are the ladder, the reserved word, `rigor.py`, the Lean arm, and the rival/null/
lesion instruments in `zeta/`. That is a much smaller and much better-validated
set than the repository's front page implies.

---

## 9. Future-neutral modernization

*The test I applied: a capability is future-neutral only if it is **needed under
all three futures**, **fixes a failure that has already occurred**, and **stores
data whose meaning does not depend on which future wins**. I rejected three
candidates on this test, listed at the end — the operator's hypothesis that
observability/provenance qualifies is largely, but not entirely, correct.*

### FN1 — Run registry (the run record)

**WHY IT IS NEEDED.** Under B: to know which of five parallel threads produced a
kernel-checked step and at what cost, and to reconstruct a campaign for a
reviewer. Under A: E4 and any equal-budget evaluation are *impossible to score*
without per-run cost and outcome. Under C: a run *is* the unit of work.

**WHAT CURRENT FAILURE IT FIXES.** `[E]` "Frontier-model tokens are exhausted
until further notice" arrived as a surprise that reorganized the entire queue and
forced a written "do not attempt on a cheap model" section. An "agent lost to a
container restart" is recorded as a prose table row. The resumption benchmark's
data is not in this tree. The one comparable question the institution can ask —
which model produced which defect — is unanswerable.

**WHAT DATA IT REQUIRES.** See §10. `run_id`, actor (model id + harness), start/
end, task ref, branch, base and head commit, prompt digest, outcome enum,
artifact digests, and cost fields that are **nullable** (many runs will not have
them).

**COUPLING.** None. A run record says nothing about departments, claims, or
mathematics. The tree already maintains one by hand for one backend
(`lean/ARISTOTLE-RUNS.md`) `[E]` — this generalizes an existing, working design.

**WHAT WE SHOULD NOT BUILD YET.** No dashboard. No autonomy score. No per-model
leaderboard — `meta/README.md`'s refusals apply and Q2 in §15 must be answered
first. No full tool-call traces (§10).

### FN2 — Git/branch/worktree reconciliation report

**WHY IT IS NEEDED.** All three futures run parallel sessions; B already runs
five `[E]`.

**WHAT CURRENT FAILURE IT FIXES.** `[E]` This is the *first entry in
`meta/interventions.jsonl`*, with its missing capability already named:
"Post-merge reconciliation between local refs, remote refs and open PRs." It
recurred as the doc-26 numbering collision across an unmerged branch, and as 14
commits living on one disk for a day. `science_preflight.py` explicitly "cannot
see other branches; that is a real gap in the instrument."

**WHAT DATA IT REQUIRES.** Nothing new — it is derived entirely from git refs and
the forge API.

**COUPLING.** None whatsoever.

**WHAT WE SHOULD NOT BUILD YET.** Automatic merging. Locking. Any policy
enforcement — the current policy ("report them, never merge them") is a human
judgment and should stay one.

### FN3 — Schedule and retain the view that already exists

**WHY IT IS NEEDED.** Every future needs the operator to see state without
reading 3122 lines of prose.

**WHAT CURRENT FAILURE IT FIXES.** `[E]` `scripts/70_lab_state.py` derives an
attention queue (undemonstrated guards, unguarded graves, reviews missing an
attack) — the exact "human-decision worklist" the memo asked for — and **nothing
consumes it**. Two guard records sit at `fired=None` and three graves are
unguarded; nobody is reminded.

**WHAT DATA IT REQUIRES.** None new. Run it, keep the output, diff it.

**COUPLING.** None — it reads only durable tree artifacts by construction, which
is why the memo's constraint ("workflow state may live in an orchestration layer;
evidence may not") is already satisfied `[E]`.

**WHAT WE SHOULD NOT BUILD YET.** An interactive app. A server. Anything with
scripts or network — the page's contract is that it has neither.

### FN4 — Tiered CI

**WHY IT IS NEEDED.** Every future depends on the governance tests, and the
institution's own thesis is "a skipped test is a silent verdict" `[E]`.

**WHAT CURRENT FAILURE IT FIXES.** `[E]` No CI has ever existed — the only file
ever added under `.github/` in this clone's history is `FUNDING.yml`, added and
removed the same day. And: the dormant `python-flint` cross-check
(the reserved word's justification was switched off for the repo's whole life,
reporting only as "5 skipped"); the doc-21 double-numbering; the doc-26 collision;
the dropped-import defect that "recurs, so it gets a guard — which finds three
more" (commit `e2fdae2`); the docs scanner walking into nested checkouts. Every
governance test in this repository runs only when a session remembers.

**WHAT DATA IT REQUIRES.** None.

**COUPLING.** None.

**WHAT WE SHOULD NOT BUILD YET.** Full-suite-on-every-push (10–20 min) or
`lake build` in CI (8739 jobs). Tier it: governance tests + fast subset on push;
the rest nightly or on demand.

### FN5 — Cross-branch doc-number and artifact allocation

**WHY IT IS NEEDED / FIXES.** `[E]` Named as a real gap in the preflight by
HANDOFF itself, after doc 21 was allocated twice and doc 26 collided.

**DATA.** Git refs only. **COUPLING.** None.
**NOT YET.** Any broader "namespace service".

### FN6 — Prompt and context capture, at digest granularity

**WHY IT IS NEEDED.** Under A and C, a blinded or equal-budget evaluation is
uninterpretable without knowing what each arm was told. Under B, reproducing a
campaign for a reviewer requires it.

**WHAT CURRENT FAILURE IT FIXES.** `[E]` The one prompt the institution
considered important enough to keep is pasted by hand into `HANDOFF.md`. The
Aristotle ledger says "Prompts pinned in the table" but the table holds
*statements*, not prompts. The resumption benchmark's "one frozen template" is
not in this tree.

**WHAT DATA IT REQUIRES.** A `prompt_digest` always; the prompt **text** only
where the operator permits it. `[I]` This is the one future-neutral item with a
genuine policy question attached (§15 Q5) — the repository is public, and
`HANDOFF.md` already records that strategy material is kept off-tree because
"publishing a strategy document creates a standing incentive to write the next
one more flatteringly."

**COUPLING.** None. **NOT YET.** Chain-of-thought capture — explicitly excluded
by the tree's own proposed schema `[E: consultant analysis §E, "Not recorded:
chain-of-thought"]`.

### Rejected as NOT future-neutral

| Candidate | Why it fails the test |
|---|---|
| **A claim registry / typed claim objects** | `[E]` The tree has *already measured* that typed research state did not beat prose (the resumption benchmark), and `dossier/` is the standing warning. Its value depends heavily on which future wins (essential under C, optional under B). Belongs in §11 as WAIT FOR EVIDENCE. |
| **Orchestration / start-pause-steer** | `[E]` Explicitly deferred; C-coupled by definition; violates "measure the loop before automating it". |
| **A database** | `[I]` Nothing found requires one. Everything in FN1–FN6 is append-only JSONL plus git, which is the format the tree already uses and merges cleanly (`merge=union` on the private ledger `[E]`). A database is a *future-coupled* choice disguised as infrastructure. |
| **Public website / auth / community** | Pure identity decisions (§11), zero current failures. |

---

## 10. Minimum provenance waist

The archaeology found: **strong head (decisions), strong tail (claim → grade →
commit), no waist.** The waist is exactly three joins. Everything else already
exists.

```
  human idea / direction        EXISTS  → ROADMAP.md dated sections          [prose, fine]
        │
        │  ← JOIN 1 MISSING: decision → task
        ↓
  research task                 EXISTS  → HANDOFF queue items, MISSION.md    [prose, fine]
        │
        │  ← JOIN 2 MISSING: task → run
        ↓
  agent/model invocation        MISSING ────────────────────┐
  prompt / context              MISSING (digest)            │  ONE RECORD
  tool activity                 OUT OF SCOPE v1             │  FIXES ALL
  result                        MISSING (outcome + digests) │  OF THIS
        │                                                   ┘
        │  ← JOIN 3 MISSING: run → artifact/claim
        ↓
  claim / evidence / defect     EXISTS  → PROOF-LEDGER, graveyard, guards, review
  verification                  EXISTS  → certainty rung, integrity grade, lake build
  artifact                      EXISTS  → files; digests already used for upstream pins
  commit                        EXISTS  → git, with Co-Authored-By + Claude-Session
```

### 10.1 The minimum schema — one record type and two trailers

**Not an ontology. One append-only JSONL record, plus two git trailers.**

```
run record (one line of JSONL per run)
  run_id            required   opaque, sortable
  started / ended   required   ISO-8601
  actor             required   { kind: human|model|prover|search|suite,
                                 id: "claude-opus-5" | "aristotle" | "operator",
                                 harness: "claude-code" | "codex" | "cli" }
  task              required   free-text one-liner + optional decision_ref
                               (a ROADMAP anchor slug — a CONVENTION, not a table)
  repo              required   { branch, base_commit, head_commit|null }
  prompt            required   { digest: sha256, text_ref: path|null }
  outcome           required   one of: landed | no-change | killed | blocked |
                               refused | crashed          ← closed vocabulary
  artifacts         required   [ { path, sha256 } ]  (may be empty — that is a result)
  cost              optional   { input, output, cache, usd, wall_seconds }  all nullable
  notes             optional   one sentence
```

```
git trailers (added to the two that already exist)
  Run-Id: <run_id>          ← JOIN 3, in the place the tree already puts provenance
```

```
existing ledgers gain ONE optional field each
  graveyard_ledger / guard_ledger / review_ledger / PROOF-LEDGER row
    run_id: <run_id>|null   ← ties a defect or a kill to the run that produced it
```

### 10.2 Why this is sufficient, and why nothing larger is justified

- **Decisions stay prose.** A `decision_ref` is a slug someone types into a
  ROADMAP heading. No Decision object. `[E: consultant analysis §D — "Session,
  Decision objects: bureaucracy until a scoreable resumption test shows prose
  loses something specific"; and the resumption benchmark did not show it.]`
- **Claims stay where they are.** `run_id` is a nullable field on records that
  already exist. No claim registry, no ids for claims, no schema migration.
- **Artifacts are already digest-addressed** in the tree's strongest habit
  (source-paper PDF SHA-256, upstream Lean commit, Mathlib pin, blind-corpus
  `SHA256SUMS.txt`, `preregistration.py`) `[E]`. FN1 reuses it rather than
  inventing addressing.
- **Tool activity is deliberately excluded from v1.** `[I]` This is where an
  ontology would metastasize, and no recorded failure in this repository was
  caused by not knowing which tool calls a session made. Record the *commands
  that produced artifacts* only if they are cheap to capture; otherwise the
  artifact digest plus the commit diff already carries it.
- **Reconstruction test:** with the above, "which run, by which model, under
  which prompt, produced the artifact behind defect #19, and what did it cost?"
  becomes a join over `run_id` — while "why did we do this at all?" remains a
  human reading one ROADMAP section, which is correct and cheap.

### 10.3 The honest cost, stated because the tree would state it
`[I]` A run record must be written by something. If a human writes it, it will
rot — the tree's own rule: "if logging costs more than the intervention, the log
dies and deserves to" `[E]`. So FN1's real prerequisite is that the *session*
emits it, which means a hook or a wrapper, which is the first thing in this
document that touches the operator's workflow. That is a small build with a real
adoption risk, and it should be measured for four weeks before anything is built
on top of it.

---

## 11. Decision map

Classification: **DECIDE NOW** (an actual choice, no experiment will help) ·
**SAFE TO BUILD NOW** (future-neutral, fixes a recorded failure) ·
**WAIT FOR EVIDENCE** (a named experiment exists) ·
**DO NOT BUILD YET** (would foreclose or violate a standing rule).

| Decision | Current evidence | What we don't know | Experiment / information needed | Reversibility | When to decide | Class |
|---|---|---|---|---|---|---|
| **Permanent institutional identity** | Only B has a stated objective (`CLAUDE.md` Phase II); front page sells A; commits are B `[E]` | Whether the operator wants a mathematics group, an instrument shop, or a lab-OS | None — this is a values choice. §6.5 shows only the *front page* is zero-sum | High (words) | **Now** — it is cheap and it unblocks §11 rows below | **DECIDE NOW** |
| **Role of the harness** | 4 roles validated (`docs/17`, NULLCONTROLS, `docs/22`); protocol layer has **zero live clients**; audit defeated 6/6 `[E]` | Whether the abstraction beats replication + checklist + review at equal budget | **The operator's blinded/equal-budget evaluation (unresolved)** + A1 usage audit + E4 | Medium — shrinking is easy, deleting departments is a one-way door for the corpus | After the evaluation reports | **WAIT FOR EVIDENCE** |
| **Role of departments** | 6 registered; 4 exist to test generality (README's words); #7+ explicitly deferred `[E]` | Whether a department is a subject or a fixture (archaeology T7) | Same as above; plus whether any outsider ever registers one | High for new ones; low for removing | With the harness decision | **WAIT FOR EVIDENCE** |
| **Role of the referee (integrity audit)** | Catches mechanical emptiness; `compiler` + `referee` grade `DETECTOR_INADEQUATE` and are unfixed `[E]` | Whether five grades are actionable or two would do | Answer the two `DETECTOR_INADEQUATE` grades — ROADMAP already calls this "the next pre-registered change" | High | **Now-ish** — it is a small, already-scheduled piece of work | **SAFE TO BUILD NOW** (answer it) |
| **Mathematics vs multi-domain** | Mathematics is the objective and the whole commit log; multi-domain is 4 fixture departments `[E]` | Whether any non-math subject would ever be *pursued* rather than *used as a control* | B1/B2 (external engagement) resolving first; ROADMAP already sequences "harden before broadening" | High | After B1/B2 report | **WAIT FOR EVIDENCE** |
| **Repo structure (split / monorepo)** | One repo, seam tests keep packages honest; `pyproject` installs only `zeta` + `ontology` `[E]` | Whether A ever needs its own distribution | Nothing today; a split is only forced by an outside adopter | Medium-low (splits are painful) | Not yet | **DO NOT BUILD YET** |
| **Database** | Everything today is JSONL + git + Markdown; private ledger merges via `merge=union` `[E]` | Nothing — no recorded failure requires a database | — | Low (schemas ossify) | Not yet | **DO NOT BUILD YET** |
| **Telemetry / run registry** | No telemetry at all; token exhaustion was a surprise; `ARISTOTLE-RUNS.md` is a working hand-built precedent `[E]` | Whether `meta/`'s anti-dashboard refusal extends to plumbing (§15 Q2) | Q2 answered; then 4 weeks of run records | High (append-only file) | **This week**, once Q2 is answered | **SAFE TO BUILD NOW** (FN1) |
| **Git/branch reconciliation** | Named as intervention #1's missing capability; recurred ≥3 times `[E]` | Nothing | — | High | **This week** | **SAFE TO BUILD NOW** (FN2) |
| **Tiered CI** | No CI; ≥5 recorded incidents a governance test would have caught `[E]` | Runner cost and whether `lake build` can be cached | — | High | **This week** | **SAFE TO BUILD NOW** (FN4) |
| **Orchestration** | Explicitly deferred; "measure the loop before automating it"; zero loops measured; nightly rig 0 nights `[E]` | Whether an autonomous loop produces anything | C2: arm the nightly rig for exactly 3 nights | Medium | After C1/C2 | **DO NOT BUILD YET** |
| **Human research cockpit** | `70_lab_state.py` exists, unscheduled, unconsumed `[E]` | Whether the operator reads it when it is put in front of them | FN3: schedule it, keep the output, diff it, for 2 weeks | High | **This week** (the scheduling half only) | **SAFE TO BUILD NOW** (FN3, read-only half) / **DO NOT BUILD YET** (interactive half) |
| **Write/direct interface** | Operator writes by editing prose or typing a prompt `[E]`; E1–E3 designed for exactly this question, unrun | Whether structured intent beats prose — **already measured once as "did not"** `[E]` | E3 (flattening) + a repaired E2 | High | After the harness decision | **WAIT FOR EVIDENCE** |
| **Public website** | The repo *is* the website; zero external readers; README is the front page `[E]` | Who the audience is — which is downstream of identity | Identity decision + B1/B2 | High | After identity | **WAIT FOR EVIDENCE** |
| **Naming / rebranding** | "Zeta Lab" names B; the front page sells A `[E]` | Nothing an experiment can tell us | — | High (but each rename costs cross-references and `docs/doors` tests) | **With the identity decision, or never** | **DECIDE NOW** (or explicitly defer) |
| **Auth / community** | No users; no contributors besides operator + agents `[E]` | Whether anyone shows up | B1/B2/E4 producing a single external participant | High | Not yet | **DO NOT BUILD YET** |
| **Donations / compute funding** | Funded personally; frontier tokens exhausted; a funding link was **added and then removed** (`d990fee` → `4ef30a3`, "Drop the funding link until there is an audience for it") `[E]` | Whether an audience exists | One external acceptance (B1) or one external reader | High | After B1/B2 | **WAIT FOR EVIDENCE** — and note the tree already made and reversed this decision once, on the correct reasoning |

---

## 12. Experiments that resolve the biggest uncertainties

Ordered by (information gained) ÷ (cost). The first three cost almost nothing and
are the highest-value acts available.

| # | Experiment | Cost | Resolves | Pre-registered kill/pass |
|---|---|---|---|---|
| **X1** | **B1 — post the Mathlib Zulip question.** Already HANDOFF item 0. | one message | Whether B's cheapest external milestone is reachable at all | "yes, wanted" → prepare the PR; "no" → the whole upstream track is saved effort, and the *justification* for `lean/`'s non-frontier work changes |
| **X2** | **B2 — send the Remark 1.1 finding to the source paper's authors.** | one email | Whether this lab can produce something an expert values, with no gatekeeper | a substantive reply → B is externally legible; silence → not evidence either way, but cheap |
| **X3** | **C1 — write one HuntSpec + one run manifest for the next hunt.** | minutes | Whether C's adopted primitives are usable at all (they have zero users) | fields feel right and a kill condition is stateable → keep; the block is filled with prose that means nothing → the primitive is decoration |
| **X4** | **A1 — route the next 2–5 substantive hunt claims through `run_battery` + `audit_department` in addition to normal practice.** | hours, spread over normal work | **The central question of §7**: does the abstraction change any verdict? | ≥1 verdict changed or caveat surfaced → the protocol layer earns its place; 0 of 5 → it is bookkeeping, and §7.6's simplification applies |
| **X5** | **FN1 pilot — emit run records for 4 weeks of normal work.** | one hook + a schema | Whether the waist is writable without rotting | records exist for ≥80% of runs → build on it; the log dies → the tree's own rule applies, delete it and say so |
| **X6** | **The operator's blinded / equal-budget harness evaluation.** ***Unresolved dependency.*** See below. | substantial | Whether the harness beats the replication baseline | to be pre-registered *before any data*, per the tree's own ninth-increment lesson `[E]` |
| **X7** | **E4 / docs/20 §8 experiment 1 — an outside party builds a department from the docs alone.** | one outside person | The generality claim, which nothing else can test | admissible + non-sham within ~2 sessions → A is real; needs forward deployment → services, not framework |
| **X8** | **C2 — arm the nightly rig for exactly three nights**, each with a HuntSpec and a run manifest. | 3 nights of compute | Whether an autonomous loop produces anything measurable | any night produces a kill condition firing or a landed artifact → a loop exists to measure; three "produced nothing" manifests → C's automation half is premature, recorded as such |

### 12.1 What X6 must contain to be decisive

`[I]` Since the design is not in the tree, this is my specification of the
minimum, built from the repository's own standards:

1. **A rival arm, not just an ablation.** The comparison must be
   *harness-adjudicated* vs *replication + pre-registered checklist +
   subject-matter review* — §7.5. An arm that removes the harness and replaces it
   with nothing measures the wrong thing.
2. **Equal budget stated in a unit the lab actually has.** `[E]` The tree's own
   economics say verification costs wall-clock and judgment costs tokens. So
   "equal budget" must be specified in **operator-minutes and model-tokens
   separately**, or the comparison is uninterpretable. **This alone is an argument
   for X5 (run records) preceding X6.**
3. **Claims that are real and not authored for the experiment**, drawn from the
   hunts' actual output — otherwise it is co-designed calibration, the audit's own
   named blind spot.
4. **Blindness that is structural, not promised** — the tree already knows the
   failure mode: `docs/23` §8.0 records that its own blind exercise ran against a
   live tree while the checks were landing, so "blindness guaranteed by
   chronology" was false as written. Pin the harness; freeze the corpus.
5. **Pre-registered thresholds before any data**, per ROADMAP's ninth-increment
   contamination lesson `[E]`.
6. **Both directions**: at least one claim the harness should kill and one it
   should pass — the repository's own admission rule turned on the experiment.

**Until X6 reports, every "role of the harness / departments / referee" row in
§11 stays WAIT FOR EVIDENCE. Nothing in this document assumes its outcome.**

---

## 13. What we can safely do this week

Everything here is future-neutral (§9), fixes a recorded failure, and is
reversible.

1. **Answer §15 Q2** (is run telemetry plumbing, or the thing `meta/` refuses?).
   One paragraph from the operator. Everything else in this list that touches
   telemetry is gated on it.
2. **X1 — post the Zulip question.** One message; highest information per unit
   cost in the institution.
3. **X2 — send the Remark 1.1 finding.** One email.
4. **X3 — write one HuntSpec + run manifest** on the next hunt opened.
5. **FN3 — schedule `scripts/70_lab_state.py`**, keep its output, and diff it
   between runs. No new code beyond a cron entry and a retention path. Its
   attention queue currently has known entries (2 undemonstrated guards, 3
   unguarded graves) that nothing surfaces.
6. **FN4 — tiered CI** running only the governance tests that already exist
   (`test_docs_numbering`, `test_repo_hygiene`, `test_hunt_probe_discipline`,
   `test_doors`, `test_claim_attribution`, `test_huntspec`, `test_meta_ledger`,
   `test_department_conformance`, `make_context.py --check`) plus the fast unit
   subset. Not `lake build`, not the slow tier.
7. **FN2 — a reconciliation report** (unpushed local commits, pushed branches
   with no PR, branches ahead of main, doc numbers taken on any ref). Read-only.
   It closes the oldest named capability gap in `meta/interventions.jsonl`.
8. **Start X4** by declaring it: the next substantive hunt claim goes through the
   battery as well as through whatever the hunt would have done. Costs nothing
   until a claim appears.
9. **Append to `meta/interventions.jsonl` as things happen** — HANDOFF queue item
   4, costs nothing, and the baseline needs 20–30 sessions before its numbers mean
   anything `[E]`.

**Explicitly not on this list, though tempting:** touching `CLAUDE.md`'s staleness
(archaeology T5). It is real, but it is an edit to the binding rules file and
should be made by the operator with the identity decision, not folded into
maintenance.

---

## 14. What we should explicitly NOT do yet

| Do not | Why | What would change it |
|---|---|---|
| Build a database | Nothing found requires one; JSONL + git already merges cleanly and is the tree's idiom `[E]` | FN1's records exceeding what a file can serve — i.e. after ~a year, not now |
| Build orchestration / start-pause-steer | Explicitly deferred; "measure the loop before automating it"; zero loops measured `[E]` | X8 producing a measurable loop |
| Build a claim registry or typed claim objects | The resumption benchmark **already measured** that typed state did not beat prose; `dossier/` is the standing warning; `docs/19` §6's burden does not reset `[E]` | A repaired E2 plus E3 both passing |
| Delete or refactor `harness/` | X6 has not reported; §7's critique is a *hypothesis*, and the counter-case in §7.7 is real | X6 + X4 + X7 |
| Add department #7 | ROADMAP defers it; broadening before hardening is the memo's own anti-recommendation `[E]` | X7 succeeding |
| Rebrand / rename | Costs cross-references, `docs/doors` tests, and every citation in ROADMAP; and it is downstream of the identity decision | The identity decision |
| Add a funding link, auth, or community infrastructure | **The tree already did this and reversed it** — `d990fee` added a funding link, `4ef30a3` removed it: "Drop the funding link until there is an audience for it" `[E]`. That reasoning has not changed | One external participant |
| Capture chain-of-thought or full tool traces | Excluded by the tree's own proposed schema; no recorded failure needs it; public repo `[E]` | A specific failure that only a trace explains |
| Publish a strategy document | `HANDOFF.md`: strategy stays off-tree because "publishing a strategy document creates a standing incentive to write the next one more flatteringly" `[E]`. **This document is analysis, not strategy — if it starts being cited as a plan, that rule applies to it too** | — |
| Merge or delete the five parallel branches / locked worktree | HANDOFF: report, never merge `[E]` | Operator instruction |

---

## 15. Questions requiring operator judgment

**Q1 — Which future is the institution *for*?** Not which will be worked on —
which one gets the front page, the name, and the benefit of the doubt when budget
is scarce. §6.5 shows this is the one genuinely zero-sum choice, and §11 gates
five other rows on it. Evidence says B is the mission and A is the marketing;
only the operator can say whether that is the intent.

**Q2 — Is a run registry plumbing, or is it the thing `meta/` refuses?**
`meta/README.md` forbids dashboards, KPIs and burndowns on principle, and warns
that the first symptom of decay is `suspicions()` returning nothing while the
ledger grows. FN1/X5 must be classified before they are built. `[I]` My reading
is that a *run record with no aggregate and no score* is on the right side of
that line — the same way `guards.py`'s `fired=None` is — but the rule is the
operator's to interpret.

**Q3 — What is the numerator?** `meta/ledger.py`'s `ratio()` refuses to divide
until someone names the externally checkable output class. Unanswered, the entire
meta-experiment produces no number, and Future C cannot be scored at all.

**Q4 — Does the harness get a rival?** §7.1 shows the harness would not be
admitted as a department by its own rule, because it has lesions and no rival.
Constructing the replication baseline is the single most consequential
methodological choice available, and X6's design depends on it.

**Q5 — What may be captured and published about a session?** Prompt text,
timings, costs, model identity. The repo is public; the operator already keeps
strategy off-tree for a stated reason. FN6 needs a rule.

**Q6 — Do the two `DETECTOR_INADEQUATE` grades get answered?** ROADMAP calls this
"the next pre-registered change"; it has not been made, and it is the cheapest
available test of whether the grade vocabulary is actionable.

**Q7 — Is X8 (three nights of the nightly rig) authorized?** It is one switch,
already built, and it is the only path to "measure the loop" — which every
deferred C item is gated on.

**Q8 — Is the failure corpus an asset to publish deliberately?** §6.6: the
graveyard, the 6/6 hollowing result, `docs/21`'s and `docs/25`'s recorded
failures, and the 11 published defects form something externally unusual that
requires no future to be validated. Nobody has decided whether it is a byproduct
or a deliverable.

**Q9 — What happens to machine-only state?** `automation/`, `external/`,
`.venv-tools/`, `conjectures/`, `~/zeta-reviews-private/` live on one disk and
records already cite them. Under any future this is a durability question, not an
architecture one.

---

## Appendix — evidence index for this document's load-bearing claims

| Claim | Evidence |
|---|---|
| Phase II objective is the only stated objective in a binding file | `CLAUDE.md` §honest-scope |
| Charter adopted, orchestration refused | `ROADMAP.md` "The outside memos, triaged"; `docs/26` §6 closing |
| Four non-math departments exist to test generality | `README.md` lines 98–102 |
| The harness protocol has zero live clients | `grep -rn "run_battery\|validate_battery\|audit_department\|ClaimReport"` → only `harness/`, `tests/`; zero in `hunts/`, `scripts/`, `zeta/`, `ontology/` |
| Live research re-implemented the roles by hand | `hunts/wide_search/probe.py` — `rival_check()` wrapping `zeta.epstein.battery`, a hand-rolled `null_band()` |
| The zeta department adjudicates only its calibration pair | `harness/departments/zeta_department.py` — `ReferenceClaim(functional_equation)`, `ReferenceClaim(multiplicativity)` |
| The roles predate the protocol | `docs/17` dated 2026-08-05; §5 is a postscript dated 2026-08-06 |
| 6/6 blind authors reached CALIBRATED with hollow batteries | `ROADMAP.md` 2026-08-10; `docs/23`; `harness/blind_authoring_2026_08_09/` |
| The audit penalised honest fidelity | `docs/23` §8.6; `harness/README.md` §"Your decoys and lesions get poked…" |
| `rival-separator-abundance` acts on nothing | `ROADMAP.md` 2026-08-10 |
| Promotion gate is KEEP AS PROBE with recorded failures | `docs/21` §10–11 |
| A null control reclassified a research finding as generic | `NULLCONTROLS.md`; `ROADMAP.md` "Previous build: moments" |
| Typed state did not beat prose | `ROADMAP.md` 2026-08-09 "The resumption benchmark ran…" |
| E1–E5 with kill conditions already designed in-tree | `docs/reviews/consultant-thesis-analysis.md` §H, §I |
| The funding link was added and reversed | commits `d990fee`, `4ef30a3` |
| No equal-budget harness evaluation exists in-tree | repo-wide search for "equal budget", "equal-budget", "blinded evaluation", "harness evaluation", "matched budget" |
| Nightly rig has run zero nights | `ROADMAP.md` "The AI-implementation half" |
| HuntSpec/run manifests have zero users | `grep -rl '```huntspec' hunts/` and `grep -rl runmanifest hunts/` return only `HUNTSPEC.md` |
| `70_lab_state.py` derives an attention queue nothing consumes | `scripts/70_lab_state.py:_attention_queue`; `docs/26` §6 |
| Intervention #1 names post-merge reconciliation | `meta/interventions.jsonl` line 1 |

---

*This is cartography, not a plan. §11 classifies; §12 tests; §15 asks. Nothing
here authorizes a change, and the harness critique in §7 is a hypothesis with a
named experiment attached — not a verdict.*
