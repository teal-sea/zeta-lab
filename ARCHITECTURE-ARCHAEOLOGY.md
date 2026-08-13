# ARCHITECTURE-ARCHAEOLOGY.md

*A reconstruction of what this repository actually is, dated 2026-08-13, written
from the tree as primary evidence. It proposes nothing, moves nothing, renames
nothing. Where a conclusion rests on a file, the file is named; where it rests on
inference, the inference is marked.*

**Method and its limits.** Everything below was derived by reading the tree at
`claude/architecture-archaeology-e4yre5` (= `origin/main` at `32e4428`), plus
`git log`. Three limits on the evidence, stated up front because they bound
several sections:

1. **This clone is shallow.** `.git/shallow` exists; the earliest commit
   reachable here is `89e16d1` (2026-08-07). `ROADMAP.md` documents decisions
   from 2026-08-02 through 2026-08-06 whose commits are *not in this clone*.
   The pre-2026-08-07 history is reconstructed from prose (ROADMAP/HANDOFF/docs),
   not from commits.
2. **Repository state ≠ machine state.** Four load-bearing directories are
   gitignored and empty or absent here: `conjectures/` (only `.gitkeep`),
   `external/` (only `README.md`), `automation/` (absent), `.venv-tools/`
   (absent). `HANDOFF.md` also names off-repo material in
   `~/zeta-reviews-private/` and a private vault. A reader of this repo sees a
   strict subset of the laboratory.
3. **No suite was run.** There is no `.venv` in this environment, so every test
   count, timing and backend statement below is quoted from the tree's own
   records, not re-measured.

---

## 1. Executive finding: what this repository actually is

**This is not a zeta repository with a validation framework bolted on. It is a
verification institution with two subjects it cares about (ζ, and itself) and
four more it keeps in order to prove the machinery is not about ζ.**

More precisely, the repository is **three co-resident laboratories plus one
governance layer**, and they are separable:

| Layer | What it studies | Where |
|---|---|---|
| **L1 — the subject laboratory** | the Riemann zeta function and RH-adjacent mathematics | `zeta/`, `lean/`, `hunts/`, `docs/00–16`, `scripts/01–41` |
| **L2 — the referee** | *whether a demonstration is about its subject at all* — subject-independent by test | `harness/`, `ontology/` (core), `compiler/`, `docs/17,20,21,22,23` |
| **L3 — the meta-laboratory** | the research *system*: what humans had to do, what the operator's judgment is worth, what a model belongs near | `meta/`, `docs/19,25,26`, `docs/reviews/` |
| **G — governance** | vocabulary, scope, admission, doc numbering, hygiene, staleness | `CLAUDE.md`/`AGENTS.md`, `tests/test_*` (about 20 of the 64 test files are governance rather than mathematics), `scripts/make_context.py`, `scripts/science_preflight.py` |

The single organizing idea, stated in `docs/20` §1 and visible everywhere, is
recursive and is the actual architecture:

> **No instrument's silence counts as evidence until that instrument's power has
> been measured against planted violations.**

Applied to ζ it gives the battery. Applied to the battery it gives the integrity
audit (`harness/integrity.py`) and department #5, `referee`. Applied to the
audit it gives the blind-authoring corpus (`harness/blind_authoring_2026_08_09/`,
ten independently authored departments, six of six hollow ones graded
`CALIBRATED`). Applied to the repo's ad-hoc guards it gives `harness/guards.py`.
Applied to cross-checks it gives `harness/independence.py`. Applied to the human
loop it gives `meta/ledger.py`. The recursion is explicitly bottomed out in
`docs/20` §6 ("no meta-meta-referee") — a deliberate architectural decision, not
an omission.

**The second finding is economic, and it is the one that explains the last
week's shape.** `HANDOFF.md` (2026-08-12) states it plainly: *verification here
costs wall-clock, not tokens; judgment costs tokens.* 8739 Lean kernel jobs and
~2200 tests consume no model output. That asymmetry — cheap machine adjudication,
expensive human/model judgment — is why the repository invests so heavily in
mechanizing rejection and so little in generating candidates.

**The third finding is the gap this document exists to expose.** The *scientific*
architecture is unusually well instrumented, versioned, and self-auditing. The
*operational* architecture is almost entirely prose in three enormous Markdown
files (`ROADMAP.md` 1597 lines, `HANDOFF.md` 1126, `CLAUDE.md` 429), plus git
history, plus a set of directories that do not exist in the repository at all.
There is **no CI**, **no telemetry**, **no run registry**, **no cost accounting**,
and **no provenance graph**. Sections 7–10 measure that precisely.

---

## 2. Current architecture

### 2.1 First-class concepts, with evidence

Concepts are listed with: meaning · implementation · dependents · **F**undamental
or **H**istorical/convenience.

| Concept | Meaning in *this* repo | Implemented in | Depended on by | F/H |
|---|---|---|---|---|
| **Laboratory** | the whole tree; a workbench, explicitly not a proof attempt | `README.md`, `docs/00` | everything | F |
| **Department** | *a registered subject + a battery of controls that could refute claims in its name + a guide page + reference claims with known verdicts + declared detectors + a scope + a provenance record*. Registration = one line in `KNOWN_DEPARTMENTS` | `harness/protocol.py:Department`, `harness/departments/__init__.py` | conformance suite, integrity audit, `docs/doors/README.md` | **F** |
| **Subject** | a thing a claim can be evaluated against; the genuine article *and* every rival are Subjects | `harness/protocol.py:Subject` (a `typing.Protocol`) | Battery | F |
| **Battery** | the unit of refereeing: rivals + decoys + surrogates + lesions | `harness/protocol.py:Battery`, `validate_battery` | Department admission | **F** |
| **Rival** | structure-matched negative control — shares the structure the claim leans on, lacks the property. "The sharpest of the four… a modus tollens" | role of `Subject`; canonical instance `zeta.epstein.battery` (Davenport–Heilbronn) | gate #3, every hunt's checklist | **F** |
| **Decoy** | ablation — swap the substantive input, see if the measurement moves | `harness/protocol.py:Decoy`, `run_ablation` | admission rule | F |
| **Surrogate** | null model — reproduce the observation from no substantive input | `harness/protocol.py:Surrogate`, `run_nulls`, `run_null_band`; subject side `zeta/surrogate.py`, `NULLCONTROLS.md` | admission rule | F |
| **Lesion** | planted fault; detector power is measured, never assumed | `harness/protocol.py:Lesion`, `run_power` | admission rule, `docs/22` | **F** |
| **Detector** | a *named* instrument staked on noticing lesions; power **and** specificity measured | `NamedDetector`, `DetectorVerdict`, `run_detector` | `validate_department` | F |
| **Claim / ClaimOutcome** | a predicate evaluated against subjects; never carries a truth value on its own | `ClaimOutcome`, `ReferenceClaim` | `run_battery` | F |
| **Integrity grade** | five states of *the battery*, no scalar: `CALIBRATED` / `DETECTOR_INADEQUATE` / `UNMEASURED` / `CONTAMINATED` / `HOLLOW` | `harness/integrity.py` (19 named checks; `_HOLLOW_CHECKS` = 13 of them) | `ClaimReport`, `promotion.decide` | **F** |
| **ClaimReport** | pairs a claim outcome with its battery's grade and *cannot state one without the other*; `.dangerous` is green-claim-from-ungraded-battery | `harness/integrity.py` | `docs/20`, promotion gate | F |
| **Sham mode** | a named way a battery can be hollow while structurally complete; 15 catalogued, **6 with `caught_by=None`** (pinned blind spots) | `harness/integrity.py:SHAM_MODES`, `harness/shams.py` | `tests/test_harness_integrity.py`, department #5 | **F** |
| **Certainty ladder** | four rungs for a *claim*: measured → hardened → kernel-checked → externally reviewed; a composite takes its **weakest** step | `CLAUDE.md` (amended 2026-08-12), applied in `README.md` front table, `docs/27`, `hunts/frontier_math/PROOF-LEDGER.md` | all claim language | **F** |
| **Reserved word (`certified`)** | owned by `zeta/rigor.py` (enclosure-carrying numerics) and `lean/` (kernel-checked); two *different* regimes | `zeta/rigor.py`, `lean/`; enforced lexically under `hunts/` by `tests/test_hunt_probe_discipline.py` | everything that describes evidence | **F** |
| **Referee** | the machinery itself, registered as department #5 with the reconstructed `431cc74` sham as its held-out rival | `harness/departments/referee_department.py`, `docs/doors/referee.md` | `docs/20` | F |
| **Discovery funnel** | generate → deduplicate → knownness → cheap screens → expensive screens → terminal, with count-in = count-out conservation | `ontology/funnel.py:STAGES`, `schema.py` (5 kinds, 6 verdicts), `metrics.py` | `scripts/13_discovery_run.py` | F |
| **Candidate** | one of 5 kinds (`constant`/`asymptotic`/`relation`/`extremal`/`structural`); carries a `proof_gap`; a survivor is a **lead**, never a result | `ontology/schema.py:Candidate` | funnel, ledger | F |
| **Ledger** | append-only JSONL record. **Four distinct ledgers exist** — see §2.3 | `ontology/ledger.py`, `meta/interventions.jsonl`, `harness/departments/{graveyard,guard,review}_ledger.py` | metrics, `scripts/70_lab_state.py` | F |
| **Graveyard / KilledResult** | a killed result as a typed card: status / why / caught-by / regression test / formal obstruction / recurrence guard. `unguarded()` is a worklist | `harness/graveyard.py`, `harness/departments/graveyard_ledger.py` (3 graves) | lab-state view | F (new) |
| **Guard record** | detection power of an ad-hoc guard as a **tri-state**: `fired=None` means nobody demonstrated anything | `harness/guards.py`, `guard_ledger.py` (5 records), `tests/test_guard_ledger.py` | attention queue | F (new) |
| **Independence radius** | how deep two "independent" verification paths share leading layers before diverging; plus shared/reconvergent/distinct layers; `bool(report)` raises | `harness/independence.py`; worked subject = the `rigor.py` two-backend cross-check (radius 3 of 5) | `docs/26` §1 | **F** (new) |
| **Preregistration / promotion boundary** | criteria frozen by *digest of pre-existing evidence*; `decide()` → ALLOW/BLOCK with every reason; `NaiveGate` is the mandatory null control | `harness/preregistration.py`, `harness/promotion.py` | `docs/21` | H→probe (explicitly "KEEP AS PROBE", not a capability) |
| **Provenance** | *declared* data about authorship/independence/contamination — attestation, never proof | `harness/provenance.py` (8 declarable fields) | integrity audit, department contract | F |
| **Hunt** | scoped exploratory study; the **one** place a claim may be written before any control has run. Nothing in `hunts/` is a result; reserved+banned vocabulary enforced on the bytes | `hunts/README.md`, `tests/test_hunt_probe_discipline.py` | 12 live hunts | **F** |
| **MISSION.md** | per-area scope contract: what this work may and may not touch | every `hunts/*/MISSION.md` | multi-agent discipline (`CLAUDE.md`) | F |
| **HuntSpec** | machine-readable contract block inside a MISSION: question / frontier / dead_routes / required_oracles / kill_conditions / agents_may / agents_may_not. `required_oracles` rejects any entry naming a model | `hunts/HUNTSPEC.md`, validator lives **only** in `tests/test_huntspec.py` | new hunts | probation |
| **Run manifest** | `runmanifest` block appended by an autonomous run: what ran, when, what it left, one outcome sentence | `hunts/HUNTSPEC.md` §"Run manifests" | — (see §9) | probation |
| **Dossier** | typed research state; "verified" split into four independent axes (`numeric`/`certified`/`literature`/`formal`), no aggregate, `Support.__bool__` **raises** | `dossier/`, `docs/19` | one worked example (Hardy Z) | probe — admission path *closed* by a failed benchmark |
| **Standing review** | two attacks per claim (blind + white-box); blindness structural (brief built without the reasoning field); the system may never resolve a dispute it is party to | `harness/review.py`, `review_ledger.py` | attention queue | F (new) |
| **Formalization / Lean arm** | second certainty regime; nothing counts with a `sorry`; 58 files, `ZetaLean` + `zeta23ext` | `lean/`, `hunts/frontier_math/zeta23ext/` | rungs 1–3, the frontier candidate | **F** |
| **Proof-agent adapter** | external prover output is *input*: static refusal scan (`sorry`/`admit`/`axiom`/`native_decide`) + local `lake build` | `lean/proof_adapter.py`, ledger `lean/ARISTOTLE-RUNS.md` | Aristotle batches 1–4 | F (new) |
| **Operator** | the human research director; holds authority the machine may not take (`meta/operator-functions.md`: severity calibration, scope discipline, skepticism routing, **authority**) | `meta/`, HANDOFF "Operator decisions" | everything | **F** |
| **Handoff** | between-session state, serial channel | `HANDOFF.md` | next session | F |
| **ACTIVE-CLAIMS** | the *parallel* channel — concurrent sessions declare what they are writing, advisory not locking | `hunts/frontier_math/ACTIVE-CLAIMS.md` | concurrent sessions | F (new, 2026-08-12) |
| **Door / guide** | one short page per audience; "the cost of adding a purpose is a guide page plus a test that its command still works" | `docs/doors/` (5 audience + 6 department pages), `tests/test_doors.py` | README table | F |
| **Agent** | not a first-class object anywhere in code. Agents appear only as *roles in prose* (director run) and as `agents_may`/`agents_may_not` lists in HuntSpec | `hunts/director_run/MISSION.md`, `hunts/HUNTSPEC.md` | — | **H / absent** — see §9 |

**Concepts that are NOT first-class, despite appearances.** Worth stating because
imposing them would be the error this exercise is meant to avoid:

- There is **no "Institution" or "Lab" object.** The institution exists as
  governance prose plus a test suite.
- There is **no orchestrator.** `ROADMAP.md` deliberately defers it ("measure the
  loop before automating it"), and `docs/26` §6 confirms it is still unbuilt.
- There is **no agent registry, run registry, or model registry.**
- **"Experiment" is not a type.** Experiments are scripts + JSON + a Markdown
  write-up, per-hunt.
- The **rogue-lab prototypes** (`ontology/01_*.py` … `16_*.py`) are explicitly
  historical: kept because `docs/17` dissects four of them and
  `tests/test_rogue_lab_controls.py` pins their control results. **H.**

### 2.2 Current-state ASCII architecture

```
                       ┌──────────────────────────────────────────────┐
                       │  OPERATOR (human research director)          │
                       │  authority · severity calibration · scope    │
                       │  discipline · skepticism routing             │
                       │  state: memory + CLI sessions + git          │
                       └───────┬──────────────────────────┬───────────┘
                               │ writes prose             │ reads prose
                               v                          ^
   ╔═══════════════════════════════════════════════════════════════════════╗
   ║  G · GOVERNANCE  (no code object; prose + tests)                      ║
   ║  CLAUDE.md/AGENTS.md — binding rules, certainty ladder, reserved word ║
   ║  ROADMAP.md — decisions, non-goals, known gaps, next build            ║
   ║  HANDOFF.md — between-session state (serial)                          ║
   ║  ACTIVE-CLAIMS.md — between-session state (parallel, frontier only)   ║
   ║  MISSION.md per area · docs/doors/ per audience                       ║
   ║  enforced by: tests/test_{doors,docs_numbering,repo_hygiene,          ║
   ║    hunt_probe_discipline,claim_attribution,huntspec,meta_ledger}.py   ║
   ║    + scripts/make_context.py --check + scripts/science_preflight.py   ║
   ║  NOT enforced by: any CI (there is none)                              ║
   ╚═══════════════════════════════════════════════════════════════════════╝
              │                          │                        │
   ┌──────────v───────────┐   ┌──────────v──────────┐   ┌─────────v─────────┐
   │ L1 SUBJECT LAB       │   │ L2 REFEREE          │   │ L3 META LAB       │
   │                      │   │ (domain-agnostic    │   │                   │
   │ zeta/ (25 modules)   │   │  by 3 seam tests)   │   │ meta/ledger.py    │
   │  core zeros explicit │   │                     │   │  interventions    │
   │  statistics heatflow │   │ harness/protocol.py │   │  .jsonl (33 recs) │
   │  weil epstein li     │   │  Subject Decoy      │   │ operator-         │
   │  criteria moments    │   │  Surrogate Lesion   │   │  functions.md     │
   │  finitefield         │   │  NamedDetector      │   │ ai-components.md  │
   │  rigor.py  ◄─── the  │   │  Battery Department │   │ asymmetry-        │
   │   "certified" owner  │   │  validate_battery   │   │  experiment.md    │
   │   (2 ball backends)  │   │  validate_department│   │                   │
   │                      │   │        │            │   │ refusals: no      │
   │ lean/ (58 files)     │   │        v            │   │  score, ratio     │
   │  ◄─ the other        │   │ integrity.py        │   │  must name its    │
   │   "certified" owner  │   │  19 checks → 5      │   │  numerator,       │
   │   0 sorrys, 8739     │   │  grades; SHAM_MODES │   │  "automated"      │
   │   kernel jobs        │   │  15 modes, 6 blind  │   │  costs an artifact│
   │  proof_adapter.py ───┼──►│  ClaimReport        │   └───────────────────┘
   │   (external provers  │   │        │            │
   │    = generators)     │   │        v            │
   │                      │   │ promotion.py +      │
   │ hunts/ (12)          │   │ preregistration.py  │
   │  probe area; nothing │   │  decide()→ALLOW/    │
   │  here is a result    │   │  BLOCK; NaiveGate   │
   │  lexical bans on the │   │  null control       │
   │  bytes               │   │  [KEEP AS PROBE]    │
   │                      │   │                     │
   │ ontology/domains/    │   │ provenance.py       │
   │  (subject-aware)     │   │ independence.py     │
   └──────────┬───────────┘   │ guards.py           │
              │               │ graveyard.py        │
              │               │ review.py           │
              │               │ shams.py            │
              │               └──────────┬──────────┘
              │                          │
              │            ┌─────────────v──────────────────────────┐
              └───────────►│  harness/departments/  (the seam)      │
                           │  KNOWN_DEPARTMENTS = 6 entries         │
                           │   zeta · finitefield · compiler ·      │
                           │   croniter · referee · stateval        │
                           │  + graveyard_ledger · guard_ledger ·   │
                           │    review_ledger  (real records)       │
                           │  audited by                            │
                           │  tests/test_department_conformance.py  │
                           │  (19 tests × 6 departments)            │
                           └─────────────┬──────────────────────────┘
                                         │
                     ┌───────────────────v────────────────────┐
                     │ ontology/ (core, domain-agnostic)      │
                     │  schema · registry · ledger · funnel · │
                     │  metrics · knownness · historical_cases│
                     │  scout / scout_online (OEIS, arXiv,    │
                     │   zbMATH — leads only, no NOVEL)       │
                     │  funnel: generate→dedup→knownness→     │
                     │   cheap→expensive→terminal             │
                     │  → conjectures/  [GITIGNORED, PRIVATE] │
                     └────────────────────────────────────────┘

   READ-ONLY VIEW:  scripts/70_lab_state.py  →  one static HTML file
     rendered from graveyard + guards + reviews + independence + hunts.
     "research state, not agent activity". No scripts, no network,
     no orchestration state. Consumes nothing that does not already
     live in the tree.

   OFF-TREE / MACHINE-ONLY (invisible to any reader of this repo):
     conjectures/  (private ledger, separate private git repo)
     external/     (7 cloned outside repos, ~115 MB)
     automation/   (nightly rig: mission, journal, arm/disarm — 0 nights run)
     .venv-tools/  (aristotlelib, openevolve)
     ~/zeta-reviews-private/ (futures map, blind pair, E1–E3 protocol)
     private vault (operator's)
```

### 2.3 The four ledgers, and why "ledger" is ambiguous

The word *ledger* names four different things. This is a real ambiguity in the
current architecture, not a naming slip:

| Ledger | Content | Format | Public? | Authority |
|---|---|---|---|---|
| `conjectures/` | funnel candidate + run streams | append-only JSONL | **private** (gitignored; separate private repo via `scripts/ledger_sync.sh`) | authoritative for funnel metrics |
| `meta/interventions.jsonl` | human interventions, meta-observations, judgments | JSONL | public | authoritative for the meta-experiment |
| `harness/departments/{graveyard,guard,review}_ledger.py` | killed results, guard power, standing reviews | **Python literals** | public | authoritative for the attention queue |
| `hunts/frontier_math/PROOF-LEDGER.md` + `hunts/director_run/CLAIMS.md` | obligation-by-obligation claim state | Markdown tables | public | authoritative for the live frontier |

Only the first two are machine-queryable as data. The third is queryable only by
importing Python. The fourth — which carries the repository's *most important
current claims* — is prose.

---

## 3. Architectural evolution

`ROADMAP.md`'s own "What is built" table gives phases 1–6. The evidence supports
a longer sequence, with two transitions the table does not name. **Derived**
order (not the one in the prompt):

```
 [1] classical zeta workbench                    (docs 00-08; core/zeros/explicit/
      "every identity a measured defect"          statistics/heatflow)
        │  problem: identities can be assumed; docstring numbers can rot
        │  abstraction: measured *defect* functions + a test per number
        ↓  SURVIVED — still the house style
 [2] ontology gates                              (weil, epstein; docs 09-11)
        │  problem: "new mathematics" was a slogan with no test
        │  abstraction: four GATES, incl. gate #3 = the Davenport-Heilbronn
        │               counterexample battery
        ↓  SURVIVED — gate #3 is now the canonical *rival*
 [3] certainty regimes                           (rigor.py ball arithmetic; li,
        │  problem: "verified" conflated float luck with proof   finitefield, criteria)
        │  abstraction: the reserved word + safe failure (proven_sign→0)
        ↓  SURVIVED — and later HARDENED into the 4-rung certainty ladder
 [4] discovery machinery                         (ontology/ + scripts/13)
        │  problem: generation is cheap; nothing measured its own hit rate
        │  abstraction: schema-first funnel with conservation + conversion metrics
        ↓  SURVIVED but STARVED — expected yield ≈ 0 *by design* (known gap #3)
 [5] formal arm                                  (lean/, rungs 1-3)
        │  problem: numerics can never be a theorem
        │  abstraction: "nothing counts with a sorry"
        ↓  SURVIVED — now the largest single subsystem by file count
 [6] FALSIFICATION HARNESS                       (docs/17, 2026-08-05/06)
        │  FORCING EVENT: five spectral "explanations" of RH arrived in ONE DAY
        │  from rogue-lab sessions. The rebuttal cost days; generation cost minutes.
        │  abstraction: the four instruments, run by hand
        ↓  SURVIVED
 [7] SUBJECT-INDEPENDENT PROTOCOL + DEPARTMENTS  (harness/, 2026-08-06)
        │  problem: the instruments were welded to zeta, so a second subject
        │           could inherit the funnel and not the referee
        │  abstraction: Subject/Decoy/Surrogate/Lesion → Battery → Department;
        │               admission rule "no department without a battery";
        │               the seam enforced by AST scan + sys.modules + lexical scan
        ↓  SURVIVED — and is now the thing the repo leads with
 [8] departments #2-#4                           (finitefield, compiler, croniter)
        │  problem: "domain-agnostic" was an argument, not a measurement
        │  abstraction: none new — protocol.py did NOT change (the point)
        ↓  SURVIVED — foreign-ingestion half of known gap #1 now measured
 [9] THE REFEREE REFEREED                        (integrity.py, 2026-08-09)
        │  FORCING EVENT: commit 431cc74's sham battery — structurally complete,
        │           validated, passed the conformance suite of its day, HOLLOW.
        │           Caught by a human. Plus: the resumption benchmark showed
        │           blinded agents reliably MISS hollow verification.
        │  abstraction: claim outcome ⟂ battery integrity; 5 grades; ClaimReport
        │               that cannot state one without the other; SHAM_MODES with
        │               pinned blind spots; department #5 = the referee itself
        ↓  SURVIVED — and immediately produced its own worst result (see below)
[10] the audit's limits, measured                (docs/21, 23; 2026-08-09/10)
        │  FORCING EVENT #1: an independent party reached CALIBRATED with a
        │           hollow battery ON THE FIRST ATTEMPT, zero adaptation.
        │  FORCING EVENT #2: repeated at n=6 — SIX OF SIX blind authors certified
        │           transparently absurd claims (Mercury retrograde over a
        │           shipping manifest) as `distinguishes`.
        │  FORCING EVENT #3: the honest controls found the audit was REWARDING
        │           reverse-engineering and PUNISHING fidelity (2 of 4 honest
        │           parties graded HOLLOW for writing faithful instruments).
        │  abstraction: blind spots as first-class pinned records; the `probe`
        │               convention; "the audit's real constraining power is over
        │               *mechanical* emptiness"
        ↓  SURVIVED, with the referee department now FAILING ITS OWN AUDIT
        │  (test renamed to ..._does_not_survive_its_own_audit and asserts it)
[11] THE DIRECTOR RUN                            (docs/25, 2026-08-10/11)
        │  problem: the operator had no way to know whether the agenda was right
        │  abstraction: nine investigators with CONFLICTING mandates, isolated
        │               contexts, "the generator of a claim never also judged it"
        │  result: SIX defects in the repo's own recorded claims, incl.
        │          rigor.py returning a WRONG proven_sign on BOTH backends
        │          (shared input-parsing layer)
        ↓  SURVIVED as a *pattern*; not yet as durable machinery
[12] THE ADOPTED BUILDS                          (docs/26, 2026-08-11, one day)
        │  FORCING EVENT: two outside memos arrived proposing a "research
        │           operating system". ROADMAP triaged them.
        │  abstractions: independence radius · guard ledger · HuntSpec ·
        │               proof-agent adapter · literature scout · standing review ·
        │               graveyard · lab-state view · run manifests
        ↓  TOO YOUNG TO SCORE — docs/26 itself says so: "the first time any of
        │  them catches something real ... is when this document gets its first
        │  follow-up section." No such section exists as of 2026-08-13.
[13] FRONTIER TRANSPLANT + PARALLEL SESSIONS     (hunts/frontier_math, 2026-08-11→13)
        │  problem: multiple concurrent sessions collided three times in one day
        │  abstraction: ACTIVE-CLAIMS.md — a *parallel* coordination channel,
        │               because HANDOFF is a serial one
        ↓  LIVE. This is where the repository's attention actually is.
```

### 3.1 The recurring failures that generated the architecture

This is the most reliable signal in the tree; every guard has an incident behind
it.

| Recurring failure | Instances | What it produced |
|---|---|---|
| **An instrument exists, therefore it works** | `431cc74` sham battery; `python-flint` absent so the two-backend cross-check was dormant while the suite showed "5 skipped"; a completeness guard whose "independent" reference was the same technique on a coarser grid; a scan column structurally unable to read False | `integrity.py`; the AGENTS.md backend check; **`harness/guards.py`** (`fired=None` tri-state); `science_preflight.py` |
| **Structural completeness ≠ verification** | the sham; 6/6 blind hollow batteries; the promotion gate promoting a hollow battery's astrological claim with an *empty reason list* | `SHAM_MODES` with `caught_by=None` rows; department #5; `docs/21` §10.4 pinned as a test |
| **"Independent" checks that share a layer** | both rigor backends wrong from one parsing layer; two `-O` levels through one toolchain (`compiler/FINDINGS.md` §6) | **`harness/independence.py`** — independence radius |
| **An artifact does not respond to added precision** | PSLQ's fake relation stable at 300 digits; `mp.diff` returning exactly 0 on rounded functions; a sign-flipped stencil | the standing precision-response rule; 40-digit PSLQ guard + `inconclusive_floor_noise`; regression pins |
| **A probe that bypasses the battery** | Hunt #2's "definitively placing zeros off the critical line" reached HANDOFF; its test set *was* the rival set | `hunts/` classified as a probe area; `tests/test_hunt_probe_discipline.py` reading the bytes |
| **Prose drifts from the structured fact it restates** | an outside reader found two Λ-bound attribution defects that 2135 tests had walked past | `tests/test_claim_attribution.py` — and its own docstring records **two failed attempts**, one of which planted a fault shaped to fit the detector |
| **Co-designed measurement** | the meta cohort authored by the agent it describes; the audit's `co-designed-calibration` blind spot | `provenance.py` attestations; `review.py`'s structural blindness; "the system may not resolve a disagreement it is party to" |
| **Verdict-shaped defaults** | a truncation guard encoding "cannot decide" as the favourable verdict | `proven_sign → 0`; `fired=None`; `UNKNOWN` capping the integrity grade |
| **Session/tree collisions** | doc 21 numbered twice; doc 26 collided across an unmerged branch; three frontier collisions in one day; docs scanner walking into nested checkouts | `tests/test_docs_numbering.py`; `ACTIVE-CLAIMS.md`; the scanner's `.git`-pruning fix |

**Reading:** every durable abstraction in this repository was produced by a
*specific recorded incident*, and almost all of them are about verification
failing quietly rather than about mathematics being wrong. That is the real
architecture.

---

## 4. The department model

**A department is not a module, a directory, a team, or a topic.** From
`harness/protocol.py`, `harness/README.md`, `docs/doors/README.md` and
`tests/test_department_conformance.py`, a department is exactly:

```
Department = Battery                      (≥1 rival, ≥1 (decoy | surrogate), ≥1 lesion)
           + ≥1 NamedDetector             (power AND specificity measured)
           + scope                        (what a pass licenses)
           + Provenance                   (declared authorship/independence)
           + ≥2 ReferenceClaims           (≥1 the battery must REJECT,
                                           ≥1 it must PASS)
           + a door page on disk          (docs/doors/<name>.md)
           + one line in KNOWN_DEPARTMENTS
```

Registration semantics, and this is the load-bearing part: **`KNOWN_DEPARTMENTS`
is a `dict[str, str]` mapping name → module path, and
`tests/test_department_conformance.py` is parametrized over it.** Adding the line
turns 19 audits on. There is no human approval step. `validate_battery` refuses a
battery that *could never fail*; `validate_department` refuses one with no
detector or no scope.

**The six departments and what each was admitted to test:**

| # | Name | Subject | The architectural question it was admitted to answer |
|---|---|---|---|
| 1 | `zeta` | ζ and RH | (the origin — the instruments were abstracted *from* it) |
| 2 | `finitefield` | curves over F_p | can every instrument be **exact**? (rivals = counterfeit Lefschetz profiles Hasse forbids) |
| 3 | `compiler` | LLVM IR rewrites | does a **foreign vocabulary** subject fit? |
| 4 | `croniter` | cron `#`/`W` union semantics | does a subject **born outside this tree**, with battery content authored by an independent party, fit the *unchanged* protocol? |
| 5 | `referee` | batteries themselves | can the machinery be its own subject? (held-out rival = the reconstructed `431cc74` sham) |
| 6 | `stateval` | statistical model evaluation | does the **single-run assumption** all earlier departments share survive a distributional claim? (it did not — it produced `run_null_band` and `payloads_same`) |

**Three rules that define the concept negatively, and are more informative than
the positive definition:**

1. *A department whose battery is another department's battery is not a
   department.* This is why `dossier/` and `hunts/` are permanently probes: their
   rivals are the zeta department's rivals (`docs/19` §6, `hunts/README.md`).
2. *No department without a battery.* Work nothing in the tree can falsify is
   exploratory and lives where nobody mistakes it for a result.
3. *A hunt cannot become a department by growing.*

**What the model has actually demonstrated, and what it has not.** `protocol.py`
survived departments #2–#4 unchanged; it then changed **once, deliberately**
(2026-08-09: detectors, scope, provenance, `run_null_band`) on the evidence of
three recorded incidents. The shared audit has needed exactly two
generalizations, and **both were the same mistake — payload-shape guessing** —
which ROADMAP records as a standing prediction about where the next false-generic
will appear.

**What it has not demonstrated (known gap #1):** *adoption by an outside team.*
Every department was orchestrated by this repository's own process. And two
departments — `compiler` and `referee` — currently grade `DETECTOR_INADEQUATE`;
the conformance cases xfail with the reason rather than being exempted.

---

## 5. Referee / shared scientific spine

The spine is thin on purpose. Four layers, each with a declared trust boundary:

```
 layer 0  SEAM            protocol.py imports nothing from any laboratory,
                          names no computed quantity. Enforced 3 ways:
                          AST import scan · a subprocess asserting no lab
                          module enters sys.modules · a lexical scan for
                          subject-matter vocabulary. Runs in ~0.1 s, which
                          is itself the check.
                             ↓
 layer 1  ADMISSION       validate_battery / validate_department.
                          Catches MISSING instruments. Cannot catch EMPTY ones.
                             ↓
 layer 2  CONFORMANCE     19 tests × 6 departments, verdicts RE-DERIVED
                          rather than trusted.
                             ↓
 layer 3  INTEGRITY       19 named checks → 5 grades (no scalar).
                          13 are hollow-class; UNKNOWN caps the grade.
                          SHAM_MODES: 15 modes, 6 with caught_by=None.
                          MEASURED POWER: catches mechanical emptiness.
                          MEASURED LIMIT: 6 of 6 blind adversarial authors
                          reached CALIBRATED with batteries measuring nothing.
                             ↓
 layer 4  PROMOTION       decide() → ALLOW/BLOCK against a preregistration
          [PROBE ONLY]    whose criteria are digests of pre-existing evidence.
                          Mandatory null control: NaiveGate.
                          RECORDED FAILURES: the mirror condition is
                          unreachable; the gate inherits every blind spot
                          beneath it; it promoted a held-out hollow battery's
                          claim with an EMPTY reason list.
                             ↓
 layer 5  BOTTOM          docs/20 §6: deterministic re-execution · the
                          conformance suite as a second expression of the
                          same requirements · one held-out mutant ·
                          human-attested provenance. NO META-META-REFEREE.
```

Two additions from 2026-08-11 sit *beside* rather than inside this stack, and
apply to instruments the harness never covered:

- **`harness/independence.py`** — bounds what "checked twice" is worth. The
  declared subject is the `rigor.py` cross-check itself: **radius 3 of 5**, one
  reconvergent layer (the S(T)/N(T) interval summation), exactly one layer
  implemented twice (the ball arithmetic).
- **`harness/guards.py`** — the same discipline applied to the repository's
  ~ad-hoc guards. Five records: three demonstrated by live mutants, **two
  honestly undemonstrated** (`fired=None`).

**The spine's honest self-assessment, in its own words:** the audit's real
constraining power is over *mechanical* emptiness; the two choices that decide
whether a battery can reject anything — how near the rivals are, and whether the
detector is independent of the claim — remain the author's, and every layer built
on the grade inherits that.

---

## 6. Research lifecycle

Reconstructed from `hunts/README.md`, `ontology/funnel.py`, `docs/25`,
`harness/`, `lean/` and the HANDOFF records. There are **two entry paths and
three exits**, and they are not symmetric.

```
                    ┌────────────────────────────────────────┐
                    │ ORIGIN                                 │
                    │  a) operator hypothesis / direction    │
                    │  b) outside memo (docs/reviews/)       │
                    │  c) funnel generator (ontology/)       │
                    │  d) an incident — something broke      │
                    └───────────────┬────────────────────────┘
                                    │
              ┌─────────────────────┴────────────────────────┐
              │ (a,b,d)                                (c)   │
              v                                              v
   ┌──────────────────────┐                    ┌────────────────────────┐
   │ HUNT                 │                    │ FUNNEL                 │
   │ hunts/<name>/        │                    │ generate               │
   │  MISSION.md (scope)  │                    │  → deduplicate         │
   │  [+HuntSpec if new]  │                    │  → knownness           │
   │  probe.py, results   │                    │  → cheap screens       │
   │  *.md write-ups      │                    │  → expensive screens   │
   │                      │                    │  → terminal            │
   │ MAY record a claim   │                    │ count in = count out   │
   │ BEFORE any control.  │                    │ verdicts: open known   │
   │ Reserved+banned      │                    │  trivial refuted       │
   │ words enforced on    │                    │  inconclusive survives │
   │ the bytes.           │                    │                        │
   │ NOTHING HERE IS A    │                    │ expected survivors ≈ 0 │
   │ RESULT.              │                    │ BY DESIGN              │
   └──────────┬───────────┘                    └───────────┬────────────┘
              │                                            │ survivor = a LEAD
              │  the standing checklist                    │ (carries proof_gap)
              │  1 rival  2 decoy/surrogate                │
              │  3 lesion 4 precision response             │
              v                                            v
   ┌──────────────────────────────────────────────────────────────────┐
   │ ADJUDICATION — the only two things that can say "yes"            │
   │   the department battery (docs/doors/refute.md)                  │
   │   the funnel            (docs/doors/discover.md)                 │
   │ + the integrity grade of whichever battery spoke                 │
   │ + [probe] the promotion boundary                                 │
   └───────┬───────────────────────┬──────────────────┬───────────────┘
           │ survives              │ dies             │ needs a human
           v                       v                  v
   ┌───────────────┐    ┌────────────────────┐   ┌──────────────────────┐
   │ CERTAINTY     │    │ GRAVEYARD          │   │ OPERATOR DECISION    │
   │ LADDER        │    │ KilledResult card: │   │ severity · scope ·   │
   │ 1 measured    │    │  why / caught_by / │   │ routing · authority  │
   │ 2 hardened    │    │  regression test / │   │ recorded in          │
   │ 3 kernel-     │    │  obstruction /     │   │ meta/interventions   │
   │   checked ────┼───►│  recurrence guard  │   │ .jsonl  +  ROADMAP   │
   │   (lean/)     │    │ unguarded() = a    │   └──────────────────────┘
   │ 4 externally  │    │  worklist, and     │
   │   reviewed ◄──┼─── │  deleting is never │
   │   NOT YET     │    │  the fix           │
   │   REACHED     │    └────────────────────┘
   └───────┬───────┘
           │ composite claim = grade of its WEAKEST step
           v
   ┌─────────────────────────────────────────────────────────────┐
   │ RECORD:  ROADMAP.md (decision) · HANDOFF.md (state) ·        │
   │  docs/NN (architectural record) · PROOF-LEDGER (obligations) │
   │  · git history · README front table (grades per step)        │
   └─────────────────────────────────────────────────────────────┘
```

**Three asymmetries worth naming, because they are design, not accident:**

1. **Killing is cheap and celebrated; promoting is expensive and rationed.** The
   README leads with "eleven defects of our own were caught during it". The
   graveyard is a deliverable (`hunts/director_run/MISSION.md` rule 4).
2. **Rung 4 (externally reviewed) has never been reached.** The README says
   "External review — none yet — invited, not required." HANDOFF makes *one
   external acceptance* the milestone gating every institutional hypothesis.
3. **The lifecycle has no scheduler.** Which hunt runs is an operator decision,
   made in prose, per session.

---

## 7. Current operational architecture

Traced separately from the science, as requested. **Finding: the operational
architecture is the human operator plus git plus three large Markdown files.**

```
   OPERATOR
     │
     ├─ opens N CLI sessions (Claude Code, Codex, "math-genius-repo",
     │   "director-run", …) — count and identity known only from
     │   branch names, commit trailers, and prose
     │
     ├─ each session reads:  CLAUDE.md → HANDOFF.md top records →
     │                       area MISSION.md → [ACTIVE-CLAIMS.md]
     │   ("the prompt for the next session" is literally a fenced code
     │    block inside HANDOFF.md, hand-written by the previous session)
     │
     ├─ each session writes: code + tests + a docs/NN record +
     │                       ROADMAP/HANDOFF appends + commits
     │
     ├─ isolation mechanism: git branches + `git worktree`
     │   (CLAUDE.md: "for parallel work use git worktree add")
     │   observed: 5 live threads at 2026-08-12; 12 worktrees under
     │   /private/tmp during the Codex relay; a locked worktree under
     │   .claude/worktrees/
     │
     ├─ merge policy: "Report them; never merge them. Only fast-forward
     │   main, only rebase your own branch."  — enforced by prose only
     │
     └─ verification: run locally.  `pytest -q -m "not slow"` (~2217 tests)
         + `cd lean && lake build` (8739 jobs, 0 sorrys)
         + `scripts/make_context.py --check`
         + `scripts/science_preflight.py`
         NO CI EXISTS.  (`find . -name '*.yml'` returns only two lakefiles.)
```

**Observed coordination failures and their in-tree fixes** — the operational
architecture, like the scientific one, is incident-driven:

- Three collisions in one day between concurrent frontier sessions → `ACTIVE-CLAIMS.md`
  (advisory rows, pushed *before* the work).
- Doc number 26 taken on an unmerged branch invisible to the preflight → HANDOFF
  instructs "Take 27, or run `git log --all --name-only -- 'docs/*'`", and records
  the preflight's inability to see other branches as "a real gap in the
  instrument".
- 14 commits living on one disk with no backup for a day →
  `worktree-lab-direction-decision` pushed "as a backup only".
- A crashed session's merge with no PR and no alarm → recorded as
  `meta/interventions.jsonl` entry #1, missing capability named:
  *"Post-merge reconciliation between local refs, remote refs and open PRs."*
  Status: `speculative`. **Still open.**
- An agent "lost to a container restart" → recorded as a `PAUSED` row in
  ACTIVE-CLAIMS; no automatic recovery.

**The one read-only cockpit that exists**: `scripts/70_lab_state.py` renders a
single static HTML page from the graveyard, guard, and review ledgers plus the
independence declarations and hunts, and derives an **attention queue**
(undemonstrated guards, unguarded graves, reviews missing an attack, hunts
without a HuntSpec). It is deliberately scriptless, networkless, and reads *no*
orchestration state. It is ~1 test (`tests/test_lab_state.py`) and is not
scheduled, published, or diffed over time.

---

## 8. State and data inventory

Per the requested schema. "Machine queryable" means: can a program get this
without parsing English prose?

| Category | STORED WHERE | STRUCTURED OR PROSE | MACHINE QUERYABLE | PERSISTENT | PUBLIC/PRIVATE | AUTHORITATIVE SOURCE | KNOWN GAPS |
|---|---|---|---|---|---|---|---|
| **Research state (overall)** | `HANDOFF.md` top record; `ROADMAP.md` | prose | **no** | yes (git) | public | HANDOFF | 1126-line file; "start there" is a human instruction |
| **Current frontier** | `hunts/frontier_math/{PREPRINT,PROOF-LEDGER,ACTIVE-CLAIMS}.md`; README front table | prose + Markdown tables | **no** | yes | public | PROOF-LEDGER | grade per obligation is a table cell, not a type |
| **Decisions** | `ROADMAP.md` (~30 dated sections) | prose | **no** | yes | public | ROADMAP | append-only by convention; no index; no supersession links (one section is marked "stale in three rows" by hand) |
| **Non-goals** | `ROADMAP.md` §"deliberately not being attempted"; the do-not-fund list | prose | no | yes | public | ROADMAP | — |
| **Known gaps** | `ROADMAP.md` §"Known gaps" (numbered 0–4) | prose | no | yes | public | ROADMAP | not linked to any worklist |
| **Agent instructions** | `CLAUDE.md` (= `AGENTS.md` symlink), per-area `MISSION.md`, `hunts/HUNTSPEC.md`, the fenced "prompt for the next session" in HANDOFF | prose (+ HuntSpec = flat YAML subset) | **HuntSpec only** | yes | public | CLAUDE.md | CLAUDE.md is measurably stale — see §13 |
| **Handoffs (serial)** | `HANDOFF.md` | prose | no | yes | public | HANDOFF | — |
| **Handoffs (parallel)** | `hunts/frontier_math/ACTIVE-CLAIMS.md` | Markdown table | no | yes | public | itself | scoped to ONE hunt; advisory, not locking |
| **Branches / worktrees** | git; `.claude/worktrees/`; `/private/tmp/zeta-*` | git refs | yes (git) | branches yes; worktrees **no** | public/local | `git` | worktrees + local branches are machine state; one symlinks into `lean/.lake` |
| **Private ledger** | `conjectures/` → separate private git repo | JSONL | yes | yes | **private** | the private repo | absent from this clone; sync is manual by design |
| **Public ledgers** | `meta/interventions.jsonl` (33 recs); `harness/departments/{graveyard,guard,review}_ledger.py` | JSONL / Python literals | JSONL yes; Python via import | yes | public | the files | graveyard has 3 graves against dozens of prose kills |
| **Experiment outputs** | `hunts/*/results*.json`, `data/*.json`, `figures/*.png` (26), per-hunt `.md` | JSON + PNG + prose | partially | `.json` yes; `.npz` regenerated | public | the JSON | no experiment index; no run→output link |
| **Proofs** | `lean/ZetaLean/` (58 files), `hunts/frontier_math/zeta23ext/`, `lean/cert/` | Lean source | via `lake build` | yes | public | the kernel | `.lake/` gitignored; a green build is not recorded anywhere as an artifact |
| **External reviews** | `docs/reviews/` (10 files); `hunts/frontier_math/EXTERNAL-AUDIT-2026-08-12.md` | prose | no | yes | public (redacted) | the memos | **no external review of the mathematics has occurred**; rung 4 unreached |
| **Provenance (battery)** | `harness/provenance.py` declarations inside each department | structured (8 fields) | **yes** | yes | public | the declarations | *declared*, never proven — the module says so |
| **Provenance (claim→evidence)** | scattered: PROOF-LEDGER rows, commit messages, docs/NN | prose | **no** | yes | public | none single | see §10 |
| **Model identity** | git trailers `Co-Authored-By: Claude {Fable 5, Opus 5}`; one prose annotation "transplant-lemma (Fable)"; session labels in `meta/interventions.jsonl` | semi-structured | **partially** (git) | yes | public | git trailers | 143 of 346 commits carry no trailer; no model↔result linkage |
| **Prompts** | one fenced block in HANDOFF; Aristotle prompts summarized in `lean/ARISTOTLE-RUNS.md`; HuntSpec `agents_may`/`may_not` | prose | no | partially | public | none | **actual session prompts are not stored anywhere** |
| **Run history (model runs)** | *nowhere* | — | **no** | **no** | — | **none** | see §9 |
| **Run history (prover runs)** | `lean/ARISTOTLE-RUNS.md` — 4 batches, project UUIDs, statuses | Markdown table | no | yes | public | itself | the one genuine run registry in the tree; hand-maintained; no timing, no cost |
| **Run manifests / HuntSpec** | specified in `hunts/HUNTSPEC.md`; validator in `tests/test_huntspec.py` | flat YAML in fenced block | yes *if written* | yes | public | itself | **neither a `huntspec` nor a `runmanifest` block exists in any hunt's `MISSION.md`** — the only blocks in the tree are the templates inside `HUNTSPEC.md` itself. Specified, validated, on probation, **unexercised** |
| **Token usage / API cost / wall-clock** | *nowhere* | — | **no** | **no** | — | **none** | see §9 |
| **Failures (scientific)** | graveyard ledger (3), `hunts/*/CLEAN-KILL-REPORT.md`, `GRAVEYARD.md`, ROADMAP/HANDOFF withdrawal records, `docs/25` §2 | mostly prose | mostly no | yes | public | prose | the memo's own point: "prose kills scatter, and a scattered kill is a kill someone will re-derive" |
| **Failures (operational)** | `meta/interventions.jsonl` | JSONL | yes | yes | public | itself | samples interruptions only — **cannot see research design** (its own §"blind spot") |
| **Agent/model performance** | *nowhere* | — | **no** | **no** | — | **none** | one prose data point: the resumption benchmark found one model family below the competence floor, cells voided |
| **Operator decisions** | HANDOFF "Operator decisions"; ROADMAP triage; `meta/interventions.jsonl` `kind=judgment` (5 records) | prose + 5 structured | partially | yes | public | HANDOFF | the 5 judgment records are the only structured ones, and record the system **0 for 4** against the operator |
| **Machine-only state** | `automation/`, `external/`, `.venv-tools/`, `~/zeta-reviews-private/` | mixed | n/a | **single disk** | private | the disk | invisible to any reader; `external/README.md` is tracked precisely so a record does not point at an untracked file |

### 8.1 State map (where a fact physically lives)

```
                       ┌─── git (346 commits here; SHALLOW clone) ───┐
                       │  code · tests · docs · ledgers-as-source    │
                       │  commit trailers: model + session URL       │
                       └────────────────────────────────────────────┘
                                        ▲
   PROSE SPINE ────────────────────────┤
     CLAUDE.md   429 lines  binding rules      [STALE — §13]
     ROADMAP.md 1597 lines  decisions          [append-only, unindexed]
     HANDOFF.md 1126 lines  session state      [serial]
     README.md   598 lines  front page         [repo map stale: says docs 00–13]
     CONTEXT.md 1355 lines  GENERATED facts    [make_context.py --check]
                                        │
   STRUCTURED ISLANDS ──────────────────┤
     meta/interventions.jsonl      33 records, 3 kinds
     harness/departments/*_ledger  3 graves · 5 guards · reviews
     harness/provenance            8 declarable fields per department
     ontology/schema               5 kinds · 6 verdicts · typed edges
     hunts/*/results*.json         raw measurements
     lean/ARISTOTLE-RUNS.md        4 prover batches with UUIDs
                                        │
   PRIVATE / OFF-TREE ──────────────────┤
     conjectures/            (separate private repo, manual sync)
     ~/zeta-reviews-private/ (futures map · blind pair · E1–E3)
     operator's vault
     automation/  external/  .venv-tools/   (one disk)
                                        │
   DERIVED VIEWS ───────────────────────┘
     scripts/70_lab_state.py  → one static HTML page (unscheduled)
     ontology.metrics.render_text → funnel conversion tables
     scripts/make_context.py  → CONTEXT.md / CONTEXT_FLAT.md
```

---

## 9. Agent/model telemetry audit

**Headline: there is no telemetry.** The string "telemetry" appears nowhere in
the repository. What exists is *incidental attribution in git trailers* and
*prose annotation*. Answering the specific questions:

| Question | Answer | Evidence |
|---|---|---|
| **How many model runs have happened?** | **We don't know.** Not recorded. A lower bound of **10 distinct Claude Code sessions** is recoverable from `Claude-Session:` trailers, covering 112 of 346 commits. Prose names more sessions than that (director run's *nine investigators*, twelve Codex worktrees, five parallel branches). | `git log --format='%B' \| grep -o 'session_[A-Za-z0-9]*'` → 10 unique |
| **Which models performed them?** | **Partially.** 203 of 346 commits carry `Co-Authored-By`: **135 Claude Fable 5, 68 Claude Opus 5**. 143 commits carry none. "Codex" appears only in prose. | git trailers |
| **Which model produced which useful result?** | **No.** Attribution is per-*commit*, not per-*claim*. One single prose exception exists: `ACTIVE-CLAIMS.md` labels four holdings "transplant-lemma (Fable)". | — |
| **Which model produced which false lead/defect?** | **No.** The defect ledgers (`PROOF-LEDGER.md`, `docs/25` §2, guard ledger) name the *mechanism* and the *catcher role* — never the model. `meta/interventions.jsonl`'s `caught_by` vocabulary is `human/test/oracle/outsider/nobody`, which is deliberately about *architecture*, not about models. | `harness/guards.py`, `meta/README.md` |
| **Exact prompts?** | **No.** One next-session prompt is stored as a fenced block in HANDOFF; Aristotle prompts are *described* in `ARISTOTLE-RUNS.md` ("Prompts pinned in the table") but the table holds statements, not prompt text. Actual session prompts are not stored. | HANDOFF §"The prompt for the next session"; `lean/ARISTOTLE-RUNS.md` |
| **Input/output/cache tokens?** | **No.** Zero token counts anywhere. The only token statement in the tree is qualitative: "frontier-model tokens are exhausted until further notice". | HANDOFF 2026-08-12 |
| **Dollar cost?** | **No.** One qualitative fact: "the operator is funding this out of pocket". | HANDOFF |
| **Runtime?** | **Partially, and only for machine work.** Test-tier and `lake build` timings are recorded in prose (fast tier ~115 s parallel; 8739 jobs; a rigor test 0.76 s vs >20 min on the fallback backend; funnel run 4.29 s). **Agent wall-clock is not recorded.** Aristotle turnaround is *estimated* ("hours"; the Grasshopper case study's ~8 h), not measured. | CLAUDE.md, ROADMAP, ARISTOTLE-RUNS |
| **Success/failure by task type?** | **No, as data.** As prose: the funnel's per-generator conversion table *is* a real success-rate instrument, but for generators, not agents. The director run reports 8/8 planted faults caught and 6/6 real defects missed by the same instrument. | `ontology/metrics.py`; `docs/25` §5 |
| **Agent/model comparative performance?** | **Effectively no.** One controlled experiment exists and it was inconclusive: the resumption benchmark, 18 blinded cold-agent runs across two model families, scored blind — **one family fell below the planted-control competence floor and its cells were voided**, and in the family that counted the typed condition did not beat prose. Run in a private fork; the data is not in this tree. | ROADMAP 2026-08-09 |
| **Provenance human idea → run → artifact → claim → verification → commit?** | **No.** See §10. | — |

**Two honest counterweights, so this section is not read as a criticism the tree
would disagree with:**

1. The repository has *deliberately* refused to build an autonomy dashboard.
   `meta/README.md`: "Not a dashboard, not a KPI, not a burndown. If it starts
   being used to show progress rather than to measure a ratio, it has become the
   thing it was built to prevent." Any telemetry proposal has to survive that
   argument.
2. The repository *does* measure the thing it decided matters — human
   intervention with a named missing capability — and its baseline is stated
   against itself: **architecture caught 3 of 14 interventions (21%)**, and the
   instrument's own blind spot (it samples interruptions, so it cannot see
   research design) is written down.

---

## 10. Provenance audit

The chain the prompt asks about:

```
human idea → agent run → artifact → claim → verification → commit
```

Segment-by-segment, as it exists **today**:

| Segment | Recorded? | Where | Machine-traversable? |
|---|---|---|---|
| human idea → decision | **yes**, richly | `ROADMAP.md` dated sections; `docs/reviews/` for outside inputs | no (prose) |
| decision → work item | **partially** | ROADMAP "Adopted/Queued/Deferred/Rejected"; HANDOFF "Queue" | no |
| work item → agent run | **no** | — | no |
| agent run → artifact | **no**, except for provers: `lean/ARISTOTLE-RUNS.md` maps project UUID → statement → status | — | no |
| artifact → claim | **yes** for the frontier: `PROOF-LEDGER.md` rows carry Obligation / Status / *Exact dependency* (file:line, upstream commit) / Evidence | Markdown | no |
| claim → verification | **yes and strong**: the certainty ladder grades each step; `ClaimReport` refuses to state an outcome without its battery grade; the README front table lists each step's rung | mixed | partially (`ClaimReport` is a real object) |
| verification → commit | **yes**: commit messages are unusually descriptive and name mechanisms; PROOF-LEDGER pins "audited local state: `<sha>`" | git | partially |
| commit → transcript | **no**: `Claude-Session:` URLs exist on 112 commits but resolve to an external service, not to a stored artifact | git trailer | no |

**What is genuinely excellent here** (and should not be disturbed): *upstream*
provenance for the frontier claim is pinned by **digest**, not by reference — the
source paper's PDF SHA-256, the companion Lean repo commit, the upstream Mathlib
commit, and the local audited SHA are all recorded in
`hunts/frontier_math/PROOF-LEDGER.md`. `harness/preregistration.py` generalizes
exactly this pattern (criteria frozen as digests of pre-existing evidence).

**What is missing** is the *middle*: nothing connects a decision to the run that
executed it, or a run to the artifact it produced. The chain has a strong head
(decisions), a strong tail (claim → grade → commit), and no waist.

---

## 11. Explicit future directions found in the repo

**Category A — explicitly planned, with a location.** These are stated as
decisions or standing next-builds, not inferences.

| # | Direction | Where stated | Status |
|---|---|---|---|
| A1 | **One external acceptance is the gating milestone** — Mathlib upstream, via Zulip first, leading with `PowerfulDecomposition.lean` (Mathlib has *no* powerful-number machinery), `theta_sq_le` second | HANDOFF queue items 0–2; ROADMAP "The upstream track" | queued, first task of next session |
| A2 | **Rung 3 (kernel-checked Davenport–Heilbronn)** — mathematics-complete; blocked on a **headroom re-plan**, not scale; the 215-site margin sweep is interrupted at 60/215 | ROADMAP "Next build"; HANDOFF item 3; `docs/25` §7 | open, priced |
| A3 | **Close the last frontier gap** — the many-pair case, now reduced to "a single bandlimited nonnegative-kernel inequality in two exponential sums" | `README.md`; `docs/27` §4; ACTIVE-CLAIMS | live |
| A4 | **The guard offensive** — per guard: name the intended lesion, build the smallest mutant, confirm it fires, map nearby misses | ROADMAP adopted build 2; `docs/25` §7 ("Guards are the frontier") | ledger exists, 2 of 5 undemonstrated |
| A5 | **Verifier-independence measurement** extended beyond the rigor cross-check | ROADMAP adopted build 1; `docs/26` §1 | one subject declared |
| A6 | **HuntSpec + run manifests earn promotion** to a real module the first time a kill condition fires mechanically | `hunts/HUNTSPEC.md` probation terms | probation; **no `huntspec` or `runmanifest` block exists in any hunt yet** — the primitive is defined and validated but never used |
| A7 | **Proof-agent adapter** — batch bounded lemmas overnight to Aristotle, kernel-decide locally; explicitly *not* rung 3 | ROADMAP adopted build 4; `lean/ARISTOTLE-RUNS.md` | 4 batches submitted, Sturm batch accepted |
| A8 | **Evolutionary search as a hunt instrument**, admissible only behind a HuntSpec naming an exact non-model evaluator | ROADMAP adoption 5 | queued behind A6 |
| A9 | **Literature scout networked half** — OEIS content-verified `FOUND`, arXiv/zbMATH leads-only, no code path to NOVEL | `docs/26` §6; `ontology/scout_online.py` | landed |
| A10 | **Queued mathematics lanes**, in order: general higher-ξ hierarchy → CUE F_k → local process of derivative zeros → corrected F₂; local-to-global positivity at most one long-horizon lane | ROADMAP "Queued" | gated on live threads finishing |
| A11 | **Departments #7+ deferred deliberately** — the memo's build order says harden before broadening | ROADMAP triage constraint 3; memo §"build order" item 11 | deferred |
| A12 | **The external-referee experiment** — "the experiment most likely to hurt"; needs an actual outside party | `docs/20` §8; ROADMAP deferred | deferred, not schedulable by a session |
| A13 | **E1–E3 protocol** — is the operating discipline carried by transferable artifacts or by the operator's unstated judgment? | `docs/reviews/e1-e3-*` (5 docs, Rev 2 + 2.1 patch is the contract) | designed, **not run** |
| A14 | **Explicitly NOT built, with reasons standing**: durable orchestration, research UI beyond the static page, attention queue as a service, start/pause/steer controls | ROADMAP deferred; `docs/26` §6 closing | refused pending "measure the loop before automating it" |
| A15 | **Phase II objective**: produce **one externally verified mathematical statement that humanity didn't previously know** | `CLAUDE.md` §honest-scope | the standing objective |

**Category A negative space — things explicitly rejected**, which are as
architecturally informative as the plans: continuous indiscriminate funnel
generation (rejected twice); any reading of the memos that bends the honest-scope
rule; going after N(T) in Mathlib (PNT+ is on it); a model judging whether a
battery is hollow; volume conjecture generation; the authority layer (permanently
open by design).

---

## 12. Implied directions

**Category B — strongly implied by the code's shape, not stated as a plan.**
Each is marked with what implies it.

| # | Implied direction | What implies it |
|---|---|---|
| B1 | **The referee, not ζ, becomes the primary artifact.** | The README leads with it; `docs/doors/adopt.md` exists for readers who "do not care about ζ"; `harness/protocol.py` is protected by three seam tests; 4 of 6 departments have no mathematical content |
| B2 | **The graveyard/guard/review ledgers converge into one claim-state store.** | Three ledgers with the same shape (typed record + `*_reasons()` + a worklist function), all consumed by one renderer (`70_lab_state.py`), all with prose duplicates elsewhere |
| B3 | **The certainty ladder wants to be a type, not a convention.** | It is applied per-step in the README table, per-obligation in PROOF-LEDGER, per-axis in `dossier/status.py`, per-grade in `integrity.py` — four independent hand-rolled implementations of one idea |
| B4 | **Provenance-by-digest becomes the general pattern.** | Already used for the source paper, upstream Lean, Mathlib pin, audited local SHA, blind-authoring `SHA256SUMS.txt`, and `preregistration.py` |
| B5 | **HANDOFF.md is being asked to do something a file cannot.** | 1126 lines; a fenced *prompt* inside it; the top record is titled "start there"; a *second* channel (ACTIVE-CLAIMS) had to be invented within one day for parallelism |
| B6 | **The lab is drifting toward being a client of external provers/searchers rather than a builder of them.** | `external/` inventories 7 outside repos; `proof_adapter.py` treats provers as generators; the adopted builds are all *adapters* and *ledgers*, no new solvers |
| B7 | **The meta-laboratory will eventually need a denominator it cannot currently compute.** | `meta/ledger.py`'s `ratio()` refuses to divide until the caller names its numerator — and no numerator class (kernel-checked theorems? accepted contributions?) is yet counted anywhere |
| B8 | **"Department" will be asked to cover non-empirical work and will refuse.** | Three separate documents (`docs/19` §6, `hunts/README.md`, `docs/doors/README.md`) restate the same refusal, which is what a repeatedly-tested boundary looks like |

**Category C — my speculation.** Clearly separated; nothing below is supported by
a stated plan.

| # | Speculation | Why I think it, and why it is speculation |
|---|---|---|
| C1 | The next durable abstraction will be a **Claim object** — id, statement, rung, obligations, evidence digests, battery+grade, killer-or-survivor — because four sub-systems already hand-roll pieces of it. *Speculation*: no file proposes it, and `dossier/` is the recorded evidence that typed research state does **not** automatically earn its keep. |
| C2 | The operational bottleneck will become **merge/branch reconciliation**, not mathematics. *Speculation*: it is intervention #1's named missing capability, it recurred as the doc-26 collision and the local-only branch, and parallel session count is rising. |
| C3 | If one external Mathlib acceptance lands, the institutional centre of gravity shifts from *self-refereeing* to *external interface*, and several internal layers (promotion gate, preregistration) lose their reason to exist as probes. *Pure speculation.* |
| C4 | The `automation/` nightly rig (0 nights run) is the single highest-variance unknown: it is built, gitignored, and gated on one operator switch. *Speculation about impact only; its existence is documented.* |

### Explicit vs implied vs speculative — summary table

| Direction | A: explicit | B: implied | C: speculative |
|---|---|---|---|
| One external acceptance as the milestone | ✅ A1 | | |
| Rung 3 headroom re-plan | ✅ A2 | | |
| Close the many-pair gap | ✅ A3 | | |
| Guard offensive / independence radius | ✅ A4, A5 | | |
| HuntSpec & run manifests promoted | ✅ A6 | | |
| Prover adapter + oracle-scored search | ✅ A7, A8 | | |
| More departments | ⛔ deferred A11 | | |
| Orchestration / UI / controls | ⛔ deferred A14 | | |
| Referee as the primary artifact | | ✅ B1 | |
| One unified claim-state store | | ✅ B2 | ✅ C1 |
| Certainty ladder as a type | | ✅ B3 | |
| Provenance-by-digest everywhere | | ✅ B4 | |
| HANDOFF outgrowing prose | | ✅ B5 | |
| Merge/branch reconciliation as bottleneck | | | ✅ C2 |
| External interface reshapes the internals | | | ✅ C3 |
| Nightly rig switched on | | | ✅ C4 |

---

## 13. Architectural tensions / ambiguities

Named rather than resolved, as requested.

**T1 — "One research program with subjects" vs "a reusable verification
framework".** Both are true and the repository does not pick. `README.md` line 3
says "plus a reusable validation framework"; `harness/README.md` says "It is
deliberately not about ζ"; but the admission rule that gives the framework its
teeth (*rivals must be structure-matched*) requires **domain knowledge the seam
forbids** — `docs/23` measured this exactly: the obvious value-comparison fix
scores real departments *more* separated than the sham, "because ζ and
Davenport–Heilbronn also agree on no numeric value. Which differences are
load-bearing is the domain knowledge the seam forbids." **The seam is the
framework's strength and the audit's ceiling simultaneously.** This is a genuine
architectural tension with a measured cost, not a wording problem.

**T2 — The referee department fails its own audit.** `compiler` and `referee`
grade `DETECTOR_INADEQUATE`; the test is named
`test_the_referee_department_survives_its_own_audit` → `..._does_not_survive_its_own_audit`.
The tree chose *record the failure* over *exempt the department*, which is
admirable and leaves an open contradiction: the machinery that grades everything
is graded inadequate by itself, and "each department owes an answer" is recorded
as the next pre-registered change — not yet made.

**T3 — Three futures implied by three subsystems.** `harness/` implies a
**reusable verification framework** for anyone. `hunts/frontier_math/` implies a
**single-program mathematics lab** racing a specific constant. `meta/` +
`docs/reviews/` imply an **agentic research operating system**. The memos
recommend the third; ROADMAP adopted its *primitives* while explicitly refusing
its *orchestration*. All three are currently funded by the same operator's
attention. **Do not resolve this by picking one on paper** — the tension is
carried, not confused, and the tree says why (build order: harden before
broadening).

**T4 — The prose spine is both the authority and the known failure mode.** The
repository's own thesis is that prose restating structured facts drifts and
nothing checks it (`tests/test_claim_attribution.py`'s docstring). Yet the
authoritative records for decisions, state, and the live frontier are all prose,
in three files totalling 3122 lines.

**T5 — Documented staleness in the governance file itself.** Measured, not
alleged:
- `CLAUDE.md` says "`docs/` 00–26"; `docs/27-state-of-the-transplant.md` exists.
- `README.md`'s repository map says "`docs/` 00–13" and "`scripts/` 01–05 and
  07–13" — there are 28 docs and 41 scripts.
- `CLAUDE.md` quotes "2189 tests / 2122 fast"; `HANDOFF.md` (later) reports 2217
  passing; `CONTEXT.md` counts 1687 test *functions* across 64 files.
- `CLAUDE.md`'s `harness/` description does not mention `guards.py`,
  `graveyard.py`, `review.py`, `shams.py` is mentioned but `scout.py`,
  `proof_adapter.py`, `70_lab_state.py`, `HUNTSPEC.md` are not.
- The one instrument that *would* catch this class (`make_context.py --check`)
  regenerates `CONTEXT.md`, which is explicitly the *facts* half; the *judgment*
  half (CLAUDE.md) is by design unchecked.

**T6 — "Ledger" names four incompatible things** (§2.3), one of which is a
private repo, one of which is Python source. Any future "the ledger" reference is
ambiguous.

**T7 — Departments are simultaneously "subjects" and "test fixtures".**
`croniter` and `stateval` exist to *test the protocol*, not because anyone cares
about cron. But they are registered identically to `zeta`. Nothing in the type
distinguishes "a subject the lab studies" from "a subject the lab uses to prove
its instruments generalize". `docs/doors/README.md`'s table lists them all in one
column.

**T8 — Machine state is load-bearing but invisible.** `automation/`, `external/`,
`.venv-tools/`, `conjectures/`, `~/zeta-reviews-private/`. The tree handles this
honestly (`external/README.md` is tracked *precisely so a record does not point
at an untracked file*), but the consequence stands: **a reader of this repository
cannot reconstruct the laboratory**, and a disk loss would destroy artifacts the
records cite.

**T9 — The shallow clone.** Reproducing pre-2026-08-07 history requires a fetch
that this environment's clone cannot serve. Several ROADMAP claims cite commits
(`bf8f6dc`, `c08296d`, `e7d52b6`, `2041d86`, `431cc74`) whose *ordering* is the
entire evidentiary basis for the pre-registration argument. Some of those resolve
here; the earliest do not.

---

## 14. Missing institutional layer

Derived strictly from gaps found in §7–§10, and constrained by the design
principle: **remove operational state from the operator's working memory without
removing their understanding of the research.**

Ordered by (evidence of pain) × (cheapness), most justified first.

**M1 — A run registry. [strongest evidence]**
*Gap:* §9 — number of runs, models, prompts, tokens, cost, runtime, per-task
outcome are all unrecorded. *Evidence it hurts:* the resumption benchmark could
not be re-derived from this tree; "an agent lost to a container restart" is a
prose row; "frontier tokens exhausted" was a surprise that reorganized an entire
queue; the model↔defect question cannot be asked.
*Note the partial precedent already in-tree:* `lean/ARISTOTLE-RUNS.md` is exactly
this, hand-maintained, for one external service. The design already exists; it is
unautomated and covers one backend.

**M2 — Post-merge / branch reconciliation. [named by the lab itself]**
*Gap:* `meta/interventions.jsonl` record #1, verbatim missing capability:
*"Post-merge reconciliation between local refs, remote refs and open PRs."*
*Recurrences:* doc-26 number collision across an unmerged branch; 14 commits
local-only for a day; the preflight explicitly "cannot see other branches …
that is a real gap in the instrument".

**M3 — A claim registry with stable identifiers. [implied by four hand-rolled
half-implementations]**
*Gap:* §10's missing waist. Today a claim exists as: a PROOF-LEDGER row, an
ACTIVE-CLAIMS row, a README table row, a `ClaimUnderReview`, a `KilledResult`, and
several prose paragraphs — with no shared id. *Consequence:* the README's front
table and `docs/27` and PROOF-LEDGER had to be edited **four times in one day**
(docs/27's own opening sentence) to stay consistent.
*Constraint from the tree:* `dossier/` is the recorded warning that typed research
state does not automatically earn its keep. Any claim registry must beat
disciplined prose on a scoreable task, per `docs/19` §6.

**M4 — A single derived research-state view, kept current.**
*Gap:* `scripts/70_lab_state.py` exists, is correct in spirit, and is **not
scheduled, not published, not diffed**. The attention queue it derives
(undemonstrated guards, unguarded graves, reviews missing an attack) is exactly
the "human-decision worklist" the memo asked for and nothing consumes it.
*Cheapest real win in this list:* run it, keep the output, diff it between
sessions. Zero new architecture.

**M5 — Continuous integration.**
*Gap:* there is none. Every governance test — doc numbering, hygiene, hunt
vocabulary, doors, claim attribution, department conformance, `make_context
--check` — runs only when a session remembers to run it. The repository's own
thesis ("a skipped test is a silent verdict") applies directly. *Caveat that must
be respected:* the full suite is 10–20 minutes and `lake build` is 8739 jobs, so
CI has to be tiered.

**M6 — Provenance edges (decision → run → artifact → claim).**
*Gap:* §10's waist. The heads and tails are strong; only the middle is absent. The
*mechanism* is already chosen by the tree — digests — so this is edge-recording,
not a new epistemology.

**M7 — A prose-drift detector generalizing `test_claim_attribution.py`.**
*Gap:* T5's measured staleness. The tree already proved (twice, in that file's own
docstring) that the naive lexical version is hollow. The non-hollow version is
narrow and derived-from-the-module, which is a design the tree has already found.

**M8 — A write interface for the operator.**
*Gap:* today the operator writes into the research by editing HANDOFF/ROADMAP or
by typing a session prompt. There is no place to attach *"here is my hypothesis /
objection / direction"* to a research context and have it survive into the next
session other than prose. The E1–E3 protocol (`docs/reviews/`) is the designed —
and unrun — experiment about exactly this transferability question.

**M9 — Progressive disclosure (institution → department → frontier → claim →
evidence → verification → run → artifact → code/Lean → commit → transcript).**
*Gap:* every one of those levels exists as an artifact today; **none of the links
between them is machine-traversable.** This is the sum of M1, M3, M4, M6 rather
than an independent build.

**Explicitly NOT recommended, on the tree's own evidence:**
- A dashboard with an autonomy score, progress bar, or aggregate "verified"
  number — `meta/README.md`'s three refusals and `dossier/status.py`'s raising
  `__bool__` are load-bearing prior decisions, not stylistic ones.
- Durable orchestration as a *first* move — ROADMAP's rule ("measure the loop
  before automating it") is unsatisfied: not one loop has been measured.
- A model judging battery hollowness — refused in `meta/ai-components.md`.
- Making the orchestration layer canonical for evidence — the memo itself
  forbids it ("Workflow state may live there. Evidence should not").

---

## 15. Minimal modernization boundary

The smallest set of changes that removes operational state from the operator's
head **without touching the scientific architecture**. Everything here is
additive and reversible; nothing renames, moves, or refactors.

```
┌─────────────────────────────────────────────────────────────────────┐
│ INSIDE THE BOUNDARY  (operational state; safe to mechanize)         │
│                                                                     │
│  · run registry: one append-only record per model/prover/agent run  │
│    (id, when, model, branch, worktree, task, outcome, artifacts)    │
│    — generalizes lean/ARISTOTLE-RUNS.md, which already works        │
│  · git-derived facts: branch/worktree/PR reconciliation report      │
│    (intervention #1's named capability)                             │
│  · scheduling + retention of the EXISTING lab-state page, plus a    │
│    diff between runs                                                │
│  · tiered CI running the governance tests that already exist        │
│  · doc-number allocation across ALL branches (the preflight's       │
│    stated gap)                                                      │
│  · edges: decision-id → run-id → artifact-digest → claim-id         │
│    (recording only; the digests already exist)                      │
├─────────────────────────────────────────────────────────────────────┤
│ ON THE BOUNDARY  (needs a decision, not an implementation)          │
│  · a claim registry with stable ids — must beat prose on a          │
│    scoreable task first (docs/19 §6 burden does not reset)          │
│  · the certainty ladder as a shared type across its four current    │
│    hand-rolled sites                                                │
├─────────────────────────────────────────────────────────────────────┤
│ OUTSIDE THE BOUNDARY  (scientific architecture — do not touch)      │
│  · the four control roles and the admission rule                    │
│  · the 5 integrity grades, 19 checks, 15 sham modes, 6 blind spots  │
│  · the reserved word and its two owners                             │
│  · the certainty ladder's rungs and the weakest-step rule           │
│  · the seam and its three enforcement tests                         │
│  · hunts/ classification and the lexical bans                       │
│  · "no department without a battery"; "a department whose battery   │
│    is another department's is not a department"                     │
│  · the funnel's stages and conservation law                         │
│  · conjectures/ staying private                                     │
│  · meta/'s three refusals (no score, ratio names its numerator,     │
│    automated costs an artifact)                                     │
└─────────────────────────────────────────────────────────────────────┘
```

The test for whether a proposed change is inside the boundary: **does it change
what the laboratory is entitled to believe?** If yes, it is scientific
architecture and this document does not authorize it. If it only changes what the
operator has to remember, it is inside.

---

## 16. Things we should NOT change yet

1. **`harness/protocol.py`.** It has changed exactly once, deliberately, on
   recorded evidence. Its stability *is* the measurement of domain-agnosticism.
2. **The seam tests.** They run in ~0.1 s, and that speed is itself the check.
3. **The reserved word and its two owners.** Two different regimes; the
   distinction is load-bearing and repeatedly re-explained.
4. **`hunts/` lexical bans.** They read the bytes, including inside a sentence
   disclaiming the word. That crudeness is the feature.
5. **`conjectures/` staying gitignored.** Publishing unreviewed leads is exactly
   what the repository refuses.
6. **The `dossier/` probe classification.** Its admission path is closed by a run
   benchmark, and reopening it costs a repaired benchmark plus beating prose.
7. **The promotion gate's status as a probe** and `docs/21`'s recorded failures,
   including the one where the gate promotes a hollow battery's claim with an
   empty reason list.
8. **The blind-authoring corpus.** Frozen, digest-pinned, and carrying a
   deliberate absolute-path exception (`tests/test_repo_hygiene.py`). Do not
   "clean" it; the digest is the evidence.
9. **The five parallel branches / locked worktree.** HANDOFF: report, never merge.
10. **ROADMAP's append-only convention** and its dated sections, including the
    ones marked stale in place. Rewriting them destroys the chronology that makes
    the pre-registrations worth anything.
11. **`meta/`'s refusals.** No score, no aggregate, no autonomy number.
12. **The rogue-lab prototypes** in `ontology/0*.py`–`16_*.py`: pinned by
    `tests/test_rogue_lab_controls.py` and dissected in `docs/17`.
13. **The three-file prose spine — for now.** It is the tension in T4, but it is
    also the only complete record. Nothing should be *moved out* of it until
    something else demonstrably carries the same information.

---

## 17. Questions requiring operator judgment

Ordered by how much downstream work they unblock. None can be answered from the
tree.

**Q1 — Which of the three futures (T3) is the lab actually funding?** A reusable
verification framework, a single-program mathematics lab, or an agentic research
OS? The tree currently pays for all three from one attention budget. *This is the
one question everything else in §14–15 depends on.*

**Q2 — Is model/run telemetry inside the lab's own epistemology, or outside it?**
`meta/README.md` refuses dashboards and KPIs on principle. A run registry (M1) is
either (a) plumbing, exempt from that refusal, or (b) exactly the self-flattering
instrument the refusal targets. The tree does not say which, and the answer
decides whether M1 is cheap or forbidden.

**Q3 — What is the numerator?** `meta/ledger.py:ratio()` refuses to divide until
someone names the externally checkable output class. Kernel-checked theorems?
Accepted upstream contributions? Pinned measurements? Until this is answered the
entire meta-experiment cannot produce a number.

**Q4 — Does the `DETECTOR_INADEQUATE` grade on `compiler` and `referee` get
answered, weakened, or left standing?** ROADMAP records it as "the next
pre-registered change, not this one" and it has not been made.

**Q5 — Is machine-only state (automation/, external/, conjectures/, the private
review directory) permanently off-tree, or does some of it need a durable
non-disk home?** Records already cite artifacts that exist on one disk.

**Q6 — Should the nightly rig be armed?** It is built, has run zero nights, and
is the memo's build-order item 10. `docs/26` notes it should carry a HuntSpec
first and cannot run proof-adapter work on a machine with no Lean toolchain.

**Q7 — Does external engagement go through Mathlib (gatekept, disclosure-sensitive)
or through the gatekeeper-free route** (reporting the Remark 1.1 gap directly to
the source paper's authors)? HANDOFF lays out both and the operator's own read
that Mathlib's culture is hostile; the session queue currently starts with a
Zulip question.

**Q8 — What is the retention policy for session transcripts?** 112 commits carry
`Claude-Session:` URLs pointing at an external service. If transcripts are part of
the provenance chain, they need a stored home; if they are not, the trailers are
decoration and the chain ends at the commit.

**Q9 — Does `ACTIVE-CLAIMS.md` generalize beyond `hunts/frontier_math/`?** It was
invented in one day for one hunt to solve a collision problem that is not
hunt-specific.

**Q10 — Who is allowed to add a department, now that six exist and #7 is
deferred?** The mechanism has no human step by design ("a department cannot be
added quietly"), but the *decision* to broaden is explicitly deferred by ROADMAP.
Those two facts are in mild conflict.

---

## Appendix — evidence index for the major conclusions

| Conclusion | Primary evidence |
|---|---|
| Three co-resident labs + governance | directory structure; `harness/README.md`; `meta/README.md`; `docs/doors/README.md` |
| The recursive thesis | `docs/20` §1 |
| Department = battery + detectors + scope + provenance + 2 reference claims + door + registry line | `harness/protocol.py:616-742`; `harness/departments/__init__.py:20-28`; `tests/test_department_conformance.py` |
| 6 departments | `KNOWN_DEPARTMENTS` |
| 19 integrity checks, 5 grades, 15 sham modes, 6 blind | `harness/integrity.py` (`_HOLLOW_CHECKS` = 13; + detector-power/specificity/claim-agreement, provenance-declared/contamination, scope-declared) |
| Audit's measured limit: 6/6 blind hollow batteries reached CALIBRATED | ROADMAP 2026-08-10; `docs/23`; `harness/blind_authoring_2026_08_09/` |
| Referee department fails its own audit | ROADMAP 2026-08-10; test renamed `..._does_not_survive_its_own_audit` |
| Both rigor backends returned a wrong sign from a shared parsing layer | `docs/25` §2.1; ROADMAP known gap 0 |
| Independence radius 3 of 5 for the rigor cross-check | `harness/independence.py`; `docs/26` §1; `harness/departments/zeta_department.py` |
| Certainty ladder, weakest-step rule | `CLAUDE.md` (amended 2026-08-12); `README.md` front table |
| Verification costs wall-clock, judgment costs tokens | `HANDOFF.md` 2026-08-12 §"The economics" |
| No CI | no `.github/`; only `pyproject.toml` and two `lakefile.toml` |
| No telemetry | zero occurrences of "telemetry"; no token/cost/runtime records |
| 203/346 commits carry a model trailer (135 Fable 5, 68 Opus 5); 10 session ids on 112 commits | `git log` trailer counts |
| Shallow clone; history starts 2026-08-07 | `.git/shallow`; `git log --reverse` |
| 33 intervention records, 4 sessions, 3 kinds | `meta/interventions.jsonl` |
| 3 graves, 5 guard records (2 undemonstrated) | `harness/departments/{graveyard,guard}_ledger.py` |
| Attention queue exists and is derived | `scripts/70_lab_state.py:_attention_queue` |
| HuntSpec / run manifests specified but unexercised | `hunts/HUNTSPEC.md`; `grep -rl '```huntspec' hunts/` and `grep -rl runmanifest hunts/` both return only `HUNTSPEC.md` |
| Machine-only state | `.gitignore`; `external/README.md`; `HANDOFF.md` §"Where the off-repo material lives" |
| CLAUDE.md/README staleness | `CLAUDE.md:350` ("docs/ 00–26") vs `docs/27-*`; `README.md:512` ("docs/ 00–13") vs 28 docs |

---

*End of archaeology. Nothing in this document authorizes a change; §15 draws a
boundary and §17 lists what only the operator can decide.*
