# Counselor critique: the master consolidation and the limits addendum

**Date:** 2026-08-23 · **Position:** institutional counselor, read-only, adversarial ·
**Subject:** "MASTER CONSOLIDATION — THE RESEARCH INSTITUTION" (2026-08-22) and the
addendum "THE LAB MAY HAVE A REAL COMPARATIVE ADVANTAGE IN FINDING LIMITS".

Labels, as the consolidation asks. **FACT** means run or read here, with the command or
file named. **REPORTED** means an artifact asserts it and I did not re-derive it.
**INFERRED** means I reconstructed it and it is not rigorous. **RECOMMENDATION** is
opinion.

Inputs: `~/Zeta` at `f8f881b`, `~/fulcrum`, `~/zeta-record`, the live hunt worktree
`.claude/worktrees/ainta-gohms/`, and Fulcrum through `fulcrum_status`, `fulcrum_cost` and
its JSON ledgers. Nothing was launched, adopted, landed or superseded. Not read, so that
this is an independent check rather than an echo: `~/brain`, and any transcript or prior
agent reasoning about this material.

---

## 1. Verdict

The consolidation is accurate about what has failed and honest about what is unproven. Its
main defect is not in the diagnosis. It is that **the document proposes building
mechanisms that already exist in the tree and are simply not switched on**, and it does not
know that, because nobody measured compliance before proposing the fix.

Three findings drive everything below.

**1.1 The research contract the consolidation wants to strengthen is failing 96% of the
time right now.** PR #82 landed `scripts/71_contribution_check.py` on 2026-08-22. Run
against the real tree, **55 of 57 hunt directories fail it** (FACT). Its test only ever
calls it on synthetic `tmp_path` fixtures (FACT). §XII says "strengthen what already
exists"; the accurate version is that what exists has never been run.

**1.2 The institution's return path has fired zero times.** Fulcrum holds **134 threads
and 53 core candidates. 133 and 52 are `unfunded`, one each is `rejected`, none is funded**
(FACT). "Forage, don't roadmap" preserves threads and has never fed one. §XLVIII asks
which science to allocate to; the honest precondition is that the allocation mechanism the
lab already built has never once been used.

**1.3 The addendum's central claim is not supported by the addendum's own standard.**
"Comparative advantage" requires someone else attempting the same thing and doing worse. I
tabulated thirteen limit-results across all five of the addendum's classes (§4 below). In
exactly one is there an outside party attempting the same object, and the lab's only
head-to-head measurement is confounded by its own account and failed the only item that
discriminated. Limit-finding is a real specialization. Calling it comparative is
pattern-matching.

One thing the consolidation gets exactly right and should not be talked out of: the
Ainta/Gohms work is genuinely good, it ran its own kill conditions, and none fired. §7
audits it.

**A note on this document's shelf life.** The board moved twice while I wrote. PR #97
committed results I had found sitting in an untracked log, and PR #98 landed the trust map
that §5 had nominated as the gating test, which resolved the question I was about to
recommend asking and found a soundness defect that **retracts one of my recommendations**
(§7.4). Everything in §7 and §9 is written against `main` at `36c6070` and should be
re-checked before it is acted on.

**And `main` is red right now, on two of its own guards.** FACT, both run here at
`36c6070`. `tests/test_hunt_numbering.py::test_no_hunt_number_is_used_twice` fails: **Hunt
#78 is claimed by both `ainta_seven_point/` and `r_a7c12f/`**. And
`scripts/make_context.py --check` reports `CONTEXT.md` stale, because
`harness/departments/review_ledger.py` grew from 272 to 356 lines without regeneration.
Neither is mine; my branch was green on `f8f881b`. Both were produced by PRs that were
green in isolation and collided on merge, which is the parallel-session hazard `AGENTS.md`
warns about, and which `test_hunt_numbering.py`'s own docstring describes as the exact
failure it was written for. The guard fired. Nothing gated the merge on it. This blocks
every open PR including this one, so it is the first thing to fix.

**And the numbering guard has a coverage hole that caused this collision.** FACT: hunt #77
exists and is AIMO-2, but its case-log heading reads `### Hunt AIMO-2 (#77):`, and the
guard's pattern is `^###\s+Hunt\s+#(\d+)\s*[:—-]`. That heading does not match, so **#77 is
invisible to the uniqueness check**. The trust map's author read the case log correctly,
saw #77 taken, and took #78, which `r_a7c12f` had also taken. AIMO-2's own entry even says
"Number #77 is provisional; if a parallel session claimed it, renumber."

The repair is two lines and worth more than the renumber: normalise AIMO-2's heading so the
guard can see it, and add an assertion that the count of parsed numbers equals the count of
`### Hunt` headings, so a heading the regex cannot read fails loudly instead of silently
dropping out of the check. This is the tree's own core-candidate finding restated
(nothing in `tests/` checks that a guard fires on what it exists to catch), and here it has
a live instance: the guard was watching 53 entries and there were 54.

---

## 2. The five lesions (§XLVII.4 A–E)

For each: the minimum mechanism, and whether the tree already does it. The instruction was
to prefer strengthening what exists. In four of five cases something already exists.

### LESION A: Hunt #76, internal work rebuilt

*Can existing internal work be recovered before duplication?*

**Minimum mechanism: a prior-art field in the HuntSpec that names what was searched, plus
one grep of `CONTEXT.md` at hunt open.** Not `scripts/frontier.py` as specified in §XIV.

**What exists.** `CONTEXT.md` already lists `zeta.explicit.prime_spectrum`, and PR #91
records that hunt #76 regenerated `CONTEXT.md` **twice without reading it** (REPORTED, PR
#91 body). The index was present, current, and machine-generated. The failure was not
missing infrastructure. It was that nothing required the worker to state what it had
searched.

**Against §XIV.** The proposed `scripts/frontier.py` searches six sources with zero model
tokens. Two objections. First, the artifact that would have prevented #76 already existed
and was regenerated by the very hunt that duplicated its contents, so adding a seventh
retrieval surface does not obviously fix a reading problem. Second, §XIV's requirement list
("ZERO model tokens; fast; deterministic; clean-clone runnable; CI-compatible") describes a
tool, and `AGENTS.md` has a standing rule against building infrastructure without a live
consumer. The live consumer here is one line in a checklist.

**RECOMMENDATION.** Add `prior_art_searched` as a required non-empty HuntSpec list, checked
lexically by `tests/test_huntspec.py` the way `required_oracles` already is, and require one
entry to name a source *inside this repository*. That is an edit to an existing validator.
Build `frontier.py` only if a second #76 happens with the field in place, which would prove
the field is not enough.

### LESION B: R-662B12, producer output promoted

*Can producer output remain merely REPORTED until independently checked?*

**Minimum mechanism: nothing new. Use the review ledger that already exists and already
enforces this.**

**What exists.** `harness/departments/review_ledger.py` (356 lines, actively maintained,
FACT) records claims and whether a blind attack has run.
`scripts/70_lab_state.py` renders "reviews missing an attack" as an attention queue item
(FACT: its docstring). And the mechanism is *live*: 6 of the 88 Fulcrum runs carry the
mission `claim 'urms2-0.51' has no recorded blind attack: the review is not standing until
one runs` (FACT). The institution is already generating exactly the right work item from
exactly the right ledger.

**The actual defect is downstream of the mechanism.** All 6 of those launches are in
`task-failed` state (FACT). The gate fires, the work is emitted, the work dies, and the
roster re-emits it. §XVII proposes a promotion rule. The tree has one. What it does not
have is a queue that notices six consecutive failures on the same item.

**RECOMMENDATION.** A `failed_attempts` counter on the roster entry and a refusal to
re-emit past two, which surfaces the item to Thomas as blocked rather than burning a
seventh launch. This is a Fulcrum change, roughly one field and one condition.

### LESION C: AIMO/Krenn, headline-premise comparison

*Can allocation avoid bad headline-premise comparisons?*

**Minimum mechanism: a required field on any allocation decision naming the per-unit
figure and its source, not the pool.** There is no existing mechanism for this and I am
not aware of one. This is the one lesion where something genuinely new is needed, and it
is a form field, not a system.

**Sharper.** The consolidation treats this as an AIMO problem. It is not confined to AIMO.
The same shape is live inside the Ainta hunt right now: the bound map `Φ(c, m)` was
reconstructed by fitting two published constants, and **Ainta's `m = 269` was solved for
from the number rather than read from the paper** (FACT: `RESULTS.md` §4 says so). The
paper is public and reading it is cheap. Every ceiling figure in that hunt, including the
"5.6% of the room" headline, is conditional on a parameter that was inferred when it could
have been read. That is Failure C, committed inside the hunt the consolidation nominates
as the instance of Failure D, four days after Failure C was named.

**RECOMMENDATION.** The field is one line: *what is the per-unit figure, where did you read
it, and what did you not read?* Its value is that the third clause is answerable and
embarrassing.

**Update, and it is the strongest evidence in this review that the institution self-corrects
faster than it fails.** Hunt #78's `TRUST-MAP.md` landed on `main` the same day and derives
`Φ` from the source instead of fitting it. `m` is not a free parameter: it is capped, the
cap is a function of `c`, and **Gohms's 267 is smaller than Ainta's 269 precisely because
their `c` is larger** (FACT, `TRUST-MAP.md` §1.2). The monotonicity puzzle I raised is
resolved, the fitted parameter is now a read one, and the family optimum is derived:
`m = 267`, `Φ(c*, 267, 3000) = 0.673025476838`. The Lesion C criticism stands as a
description of what Hunt #77 did. It was closed within a day by the companion hunt, without
anyone outside asking.

### LESION D: Ainta, certificate reproduction versus theorem verification

*Can the institution distinguish finite certificate reproduction from complete theorem
verification?*

**Answer: yes, and it did, unprompted.** This lesion is already passed and the
consolidation does not seem to know it.

FACT, from `hunts/ainta_seven_point/RESULTS.md` §5: "It does not call the seven-point
theorem verified. The finite certificates are." FACT, from `MISSION.md`, `agents_may_not`
includes "declare the seven-point theorem verified, only its finite certificates are", and
the analytic bridge is explicitly routed to a companion `TRUST-MAP.md`. FACT, from PR #97's
own checklist: "The authoring agent did not assign evidentiary status to its own output".

**The mechanism that produced this is the HuntSpec `agents_may_not` list**, which is
already required, already validated by `tests/test_huntspec.py`, and already worked. No new
mechanism is needed for Lesion D. What is needed is that the list be required of every
hunt, which returns to §1.1: it is absent from 13 of 57 hunt directories (FACT).

**The residual risk is not in the hunt, it is in the reading surface.** `zeta-record` is
where an outside reader meets this. §7.5 covers what should and should not go there.

### LESION E: Fulcrum stale console and orphans

*Does operational state correspond to reality?*

**Partly, and the gap is now measurable.** The liveness repair described in §XX is real and
I did not attempt to re-break it. But three ledger facts say operational state is still not
reality:

- **Cost is known for 14 of 88 runs** (FACT: `fulcrum_cost` reports `priced_runs: 14`,
  `unpriced_runs: 22`, and the cost view covers 36 of the 88 runs at all). Every
  `antigravity` run, **37 of 88 and the largest single backend**, is unpriced.
- **45 of 88 runs carry no `result_status`** (FACT).
- **20 of 88 runs have no recorded backend** (FACT).

**RECOMMENDATION.** §XXII says economics must include Thomas's attention and provider cost.
Before any of that, the cheaper fix: a pricing table for the non-Claude backends. An
objective whose denominator exists for one run in six is not being optimized, it is being
asserted, and `AGENTS.md` has a rule against metrics without denominators.

### The lesion the consolidation does not have, found while running its own required tests

**FACT.** `tests/test_doors.py` fails 2 of 4 on `main` at `f8f881b`, in the shared
checkout, before any change of mine. The cause is not in the tree. The shared virtualenv's
editable install points at a deleted directory:

```
MAPPING = {'ontology': '<home>/.gemini/antigravity/worktrees/fulcrum/
            enable_fulcrum_mode/.worktrees/5b1bc3b4-.../ontology',
           'zeta':     '.../5b1bc3b4-.../zeta'}
```

(FACT: `.venv/.../__editable___zeta_lab_0_1_0_finder.py` line 9; the target directory does
not exist.) Some session ran `pip install -e .` from inside a temporary Fulcrum worktree,
repointing the shared venv, and the worktree was later swept.

Consequences, all FACT. `import zeta` fails from every working directory except the repo
root, where `sys.path` happens to supply it. `scripts/06_tour.py` does not run, which is
what the door tests report. And the preflight `AGENTS.md` instructs every session to run
before trusting a green suite,
`python -c "from zeta import rigor; print(rigor.BACKEND, rigor.available_backends())"`,
**cannot be executed at all** from outside the root.

Three things make this worse than a broken install. `pytest` masks it, because it inserts
the rootdir on `sys.path`, so the suite is green for a reason unrelated to the package
being installed. It silently disables the one check the tree mandates against a silently
degraded rigor backend, which means **"the backend is Arb" is currently believed and not
checkable**. And it was caused by precisely the hazard `AGENTS.md` already warns about,
parallel sessions against a shared checkout, in the one resource that is shared and is not
version controlled.

**RECOMMENDATION.** `.venv/bin/pip install -e .` from the repository root, then re-run
`tests/test_doors.py`. Then one assertion worth more than the fix: a test that
`zeta.__file__` resolves under the repository root. Same family as
`tests/test_check_secrets.py`, the guard written after a guard failed open.

---

## 3. §X.G and Q11: RUNS.md should be generated, not killed

**FACT.** `RUNS.md` is present in 2 of 57 hunt directories. As a discipline asking humans or
agents to write it, it has failed: 3.5% over the tree's whole history is not a habit that
needs strengthening, it is a habit that does not exist.

**FACT.** The data is already stored. Of the 34 hunt directories named `r_XXXXXX`, **33
have a matching Fulcrum run record** keyed by `roster_id` (`hunts/r_2ac05f` ↔ `R-2AC05F` ↔
run `55786d8e`, branch `hunt/r-2ac05f-55786d8e`). Of those 33, **28 carry a `conclusion`
sentence** and **26 carry both a terminal timestamp and a branch**.

| runmanifest field | source | status |
|---|---|---|
| `id` | `roster_id` + `run_id` | stored |
| `hunt` | directory name from `roster_id` | stored |
| `started` / `finished` | run timestamps, `task_terminal_at` | stored for 26 of 33 |
| `outcome` | `conclusion` | stored for 28 of 33 |
| `artifacts` | `git diff --name-only start_commit..branch` | derivable |
| `ran` | nothing records the commands executed | **not stored** |

**RECOMMENDATION: generate it, drop `ran` to optional, and do not kill it.** Five of six
fields are already there. `ran` is also the field with the least evidentiary value: what a
run executed is recoverable from its branch diff, whereas what it concluded is not
recoverable from anything else.

Two objections to my own recommendation, since §X.G warns against ticking a box. First,
this covers only the 34 Fulcrum-launched hunts; the 23 hand-made ones have no run record
and a generator leaves them empty, so the compliance number improves without the hand-made
hunts improving. Second, generating `outcome` from the launcher's record inherits whatever
the run chose to report, which is the self-assessment problem moved one indirection back.

**Do not kill it,** because the format demonstrably works when used. `hunts/r_044dd2/RUNS.md`
carries four manifests, one recording a configuration killed after the unresolved coloring
count rose from 117 to 1002, with no mathematical conclusion (FACT). And
`hunts/ainta_seven_point/RUNS.md` carries eight, "including the one first attempt that
produced nothing" (REPORTED, PR #97). A night of work kept as a fact is exactly the stated
purpose, and both examples are recent.

---

## 4. The addendum: limit-finding (Q1, Q12, and §10's taxonomy)

Every limit-type result I could locate, classified by the addendum's own §10 taxonomy. The
rightmost column is the one that decides the question.

| # | result | where | §10 class | outside party attempted the same? |
|---|---|---|---|---|
| 1 | harness never beat control: 4 preregistered experiments, 3 subjects, 74 runs, control 37/37, b−c = 0 in every design | `harness/VERDICT.md` | economic | no |
| 2 | zero call sites of the harness API outside `harness/` and `tests/`, while ten `hunts/` files reimplement its four roles by hand | `harness/VERDICT.md` §3 | economic | no |
| 3 | exhaustive testing over all 65,536 i8 inputs provably cannot observe poison-class defects; 3 invalid rewrites byte-identical at -O0 and -O2 | `compiler/semantics.py` | formal | no |
| 4 | `shams.py` cannot plant the modes `integrity.py` declares itself blind to; 3 of 6 blind spots have mutators, 2 of those are caught, leaving 1 artifact that tested the question | `docs/28` | evidentiary | no |
| 5 | three commonly-cited structural properties of ζ discriminate nothing | issue #21, `docs/22` | structural | no |
| 6 | the Davenport-Heilbronn battery: a property a structure-matched rival also satisfies has distinguished nothing | `zeta/epstein.py`, `docs/09` gate #3 | structural | no |
| 7 | Bian Lemma 12 erratum, with the general κ form an earlier internal hunt did not state | `docs/31` | structural | two internal hunts, no outside party |
| 8 | Krenn-Gu measured algebra wall: ~13.38M relation multiples, ~2.9M columns, fill-in explosion | `hunts/r_31b6c1/`, §XXXV | computational | no |
| 9 | five longshot probes run to their walls | `docs/18`, `ROADMAP.md` §215 | mixed | no |
| 10 | the `dps=min(_d, 20)` cap silently defeating higher requested precision | PR #81 (open) | computational | no |
| 11 | hunt #76 measured what `zeta.explicit.prime_spectrum` already computes | PR #91 (open) | evidentiary | no |
| 12 | nothing in `tests/` checks that a guard fires on the thing it exists to catch | core candidates from runs `454cd7c2`, `cccb40e0`, `aa4aacde` | evidentiary | no |
| 13 | the seven-point certificate family stops at ≈0.673025, ~5.6% of the room under 0.68185 | `hunts/ainta_seven_point/` | structural | **three groups climbing it, none mapping the ceiling** |
| 14 | the verifier's compactification prune is unsound at any target above `19/5000`, so Gohms's published certificate does not establish its own claim | `TRUST-MAP.md` §5.1 | evidentiary | **yes: Gohms published it, the lab found the defect** |

**FACT: the lab produces limit-results at volume and no class is empty.** Fourteen entries
across all five. As a description of what the lab does well and keeps choosing to do,
"limit-finding" is accurate.

**FACT: "comparative" is evidenced once, and row 14 is the instance.** In twelve of the
fourteen rows there is no outside party attempting the same object, so there is no
comparison to win, and what those rows demonstrate is a lab unusually willing to audit its
own instruments. That is a disposition, not an advantage over anyone.

Row 14 is different and it arrived during this review. Three groups are running the same
verifier; one of them published a certificate at a target the verifier's compactification
argument does not support; the lab found it by reading the source (§7.4). That is a real
head-to-head on a live object, and the lab won it. **One instance is not a comparative
advantage**, and the qualifier in §7.4 matters: the lab reproduced the same defect before
catching it. But it is the first data point of the right shape, it did not exist when the
addendum was written, and it is worth more than the twelve rows above it combined for the
question the addendum is actually asking.

**The one head-to-head does not carry the claim.** E0 (2026-08-20) is the only measurement
in the tree that puts the lab's method against outside checkers on the same task. The
co-designed audit scored 0.889 detection against 0.667 (`claude-opus-5`), 0.556
(`gemini-3.1-pro`) and 0.333 (`grok-4.6`) (FACT: `docs/28` line 117ff). Three reasons it
fails as evidence of comparative advantage:

1. **`docs/28` disqualifies it itself.** The audit *runs* the battery via
   `run_battery`/`run_detector`; the models were handed static text. That is a capability
   difference the design never named.
2. **On the only discriminating item, every arm scored 0 of 1, the lab's audit included**
   (FACT: `docs/28` line 155, "No credible checker caught the one genuine blind spot").
   The lab won an aggregate over items that did not discriminate.
3. **The load-bearing finding was not produced by the designed comparison.** It came from
   noticing the catalog and the planter had drifted apart, an after-the-fact dataset audit.
   The experiment built to test the lab's advantage did not find the limit; a person
   reading the dataset did.

**Q1, answered (INFERRED, and this is the review's load-bearing judgment).** Limit-finding
is a demonstrated specialization and a genuine institutional habit. It is **not yet** a
demonstrated comparative advantage, but it is closer than it was three days ago. Of the two
comparisons against outside parties the lab has: E0 is confounded by access on its own
account and the lab failed its only discriminating item; row 14 is clean and the lab won it.
That is n = 1 for the claim, with a qualifier (§7.4) that the lab first reproduced the
defect it later caught. Twelve of fourteen rows are the lab auditing itself, which is the
selection bias §10 asks to be checked for. **The honest statement is: one instance, not a
pattern, and the pattern is testable now that the lab knows what the right instance looks
like.**

**Q12, answered.** Better positioned to explain where the race ends, and the reason is
mostly **position** rather than capability: three groups are optimizing the same certificate
and none is asking where it stops, so the ceiling question is unoccupied. Opportunities
close. Take it because it is empty.

But row 14 adds something the addendum did not anticipate and it is the more durable
version of the thesis. The lab's edge on this object turned out not to be finding a better
number or even the ceiling. It was **reading the verifier rather than running it**. Three
AI-driven groups ran the same program and none checked whether its compactification argument
survived a change to the constant they were all changing. That generalizes further than
"limit-finding" does, it is cheap, and it is the one thing in this whole board that nobody
else appears to be doing.

**The cheapest test that would convert this into a pattern.** Do it once more, deliberately,
on a different object: take the next externally published computer-assisted result the lab
cares about, and before reproducing it, read its reduction arguments against its own
parameters. If that finds a second defect, the addendum's thesis has real support and a
mechanism to go with it. If it finds nothing, row 14 was luck, and knowing that is worth the
afternoon.

---

## 5. Decision 2 (§XLVIII): ranking, with the cheapest discriminating test

Ranked. The discriminating test is the cheapest observation that would move the candidate
up or down, and in three of four cases it costs under a day.

### 1st: Ainta formal-native (the parameterized bridge)

**Why first.** It is the only candidate where the expensive precondition is already paid.
Both certificates reproduce, the floor is bracketed at both ends (§7.3), and the target
theorem has a clean shape the addendum §6 states correctly: separate `F6 ≥ c` from
`Φ(c, m)`, so a better certificate tomorrow leaves the Lean bridge untouched. It also
directly serves Q12's one available data point.

**Cheapest discriminating test: already run, and it passed.** I had drafted this as "read
Ainta's paper and recover `m`". PR #98 landed `TRUST-MAP.md` before I finished, and it does
exactly that and more. The results that matter for the ranking, all FACT from that document:

- **World verdict B**, one substantial analytic bridge, with a large but well-templated
  certificate-consumption job hanging off it. Not A (a few missing lemmas), not C
  (infrastructure only), not D (poor marginal value).
- **The bridge is two steps, S8 and S9**: carrying a new nonnegative spectral defect term
  uniformly through the tail passage, and establishing the limiting overlap kernel with
  uniformity in `T`. Both reach into the source preprint's proof rather than citing its
  theorem.
- **Six of sixteen steps are already kernel-checked** in a sorry-free development, including
  von Neumann and the positive-part splitting, and four more are small finite statements.
- **The smallest obligation is named, scoped and written out in Lean-ready form**: S2, the
  stability rank-trace lemma, finite-dimensional, no analysis, no limits, no zeta, whose
  three structural inputs are existing declarations and which has a built-in non-vacuity
  check (specialising `Ψ` to 0 must recover the existing lemma exactly).
- **What a probe should not be pointed at is also named**: S8 and S9.

That is the best-specified research task on the entire board, and it is the only one where
the next action is a single named theorem with a scoring criterion attached.

**Revised gate, since the old one is spent.** Point a bounded Aristotle probe at S2 and
nothing else. Success is *not* "Aristotle returned a proof": it is whether the residual goals
say something about the mathematics, which is §LI's own test for formal-native work and has
never been run in this tree. The trust map's own caveat should be carried into the scoring:
"a probe that lands S2 has not moved the theorem, it has moved one lemma."

**Risk to name.** §XXXII calls this a formal-native pilot. It is mostly a *formalization*
pilot with a research question attached. Do not let it be scored as evidence about
Lean-in-the-loop discovery (§LI) unless the residual goals actually change the mathematics.

### 2nd: Davenport-Heilbronn

**Why second and not first.** It is the strongest sustained program by depth, with Λ_DH
bounds, the unconditional Λ_DH > Λ_ζ result, a formalized analytic half, and a Palomar
entry. Second only because it has no clock on it. Nobody outside is racing it, so its value
does not decay if it waits a month. Ainta's does.

**Cheapest discriminating test.** State the single next theorem on the off-line-zero side
and estimate its difficulty against the existing `DHAnalytic`/`DHTailBound`/
`DHZeroCriterion` modules. If the next step is "compute", it stays parked behind Ainta,
because `AGENTS.md` already records rung 3 as "mathematics-complete and waiting on compute"
and more compute is not a research decision. If the next step is a lemma, it competes.

### 3rd: Cross-Arm Transfer

**Why third.** §XLVIII already says "run its cheap discriminator first; only earns program
status if it survives", and that is right. I have nothing in the tree that raises or lowers
it, which is itself the finding: I could not locate a Cross-Arm artifact in `~/Zeta` at all.

**Cheapest discriminating test.** Run the discriminator the document already names, and if
nobody can say in one sentence what it discriminates, that is the answer.

### 4th: Verification science

**Why last, and this is a demotion from how the consolidation frames it.** §XLII proposes
unifying the harness result, E0, AIMO, and the promotion failures into one question: when
does verification machinery manufacture the appearance of correctness? It is a real and
interesting question. It is also the candidate most likely to reproduce the harness
mistake, because it is a *meta*-program about the lab's own instruments, and
`harness/VERDICT.md` is 8,000 lines of exactly that with zero consumers.

**Cheapest discriminating test, and it is genuinely cheap.** The four anecdotes share a
thesis only if they share a mechanism. Take the one mechanism that is already pinned,
`docs/28`'s finding that a planter and a catalog drifted apart with nothing comparing them,
and ask whether it is present in the other three. If the harness result, AIMO, and the
promotion failures each reduce to "the instrument's declared coverage was never compared
against its actual coverage", it is one line and worth funding. If they reduce to three
different mechanisms, it is three anecdotes with a shared mood, and §XLII should be closed.
Cost: one reading pass over three existing documents. Do this before allocating anything.

**Do not launch all four**, which the document already says. The ordering above is also a
statement that only the first has a deadline.

---

## 6. Q28: where Thomas is still acting as infrastructure

Four places, one example each, all FACT.

**6.1 As the failure memory of the queue.** The mission `claim 'urms2-0.51' has no recorded
blind attack` was launched **6 times** and is `task-failed` in all 6. Four other missions
were launched 2 to 4 times each. Nothing in the roster records that a previous attempt
failed, so the only thing that stops the seventh launch is Thomas noticing. *Fix:* a
`failed_attempts` counter and a refusal past two.

**6.2 As the funding decision for every thread.** 134 threads and 53 core candidates, none
funded. Every one of the 187 is waiting on a human to read it and choose. There is no
triage, no expiry, and no batch. *Fix:* this is not a mechanism, it is a decision. Either
schedule one hour that dispositions threads in bulk, or stop writing them.

**6.3 As the cost accountant.** 37 of 88 runs are on a backend that reports no price at all.
Any economic judgment about those runs is currently Thomas's estimate. *Fix:* a pricing
table for the non-Claude backends.

**6.4 As the integration layer between hunts and the record.** The Ainta hunt has produced
results that its own PR does not contain (§7.3). The only thing that will notice is a person
looking in the directory. *Fix:* see §7.3; it is a one-line addition to the hunt's own
results file, not a system.

**What is not on this list, deliberately.** Thomas reading and deciding this document is
not infrastructure, it is ownership, and §V is right about that. The four above are all
cases where a human is substituting for a counter, a table, or a scheduled hour.

---

## 7. Lesion D's instance: the Ainta/Gohms record, audited

The hunt is now complete and PR #97 is open and mergeable (FACT). This section is
adversarial; the mathematics survives it.

### 7.1 What reproduces, and one thing sharpened

**FACT.** Ainta's seven-point certificate reproduces field for field except
`elapsed_seconds` and `second_derivative_table_sha256` (`7913c55…` published, `db0327b0…`
local). Gohms's `191/50000` reproduces on the three figures the issue reports (nodes
786,421, pruned 393,575, depth 43).

**Sharpening the hash, which the consolidation §XXVI records as "cause unconfirmed".** The
same local value `db0327b0…` appears in *both* the seven-point local run and the
independent Gohms run at a different target, while `kernel_table_sha256` matches upstream
in both (FACT: both artifacts). So the difference is deterministic and
environment-determined, not nondeterminism and not a per-run fluke: one of the two tables
the verifier builds is stable here and differs from upstream, the other agrees. That
narrows the cause to the second-derivative table's construction. `RESULTS.md` states the
version hypothesis was not tested because older `python-flint` does not build on Python
3.14 here, which is the honest position.

### 7.2 A genuine defect in the upstream verifier, worth the reproducibility report

**FACT.** The Gohms artifact header reads `effective target: 191 / 50000 = 0.00382`, and
eight lines later the verifier's own report field reads `target=F6 >= 19/5000`. `gohms.py`
patches `vs.TARGET_NUMERATOR`/`TARGET_DENOMINATOR` before calling `verify_seven()`; the
report's label does not derive from them. The run did the harder work (786,421 nodes and
1,158 s against 707,901 and 155 s), so the intended target was checked. But **the
certificate does not record which target it checked**, and that is the field an outside
reader would rely on. This belongs in the report to Ainta alongside the hash.

### 7.3 The bracket is rigorous on both sides, and the eight-point reading is not what it looks like

**Status note, because this moved under me.** When I first read the hunt, a Modal run
(`modal_ceiling.py`, `modal-run.log`, 317 KB) was dated 00:59 and 01:00 against 00:49 on
`MISSION.md`, `RESULTS.md` and `RUNS.md`, and its output was untracked: the hunt's results
file said a computation "was not done here" that had in fact been done. That gap is now
closed. `artifacts/modal-results.json` is committed, `RESULTS.md` §3 carries the results,
and PR #97 was updated at 06:07Z (FACT). I record the window only because it is the same
shape as §XLI's "research state existing outside the canonical tree", it lasted about five
hours inside the hunt nominated as the instance of Lesion D, and it closed without anyone
outside noticing. No action needed.

**FACT, now in the record, and see §7.4 before citing the lower end.** The hunt states the
bracket as

```
0.003826  ≤  inf F6  ≤  0.0038262312115073
```

Upper end: Arb at 256 bits evaluating F6 at the minimiser, an upper bound on the infimum
because it is the value at an admissible point. That end is sound. **The lower end is not**:
it rests on an accepted run carrying the unsound compactification prune that
`TRUST-MAP.md` §5.1 identifies (§7.4). The bracket that is actually established is
`0.0038 ≤ inf F6 ≤ 0.0038262312115073`, width 2.6e-5.

**FACT: the grid control was run and it is the strongest single piece of evidence in the
hunt.** The two targets were rerun with the verifier's grid doubled to 8000 and its two
grid-scaled constants doubled with it. `1913/500000` accepted (898,669 nodes, depth 57,
233 s); `0.0038263` refused at cell `(8368, 15919, 15889, 8333, 15816, 8360)/8000`, the
same configuration to four decimals at double resolution. This is what answers addendum Q9,
and better than anything I would have proposed.

**Correction to a reading I had made.** The eight-point floor is 0.0043887, *higher* than
the seven-point 0.0038262, and I initially read that as "more points buys something". The
hunt's own analysis is better and I defer to it: the `1/3000` linear pressure is not the
right scaling at eight points, the pressure term and the block size `m` are one parameter,
and the certificate-to-bound map changes with `n`. So the comparison is confounded by the
same hole §4 of that document names, and **the eight-point number currently says nothing
about whether widening the window helps.** It is the trust map's first obligation seen from
the other side. Addendum Q10 is therefore still open, and §9.10 below is written accordingly.

### 7.4 RETRACTED: the lab is not sitting on a stronger certificate, and neither is Gohms

An earlier draft of this review recommended publishing the lab's accepted probes at
`153/40000` and `1913/500000` as certificates stronger than the published frontier. **That
recommendation is withdrawn.** Hunt #78's `TRUST-MAP.md` §5.1 landed the reason while this
was being written, and it applies to the lab's probes at least as hard as to Gohms's run.

**The defect (FACT, `TRUST-MAP.md` §5.1, and I re-checked the arithmetic).** The verifier
reduces an unbounded region to a compact box by one argument: if `Σgᵢ ≥ 11.4`, the linear
pressure alone proves the target. `PRESSURE_CUTOFF_CELLS = 45600` at `GRID = 4000` is
`Σgᵢ ≥ 11.4`, and `11.4 / 3000 = 0.0038 = 19/5000` **exactly**. The prune is sound at
Ainta's target, at equality, with nothing to spare. `verify_seven.py:276` applies it
unconditionally, without consulting the target.

So any run that changes only the target constants prunes boxes on grounds that prove
`0.0038` and nothing more. Gohms's run pruned 3,087 such boxes (FACT: `pressure_pruned` in
the local artifact, matching the issue's counts). **The lab's own probes have the same
defect and a larger shortfall**: `1913/500000 = 0.003826` would need `Σgᵢ ≥ 11.478`, i.e.
45,912 cells, and the verifier pruned at 45,600.

**Three consequences, in order of importance.**

1. **My §7.3 bracket has an unsound lower end.** `0.003826 ≤ inf F6` rests on an accepted
   run carrying this defect. The lower bound that is actually established is Ainta's
   `0.0038`. The sound bracket is `0.0038 ≤ inf F6 ≤ 0.0038262312115073`, width 2.6e-5, not
   2.3e-7. The upper end is unaffected: it is an Arb evaluation at a point and owes nothing
   to the prune.
2. **Nothing here says the claims are false.** The apparent floor is 0.0038262 and the
   minimiser sits at `Σg = 9.085`, well inside the cutoff, so all of these targets are
   likely true. What fails is the artifact, not the arithmetic.
3. **The repair is one line and a re-run**, `PRESSURE_CUTOFF_CELLS = ceil(GRID · p ·
   target)`. Whether the enlarged region still closes at grid 4000 is OPEN and needs the
   run, not an argument.

**Revised RECOMMENDATION.** The report to Ainta should carry four items and one of them is
now different: the hash discrepancy with `TRUST-MAP.md` §5.2's two candidate causes, the
target-label defect (§7.2), **the unsound compactification prune**, and the one-line repair.
Do not send a stronger certificate, because the lab does not have one. Send the defect that
means nobody has one above `19/5000`.

**This is a better outcome for the addendum's thesis than the one I retracted, and §4 is
updated accordingly.** A stronger constant would have been an epsilon. A soundness defect in
the artifact three groups are climbing is a limit-result of the evidentiary class, on an
object outside parties are actively working, found by the lab. That is the first row in §4's
table where the comparative condition is genuinely met.

**The honest qualifier, which the lab should state before anyone else does.** The lab
reproduced this defect before it detected it. Hunt #77 ran two probes that inherited the
unsound prune and recorded them as accepted; Hunt #78 caught it a day later by reading the
verifier's source rather than running it. The catch is real and the sequence is not
flattering, and saying both is what makes the first credible.

### 7.5 What must not reach `zeta-record`

`zeta-record` currently carries two checked results and discloses Ainta's larger number
without vouching for it (REPORTED, and the site generator at `site/72_site.py` lines 130 and
183 carries both Palomar entry IDs, FACT). That is the correct posture. When Hunt #77 lands,
the page must say **finite certificates reproduced, analytic bridge not audited**, because
that distinction is Lesion D and the reading surface is where it will be lost. The ceiling
figure of 0.673025 must not appear without the conditionality on `m`, which is currently an
inferred parameter (§2, Lesion C).

---

## 8. §LIV, questions 1 to 31

Short answers. Where a section above carries the argument, it is cited rather than repeated.

**1. Are the six functions still the right minimal map after removing Brain?** Yes, with one
correction: function 5 (Memory & Current State) is not weak because Brain was removed. It is
weak because its outputs are hand-maintained. See Q10.

**2. Any recurring function missing?** One: **disposition**. Every function produces
candidates and nothing closes them. 187 threads and core candidates, zero funded (§1.2). It
is not a seventh department; it is a scheduled hour with authority to write `rejected`.

**3. Any of the six fake?** No, but function 4 (Research Operations) and function 1
(Direction) are currently one thing wearing two labels. Fulcrum both executes and allocates,
and its allocation half has never fired.

**4. Do the four invariants capture the major failures?** Three of four, well. Invariant 2
("which cheap assumptions could change this decision") is stated for allocation only, and
the live violation is scientific: `m = 269` was fitted, not read (§2 Lesion C). Extend it
to premises inside research, not just money.

**5. Is Zeta the right enforcement boundary?** Yes, and §XIII's argument is correct. 23 of 57
hunt directories are not `r_*` and have no Fulcrum record (FACT), so a Fulcrum-only gate
would miss 40% of the tree.

**6. Is Fulcrum correctly scoped?** Scoped correctly, staffed incorrectly. It holds
operations well and holds allocation state that nothing acts on.

**7. Smallest mechanism that would have prevented Hunt #76?** A required
`prior_art_searched` HuntSpec field with one in-repository entry, validated by the existing
`tests/test_huntspec.py`. Not `frontier.py`. See §2 Lesion A.

**8. Smallest mechanism that would have prevented R-662B12 promotion?** None needed: the
review ledger already emits the blind-attack requirement, and did, six times. The missing
piece is a failure counter on the queue. See §2 Lesion B.

**9. What would have prevented the AIMO prize-premise error?** A field naming the per-unit
figure and its source. This is the one lesion needing something new, and it is a form field.

**10. Can current scientific state be generated from existing Zeta artifacts?** Partly, and
the renderer already exists. `scripts/70_lab_state.py` renders research state from the
graveyard, guard and review ledgers, independence declarations, the hunts case log and
HuntSpec blocks, with a derived attention queue (FACT: its docstring). **The honest limit:
three of those inputs are hand-written Python modules** (`graveyard_ledger.py`,
`guard_ledger.py`, `review_ledger.py`, 627 lines total, FACT). They are current, last
touched 2026-08-20 and 2026-08-21. But a `STATE.md` generated from hand-maintained ledgers
moves the staleness problem one level down rather than removing it. Only two inputs are
genuinely derived: git, and the hunts' own files. **RECOMMENDATION:** do not build
`STATE.md` as a new artifact. Extend `70_lab_state.py` with the §XIX status vocabulary and
a `CONFLICT` output, and be explicit on the page about which inputs are declared and which
are derived.

**11. Should RUNS.md die?** No. Generate it. §3.

**12. Does Fulcrum's live loop work today?** Not established, and the ledger says the loop
has a specific weak stage: **14 of 88 runs are `task-failed`, 16%** (FACT), and 45 of 88
carry no result status. §XXI's one-child test is the right experiment and should be run as
specified, with the first failure taken as the result.

**13. How to measure Fulcrum against Git + strong prompts?** The denominator already exists:
34 Fulcrum-launched hunts against 23 hand-launched ones, in one tree, on comparable work.
Do not run a new experiment first. Grade the existing 57 against the contract in §1.1 and
against whether they produced a landed result, split by launch path. If Fulcrum's hunts are
not better on either axis, that is the answer and it cost one afternoon.

**14. Is the resurrection experiment sound without Brain?** Sounder. Removing Brain removes
the confound that made Arm B unreproducible. But §XXIV's instruction "do not run this yet"
is correct for a reason the document does not give: **the treatment does not exist yet**.
There is no generated frontier and no generated state, so Arm B currently equals Arm A.

**15. How to measure operator minutes without bureaucracy?** `meta/ledger.py` already exists
for exactly this and already refuses to divide until the caller names its numerator. Use it.
Do not build a timer.

**16. Is external transfer a real function or owner housekeeping?** Real, and §7.4 is the
proof: a stronger certificate and a rigorous bracket are sitting unpublished while three
groups work the same object. That is not housekeeping, it is the highest-value action
available, and no function owns it.

**17. Does Ainta end the numerical Pub 1 race?** Yes, and more sharply than §XXVI says. The
race does not end because Ainta won it. It ends because the floor is now bracketed to
2.3e-7 (§7.3) and the remaining purse is arithmetic.

**18. Is Pub 1's barrier result more valuable now?** Yes, and the reason is positional, not
mathematical: three groups are hill-climbing toward a ceiling the barrier work already
bounds. Value rises with the number of people about to hit it.

**19. Is Ainta the best formal-native pilot?** Best available, conditional on Q7 of the
addendum. See §5.

**20. Are we overexcited about "research in Lean"?** Somewhat. §XXIX's loop is plausible and
has zero instances in this tree. §LI already states the right test and the honest current
answer is that it has never been run.

**21. What experiment would demonstrate formal state improved discovery?** A pre-registered
one: before formalizing, write down the expected obligations; after, record which residual
goals were *not* on the list and whether any changed the mathematical plan. The prediction
written first is what makes it an experiment rather than a story.

**22. Is Aristotle useful as a probing instrument in practice?** Unknown here. No artifact in
`~/Zeta` records an Aristotle probe outcome, so any answer would be invention.

**23. Should DH remain the default sustained program?** Yes as default, no as first. §5.

**24. Should Cross-Arm get its cheap discriminator first?** Yes. And if nobody can state in
one sentence what it discriminates, that is the result.

**25. Is verification science one line or three anecdotes?** Undetermined, and there is a
one-pass test for it. §5, 4th.

**26. Are AIMO and Krenn rationally allocated?** Krenn yes: PARKED with a named re-entry
condition is correct and §XXIII's separation of scientific from allocation status is the
document's best single idea. AIMO yes on timing, with one caution: §XXXVIII's activation
probe at "$15 to 25" is the same headline-premise error in miniature, priced in dollars
while its real cost is attention.

**27. Which finished outputs should leave first?** In order: (1) the reproducibility report
to Ainta, four items, §7.4; (2) the Pub 1 barrier note to the authors whose method it
bounds; (3) the OEIS correction from prime zeta. All three are written or nearly written.

**28. Where is Thomas still infrastructure?** §6, four places.

**29. What process should be deleted immediately?** The thread and core-candidate ledgers as
currently operated. 187 entries, 0 funded. Either disposition them in bulk this week or stop
writing them, because a backlog nobody reads is the thing `AGENTS.md` refuses to build, and
it is currently being built one handback at a time.

**30. What do we "know" only because an agent said it confidently?** Three, and the third is
the one that matters. (a) `Φ(c, m)`'s form, fitted from two points, with `m = 269` solved
for rather than read. (b) The Arb-version explanation of the hash discrepancy, explicitly
untested. (c) **That `rigor.BACKEND` is Arb.** `AGENTS.md` mandates checking it before
trusting a green run, and that check currently cannot execute (§2, last lesion). Every
"certified" claim in the tree rests on a preflight that has been unrunnable for an unknown
period.

**31. What are we still too close to see?** That the lab measures its instruments far more
than its output. Of the thirteen limits in §4, eight are limits of the lab's own machinery.
That is admirable and it is also where the effort went. The addendum reads this as a
research identity. Read the other way, it is a lab that has become very good at auditing
itself and has published two checked results.

---

## 9. Addendum §11, questions 1 to 12

**1. Real comparative advantage or overinterpretation?** Real specialization, not
comparative. §4.

**2. Should it influence problem selection?** Yes, weakly, and as a tiebreak rather than a
strategy. Prefer questions where the frontier is unoccupied over questions where it is
crowded, which is a positional rule and does not require the capability claim to be true.

**3. Is the stronger strategy reproduce → locate ceiling → characterize → formalize?** Yes,
and steps 1 and 2 are done, with the floor now bracketed rigorously at both ends and a
grid-doubling control confirming the refusal is the inequality's and not the grid's (FACT,
§7.3). Step 3 has begun and its first datum is not yet interpretable (§7.3). Step 4 is
gated on reading the paper for `m` (§5).

**4. How does the Pub 1 barrier work interact with the new frontier?** They bound the same
family from opposite sides. Remark 1.1 caps configuration-coupled information at 0.68185;
this certificate stops at ≈0.673025. The interval between them is the real research object
and neither party is working it.

**5. Could the barrier become more relevant now?** Yes. §LIV.18.

**6. Should Ainta/Gohms be the first formal-native pilot?** Yes, and the condition I would
have attached has since been discharged by `TRUST-MAP.md`. §5.

**7. Cleanest parameterized Lean theorem?** Answered by the trust map, not by me. The
addendum's shape was right, and the obstruction I was going to name is gone: **`m` is not a
free parameter.** It is capped, the cap is a function of `c`, and Gohms's 267 is below
Ainta's 269 because their `c` is larger (FACT, `TRUST-MAP.md` §1.2). So the theorem is
`Φ(c, m, p)` with `m = m_max(c)`, and the deduction's arithmetic has been re-derived rather
than fitted, reproducing both published constants. The formula is no longer the blocker; the
bridge (S8, S9) is.

**8. Which parts should Aristotle probe?** **S2, the stability rank-trace lemma, and
nothing else.** The trust map states it in Lean-ready form in the target development's own
vocabulary, notes that its proof is an existing proof with one scalar estimate sharpened
(`min_{n≥0}((p−n)² + 4n) = 2p − 1 + Ψ(p)`, a one-variable calculus fact), and supplies a
non-vacuity check. It also says explicitly what not to probe: S8 and S9, which import the
source preprint's machinery. Second target if S2 lands: S12, same file, two cases. This is
the most probe-ready obligation anywhere in the tree and it did not exist yesterday.

**9. What distinguishes a genuine ceiling from a verifier limitation?** Answered, and it is
the best-evidenced thing in the hunt. A verifier limitation would show as a refusal whose
terminal cell moves with the grid. Three independent signals say it does not. The refusal at
0.0038263 lands on the single cell `(4184, 7960, 7944, 4166, 7909, 4180)`, which is the
configuration the float minimiser reaches by a completely different route. Doubling the grid
to 8000 reproduces both the acceptance and the refusal, at the same configuration to four
decimals. And the 256-bit Arb enclosure at the minimiser closes the bracket from above
(FACT, all three, §7.3). Two methods with nothing in common agreeing on the minimiser, and
the answer surviving a resolution change, is the discriminator.

**10. If the ceiling is found cheaply, what is the highest-value next question?** It was
found cheaply, and the answer has changed twice in a day. Not the eight-point floor as a
number (§7.3), and no longer the `m` coupling, which the trust map closed. **The
highest-value next question is now whether the repaired verifier still closes at grid 4000.**
`TRUST-MAP.md` §5.1 leaves it OPEN and says explicitly that it needs the run and not an
argument. It decides three things at once: whether any target above `19/5000` is actually
established by anyone, whether the lab's own probes survive, and therefore where the ceiling
really sits. It is one line of code and one re-run, and it is the only open question on this
object whose answer nobody can currently predict.

**11. Does this change the ranking?** Yes. It moves Ainta above Davenport-Heilbronn, on
deadline rather than merit. §5.

**12. Win races for constants, or explain where the race ends?** Explain where it ends, and
the last day sharpened why. It is not that the lab is better at ceilings. It is that **the
lab reads the instrument and the other three groups run it** (§4, Q1). An earlier draft of
this answer said the lab holds the best constant and is choosing not to say so; that was
wrong, and the reason it was wrong is the same finding. Nobody holds a sound certificate
above `19/5000`, including the lab, because they all inherited an unaudited prune. Racing
would have meant inheriting it further.

---

## 10. The three decisions of §XLVIII, as options

Each is drafted as options with a recommendation. Take or reject.

### DECISION 1: Institutional implementation

**Option A. Build §XLVIII's minimum list**: frontier check, standardized search records,
generated state, promotion rule, supersession rules, RUNS.md removed or generated. *Against:*
four of the six already exist in some form, and the list was written without measuring them.

**Option B (RECOMMENDED). Switch on what exists, in this order, and build only the one thing
that is genuinely missing.**

0. **Unblock `main`, which is red on two of its own guards** (§1). Renumber one of the two
   Hunt #78 entries to #79, since #77 is genuinely held by AIMO-2. Regenerate `CONTEXT.md`.
   Then close the guard's coverage hole: normalise AIMO-2's non-standard heading and assert
   that parsed numbers equal `### Hunt` headings, so an unreadable heading fails loudly.
   Every open PR including this one is blocked until the first two are done, and neither
   takes a minute. *This is item 0 because nothing else can land.*
1. `.venv/bin/pip install -e .` in the repository root; re-run `tests/test_doors.py`. Then
   the `zeta.__file__` assertion. *Next because the rigor preflight is currently unrunnable
   and everything else is downstream of trusting the suite.*
2. One test running the existing `structural_problems()` over the real `hunts/` tree with an
   explicit grandfather list. Converts a 2-of-57 contract into a guard.
3. Add `prior_art_searched` to the HuntSpec, validated by the existing test. Lesion A.
4. Generate `RUNS.md` from Fulcrum; make `ran` optional. Lesion G.
5. `failed_attempts` on the roster, refuse past two. Lesion B.
6. A per-unit-figure field on allocation decisions. Lesion C. *The only new thing.*
7. Extend `70_lab_state.py` with the §XIX vocabulary; do not create `STATE.md`.

*Not on the list, deliberately:* `scripts/frontier.py`. Revisit only if item 3 proves
insufficient.

**Option C. Do nothing structural; run the science.** *For:* defensible, and `harness/VERDICT.md`
is the standing warning against governance for its own sake. *Against:* items 1 and 2 are
under an hour together and item 1 is a live correctness problem.

### DECISION 2: Science allocation

**Option A (RECOMMENDED). Ainta formal-native first. The gate I would have set has already
been passed.** `TRUST-MAP.md` returned world verdict B, named the bridge (S8, S9), and wrote
out the smallest obligation (S2) in Lean-ready form with a non-vacuity check. Three actions,
in order, none large:

1. **Repair the compactification prune and re-run** (§9.10). One line. It decides whether
   anyone has a sound certificate above `19/5000`, and every other number here waits on it.
2. **Send the report to Ainta** (§7.4, revised): hash discrepancy with the trust map's two
   candidate causes, target-label defect, unsound prune, one-line repair. Independent of
   everything else and the highest-value hour on the board.
3. **One bounded Aristotle probe at S2 and nothing else**, scored on whether the residual
   goals change the mathematics rather than on whether a proof came back. This is the first
   real test of §XXIX's formal-native loop, and it is cheap because someone already did the
   hard part of specifying it.

**Option B. Davenport-Heilbronn as the sustained program**, with Ainta reduced to the report
and the ceiling note. *For:* more depth, no dependency on an outside author's paper. *Against:*
gives up the only lane with a clock on it, and gives it up the week its next step became the
best-specified task in the tree.

**Option C. Verification science first.** Not recommended. Run its one-pass discriminator
(§5, 4th) before it is allowed to compete at all.

**Reject in all cases:** launching more than one, and treating Cross-Arm as a program before
its discriminator runs.

### DECISION 3: Economic and external allocation

**Option A (RECOMMENDED). Transfer before new allocation.** Nothing new is funded until the
three finished outputs leave: the Ainta report (four items, §7.4), the Pub 1 barrier note,
the OEIS correction. *Rationale:* §XLV lists external transfer as the weakest recurring
function, the cost is hours, and it is the only item on the board that converts existing work
into outside contact. The Ainta report is now urgent rather than merely ready: it carries a
soundness defect affecting a published certificate that at least two other groups are
building on, and the longer it sits, the more work is done on top of it.

**Option B. Fund AIMO's activation probe and the Krenn re-entry scouting in parallel with
transfer.** *Against:* §XXXVIII's own caution applies to itself. The probe is cheap in dollars
and not cheap in attention, and attention is the scarce input this document keeps identifying.

**Option C. Hold everything until the Fulcrum loop test returns.** Not recommended: the loop
test is about operations and the transfer items do not depend on it.

**On both prize lanes, no change.** Krenn PARKED with its re-entry condition is correct. AIMO
prepared and waiting for its phase is correct. Both are owner decisions already taken and
nothing in the repositories contradicts them.

---

## 11. Three things this review could be wrong about

**What I got wrong once already, recorded because the pattern matters more than the item.**
This review made three claims that the tree corrected within hours: that the Ainta hunt's
rigorous bracket had not been computed (it had, in an untracked log), that the eight-point
floor showed widening the window helps (it does not, the pressure scaling is confounded),
and that the lab held a stronger certificate worth publishing (it does not, the prune is
unsound). Each was corrected by the hunts themselves, not by me. **A counselor reviewing
work in flight will be behind it**, and the right conclusion is not that the counselor should
be faster; it is that this role should be pointed at landed state. That is a finding about
the §XLVII.4 exercise, not an apology.

**The Ainta material may move again.** Anything in §7 and §9 should be checked against
PR #97 and `main` as they stand when acted on, not against this document.

**"Zero funded" may be a vocabulary artifact.** I read `status` fields in `threads.json` and
`core-candidates.json` and found only `unfunded` and `rejected`. If funding a thread is
recorded elsewhere, by launching a roster item rather than by mutating the thread, then §1.2
overstates the case and the real finding is narrower: the thread ledger does not record its
own outcomes. That distinction is worth thirty seconds of checking before acting on
§LIV.29, and it does not change §6.2, since either way a human is the only route from a
thread to work.
