# 21 — Forward-deployed verification: can a report refuse a crossing?

**Status when this file was committed: pre-registration only. No result in it.**
Everything below §5 was written before the gate existed, before any case was
run, and before any number was seen. The commit that adds this file adds no
implementation; that ordering is checkable in `git log` and is the only reason
the criteria below are worth anything. `REDTEAM.md` W2 is what happens when it
is not done.

---

## 1. The question

`docs/20` established that a claim outcome and the integrity of the battery
that produced it are two measurements, and made the second one mechanical
where it could be. It pairs them on a report and **prints a banner** when a
green outcome comes from a referee that has not earned trust:

```python
@property
def dangerous(self) -> bool:
    return self.claim_status == "distinguishes" and self.integrity.grade != CALIBRATED
```

A banner is advice. Nothing in the tree consumes a grade in order to **refuse**
anything. This document asks whether the pairing can become a boundary:

> Can an existing verification report decide whether a claim is permitted to
> cross from candidate information into promoted information — and does the
> **verifier's own** integrity materially change that decision while the
> claim's own numbers are held fixed?

The first principle under test is one the repository already asserts twice in
prose and enforces nowhere: **a claim may not promote itself**
(`docs/doors/adopt.md` §"The same discipline is applied to language";
`hunts/README.md`, the "may not" table).

## 2. What already exists, stated so this cannot be sold twice

This is not a green field, and most of the concept is already built. Honest
accounting, because the temptation to rename existing work is the whole
failure mode under study:

| Already shipped | Where |
|---|---|
| claim outcome vocabulary, deliberately not a truth vocabulary | `harness/protocol.py` `BatteryVerdict` |
| "the detector is blind, and its silence measures that" | `PowerVerdict.blind_to` / `has_power` |
| a battery that could not fail is refused admission | `battery_reasons` / `validate_battery` |
| five integrity grades, 16 named checks, declared blind spots | `harness/integrity.py` |
| contamination and dependence as declared data | `harness/provenance.py` |
| planted battery corruptions (the lesion principle, one level up) | `harness/shams.py` |
| refusal to aggregate independent axes | `dossier/status.py` `Support.__bool__` |
| a promotion refusal on **process** grounds with green numbers | `ontology/funnel.py:1027-1052` — `survives` needs every required screen to have run *and* verification effort above generation effort |

That last row deserves emphasis: a forward gate keyed on verifier quality
**already exists** in the discovery arm. Anyone proposing "a claim cannot
promote itself" as a new capability should be shown `funnel.py:71-76` first.

### The two gaps, both named by the shipped code itself

**Gap 1 — integrity is advisory.** `report_claim()` returns a report;
`ClaimReport.dangerous` renders text. No caller refuses a crossing. The
enforcement delta is, honestly priced, close to one conditional.

**Gap 2 — contamination is declared, not derived.** `harness/provenance.py`
says it outright: *"a provenance record is a declaration, and nothing here can
verify that a declaration is true."* `contamination_reasons` fires only when
`results_visible_when_authored is True`. `docs/20` §4 records the same limit in
its own catalog: the W2 shape is caught **"if declared"**. A producer that
writes `results_visible_when_authored=False` over contaminated work is, today,
undetectable.

Gap 2 is the interesting one. Gap 1 is plumbing.

## 3. What is being built

Two files, deliberately small.

* `harness/preregistration.py` — a `Preregistration` carrying
  `evidence_visible_at_freeze`: the digests of evidence artifacts that already
  existed when the criteria were frozen. `derived_contamination_reasons`
  recomputes contamination from digests instead of reading a boolean, and
  `declared_vs_derived` reports the **divergence** between what a provenance
  record declares and what its artifacts imply.
* `harness/promotion.py` — `decide()`, returning an ALLOW/BLOCK `Decision` with
  every reason at once as machine-readable codes; a `Boundary` on disk whose
  `audit()` reconciles `promoted/` against `decisions/`; and `NaiveGate`, the
  mandatory null control.

## 4. The null control, and why it is the whole experiment

`NaiveGate` is ~15 lines: ALLOW unless a self-declared field says
contaminated or the declared grade is bad. It reads declarations and
recomputes nothing.

**`NaiveGate` passes the clean case, the contaminated case and the
blind-verifier case exactly as well as the real gate does.** Three cases are
three constraints, and a lookup table satisfies three constraints. So the
three cases that motivated this work prove nothing on their own, and any
write-up that reports 3/3 as a success is reporting the sham's score.

The real gate is distinguishable from the sham by exactly one property:

> it re-derives contamination or blindness **from artifacts**, and therefore
> can disagree with a declaration that looks clean.

The load-bearing case is therefore **case E, the lying report**: artifacts that
imply contamination, submitted with declarations that say clean. Sham: ALLOW.
Real gate: BLOCK. If that divergence cannot be produced, the gate *is* the
sham and must be scored as one.

## 5. Pre-registered success conditions

Frozen before implementation. All are assertions.

- **S1** Clean case → ALLOW; blind-verifier case → BLOCK; derived-contaminated
  case → BLOCK, with the claim's own `BatteryVerdict` byte-identical across all
  three. If the claim's numbers must move to make a case fire, the premise is
  not demonstrated here.
- **S2 (load-bearing)** At least one case where `naive_decide` → ALLOW and
  `decide` → BLOCK, the block resting on a recomputed digest and not on any
  declared field. Without S2 the initiative is dead regardless of every other
  result.
- **S2′** The mirror: at least one case where `naive_decide` → BLOCK and
  `decide` → ALLOW (a report declared dirty out of caution whose artifacts are
  clean). Guards against a gate that is merely stricter.
- **S3** Every BLOCK reason independently reproduces its own BLOCK under
  `recheck(..., only=code)` — a reason string that cannot re-derive its verdict
  is a caption.
- **S4** `(verdict == "BLOCK") == bool(reasons)` holds for every input,
  including malformed, `None`, and garbage.
- **S5** Unknown / missing / unrecognised integrity blocks. Explicitly sweep
  `None`, `""`, `"CALIBRATED "`, `"calibrated"`, an unrelated object. Default-open
  is the single most likely real bug and three cases cannot see it.
- **S6** Not everything is blocked: at least one case that looks alarming
  (undeclared provenance fields, a detector with a stated floor, no formal or
  enclosure-carrying support) is nevertheless ALLOWED, with its blind spots
  printed.
- **S7** A claim-side failure (a claim shared with a rival, clean verifier)
  blocks with a reason code disjoint from every verifier-side code.
- **S8** Identity binding: a well-formed report presented for a different claim
  blocks; evidence mutated after the report was written blocks.
- **S9** Every decision carries the audit's declared blind spots.

## 6. Pre-registered kill conditions

The initiative is **unearned** if any of these holds. These are not to be
edited after seeing results; if one fires, it is reported as fired.

- **K1** No case exists where the real gate BLOCKs and `NaiveGate` ALLOWs.
  (Negation of S2.) The gate is then a boolean flag with extra steps.
- **K2** Every block the gate produces is already produced by
  `ontology.schema.candidate_reasons`, `dossier.status.support_reasons`, or
  `harness.integrity.audit_department`. The gate then restates existing status.
- **K3** More than 60% of the case set blocks, or the anti-paranoia case (S6)
  blocks. A referee that only says no is the failure `ReferenceClaim` exists to
  catch.
- **K4** The clean case cannot be made to pass without weakening a check.
- **K5** Any single self-declared field is sufficient to flip clean→BLOCK or
  contaminated→ALLOW in the **real** gate. The producer then sets its own
  integrity.
- **K6** A three-line prose checklist, applied by a human, catches every case
  the gate catches. `ROADMAP.md` (2026-08-09) already recorded one benchmark in
  which typed machinery did **not** beat governance prose; that precedent makes
  this condition mandatory, not optional.
- **K7** Making the contaminated and blind cases green requires perturbing the
  claim's numbers.
- **K8** The gate sits on no path anyone must traverse — not in
  `register_department`, not in the funnel, not in CI — and is therefore
  decoration.
- **K9** Total genuinely-new logic exceeds ~300 lines while the enforcement
  delta over `harness/integrity.py` remains a single conditional. The pitch must
  be priced honestly.
- **K10** Contamination is detected only because a fixture annotated it as
  contaminated. Re-run with the annotation removed; if the block disappears, the
  gate detected the label.
- **K11** The gate's verdict is a scalar, or is collapsed to a boolean anywhere
  in the tree (`Support.__bool__` precedent).
- **K12** No held-out artifact: every case was authored by the process that
  authored the gate. `docs/20` §4 pins co-designed calibration as caught by
  **nothing**, so co-authorship is a fail, not a caveat.

## 7. Pre-registered predictions, recorded to be scored

An independent referee, before implementation, predicted **1 of 3 cases
informative**:

1. **Clean → theatre.** The specimen the gate was written against; at ceiling.
2. **Contaminated → theatre.** "The gate will detect the annotation, not the
   contamination" (K10).
3. **Blind → genuinely informative.** Blindness is the one axis mechanically
   re-derivable with no declaration involved.

Prediction 2 is exactly what `harness/preregistration.py` is built to falsify.
It is recorded here so that beating it counts and failing to beat it is not
quietly dropped.

A second prediction, from `docs/20` §6.4, stands **against** this work: *"A
lying provenance record defeats the audit; another referee layer would not
change that, only move it."* The honest claim available to us is narrower than
a refutation: derivation moves the lie from "flip a boolean, free" to "forge a
digest that a third party recomputes". Moving a trust boundary is not removing
it, and any write-up that blurs those is overclaiming.

## 8. Known blind spots, declared in advance

- Digests are supplied by the producer. Derivation raises the cost of lying; it
  does not make lying impossible. There is no attestation here and none is
  claimed.
- Blindness is measured only against lesions somebody imagined. Unimagined
  failure modes still grade well (`docs/20` §4's two pinned-blind rows).
- Semantic scope containment is undecidable. Only interval scope is compared;
  anything else must be refused rather than guessed.
- Staleness detects change, not relevance. A comment edit and a load-bearing
  edit are the same digest change, and the false-BLOCK rate is unmeasured.
- The gate adjudicates process, never content. A clean, calibrated, fresh,
  in-scope report on a trivial claim is ALLOWED. Nothing here distinguishes
  sound from interesting, and nothing here is evidence for anything
  (`docs/08`).

## 9. The prose rival, frozen before any result

K6 kills this work if a human checklist catches everything the gate catches.
That comparison is only fair if the checklist is written before anyone knows
which cases the gate wins, so it is frozen here, in the same commit as the
criteria, and it is written to be **as strong as I can make it** — a rival
built to lose is the sham this repository already refuses (`docs/09` gate #3).

> **The reviewer's checklist.** For each promoted claim, ask:
> 1. Is the outcome distinguishing, and does the battery's integrity grade say
>    `CALIBRATED`?
> 2. Were the pass criteria — thresholds, windows, the lesion roster, the rival
>    roster — fixed before the runs they judge, and can you see where that was
>    recorded?
> 3. Is the evidence this report was computed on still the evidence in the tree?

A careful reviewer applying those three questions catches the contaminated case
and the blind case. The claim under test is **not** that the checklist is
wrong. It is that questions 2 and 3 ask a human to compare present state
against remembered prior state, and that a person who was not present when the
criteria were frozen cannot answer them from the artifact in front of them.

The measurable form of that claim, and the only one that counts:

- **P1** Run the case set past a reviewer who has the checklist and the same
  artifacts the gate gets, and who did not author the cases. Record which cases
  they catch.
- **P2** The gate earns something over prose only on cases the checklist-holder
  misses *while holding the artifacts*. If they catch everything, K6 fires.
- **P3** A case where the reviewer must answer "I cannot tell from here" is the
  interesting cell — it is where the mechanism supplies information rather than
  discipline.

Recorded prediction: the reviewer catches the case with a false declaration
(question 2 invites suspicion of a self-report) and **misses** the
dropped-lesion case, because nothing visible in the artifact says a lesion was
ever there. If that prediction is wrong in the direction of the reviewer
catching more, K6 fires and this work is unearned.

## 10. Results

Everything below was produced after §1–§9 were committed (`bf8f6dc`, `c08296d`),
and neither the criteria nor the prose rival were edited afterwards. Where a
condition failed, it is recorded as failed.

### 10.1 The case table

All four cases hold the claim's own `BatteryVerdict` byte-identical; only the
verifier's artifacts vary. Measured by `tests/test_harness_promotion.py`:

| case | claim status | audit grade | `dangerous` | NaiveGate | gate |
|---|---|---|---|---|---|
| clean control | distinguishes | CALIBRATED | False | ALLOW | **ALLOW** |
| constant-True detector | distinguishes | DETECTOR_INADEQUATE | True | BLOCK | **BLOCK** |
| declared clean, artifacts contradict | distinguishes | CALIBRATED | False | **ALLOW** | **BLOCK** |
| dropped hardest lesion | distinguishes | **CALIBRATED** | **False** | **ALLOW** | **BLOCK** |

**S2 holds, twice.** The last two rows are divergences: the naive gate allows,
the real gate blocks, and both blocks rest on a recomputed digest. The block
survives replacing the provenance record with a maximally flattering one — no
declared field participates. That is the one property separating this gate from
the sham, and it is the only reason the work continued.

The dropped-lesion row is the stronger of the two, because nothing in it is
lying: the audit is honest, the declarations are true, and the audit is simply
structurally unable to know what was removed. The frozen roster
`['large','medium','small']` no longer matches the applied `['large','medium']`.
The audit's own pin (`test_the_audit_is_blind_to_a_silently_dropped_hardest_lesion`)
still passes unchanged, as it should — **the audit is not fixed**. A record from
before supplies a prior state one audit of one battery at one moment cannot have.

### 10.2 Conditions that failed

- **S2′ FAILED, and is pinned as an xfail.** No case exists where the naive gate
  blocks and the real gate allows. Any declared contamination makes
  `audit_department` grade the battery `CONTAMINATED`, and the gate blocks on the
  grade, so both gates block together. The mirror is unreachable with one
  consistent record. **On every case we can construct, this gate is only ever
  stricter-or-equal to the naive one.** That is weaker than §5 asked for.
- **The blind-verifier case is not a divergence.** `detector-specificity` already
  catches a constant-True detector, so the shipped layer had this axis and the
  gate adds nothing to it. This contradicts §7's prediction that blindness would
  be the one informative case. Recorded as a wrong prediction, not reframed.
- **A default-open bug was found in this gate, in review.** `_check_independence`
  coerced party identifiers with `str()`, so `None`, `0`, `[]` and `object()` all
  read as two distinct non-empty parties and the check returned `PASS`. Found by
  the test agent, not the author; fixed; kept as a regression pin. The failure
  mode this document is about occurred inside the artifact arguing against it,
  and survived the smoke run because `Boundary.promote()` guards the happy path.

### 10.2b Conditions that held, with their numbers

- **S6 holds, thinly.** Blocked fraction **7 of 13 = 53.8%**, against a 60%
  ceiling. The margin depends on the case table mixing ordinary submissions with
  the pre-registered attacks; that is stated in the test docstring rather than
  tuned quietly. Allowed: clean, unrelated-evidence-visible-at-freeze,
  scope-requoted, declared-dependence, no-provenance-record, alarming-but-fine.
- **K5 fires only in the harmless direction.** Swept over all six tri-state
  provenance fields × {True, False, None}: **no self-declaration can buy an
  ALLOW**. A declaration *can* cost a producer one, via the grade. Both pinned.
- **S3, S4, S5, S7, S8, S9 hold.** Every reason independently reproduces its own
  BLOCK under `recheck`; the BLOCK⇔reasons invariant holds on garbage input
  including `None`, `0`, `object()` and NaN; the grade sweep blocks `None`, `""`,
  `"CALIBRATED "`, `"calibrated"`, `"GOOD"` and every non-CALIBRATED grade.
- Suites: `tests/test_harness_promotion.py` **214 passed, 1 xfailed** in 0.22 s;
  the full harness set (protocol, integrity, conformance, promotion, demo, and
  the referee/stateval/croniter/finitefield departments) **452 passed,
  1 xfailed** in 124 s. Fast tier before this work: 1897 passed.

### 10.3 The prose rival (§9), scored

Three reviewers, each shown one report in isolation, each holding the frozen
checklist and the same artifacts the gate gets. A first batched run was
discarded: it gave the clean report no criteria record while the contaminated one
had one (a two-variable contrast), and showing all reports together let a
reviewer compare rosters. Both were design defects of mine.

| report | human | gate |
|---|---|---|
| clean, criteria record legible | CANNOT TELL (Q3) | ALLOW |
| dropped lesion, roster legible in the record | **BLOCK**, high confidence | BLOCK |
| dropped lesion, record carries only a digest | CANNOT TELL (Q2) | **BLOCK** |

**K6 does not fire, but the honest claim is much narrower than "the gate beats
prose".** When the frozen criteria are human-legible, a careful reviewer catches
the dropped lesion by eye, names it correctly, and is right. The gate wins one
cell: where the criteria are a digest rather than an enumeration, the reviewer
cannot decide and the gate can. The contribution is therefore

> **decidability from a compact artifact**, not detection of something a human
> could never see.

The reviewers also found two things the gate does not check at all: the criteria
freeze the rosters but not the *detector*, so a detector swapped after seeing
results leaves no trace; and one reviewer noticed the roster magnitudes differed
from the in-tree specimen's, inferring a lesion that may have been dropped
*before* the criteria were frozen — which this mechanism cannot catch by
construction, since the digest would be frozen around the already-weakened set.

### 10.4 The held-out sham, and the gate's inherited blindness

`docs/20` §8 names as its second most damaging experiment: *"have an independent
party author a hollow battery trying to pass the audit, without seeing
`SHAM_MODES`."* That experiment was run. An agent given only `protocol.py` and
`harness/README.md`, and forbidden the integrity source and its catalog, built a
battery graded **`CALIBRATED` on the first attempt, with zero adaptation
iterations**, passing all 19 conformance tests. Three findings:

1. **Strawman rivals** — nothing requires a rival to be *near* the target, so
   `anything AND target_only_property` distinguishes. An explicitly astrological
   claim renders as `distinguishes` under a `CALIBRATED` banner.
2. **The detector is the claim, negated** — identical on 29/29 payloads;
   `detector-power` and `detector-specificity` both pass while the detector
   carries no information independent of the claim.
3. **`UNKNOWN` does not block `CALIBRATED`** — using callables rather than
   mappings makes `payload-symmetry` return `UNKNOWN`, which the top grade
   tolerates. Default-open, in the audit.

Neither (1) nor (2) is in `SHAM_MODES`. Per §8's own scoring rule — *"every mode
they find that the catalog lacks is a real hole"* — these are holes.

**And the consequence for this work is the worst result in this document:**

> The gate **ALLOWs** the hollow battery's astrological claim, with an empty
> reason list.

`decide` requires the grade to be `CALIBRATED`; it cannot re-derive whether that
grade was earned. Pinned as `test_the_gate_promotes_a_worthless_claim_from_a_hollow_battery`.
Forward-deployed verification does **not** make a hollow referee safe. It makes
an *unrecorded change* to a referee visible. Only the second is claimed.

## 11. Verdict

**KEEP AS PROBE.**

Not KILL: S2 holds twice, on divergences that rest on recomputed digests and
survive a maximally flattering declaration, and one of them beats not just the
naive gate but the shipped audit. `docs/20` §4's "*if declared*" qualifier on the
W2 shape is now narrower than it was, and `dropped-hardest-lesion`'s
countermeasure moved from a convention ("pin the lesion set in tests") to a
mechanism (a digest that moves). That is real and it is small.

Not EARNED NEXT EXPERIMENT: S2′ failed, the blind axis added nothing, the gate
inherits every blind spot of the audit beneath it — demonstrably, on a held-out
sham — and against a legible criteria record a human reviewer performs as well.
The enforcement delta remains close to one conditional, honestly priced.

`docs/20` §6.4 predicted: *"A lying provenance record defeats the audit; another
referee layer would not change that, only move it."* That prediction stands. The
lie now has to be a false digest instead of a false boolean, and a false digest
is checkable by anyone holding the artifacts — the boundary moved, and moving it
was the whole contribution. It did not disappear, and this document should not be
cited as though it had.

The next experiment worth running is not a bigger gate. It is the one the held-out
sham exposed: **`SHAM_MODES` is missing at least two modes, and a `CALIBRATED`
grade can be obtained on the first attempt by an outsider.** Until a rival's
*nearness* to its target is something the audit measures rather than assumes,
every layer built on top of that grade — this one included — inherits a referee
that an afternoon's work can hollow out.
