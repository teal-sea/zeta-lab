# 23 — Rival distance and detector independence: closing two declared blind spots

**Status of this file when it was committed: pre-registration only. Nothing in
§§5–8 existed. No number below §4 had been measured.**

`docs/21` earned whatever weight it has by committing its criteria before its
implementation (`bf8f6dc`, `c08296d`). This document follows that pattern
exactly, for the same reason: the checks proposed here have a threshold in
them, and a threshold chosen after seeing the calibration set has no
falsification weight. ROADMAP records why — the ninth moment increment was
withdrawn because its gates were "chosen after seeing those values".

---

## 1. The two holes, in the audit's own words

`harness/integrity.py` ships a catalog of twelve `SHAM_MODES`. Ten name a
mechanical check that catches them. Four carry `caught_by=None`; two of those
four were added on 2026-08-09 after an independent party, given only
`harness/protocol.py` and `harness/README.md`, reached `CALIBRATED` **on the
first attempt with zero adaptation iterations**:

> **`distant-rivals`** — rivals that do not share the structure the claim leans
> on: they differ from the target in gross, arbitrary ways, so the modus
> tollens never bites and any claim of the form "anything AND a target-only
> property" distinguishes.

> **`detector-is-the-claim`** — the detector whose power is measured is the
> claim under test, negated: power and specificity both pass while the
> detector carries no information the claim did not already assert, because
> the lesion family was chosen to be exactly what it looks for.

ROADMAP's summary of that incident is the thesis this document attacks:

> The audit's real constraining power is over *mechanical* emptiness. It has no
> purchase on the two choices that decide whether a battery can reject
> anything: how near the rivals are, and whether the detector is independent of
> the claim. Both are the author's to pick.

Each mode's `countermeasure` field currently names a human procedure. For
`detector-is-the-claim` that field already contains a *mechanical* instruction
nobody implemented: "compare the detector and the claim on the same payloads
and treat agreement everywhere as a finding, not a comfort."

There is also a third thing, which is not a blind spot but a defect.

## 2. The defect: `UNKNOWN` walks past the top grade

`IntegrityReport.grade` (`harness/integrity.py:378`) inspects `_HOLLOW_CHECKS`
members only for `status == FAIL`. `UNKNOWN` caps the grade for exactly two
checks, `detector-power` and `detector-specificity` (line 390). `payload-symmetry`
is a `_HOLLOW_CHECKS` member (line 152) that returns `UNKNOWN` whenever the
target payload is not a `Mapping` — so, as ROADMAP records, it "is sidestepped
for free by using callable payloads" and the battery still reaches `CALIBRATED`.

This contradicts the repository's own safe-failure rule one floor down, where
`proven_sign` returns `0` for "not decided" and `certified` is `False` whenever
`uncertified_steps` is non-empty. Undecided is not passed there and should not
be passed here.

## 3. What is *not* being claimed

Neither check below is a nearness certificate or an independence certificate.

- **B measures structural distance only.** A rival that is structurally
  identical to the target and semantically absurd — noise where the target is
  signal — scores zero and passes. What B catches is *gross* distance, which is
  what the recorded incident used.
- **A cannot run when a department's claims and detectors consume different
  payload shapes**, which `harness/protocol.py` explicitly permits
  (`run_ablation`'s docstring: "forcing a single payload type across all four
  would make the protocol tidier and the departments dishonest"). When the
  shapes are disjoint the check reports `UNKNOWN`, never `PASS`. Partial
  consolation, stated rather than relied on: shape-disjointness makes the mode
  itself harder to instantiate, since a detector that consumes a different
  shape cannot literally *be* the claim. The author still picks the shapes, so
  this is a mitigation and not a closure, and it is registered below as a new
  mode with `caught_by=None`.
- **Neither check touches the two remaining blind spots**
  (`value-encoded-label-leak`, `co-designed-calibration`, `dropped-hardest-lesion`),
  whose countermeasure remains independent authorship, attested and not
  mechanically verifiable.

---

## 4. The frozen specification

### 4.1 Check A — `detector-claim-agreement`

**Payload set.** Assembled from the department's own instruments, in this
order: the target payload; each rival payload; each declared lesion applied to
its detector's clean probe; each decoy substituted on the target payload; one
sample from each surrogate.

**Vectors.** For each declared detector `d` and each declared reference claim
`c`, evaluate both over the payload set. An entry where the callable raises is
recorded as *missing*, never as `False`.

**Comparison.** Let `I` be the payloads on which both `d` and `c` answered.

- `|I| < 2` for every pair → the check is `UNKNOWN`.
- A pair whose detector vector restricted to `I` is *constant* is skipped: a
  constant detector carries no information regardless, and `detector-specificity`
  and `detector-power` already own that case.
- A pair is **flagged** when the two vectors on `I` are identical, or exactly
  complementary. Exact complement counts because the mode's own name is "the
  claim under test, **negated**".

**Verdict.** `FAIL` if any pair is flagged; `PASS` otherwise, with the evidence
reporting the extremal agreement rate and `|I|`. A `FAIL` grades the department
`DETECTOR_INADEQUATE` — the detector's alarms carry no information the claim did
not already assert.

**`UNKNOWN` does not cap the grade for this check**, because shape-disjointness
is a legitimate department design and not an evasion the department chose. That
asymmetry with §4.3 is deliberate and is the weakest joint in this build.

### 4.2 Check B — `rival-separator-abundance`

**The idea.** Nearness is not mechanically decidable; its observable
consequence is. If a rival genuinely shares the structure the claim leans on,
then an *arbitrary* structural predicate should rarely separate it from the
target — only the claim's own property should. If nearly every arbitrary
predicate separates them, the rival is far, and "anything AND a target-only
property" distinguishes.

**The predicate family.** Generated deterministically from the payloads
themselves (target and rivals), domain-blind throughout, in this order:

1. type-name probes, one per distinct `type(p).__name__` observed;
2. shape probes: `p is None`, `bool(p)`, `callable(p)`, `isinstance(p, Mapping)`,
   `isinstance(p, str)`, `hasattr(p, "__len__")`, numeric-and-not-bool;
3. length probes, `len(p) == L` and `len(p) > L`, one pair per distinct observed
   length;
4. membership probes `k in p`, one per distinct key observed across mapping
   payloads;
5. per-key value probes, for each observed key: the type-name, `callable`,
   truthiness and observed-length probes of §1–3 applied to `p[k]`;
6. positional probes for non-string sized payloads: the same, applied to `p[i]`
   for `i` below the shortest observed length.

Capped at 512 predicates in that deterministic order; the count that actually
ran is reported in the evidence.

**The statistic.** For each rival `R`,

```
separator_fraction(R) = |{ f : bool(f(T)) != bool(f(R)) }| / |{ f : f ran on both }|
```

and the department's statistic is `min` over rivals — the *nearest* rival.
One near rival is enough for the modus tollens to bite; extra distant rivals are
not a defect.

**Verdict.** `FAIL` when the nearest rival's fraction exceeds **θ = 0.5**;
`UNKNOWN` when fewer than 8 predicates ran on any pair; `PASS` otherwise. The
fraction is reported in the evidence whatever the verdict. A `FAIL` is a
`_HOLLOW_CHECKS` member: a battery whose nearest rival is far cannot refute
anything.

**θ = 0.5 is frozen here and will not be retuned after the calibration is
read.** If the calibration shows 0.5 sits in the wrong place, that is reported
as a limitation of this pre-registration, and any retune ships as a separate,
later-dated change carrying its own numbers.

### 4.3 Fix C — `UNKNOWN` caps the grade

Any `_HOLLOW_CHECKS` member whose status is `UNKNOWN` caps the grade at
`UNMEASURED`, exactly as `detector-power` and `detector-specificity` already do.

### 4.4 New sham modes and their planted mutations

`harness/shams.py` gains two mutators, so the new checks' power is measured
against planted corruptions rather than asserted:

- `with_distant_rivals` — keeps every rival's payload key set identical (so
  `payload-symmetry` still passes) and replaces the values with structurally
  alien objects. Every existing check must still pass; only B may fail.
- `with_detector_as_claim` — replaces the declared detectors with one whose
  `fires` is the department's distinguishing reference claim, negated, guarded
  so a shape mismatch answers rather than raises. Every existing check must
  still pass, including `detector-power` and `detector-specificity`; only A may
  fail.

`SHAM_MODES` additionally gains `detector-claim-shapes-disjoint`, with
`caught_by=None`: the residue A leaves behind, named rather than hidden.

---

## 5. The held-out set

Ten batteries were authored by ten independent parties on 2026-08-09, **before
any line of §4 was implemented**, so their blindness to these checks is
guaranteed by chronology rather than by promise. Each party was given a sealed
kit — `harness/protocol.py`, `harness/provenance.py`, `harness/README.md`, and a
runner printing only the integrity grade and the pass/fail/unknown status of
each named check — and was instructed not to read `harness/integrity.py`,
`harness/shams.py`, any existing department, `docs/20`–`docs/22`, `ROADMAP.md`
or any test. Compliance with that instruction is **declared, not verified**, and
that is a real limitation: it weakens the baseline hollowing rate in §6, but it
does not touch the held-out property, which chronology guarantees.

- **Six hollow parties** were told to reach `CALIBRATED` with a battery that
  measures nothing, and to demonstrate hollowness operationally: after the
  department passes, a transparently absurd claim about its own subject must
  come back `distinguishes=True`.
- **Four honest parties** were told to author genuine departments in toy
  domains, taking every word of the contract seriously, and to demonstrate that
  their battery *kills* the absurd claim.

The honest four exist because the calibration set for B would otherwise be six
real departments in one repository's house style, and a threshold that only
separates "this tree's departments" from "toy shams" would be measuring
authorship, not distance.

## 6. Frozen predictions

Recorded before measurement. Each is scored in §8 as HELD or FAILED, and a
FAILED prediction is reported as failed rather than reframed.

- **P1 — specificity of B.** All six registered departments score a nearest-rival
  separator fraction ≤ 0.5 and pass `rival-separator-abundance`.
- **P2 — power of B.** The referee specimen mutated by `with_distant_rivals`
  fails `rival-separator-abundance`, and no other planted sham mode's grade
  changes as a result of adding B.
- **P3 — specificity of A.** No registered department fails
  `detector-claim-agreement`.
- **P4 — power of A.** The referee specimen mutated by `with_detector_as_claim`
  fails `detector-claim-agreement`, while every check it passed before still
  passes.
- **P5 — cost of the cap.** Fix C re-grades **at most one** of the six
  registered departments away from `CALIBRATED`.
- **P6 — the held-out test.** Every hollow blind-authored battery that reached
  `CALIBRATED` under the pre-existing audit is caught by at least one of
  {A, B, C}; no honest blind-authored battery that reached `CALIBRATED` is
  newly rejected.

P6 is the prediction most likely to fail, and its failure is the most valuable
outcome available here: every hollow battery that survives all three checks is a
sham mode the catalog does not have, and it goes into `SHAM_MODES` with
`caught_by=None` rather than being quietly repaired.

## 7. Decision rules, frozen in advance

- **If P1 fails for a department**, the check is not weakened and the
  department is not exempted. The specific predicates that separated are read,
  and the result is recorded either as a finding about that department's rivals
  or as a finding about the predicate family — whichever the predicates show.
- **If P5 fails**, the fix is to make the undecided check *decidable* on the
  affected department's payload shape. Exempting the department, or weakening
  the cap, are both excluded.
- **If P3 or P4 fails**, check A ships anyway if and only if it is strictly
  better than nothing on the held-out set; otherwise it is withdrawn and the
  blind spot stays open with the attempt recorded.
- **θ is not retuned.** See §4.2.
- **No blind-authored battery is edited** after §4 is implemented, for any
  reason, including to make it pass or fail.

## 8. Results

*Empty at commit time. Filled in after §4 was implemented and run.*
