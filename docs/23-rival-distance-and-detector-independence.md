# 23. Rival distance and detector independence: closing two declared blind spots

**Status of this file when it was committed: pre-registration only. Nothing in
§§5–8 existed. No number below §4 had been measured.**

`docs/21` earned whatever weight it has by committing its criteria before its
implementation (`bf8f6dc`, `c08296d`). This document follows that pattern
exactly, for the same reason: the checks proposed here have a threshold in
them, and a threshold chosen after seeing the calibration set has no
falsification weight. ROADMAP records why, the ninth moment increment was
withdrawn because its gates were "chosen after seeing those values".

---

## 1. The two holes, in the audit's own words

`harness/integrity.py` ships a catalog of twelve `SHAM_MODES`. Ten name a
mechanical check that catches them. Four carry `caught_by=None`; two of those
four were added on 2026-08-09 after an independent party, given only
`harness/protocol.py` and `harness/README.md`, reached `CALIBRATED` **on the
first attempt with zero adaptation iterations**:

> **`distant-rivals`**, rivals that do not share the structure the claim leans
> on: they differ from the target in gross, arbitrary ways, so the modus
> tollens never bites and any claim of the form "anything AND a target-only
> property" distinguishes.

> **`detector-is-the-claim`**, the detector whose power is measured is the
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
target payload is not a `Mapping`, so, as ROADMAP records, it "is sidestepped
for free by using callable payloads" and the battery still reaches `CALIBRATED`.

This contradicts the repository's own safe-failure rule one floor down, where
`proven_sign` returns `0` for "not decided" and `certified` is `False` whenever
`uncertified_steps` is non-empty. Undecided is not passed there and should not
be passed here.

## 3. What is *not* being claimed

Neither check below is a nearness certificate or an independence certificate.

- **B measures structural distance only.** A rival that is structurally
  identical to the target and semantically absurd, noise where the target is
  signal, scores zero and passes. What B catches is *gross* distance, which is
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

### 4.1 Check A: `detector-claim-agreement`

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
`DETECTOR_INADEQUATE`: the detector's alarms carry no information the claim did
not already assert.

**`UNKNOWN` does not cap the grade for this check**, because shape-disjointness
is a legitimate department design and not an evasion the department chose. That
asymmetry with §4.3 is deliberate and is the weakest joint in this build.

### 4.2 Check B: `rival-separator-abundance`

**The idea.** Nearness is not mechanically decidable; its observable
consequence is. If a rival genuinely shares the structure the claim leans on,
then an *arbitrary* structural predicate should rarely separate it from the
target, only the claim's own property should. If nearly every arbitrary
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

and the department's statistic is `min` over rivals, the *nearest* rival.
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

### 4.3 Fix C: `UNKNOWN` caps the grade

Any `_HOLLOW_CHECKS` member whose status is `UNKNOWN` caps the grade at
`UNMEASURED`, exactly as `detector-power` and `detector-specificity` already do.

### 4.4 New sham modes and their planted mutations

`harness/shams.py` gains two mutators, so the new checks' power is measured
against planted corruptions rather than asserted:

- `with_distant_rivals`: keeps every rival's payload key set identical (so
  `payload-symmetry` still passes) and replaces the values with structurally
  alien objects. Every existing check must still pass; only B may fail.
- `with_detector_as_claim`: replaces the declared detectors with one whose
  `fires` is the department's distinguishing reference claim, negated, guarded
  so a shape mismatch answers rather than raises. Every existing check must
  still pass, including `detector-power` and `detector-specificity`; only A may
  fail.

`SHAM_MODES` additionally gains `detector-claim-shapes-disjoint`, with
`caught_by=None`: the residue A leaves behind, named rather than hidden.

---

## 5. The held-out set

> **Corrected after the fact, see §8.0.** The claim in this section that
> blindness is "guaranteed by chronology" is **false as written**. The parties
> ran against the live working tree, and §4 landed in it while they were still
> iterating, so most of them saw the new checks. The per-party accounting is in
> §8.0. The contamination runs against the parties rather than for them, so
> §8.2's headline is unaffected, but check B ends up with no clean blind test
> and check A with one. This paragraph is left standing rather than edited,
> because a pre-registration quietly corrected after its results are known is
> not a pre-registration.

Ten batteries were authored by ten independent parties on 2026-08-09, **before
any line of §4 was implemented**, so their blindness to these checks is
guaranteed by chronology rather than by promise. Each party was given a sealed
kit, `harness/protocol.py`, `harness/provenance.py`, `harness/README.md`, and a
runner printing only the integrity grade and the pass/fail/unknown status of
each named check, and was instructed not to read `harness/integrity.py`,
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

- **P1, specificity of B.** All six registered departments score a nearest-rival
  separator fraction ≤ 0.5 and pass `rival-separator-abundance`.
- **P2, power of B.** The referee specimen mutated by `with_distant_rivals`
  fails `rival-separator-abundance`, and no other planted sham mode's grade
  changes as a result of adding B.
- **P3, specificity of A.** No registered department fails
  `detector-claim-agreement`.
- **P4, power of A.** The referee specimen mutated by `with_detector_as_claim`
  fails `detector-claim-agreement`, while every check it passed before still
  passes.
- **P5, cost of the cap.** Fix C re-grades **at most one** of the six
  registered departments away from `CALIBRATED`.
- **P6, the held-out test.** Every hollow blind-authored battery that reached
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
  or as a finding about the predicate family, whichever the predicates show.
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

Everything below was produced after §§1–7 were committed (`e7d52b6`). Where a
prediction failed it is recorded as failed.

### 8.0 A method failure in this experiment, stated first

**§5's claim that the held-out set's blindness is "guaranteed by chronology"
is false as written, and the error is mine.** The ten parties iterated against
a runner that imports the *live* harness, and the implementation of §4 landed
in that same tree while they were still working. Reconstructed from the check
counts each party recorded in its own notes (the audit had 16 named checks
before this build, 17 after B, 18 after A, 19 after the check added in §8.6):

| party | checks it saw | blind to |
|---|---|---|
| party02 | 17 | **A**, and the §8.6 check |
| party01, 03, 04, 05, 06 | 18 | the §8.6 check only |
| party08 | 18 | the §8.6 check only |
| party07, party10 | 19 | nothing |
| party09 | (no notes) | unknown |

The contamination runs *against* the parties, not for them: every one of them
faced an audit at least as strict as the baseline, and five of the six hollow
parties reached `CALIBRATED` **while looking at the checks built to stop
them**. So the headline in §8.2 is if anything understated. What is genuinely
damaged is narrower and is not glossed:

- **Check B has no clean blind test at all.** Every hollow party saw it.
- **Check A has exactly one** (party02), and it caught it. A second clean blind
  test arrived from outside this experiment, see §8.5.
- The §8.6 check has one blind subject, party06, but was *derived* from
  party06, so that is not an independent test either and the catalog entry
  says so.

The fix for anyone repeating this: run the authoring against a pinned copy of
the harness, not the working tree.

### 8.1 The predictions, scored

| | prediction | verdict |
|---|---|---|
| **P1** | all six departments pass `rival-separator-abundance` | **HELD** |
| **P2** | the `with_distant_rivals` plant fails it | **FAILED** |
| **P3** | no registered department fails `detector-claim-agreement` | **FAILED** |
| **P4** | the `with_detector_as_claim` plant fails it, passing everything else | **HELD** |
| **P5** | the cap re-grades at most one department | **FAILED**, then repaired by §7's rule |
| **P6** | every successful hollow battery is caught; no honest one newly rejected | **FAILED** on the first half, held on the second |

### 8.2 The headline: the audit does not constrain an adversarial author

Six independent parties, given only `harness/protocol.py`,
`harness/provenance.py` and `harness/README.md`, were asked to reach
`CALIBRATED` with a battery that measures nothing. **Six of six succeeded**,
every one of them certifying a transparently absurd claim as `distinguishes`,
a waxing moon over a weather station, Mercury retrograde over a shipping
manifest, a lunar phase over a chord progression. The prior estimate of this
rate came from a single party in `docs/20` §8; at n=6 it is unchanged at 100%,
and five of the six did it while watching the new checks fire.

Of the six, the audit as it now stands catches **two**: party02 by
`detector-claim-agreement`, party06 by the check in §8.6. Four survive.

### 8.3 The four survivors are one mode, and it is not mechanically reachable

Independent analysts named the four surviving mechanisms
`coordinatewise-disjoint-rivals`, `schema-matched-unrelated-rivals`,
`unmatched-covariate-separation` and `sibling-rivals`. They are one thing:
**rivals matched in structure and disjoint in value**. Same keys, same types,
same shape, agreeing with the target on no substantive number, so no single
field is the tell, the joint value vector is the label, and any predicate
keyed to a target value is target-exclusive by construction. It is now in the
catalog as `structure-matched-value-disjoint-rivals` with `caught_by=None`.

The obvious fix was tried and **inverts**, which is why the entry is blind
rather than open. Measured on this tree: a value-comparison family scores the
laboratory's own honest departments *more* separated than the sham
(`zeta`, `compiler`, `croniter` and `referee` all at 1.00 leaf-separation
against the weather-station sham's 0.83), because ζ and Davenport–Heilbronn
also agree on no numeric value. A good rival differs from its target in its
numbers too. *Which* differences are load-bearing is exactly the domain
knowledge the seam forbids the audit to have, so "rivals must agree with the
target on most values" is not a weaker version of the right principle, it is
false.

### 8.4 Check B: the number is right, the threshold is not, and the dimension is wrong

`rival-separator-abundance` ships and acts on nothing.

| | nearest-rival separator fraction |
|---|---|
| `finitefield`, `compiler`, `croniter`, `referee`, `stateval` | 0.00 |
| `zeta` | 0.04 |
| `with_distant_rivals` planted on the referee specimen | 0.24 |
| `with_distant_rivals` planted on the six real departments | 0.31 – 0.50 |

The statistic separates cleanly; **θ = 0.5 sits above the entire measured
range**, so P2 failed everywhere and not only on the toy specimen. Anything in
0.05 < θ < 0.24 would separate with margin on both sides. Per §4.2 the
threshold is *not* retuned here, a cut chosen after reading its own
calibration has no falsification weight, and this experiment's held-out set is
now spent, so a retune would have nothing to be evaluated against. It ships as
a reported number and a pinned blind spot
(`test_the_audit_is_blind_to_gross_rival_distance_at_the_frozen_threshold`),
and `distant-rivals` keeps `caught_by=None` because a catalog that claimed the
catch would be lying.

The deeper result is §8.3's: even at a correct threshold this check would have
caught none of the four survivors, because it measures structural distance and
the mode lives in values. §3 declared that limitation before the measurement,
which is the one thing that makes the negative result readable.

### 8.5 Check A: three catches, two of them clean, and a false positive it cannot see through

`detector-claim-agreement` ships. Its evidence:

1. **The planted mutation.** `shams.with_detector_as_claim` passes every
   pre-existing check, including `detector-power` and `detector-specificity`,
   and this check is the only thing that fails it.
2. **party02**, a blind-authored hollow battery that reached `CALIBRATED`, and
   the one hollow party that never saw this check. Nothing else catches it.
3. **`docs/21`'s hollow battery**: and this is the significant one. `docs/21`
   §10 recorded, as its worst result, that the promotion gate promotes that
   battery's astrological claim with an empty reason list. Its declared
   detector is `lambda f: not zero_mean(f)`: the reference claim, negated. The
   check catches it, so that specific promotion no longer happens.

   Precisely what this is worth, since the distinction matters: that specimen
   is a *reconstruction*, authored by this repository's own process on
   2026-08-09 from a held-out party's battery, not the party's own file. So
   the chronology is clean (it predates this check by a day and nobody had
   this check in mind when writing it) but the authorship is not independent.
   It is weaker evidence than party02 and stronger than a plant.

`docs/21`'s *general* negative result is untouched and is deliberately kept:
the gate still inherits every blind spot beneath it, and
`test_the_gate_promotes_a_worthless_claim_from_a_hollow_battery` now runs
against a specimen whose detector is genuinely independent and whose
hollowness lives where it always lived, in the rivals. Repairing one instance
was not allowed to make the gate look safe.

**Against it: P3 failed, on `compiler` and `referee`.** Both declare a
detector that is a reference claim negated on every payload both answer, and
in both cases the detector is a *decision procedure*, `compiler`'s is
exhaustive over i8, `referee`'s is the audit itself. The mode has two
conjuncts, "the detector is the claim negated" **and** "the lesion family was
chosen to be exactly what it looks for", and only the first is visible from
this layer. The check cannot tell a decision procedure from a co-designed
detector.

Per §7 the rule was: ship iff strictly better than nothing on the held-out
set. It is (party02, plus `docs/21`'s battery), so it ships as frozen, and the
consequence is recorded rather than smoothed:

- `compiler` and `referee` now grade `DETECTOR_INADEQUATE`.
- `tests/test_department_conformance.py` xfails those two with the reason, in
  the same idiom as `docs/21` §10.2's S2′.
- `test_the_referee_department_survives_its_own_audit` was renamed to
  `..._does_not_survive_its_own_audit` and asserts the failure, because it is a
  fact about the current tree and not an aspiration. **The referee department
  fails its own audit**, on one named check, for a reason its own module
  docstring anticipated in prose.
- Neither department is exempted and the check is not weakened. Each owes an
  answer: declare why its detector is a decision procedure in a form the audit
  can read, or stake its power on an instrument independent of its claim. That
  declaration is the next pre-registered change, not this one.

### 8.6 What the honest controls found, which was not what they were for

The four honest parties were a calibration set for check B. They produced a
bigger result than that.

Under the audit as it stood, **2 of the 4 honest parties were graded `HOLLOW`**,
the worst grade the audit issues, the one reserved for a battery that could
not kill anything, and both failed on the same checks:
`decoys-move-their-probe` and `lesions-plant-something`. (Mid-run, before any
of them had finished iterating, all four were failing those two checks; the
2-of-4 figure is from the frozen final submissions and is the one that counts.)
The cause is exact.
Those checks poked an instrument with department #1's shapes, a list of ints,
an empty tuple, whenever the instrument declared no `probe` attribute, and
reported "ablates nothing" when it raised on them. **That `probe` attribute is
declared nowhere in `harness/protocol.py` and nowhere in `harness/README.md`**;
it exists only inside `harness/integrity.py`, which the parties were forbidden
to read. Verified directly: every honest party's decoys and lesions move their
*own* department's payload correctly and raise on the foreign probe.

Measured on the frozen submissions: party09's instruments move 0 of 7 foreign
probes and party10's move 3 of 8, while every one of them moves its own
department's payload correctly. The two honest parties that did reach
`CALIBRATED` got there by writing shape-general fallbacks: 7 of 7 and 8 of 8
foreign probes moved, which is the same workaround party02 used to *hollow*
the audit. None of the four declared a `probe` attribute, because none of them
could have known it existed.

So the audit measured totality over foreign shapes, not substance, and it
selected against exactly the authors it existed to select for. Party02 found
the convention by instrumenting its own decoy to log what it was handed. Writing
a domain-faithful instrument was penalised; reverse-engineering the audit was
rewarded, in both arms of the experiment, for and against.

Fixed: an instrument now has to move *one* of several candidate probes, its
declared `probe`, its department's own target payload, or the historical
shape. Inert instruments are still caught (`with_inert_lesions` still fails).
After the fix, **4 of 4 honest parties grade `CALIBRATED`** and none is newly
rejected by anything in §4, which is P6's second half.

This was not predicted, and it is the most actionable defect the exercise
found.

### 8.7 One genuinely new sham mode

party06 reached `CALIBRATED` with a payload class whose `keys()` is honest and
whose `__missing__` is not: ask it for a field nobody declared and it answers
with a truthy sentinel that compares equal to anything, while the rivals
answer nothing. Identity therefore lives on the *complement* of the declared
key set, where `payload-symmetry`, which compares `keys()`, cannot look.

`undeclared-field-symmetry` now probes every payload with names nobody
declared and requires the target and every rival to answer identically, and
refuses any payload whose absent-field answer compares equal to an arbitrary
sentinel. `shams.with_agreeable_absent_fields` plants it so the check's power
is measured. Both the mode and the check are new; since the check was built
from party06, party06 is not an independent test of it, and the catalog entry
says so.

### 8.8 The cap, and what it cost

P5 failed: `payload-symmetry` was `UNKNOWN` for `compiler`, `croniter` and
`referee`, so capping at `UNMEASURED` re-graded three departments, not one.
§7's frozen rule required making the check decidable rather than exempting
them, and that turned out to be the right instruction, `croniter`, authored
outside this tree, hands out **bare functions** as payloads, so the
callable-payload sidestep was never only a sham author's trick. It was a real
department going unmeasured for two years' worth of commits.

`payload-symmetry` now compares named fields: mapping keys, or an object's
public attributes, with the empty tuple as a decision rather than an absence of
one (a payload with no names cannot carry a *named*-field leak). All six
departments now decide it, the 431cc74 leak is still caught, and no department
is re-graded by the cap.

### 8.9 Net effect on the audit

- 16 named checks → 19. The referee department's measured lesion magnitudes and
  pass counts moved accordingly; its luck floor is now pinned as a *margin*
  rather than an absolute count, so it stops drifting every time a check is
  added.
- `SHAM_MODES`: 12 entries → 15. One mode moved from blind to caught
  (`detector-is-the-claim`). Three added: `agreeable-absent-field-oracle`
  (caught), `structure-matched-value-disjoint-rivals` (blind),
  `detector-claim-shapes-disjoint` (blind). `distant-rivals` stays blind.
  Blind spots: 4 → 6.
- Hollow batteries caught that were not caught before: 3 (party02, party06,
  `docs/21`'s specimen).
- Hollow batteries still uncaught: 4, all one mode, argued unreachable in §8.3.
- Honest departments rescued from a false HOLLOW: 4 of 4 blind-authored, plus
  three registered departments moved out of `UNMEASURED`.

The thesis `ROADMAP` stated after the first hollowing, *"the audit's real
constraining power is over mechanical emptiness"*, survives this build intact.
Two mechanical emptiness modes were added to the caught column. The choice that
actually decides whether a battery can reject anything, how near the rivals
are, remains the author's, and is now measured, printed, and not acted upon.
