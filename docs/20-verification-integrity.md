# 20 — Verification integrity: the referee, refereed

*The architectural record of the 2026-08-09 build: what was latent, how it
was attacked before it was built, what survived, and where it stops.*

---

## 1. The thesis, and where it came from

Zeta Lab's deepest reusable idea is not "departments" and it is not "the
referee". It is one principle, applied recursively:

> **No instrument's silence counts as evidence until that instrument's
> power has been measured against planted violations.**

Departments are the packaging that lets unrelated subjects supply
instruments. The battery is the unit of refereeing. And the principle
applied to the battery *itself* — plant known corruptions in batteries,
measure whether the audit notices — is the layer the repository had
discovered twice by hand and never built:

1. **The sham battery** (commit `431cc74`). A finite-survey battery whose
   decoys, surrogates and lesions were placeholders written to the
   conformance tests' shapes, and whose rivals carried a `virtual_a_p`
   payload field a claim could read as a label. Structurally complete.
   Validated. Passed the conformance suite of its day. Caught by a human.
2. **The dossier resumption benchmark** (ROADMAP, 2026-08-09). Blinded
   agents ran against planted failures from this repository's own incident
   history: they caught *recorded contradictions* nearly everywhere, and
   reliably missed *hollow verification* — in every representation tested.

Add the two written-down-but-unconsumed measurements — `compiler/FINDINGS.md`
§8 ("a department can declare four lesions, be blind to all four, and still
be structurally admissible; nothing in the admission rule consults
`has_power`") and `REDTEAM.md` W2 (a "pre-registered" attack whose criteria
had seen their own answers, pass probability near 1) — and the shape of the
missing layer was fully specified by the repository's own history. Nothing
in this build required a new idea; it required taking four recorded
incidents seriously as architecture.

## 2. How the thesis was attacked before it was built

**"Referee-as-department is forced symmetry."** Tested by deriving all four
instrument roles in the meta-domain and requiring each to carry semantic
content rather than satisfy the validator. All four turned out natural:
the rival is the *historical sham itself* (shares the structure: validates;
lacks the property: no discriminating power), the decoy strips calibration
content keeping shape, the surrogate is an unguided bundle generator, the
lesion is a planted battery corruption with measured magnitude. Survived.

**"The deeper abstraction is the two-regime certainty split (accurate vs
certified)."** Rejected: certification classifies *statement strength*,
measured power classifies *instrument trustworthiness*; only the second
transfers to compilers, cron and model evaluation, and both historical
failures were instrument failures, not statement failures.

**"Integrity cannot be a verdict, because most sham modes are mechanically
undetectable."** Half true, and the half that is true changed the design:
integrity is a **named checklist with explicit unknowns and five crisp
grades**, never a scalar, and the audit prints its own blind-spot catalog
on every report. "Self-auditing" was weakened to "self-auditing where
decidable, loud about where not" — which is the version this repository's
ethos permits anyway.

**"Adopt a truth-flavored claim vocabulary (SUPPORTED / REFUTED)."**
Rejected as a regression. The harness adjudicates the weaker, decidable
question — *is this demonstration about its subject at all?* — and per
`docs/08` nothing here is evidence for or against RH. Claim outcomes stay
the harness's own (distinguishes / shared / does-not-fire / inconclusive);
what is new is that no outcome can be stated without the integrity of the
battery that produced it.

## 3. The two axes

`harness/integrity.py` produces two things and always pairs them:

* **claim outcome** — did the claim fire for the target, and was it shared
  with any rival;
* **battery integrity grade** — `CALIBRATED`, `DETECTOR_INADEQUATE`,
  `UNMEASURED`, `CONTAMINATED`, or `HOLLOW`, derived from sixteen named
  checks, each `pass` / `fail` / `unknown` with one line of evidence.

`ClaimReport` is deliberately incapable of stating the outcome alone, and a
distinguishing claim over a non-CALIBRATED battery renders with a danger
banner. The requirement "a claim passing a weak battery must never look
like a claim passing a strong one" is a pinned test
(`test_a_green_claim_from_a_hollow_battery_is_marked_dangerous`).

The contract grew three fields, on the evidence of the incidents above:
**detectors** (a department with lesions but no declared detector is power
theater — admission now refuses it), **scope** (the compiler department's
evidence-string pattern generalised: a verdict that travels without its
scope gets read as more than it is), and **provenance** (independence and
contamination as declared, human-attested data — `harness/provenance.py`).
`DetectorVerdict` measures specificity alongside sensitivity, closing the
hole a constant-`True` detector walked through: it noticed every lesion and
earned a perfect `PowerVerdict` while carrying no information.

## 4. The sham catalog, and the audit's measured power

`integrity.SHAM_MODES` records ten known ways a structurally valid battery
can be hollow. For each, either the check that catches it, or `None` plus
the countermeasure. The audit's power is measured the way it measures
everyone else's — `harness/shams.py` plants each corruption into a
calibrated specimen and `tests/test_harness_integrity.py` asserts the named
check fails:

| Sham mode | Caught by |
|---|---|
| placeholder instruments | `lesions-plant-something` / `decoys-move-their-probe` |
| constant-True detector | `detector-specificity` |
| constant-False detector | `detector-power` |
| target as rival | `calibration-rederived` |
| inert lesion | `lesions-plant-something` |
| key-asymmetry label leak (the `431cc74` shape) | `payload-symmetry` |
| vacuous calibration | `calibration-rederived` |
| contaminated preregistration (the W2 shape) | `provenance-contamination` if declared; derived from digests where a `harness.preregistration` record exists (`docs/21` §10.1) |
| **silently dropped hardest lesion** | **nothing** here — caught only against a preregistered criteria digest (`docs/21` §10.1) |
| **value-encoded label leak / co-designed calibration** | **nothing** — pinned blind |
| **distant rivals** (added 2026-08-09) | **nothing** — pinned blind |
| **detector is the claim, negated** (added 2026-08-09) | **nothing** — pinned blind |

The last two rows were added after §8's second experiment was actually run. An
independent party, given only `protocol.py` and this package's README and
forbidden the integrity source and this catalog, built a battery graded
`CALIBRATED` **on the first attempt with zero adaptation iterations**, passing
all 19 conformance tests. Its rivals were distant enough that `anything AND a
target-only property` distinguished — an explicitly astrological claim rendered
as `distinguishes` under a `CALIBRATED` banner — and its detector was its claim
negated, identical on 29/29 payloads while passing both power and specificity.
A third observation is not a sham mode but a weakness in this module: a check
returning `UNKNOWN` (here `payload-symmetry`, unreachable because the payloads
are callables rather than mappings) does not prevent the top grade. The scoring
rule in §8 was "every mode they find that the catalog lacks is a real hole";
these are holes, and the audit's real constraining power is over *mechanical*
emptiness, not over the two choices that decide whether a battery can reject
anything — how near the rivals are, and whether the detector is independent of
the claim. Both are the author's to pick.

The last two rows are the important ones. A fully co-designed sham —
identity encoded in the *values* of a shared payload key, with claims
written to read it — is constructed in full in the test suite, and its
CALIBRATED grade is **asserted**, poison-lesion style: the day somebody
builds a check that catches it, the pin fails and the catalog gets
corrected. The countermeasure for both blind rows is independent authorship
of battery content, which is a provenance declaration and not a mechanical
fact. That boundary is printed on every report.

## 5. The referee as department #5

`harness/departments/referee_department.py`. Batteries are the subjects.
The rejected reference claim is `validates_structurally` — true of the
calibrated specimen *and of every sham rival*, measured, which makes
"structural completeness is not verification" a re-derived verdict rather
than a slogan. The distinguishing claim is the full audit at CALIBRATED.
The detector is the audit itself as a predicate, with measured specificity
(quiet on the specimen) and measured power (fires on all four planted
corruptions). The null is an unguided bundle generator *conditioned on
structural validity* — the null class worth beating, since every sham
validates — and its measured luck floor is 10–11 of 16 checks against the
specimen's 16.

The held-out element is the reconstructed `431cc74` sham: authored by a
different process, at a different time, with no knowledge of today's audit.
Its anatomy is pinned: calibration re-derives, its co-designed detector has
mechanical power — everything a sham author could co-design passes — and
the one thing its author could not hide, the payload asymmetry the label
leak *is*, catches it.

## 6. Where recursion bottoms out

There is no meta-meta-referee, by design. The trust chain is:

1. **Deterministic re-execution** — every verdict re-derives from a fresh
   run; nothing is a stored label.
2. **The pinned conformance suite** — parametrized over all departments,
   re-run on every change. The suite and the audit are *two independent
   expressions of the same requirements*: the repository's two-backend
   habit, applied to its own referee. A corrupted referee is caught by its
   own machinery (pinned); a corrupted *audit* would be caught by the
   suite; a corruption of both at once is a lied-about tree, which no
   in-tree machinery can survive.
3. **One held-out mutant** — the `431cc74` sham. The scarcity is the
   honest number: the repository owns exactly one externally-authored
   calibration case for its audit, and says so.
4. **Human-attested provenance** — declarations the audit reads and cannot
   verify. A lying provenance record defeats the audit; another referee
   layer would not change that, only move it.

Mechanically checked: everything in §4's caught column. Empirically
powered: the audit (measured against planted corruptions and one held-out
sham), every department detector (measured against lesions, floors stated).
Still requiring human judgment: semantic emptiness that survives the probe
checks, independence of authorship, the truthfulness of declarations, and
whether a department's instruments measure what its prose believes. That
list is a feature; the failure mode this document exists to prevent is its
silent deletion.

## 7. What the foreign departments broke — the record

The mission rule was: a new department must attack an assumption existing
departments do not, and record what broke.

**Department #6 (stateval)** attacked the single-run assumption. Broke two
things, both fixed as strengthenings in the FINDINGS §7 tradition:

1. `run_nulls` compares one draw per surrogate with a distance tolerance —
   exact for deterministic surrogates, and precisely the REDTEAM W3/W4
   failure for a distributional null. The protocol gained `run_null_band`:
   many draws, an exceedance count, a verdict that states its own draw
   count. Measured: genuine improvement +0.83 against a 100-draw
   selection-null band of [−0.23, +0.11], zero exceedances.
2. The audit's and the conformance suite's payload comparisons had earlier
   departments' shapes baked in: mappings compared by *keys alone* (a
   lesion changing a value "plants nothing"), array payloads raised.
   `payloads_same` walks structure instead. This is the probe-convention
   lesson repeated one layer down, and it is worth stating the pattern:
   **every false-generic so far has been payload-shape guessing, and each
   was invisible until a foreign shape arrived.**

The department also supplied the build's best preserved false start: two
drafts of its "seed-hacked" rival *acquired genuine skill*, because
selection on signal-bearing data is training and because in its task about
a third of unconstrained small random predictors genuinely beat the mean.
The calibration re-derivation caught both drafts before they shipped — the
architecture catching its own author. A rival lacks the property by
construction or it is not a rival.

## 8. What a skeptic should check, and the three experiments that would
hurt most

Check: run `.venv/bin/python -m harness.demo`; read the pinned blindness
tests in `tests/test_harness_integrity.py`; try to write a battery that
passes the audit and measures nothing — the two known routes are declared,
a third would be a finding, and `python -m harness.new_department` is the
honest way in.

The three experiments most likely to damage this architecture, stated so
that nobody has to rediscover them:

1. **Outside adoption** (known gap #1's open half, now sharper): an
   external team builds a department from the docs alone. Prediction if it
   fails: their battery passes the audit while measuring nothing domain-
   relevant — i.e. the audit's checks are necessary but far from
   sufficient, and only the co-designed-sham blind spot at larger scale.
2. **A second held-out sham.** Have an independent party author a hollow
   battery *trying* to pass the audit, without seeing `SHAM_MODES`. Every
   mode they find that the catalog lacks is a real hole. One held-out
   mutant is a floor, not a validation.
3. **Stateval transfer.** The stateval instruments on a real dataset with
   unknown ground truth — where "sham by construction" is unavailable and
   the oracle is genuinely weak. If the null-band machinery cannot say
   anything useful there, the department's scope line was doing more work
   than its instruments.
