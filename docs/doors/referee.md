# Department: referee — the verification machinery as a subject

**Subject.** Batteries themselves. The payload of every claim in this
department is a `harness.protocol.Department` bundle, and the claims are
about whether such a bundle deserves trust: not whether its subject's claims
are true, but whether the instruments that judge them could ever have said
no.

**Why this department exists.** The repository learned twice that a
structurally complete battery can be epistemically worthless. Commit
`431cc74` records the first time: a finite-survey battery whose decoys,
surrogates and lesions were placeholders written to the conformance tests'
shapes, and whose rivals carried a `virtual_a_p` payload field a claim could
read as a label. It validated. It passed the conformance suite of its day.
A human caught it. The dossier resumption benchmark (ROADMAP, 2026-08-09)
then measured the same failure in blinded agents: they caught recorded
contradictions nearly everywhere and reliably missed hollow verification.
The harness's own admission rule — work whose claims nothing can falsify is
not a department — applied to verification claims themselves, demands this
department: until it existed, "this battery is trustworthy" was a claim
nothing in the tree could kill.

**The battery.**

| Role | Instrument |
|---|---|
| target | a calibrated specimen department in a neutral toy domain — every audit check passes on its merits |
| rivals | the **reconstructed 431cc74 sham** (label leak, placeholder instruments — the held-out rival, authored by another process before this audit existed), a constant-detector sham, an inert-instrument sham |
| decoys | vacuous calibration claims; an undeclared provenance record — the substance an integrity verdict reads, removed with the shape kept |
| surrogates | bundles from an unguided generator (seeded random reference labels, detector directions, lesion behavior): the luck floor for "checks pass" |
| lesions | `harness.shams` mutations planted in the specimen, magnitudes **measured at import** as the fraction of audit checks each flips |

The detector is the integrity audit itself as a predicate — quiet on the
specimen, fires on every planted corruption. The killed reference claim is
`validates_structurally`, true of the specimen and of every sham alike:
**structural completeness is not verification**, stated as a measurement.
The distinguishing claim is `audits_calibrated`, the full audit at grade
CALIBRATED.

**First commands:**

```bash
.venv/bin/python -m pytest -q -o addopts='' tests/test_harness_integrity.py tests/test_harness_referee_department.py
.venv/bin/python -m harness.demo          # watch the machinery turn on itself
```

**Where the recursion stops — the trusted kernel.** There is no
meta-meta-referee, and refusing to build one is a design decision, not an
omission. The regress bottoms out in four things, each named:

1. **Deterministic re-execution.** Every audit check and every measured
   magnitude re-derives from a fresh run; nothing is a stored label.
2. **The pinned conformance suite.** `tests/` re-runs the audit, the sham
   catalog and the blind-spot pins on every change. The suite and the audit
   are two independent expressions of the same requirements — the
   repository's two-backend habit, applied to its own referee.
3. **One held-out mutant.** The 431cc74 sham was authored by a different
   process, at a different time, with no knowledge of today's audit. It is
   the closest thing to an externally authored calibration case the
   repository owns, and it is the only one — that scarcity is recorded, not
   hidden.
4. **Human-attested provenance.** Independence and contamination are
   *declarations* (`harness/provenance.py`). The audit reads them; it cannot
   verify them. A lying provenance record defeats it, and no additional
   referee layer would change that — it would only move the same trust one
   level up.

**Honest scope.** A CALIBRATED grade means the bundle survives the named
sham classes in `integrity.SHAM_MODES` — nothing more. Two classes are
declared blind spots, pinned as such in `tests/test_harness_integrity.py`
exactly the way the compiler department pins its concrete backend's poison
blindness: a **value-encoded label leak** (identity in the values of a
shared field) and **co-designed calibration** (claims and instruments
authored together to pass every mechanical check) both defeat the audit,
and the countermeasure — independent authorship of battery content — lives
in provenance, where it is attested rather than proven. A green verdict
from this department must be read with those limits attached; the report
prints them every time so that forgetting is work.
