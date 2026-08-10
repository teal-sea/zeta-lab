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
nothing in the tree could refute.

**The battery.**

| Role | Instrument |
|---|---|
| target | a calibrated specimen department in a neutral toy domain — every audit check passes on its merits |
| rivals | the **reconstructed 431cc74 sham** (label leak, placeholder instruments — the held-out rival, authored by another process before this audit existed), a constant-detector sham, an inert-instrument sham |
| decoys | vacuous calibration claims; an undeclared provenance record — the substance an integrity verdict reads, removed with the shape kept |
| surrogates | bundles from an unguided generator (seeded random reference labels, detector directions, lesion behavior): the luck floor for "checks pass" |
| lesions | `harness.shams` mutations planted in the specimen, magnitudes **measured at import** as the fraction of audit checks each flips |

The detector is the integrity audit itself as a predicate — quiet on the
specimen, fires on every planted corruption. The rejected reference claim is
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
3. **Held-out mutants.** The 431cc74 sham was authored by a different
   process, at a different time, with no knowledge of today's audit. Ten more
   arrived on 2026-08-10 from ten independent parties working from the public
   contract alone (`harness/blind_authoring_2026_08_09/`), and they are the
   reason this page has a sharper honest-scope section than it used to: six of
   six parties told to hollow the audit succeeded. That corpus is now *spent* —
   two current checks were built with it in hand — so the scarcity of genuinely
   held-out calibration cases is recorded rather than solved.
4. **Human-attested provenance.** Independence and contamination are
   *declarations* (`harness/provenance.py`). The audit reads them; it cannot
   verify them. A lying provenance record defeats it, and no additional
   referee layer would change that — it would only move the same trust one
   level up.

**Honest scope, and it is narrower than it looks.** A CALIBRATED grade means
the bundle survives the named sham classes in `integrity.SHAM_MODES` — nothing
more. Six of the fifteen are declared blind spots, pinned as such in
`tests/test_harness_integrity.py` exactly the way the compiler department pins
its concrete backend's poison blindness. The one that matters most:
**structure-matched, value-disjoint rivals** — rivals sharing the target's
keys, types and shape while agreeing with it on no substantive value, so the
joint value vector is the label and any predicate keyed to a target value
distinguishes. Four of six independent parties reached CALIBRATED that way on
2026-08-10, and the obvious mechanical fix is *measured to invert*: comparing
values leaf by leaf scores this repository's own honest departments more
separated than the sham (`docs/23` §8.3).

The countermeasure for that mode and for **value-encoded label leaks** and
**co-designed calibration** is independent authorship of battery content,
which lives in provenance, where it is attested rather than proven. A green
verdict from this department must be read with those limits attached; the
report prints them every time so that forgetting is work.

**This department currently fails its own audit**, and that is not a bug in
this page. `detector-claim-agreement` flags its declared detector — the
integrity audit as a predicate — as the exact negation of its distinguishing
reference claim `audits_calibrated`. They are the same computation. The
department's power measurement for its own detector is its own claim measuring
itself, which is true, was anticipated in prose ("the recursion, and also where
it stops"), and is now measured. `docs/23` §8.5 states the open question:
either declare why a detector is a decision procedure in a form the audit can
read, or stake the department's power on an instrument independent of its
claim.
