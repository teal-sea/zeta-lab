# Department: croniter — cron schedule semantics, the first foreign subject

**Subject.** A frozen implementation of true union semantics for restricted
day-of-month/day-of-week cron fields under the `#` (nth weekday) and `W`
(nearest weekday) special forms — a feature added to the widely-used
`croniter` library (upstream commit pinned in
`harness/departments/croniter_fixtures/`, MIT licensed, vendored so the
refereed subject cannot drift).

**Why this department exists.** `ROADMAP.md` known gap #1: every earlier
department was authored inside this repository, so "the protocol is
domain-agnostic" rested on in-house evidence. This subject was born outside —
a codebase this repository had never touched — and its calibration has an
unusual provenance: an external referee suite was first authored *blind* by a
party independent of the implementer, then proven against five planted
mutants (5/5 caught, 2026-08-08). **That external referee is not vendored
here.** The instruments below — oracle, claims, decoys — were re-authored by
the implementing process in this repository's own format, and are accepted
only because they reproduce the independent calibration's verdicts: the same
five mutants, still all killed, now through the unchanged
`harness/protocol.py`. Who authored what: implementation and in-repo
instruments by the implementer; the blind external referee and the five
mutant classes by the independent party; the mutant diffs by the implementer
to the independent party's specification.

**The battery.**

| Role | Instrument |
|---|---|
| rivals | the two semantic calibration mutants: an inverted forward combiner, and a union whose sides stay contaminated by each other's special form — same API, same claim, wrong dates |
| decoys | degenerate probe expressions (`0 0 * * *`), and the special forms stripped from the probes — the substance under test removed, shape kept |
| surrogates | fixed-stride and first-of-month date generators — schedules with no cron semantics |
| lesions | the other three calibration mutants as exact source patches, magnitudes **measured at import** as the share of a bounded behavioral fingerprint each changes |

The distinguishing reference claim is exact agreement with an independent
calendar-arithmetic oracle that never calls the subject; the killed reference
claim is "accepts the API flag," true of every rival — presence of an API
proves nothing about its semantics.

**First command** — the audit, which is parametrized over all departments:

```bash
.venv/bin/python -m pytest -q -o addopts='' tests/test_department_conformance.py tests/test_harness_croniter_department.py
```

**Honest scope.** This department measures the *ingestion* half of known gap
#1: a foreign subject, refereed by the unchanged protocol, with
independently-authored battery content. What it does not measure: adoption by
an outside team — every step here was still orchestrated from this
repository's own process. That axis stays open, and saying otherwise would be
the exact promotion this tree exists to refuse.
