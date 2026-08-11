# `meta/` — the second laboratory

This repository studies a mathematical object. It also, increasingly, studies the
research system attempting to study it. This directory holds the second kind of
evidence.

> **Nothing here is a mathematical result, and nothing here is evidence about the
> mathematics.** It is evidence about the laboratory. The two must not be traded
> against each other: a session that produced no mathematics and a tidy ledger
> produced nothing.

## Why it exists

The question the laboratory is now also an experiment for:

> How much legitimate research output can a very small human organisation produce
> when generation is cheap, skepticism is architectural, verification is
> systematic, and routine work can be delegated?

That question is unanswerable without a denominator. So the quantity of interest
is not autonomy and not "how much did the agent do". It is

**legitimate research output per unit of scarce human judgment.**

An increase in that ratio matters even if humans never leave the loop. A
*decrease* while output rises is a warning, not a success.

## What gets recorded

Two record types, both in `interventions.jsonl`, one JSON object per line.

**An intervention** — a human did something that materially changed the research
process. Five things are recorded, and four of them are the interesting ones:

| field | why |
|---|---|
| `what_required_intervention` | the observable event |
| `why_the_system_stopped` | the mechanism, not the symptom |
| `missing_capability` | **the gap, named.** You cannot automate what you cannot state |
| `automatability` | `no` / `speculative` / `designed` / `automated` |
| `evidence_that_would_demonstrate` | what would show the gap is closed |
| `caught_by` | `human` / `test` / `oracle` / `outsider` / `nobody` |

`caught_by` is there because this ledger also feeds a separate question: `test`
and `oracle` are architectural skepticism working, `human` and `outsider` are it
failing to.

**A meta-observation** — something learned about the research system by doing
ordinary research. It must name the work it arose from (`arose_from`) and must
either support or undercut something stated. A meta-observation attached to no
actual work is an opinion.

## Four categories, and which two matter

`automatable` · `assistable` · `domain-judgment` · `owner-authority`

The last two are the denominator. An honest early ledger is mostly those, and the
thesis under test is whether the ratio of output to *those two* improves. The
first two are engineering debt; closing them is good and is not evidence of
anything deep.

`owner-authority` is not a failure to automate. Deciding what the laboratory is
for, what may be published, and which of the operator's other projects are
private are not capability gaps. They are correctly outside the machine.

## Three refusals, on purpose

The instrument is built to be hard to flatter, because the standing principle is
that the laboratory should examine its own operation *without becoming
self-validating*.

1. **No score.** `Ledger` has no `__bool__`, no `autonomy`, no total. `render()`
   prints every category instead. Same reasoning as `dossier/status.py`'s
   `Support`: a single number would let a caller ask "are we autonomous yet" as
   though it were one question.
2. **A ratio must name its numerator.** `ratio()` refuses until the caller says
   which externally checkable output class it means — kernel-checked theorems,
   accepted upstream contributions, pinned measurements. "Research output" is not
   a number.
3. **Claiming automation costs a named artefact.** `automatability=automated`
   without one is refused. It is the cheapest claim in this project to assert and
   therefore the one that must be paid for.

And `suspicions()` reports the shapes a self-validating ledger takes: no
owner-authority entries, nothing caught by a human or outsider, more automation
claims than judgment calls, no meta-observations. Those are reported as reasons to
distrust the log, not as errors.

## Usage

```bash
.venv/bin/python -m meta.ledger          # validate and render
.venv/bin/python -m pytest -q tests/test_meta_ledger.py
```

Add an entry by appending a line. `tests/test_meta_ledger.py` refuses the
inadmissible shapes and demonstrates its own detector power by planting them.

## The baseline

First cohort, the session of 2026-08-10 that ran the futures analysis. Recorded
because a baseline taken later would be taken after the lessons:

- **14 interventions, 4 meta-observations.**
- By category: automatable 8, assistable 0, domain-judgment 2,
  **owner-authority 4** — so **6 scarce-judgment interventions**.
- By what noticed: human 10, oracle 2, outsider 1, test 1 — **architecture caught
  3 of 14 (21%)**.
- By automation status: 6 `automated` (all closed during that same session), 1
  `designed`, 3 `speculative`, 4 `no`.

Read honestly, that is one encouraging number and one sobering one. Six of the
eight automatable gaps were closed the same day they were found, which is the
loop working. And 11 of 14 interventions were caught by a person or an outsider
rather than by the machinery, which is the same finding the harness has been
producing about itself all along.

### Where the machine belongs

`meta/ai-components.md` asks which parts of the laboratory should be run by a
model rather than by mechanism, and proposes one sorting principle: **a model
belongs wherever its output is checked against an oracle that is not a model,
and not where the only check is another model's agreement.** That is the
standing rule about cross-checks turned on the system itself — agents drawn from
the same weights are not independent instruments, and their agreement is nearly
free.

It ranks the targets (the empty literature backend in `ontology/knownness.py`
first, formal codegen second, standing adversarial review third), names the ones
to refuse (a model judging whether a battery is hollow; volume conjecture
generation, now dead twice on the record; the authority layer, permanently open
by design), and ends with the cheapest experiment that would show the principle
itself to be wrong. Proposal, not a decision.

### Calibration

`meta/operator-functions.md` decomposes what is left after the automatable gaps
are subtracted, into four functions: **severity calibration**, **scope discipline
on negative results**, **skepticism routing**, and **authority** — the last of
which is not a gap and is recorded as permanently open.

The reframe that makes this measurable: you do not automate judgment, you measure
*calibration*. A `Judgment` record holds the system's assessment, the operator's,
and what turned out to be true. Convergence per function is then a number rather
than an impression.

Three guards, and the first is the one that matters:

1. **The system may not resolve a disagreement it is party to.**
   `resolved_by=system` is refused outright. Without this the record is a progress
   report, and it is the same co-designed-verification failure the audit has.
2. `unresolved` is not scorable. An open disagreement is not a draw.
3. No aggregate calibration score — reported per function, because averaging
   severity against scope would hide which one transferred.

**Baseline: the system is 0 for 4 against the operator** on scored judgment calls
— severity of a disclosure, scope of a negative result, the premise of a
prioritisation argument, and the claim that the operator's contribution is mostly
friction. Four is a starting line, not a sample.

> The whole cohort, including this calibration record, was authored by the agent
> whose behaviour it describes. That is co-designed measurement. The structure is
> the contribution; re-derive the counts before believing them.

## The instrument's known blind spot

**This ledger samples interruptions to running sessions. It therefore cannot see
research design.**

Everything decided before a session exists — the honest-scope rule, the reserved
word, reference claims in both directions, the four control roles, the
counterexample battery, the mirror pattern, blind authoring with honest controls,
preregistration by digest — is invisible here, and all of it is load-bearing for
whatever a session produces. A decomposition drawn from this log alone concluded
that the operator's role was mostly friction, which is an artifact of the sampling
frame. The correction is recorded in `operator-functions.md` §0.

The consequence for the metric: **the ratio this directory measures can improve
while the function that matters goes unmeasured.** Friction removal moves it;
research design does not appear in it at all. Any serious use of these numbers has
to sample the design record too — `ROADMAP.md`'s decisions, the harness admission
rules, the pre-registrations — and not only this file.

This is the same failure the laboratory keeps finding in its own audit: an
instrument sees what it was built to sample, and reading its silence as absence is
how four hollow batteries were graded calibrated.

## What this directory is not

Not a dashboard, not a KPI, not a burndown. If it starts being used to show
progress rather than to measure a ratio, it has become the thing it was built to
prevent — and the first symptom will be `suspicions()` returning nothing while
the ledger grows.
