# Department: stateval — statistical model evaluation

**Subject.** The commonest claim in applied machine learning: *"model B
genuinely improves on the baseline."* A subject here is a **comparison** —
candidate pipeline, baseline, and the pair's own evaluation protocol — on a
fixed synthetic regression task (eight features, two informative, seeded
noise, n = 64). Payloads expose behavior only: the pair's own reported
improvement, and the candidate rebuilt on fresh draws the subject's author
never chose.

**Why this department exists.** Every earlier department judges
deterministic subjects with deterministic instruments — one run settles a
claim. This subject's measurements are draws from a distribution, its
oracle is weak, and its canonical failures are not wrong code but wrong
*protocols*: test contamination, selection on the evaluation set, a
crippled baseline. It was chosen to attack the single-run assumption the
other departments never test — and it found real targets:

- **`run_null_band` exists because of this department.** `run_nulls`
  compares an observation against one draw per surrogate with a distance
  tolerance — exact for deterministic surrogates, and the REDTEAM.md W3/W4
  failure (a gate whose pass probability under the null nobody measured)
  for a distributional one. The multiple-comparison null here is
  irreducibly a distribution, so the protocol gained an exceedance-count
  verdict over a stated number of draws. Measured: the genuine comparison
  reports +0.83; one hundred draws of best-of-40 junk selected on its own
  evaluation set, on signal-free data, span [−0.23, +0.11] and never reach it.
- **The audit's payload comparison had shapes baked in.** Mapping payloads
  were compared by keys alone; array payloads raised. Department #6's
  shapes exposed both — the probe-convention lesson, one layer down — and
  `payloads_same` in `harness/integrity.py` is the strengthening.

**The battery.**

| Role | Instrument |
|---|---|
| rivals | **memorizer-leak** (shown the evaluation rows; reports +1.00, fresh skill none), **seed-hacked** (best-of-40 junk selected on its own eval slice; reports +0.23, fresh skill none), **crippled-baseline** (junk beating a constant nailed far from the data; reports +1.00) |
| decoys | label shuffle, noise labels — every marginal survives, the relationship does not; measured in-sample improvement collapses 0.88 → ~0.11 |
| surrogates | the selection-null distribution: apparent improvement of best-of-N junk on data with **no signal at all**, drawn afresh per call |
| lesions | planted contamination of an evaluation protocol at 3.1% / 25% / 75% of evaluation rows — the magnitude is the violation's own size |

Detectors, in the compiler department's two-backend pattern: an exact
**row-overlap scan** (full power down to one leaked row; blind in principle
to contamination that is not literal duplication) and a behavioral
**generalization-gap detector** (catches contamination however it entered;
measurably blind below its floor — two leaked rows of 64 move the gap by
0.08, under the 0.1 threshold, and that blindness is pinned, not hidden).

The rejected reference claim is `reports_improvement`, true of everything in
the room: **a green number on a self-chosen benchmark distinguishes
nothing.** The distinguishing claim is `improves_when_fresh` — beating the
department's honest oracle (the mean predictor, computed by department code
that never calls any subject) on three fresh draws.

**A preserved false start, because it is the subject matter.** The first
two drafts of the seed-hacked rival *acquired genuine skill*: selection on
signal-bearing data is weak training, and in this task about a third of
unconstrained small random predictors genuinely beat the mean. The
calibration re-derivation caught both drafts (the "distinguishing" claim
stopped distinguishing). The pool is now skill-free by construction —
junk predictors read only the uninformative features — the same move
finitefield makes when it constructs counterfeits with `a² > 4p`: a rival
lacks the property by construction or it is not a rival.

**First command:**

```bash
.venv/bin/python -m pytest -q -o addopts='' tests/test_harness_stateval_department.py
```

**Honest scope.** A surviving claim distinguishes genuine improvement from
the three named protocol shams on this synthetic task at n = 64. It says
nothing about real datasets, other model classes, or effect sizes inside
the null band's resolution. The task is synthetic *on purpose* — ground
truth is known exactly, so every sham is a sham by construction and not by
opinion — and the cost of that choice is stated here: nothing below
demonstrates that these instruments transfer to datasets where ground truth
is unknown, which is precisely the case practitioners care about. That
transfer is an open experiment, not a footnote.
