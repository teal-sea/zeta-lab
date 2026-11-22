# Issue #335: repair of the gate() regime test

Branch `muse/fix-335-gate`. Diagnosis and design constraints: `hunts/local_positivity/DIAGNOSIS-335.md`.

## Root cause in one line

For a conjugate pair the weighted terms are `w_m = 2 R^m cos(m phi)`. The old test read
the regime off two sampled terms, so its "envelope rate" was `R * |cos ratio|^(1/spacing)`.
Either sampled term can sit arbitrarily close to a cosine zero, so the reading can land on
either side of 1 for any true `R` (measured errors 4 to 24 percent on the issue's cases, and
a factor of ~591 for Davenport-Heilbronn at p=3, where the sampler hit a float-noise subsequence).

## The repair

`threshold()` keeps the truncated `c` and its depth exactly as before (so all recorded
truncated numbers are untouched), and reads the regime from an envelope fit: block maxima of
`|w_m|` over the second half of a >=96-term window, least-squares slope in log space, with an
uncertainty interval built from estimator variants (block widths, block RMS, half-window slopes)
plus a statistical term, floored at the old `1e-6` band. Summable/divergent require the whole
interval on one side of 1; straddling reads INDETERMINATE rather than a wrong verdict. The
summable tail now uses the fitted envelope level, which reduces to the old formula exactly for
steady weights. Slow-oscillation near-boundary cases are honestly undecided: at fixed depth no
envelope functional can separate smooth amplitude drift from envelope growth, so the target is
no wrong decisive verdicts, pinned as such in the tests.

## Verification (re-run independently after the worker hit a quota wall)

Named cases from the issue, output of `hunts/local_positivity/reproduce_335.py`:

```text
inside_bound: radius=0.9 p=2 phi=0.2 expected=PASS | gate=PASS regime=summable
on_bound: radius=1.0 p=2 phi=0.9 expected=INDETERMINATE | gate=INDETERMINATE regime=boundary
outside_bound: radius=1.2 p=7 phi=0.4 expected=FAIL, c_p=+inf | gate=FAIL regime=divergent
on_bound_phi2: radius=1.0 p=2 phi=2.0 expected=INDETERMINATE | gate=INDETERMINATE regime=boundary
current_gate: PASS=60 FAIL=0 INDETERMINATE=0 of 60
margin 2-max_c: min=0.343354 max=0.650851
```

Full hunt suite: `13 passed in 589.97s`, including
`test_the_recorded_numbers_reproduce_under_the_repair` (reference table, lesion
eps_star = 0.1841018918280497, null distribution), the 60-angle margin pin, and a
conjugate-pair sweep with no wrong decisive regime.

## Provenance

Produced by Muse Code (Muse Wonder Full, reasoning max). The worker was cut off by the
subscription window limit after implementing and testing the repair but before committing;
the working tree was verified (reproduce script and full suite re-run) and committed by a
separate agent. Draft PR: no merge intended without review.
