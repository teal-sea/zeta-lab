# Session handoff — zeta moments programme

**Snapshot:** 2026-08-04
**Branch:** `main`
**Remote state before the red-team correction:** `origin/main` at `12cb822`
**Detailed sources of truth:** `ROADMAP.md`, `docs/13-moments.md`, `REDTEAM.md`,
`NULLCONTROLS.md`

**Status in one line:** the moments programme is finished and its candidate
finding was explained by controls, not confirmed. No next build is chosen.

## Where the work landed

The moments programme now has a full finite-height comparison instrument for
the 2nd, 4th, 6th, and 8th critical-line moments:

- `zeta.moments.moment_polynomial(k)` returns the full degree-`k²` polynomial
  in the convention `P_k(log(t/(2*pi)))` for `k=1,…,4`.
- `moment_polynomial_mean` integrates every polynomial term over the actual
  window; it does not use a midpoint or leading-only approximation.
- `moment_scorecard` calibrates on the theorem cases `k=1,2` before releasing
  the conjectural `k=3,4` rows.
- `scripts/14_moment_experiment.py` computes local critical-line values and now
  supports convergence, disjoint-block, peak-concentration, multi-height, and
  a retrospective multi-offset diagnostic.

The `k=1,2` full polynomials are theorem-backed. The `k=3,4` polynomials are
CFKRS conjectures. Published decimal coefficients have reported stable digits
but no interval enclosure; the code never calls them certified.

## Red-team correction — read before interpreting results

The earlier handoff incorrectly called the multi-offset calculation a
pre-registered falsification attack. That verdict is withdrawn.

- Window zero at `10^4`, `10^5`, and `10^6` is exactly the already-observed
  `--replicate` window.
- The monotone-concentration gate was chosen after seeing the window-zero trend
  `90.25% → 96.52% → 98.96%`.
- Therefore the gate selection was contaminated and the historical pass has no
  falsification weight.
- The gates were not calibrated against a heavy-tailed null. A red-team audit
  reports a `1/6` exchangeable-order baseline for the order gate and roughly
  `40%` false rejection for the `15%` gate under true CFKRS. These two numbers
  still require independent reproduction; until then, gate power is unknown.

The underlying numerical tables and focused tests remain valid. What changed
is the interpretation, not the computed values.

## Main numerical observation

The empirical observation is:

> With increasing height and moment order, moment mass becomes increasingly
> concentrated in rare large-value intervals, while pooling enough disjoint
> windows recovers the full CFKRS polynomial aggregate.

This is not claimed as novel, proven, probabilistic, or related evidence for
RH. **It has since been explained** — see "Steps 1–7 were carried out" below.
The rise of concentration is reproduced by controls with no arithmetic input,
and by the Davenport–Heilbronn function, which violates RH.

### Pinned results

One width-4000 window at `t=10^5`, spacing `0.005`:

| moment | full-polynomial ratio | block-ratio CV | top 1% integral share |
| ---: | ---: | ---: | ---: |
| 2nd | `0.9982` | `1.28%` | `25.81%` |
| 4th | `0.9893` | `7.43%` | `67.06%` |
| 6th | `0.9653` | `19.20%` | `88.67%` |
| 8th | `0.9229` | `34.63%` | `96.49%` |

The nested-grid audit changed every moment by less than `1.1e-6` relatively,
so grid resolution was not the observed limitation. Window-ratio drift reached
`18.05%` for the 8th moment.

Height-normalized single-window replication used 6,000 nominal mean zero gaps,
128 points/gap, and 768,001 samples per height:

| height | 2nd | 4th | 6th | 8th | 8th-moment top 1% share |
| ---: | ---: | ---: | ---: | ---: | ---: |
| `10^4` | `1.0004` | `1.0014` | `1.0052` | `1.0199` | `90.25%` |
| `10^5` | `0.9996` | `0.9947` | `0.9755` | `0.9368` | `96.52%` |
| `10^6` | `1.0061` | `1.0154` | `1.0084` | `0.9677` | `98.96%` |

## Retrospective multi-offset diagnostic — no verdict

The historical calculation applied three gates:

1. pooled 2nd/4th theorem controls within `5%` of one;
2. pooled 6th/8th conjectural ratios within `15%` of one;
3. median top-one-percent concentration strictly increasing with height for
   both the 6th and 8th moments.

Four consecutive disjoint whole windows were evaluated at each height band: 12
windows and about 9.2 million finest-grid points. Mutation tests force all three
code paths to fail. The table passes these retrospective gates, but window zero
was reused and the concentration gate was selected after its result was known.
Do not call this survival, rejection, pre-registration, or a successful attack.

| height | pooled 2nd | pooled 4th | pooled 6th | pooled 8th |
| ---: | ---: | ---: | ---: | ---: |
| `10^4` | `1.0000` | `1.0002` | `1.0006` | `1.0001` |
| `10^5` | `1.0003` | `0.9986` | `0.9866` | `0.9633` |
| `10^6` | `1.0001` | `1.0075` | `1.0301` | `1.0628` |

At `10^6`, individual 8th-moment whole-window ratios ranged from `0.5831` to
`1.4362`, yet pooling returned `1.0628`; median top-one-percent concentration
was `99.12%`.

The suspiciously close `10^4` pooled row was checked for circularity,
pointwise evaluator error, and grid error; no defect was found. A fresh
four-window run anchored at `1.5×10^4` also pooled within `0.156%` for all four
orders. This is descriptive only; `REDTEAM.md` §6 records the audit, and exact
`N(T)` exposure normalization remains open.

## Reproduction commands

Always run from the repository root with the project venv:

```bash
.venv/bin/python scripts/14_moment_experiment.py --start 1e5 --length 4e3 --spacing 5e-3 --convergence
.venv/bin/python scripts/14_moment_experiment.py --start 1e5 --length 4e3 --spacing 5e-3 --blocks 8
.venv/bin/python scripts/14_moment_experiment.py --replicate
.venv/bin/python scripts/14_moment_experiment.py --attack
.venv/bin/python -m pytest -q -o addopts='' tests/test_script_14_moment_experiment.py
```

The last command collects 26 tests, including pinned real numerical runs and
mutation tests for the attack gates.

The null controls (about ten minutes for the Davenport–Heilbronn pass, which is
the slow one):

```bash
.venv/bin/python scripts/15_null_control.py --verify      # adapter vs the pipeline, 1.7e-16
.venv/bin/python scripts/15_null_control.py               # zeta vs both Euler surrogates
.venv/bin/python scripts/15_null_control.py --tails       # variance vs upper quantiles
.venv/bin/python scripts/15_null_control.py --cue         # the CUE control
.venv/bin/python scripts/15_null_control.py --dh          # the counterexample control
.venv/bin/python scripts/15_null_control.py --approach    # rate of approach to CUE
.venv/bin/python -m pytest -q -o addopts='' tests/test_surrogate.py -m "not slow"
```

That test command collects 22 tests; a 23rd is marked slow because it evaluates
the Davenport–Heilbronn function pointwise.

## Commits in this build sequence

```text
6814f9d Add locally generated moment experiment
f6ffadc Add full CFKRS moment polynomials
e0f5d98 Add nested moment convergence study
3dbac1e Measure moment peak concentration
fcc0c3a Replicate moments across heights
40d27ff Attack moment pattern across offsets
12cb822 Add moments session handoff
9bd6dd3 Withdraw contaminated moment attack verdict
8950568 Add moments red-team audit
18967ff Add randomised Euler product null control
61e3cbf Add full random Euler product to the null control
bb634a8 Separate variance from the upper tail in the null comparison
e248d15 Add CUE control, which reproduces the concentration pattern
11a700f Add Davenport-Heilbronn control and the null-control report
5925ee3 Regenerate CONTEXT.md for the surrogate module
3a72626 Measure the rate of approach to the CUE control
becc89c Record the moments programme as closed by the controls
```

## What not to infer

- Deterministic disjoint blocks are not asserted to be independent samples.
- Block CV, nested-grid drift, and peak shares are not confidence intervals or
  rigorous error bounds.
- “Top 1%” means ranked uniform-grid trapezoidal interval contributions, not
  one percent of independent peaks.
- The mean-zero-gap normalization is asymptotic and fixes nominal exposure; it
  is not an exact count of zeros inside each window.
- Agreement does not prove CFKRS, establish novelty, support RH, or weaken RH.
- Any apparent RH consequence should be treated as a bug.

## Steps 1–7 were carried out; the programme is closed

Every item on the previous checklist was executed on 2026-08-04. Full detail,
including the limits of each control, is in `NULLCONTROLS.md`; the instrument is
`zeta/surrogate.py` with `scripts/15_null_control.py`.

**Literature (step 2).** The concentration heuristic is Soundararajan's (Annals
2009): values of size `(log T)^k` on measure `T(log T)^{-k²}` supply the
CFKRS-sized moment. Odlyzko–Rubinstein already reported slow finite-height
convergence with large window-to-window fluctuation driven by rare large values.
The observation restates known material. Only the "top x% carries y%" phrasing
looks non-standard, which is a choice of statistic, not a result.

**Controls (steps 3–5).** `interval_statistics` reproduces `block_peak_sweep` on
real zeta data to `1.7e-16`, so every control runs the same code path.

- Both randomised Euler product surrogates reproduce the rise of concentration
  with moment order and with height using no arithmetic input.
- The arithmetic factor is not the explanation: a top-share is a ratio of
  integrals, so any scale factor cancels. Adding `a_k` moved the eighth-moment
  share from `94.36%` to `93.76%`.
- The variance is not the explanation either, and the obvious calibration is
  backwards. Zeta's variance exceeds both surrogates' (`1.9532` against `1.4571`
  and `1.5164` at `10⁶`) while its upper tail is *shorter* (`p99.9` of `3.3605`
  against `3.6623` and `3.6647`), because `log|ζ|` diverges at every zero and
  both surrogates are zero-free. Matching a zero-free null to zeta's variance
  would widen its upper tail and worsen the fit.
- The CUE control, whose only quantity `N = round(log(T/2π))` is fixed by the
  height and not fitted, matches within a couple of points at `10⁶`
  (`31.58/76.25/93.68/98.39` against `30.26/78.26/95.75/99.26`) and matches the
  `p99.9` tail at `3.3707` against `3.3605`.
- The Davenport–Heilbronn function shows the same rise with order and with
  height (`7.28 → 42.79%` at `t=200`, `9.18 → 54.21%` at `t=2000`), so under the
  standing counterexample gate the pattern distinguishes nothing structural.

**Rate of approach.** With the band taken from 200 CUE seeds per height instead
of a chosen threshold, the eighth-moment gap to the CUE median runs `-19.03%` at
`10³`, then `-7.26%`, `-2.01%`, `+0.84%`, `-0.23%`, `+0.63%` through `10⁸`. Zeta
lies outside the central 95% only at `10³` and only for the 6th and 8th moments.
The band is wide enough that "inside" is a weak test — the 2nd and 4th moments
are inside at every height — so this bounds the residual rather than showing
agreement.

**Byproduct.** `a_k` from the random Euler product times `g_k` from the
Keating–Snaith product converges to the CFKRS leading coefficient derived
independently in `scripts/14_moment_experiment.py` (ratio `1.0016` at
`N = 40000`, falling tenfold per decade of `N`). Neither factor is read from a
table.

**Decision (step 7): no `conjectures/` ledger entry.** The pattern is generic,
the RH-violating counterexample shares it, and the gap to the random-matrix
control closes with height.

External high-height critical-line value data remains desirable, but no public
dense row table was found in the 2026-08-04 source audit. Never substitute zero
ordinates for independently evaluated `|zeta|` samples.

## What is open now

There is **no next build chosen**. `ROADMAP.md`'s only "Next build" heading was
moments, and moments is finished. Whatever comes next is an open decision, not
something already recorded.

Three narrow moments items were left unfinished, none of them load-bearing:

1. Exact `N(T)` exposure in place of nominal mean-gap windows.
2. Seed replication of the CUE and Davenport–Heilbronn rows, which are
   single-realisation; the Euler rows were replicated over five seeds.
3. The drift of the 2nd and 4th moments above the CUE median at `10⁷`–`10⁸`
   (`+7.73%`, `+10.64%`, both inside the band) — window luck until replicated
   across offsets.

## Test-run caveat

The focused moments and script suites pass. The repository's parallel pytest
runner has a pre-existing teardown/worker hang near completion; the last broad
fast run reported 1,370 passes and 4 skips before manual interruption. Do not
misreport that interrupted run as a clean full-suite exit. Use the focused
single-process command above for this work, and investigate the unrelated
runner hang separately if a clean repository-wide exit is required.

The null-control work was verified the same way, single-process and focused:
`tests/test_surrogate.py` 22 passed with 1 deselected as slow, and
`tests/test_epstein.py tests/test_statistics.py tests/test_moments.py` 128
passed. The full repository-wide suite was **not** run to a clean exit in this
session, and nothing here should be read as claiming it was.
