# Red-team report: moments programme

**Date:** 2026-08-04
**Scope:** the moments build sequence `6814f9d..9bd6dd3` (module `zeta/moments.py`,
`scripts/14_moment_experiment.py`, its tests, `HANDOFF.md`, `ROADMAP.md`,
`docs/13-moments.md`).
**Produced by:** one code-verification pass (claims vs. `file:line`), one
statistical red-team pass, one docs-consistency pass, plus a live run of the
focused suite. Everything in §1 is checked against the tree; §2–§4 contain
judgment and *estimates*, flagged as such.

**Verdict in one line:** the numbers are honest and reproducible; the
ninth-increment "pre-registered attack" was not a severe test (now correctly
withdrawn in `9bd6dd3`); the observed pattern is most plausibly a generic
consequence of a heavy-tailed value distribution, and the decisive next step is
a matched null model plus the Davenport–Heilbronn control, not exposure
scaling.

---

## 1. What was verified

- `.venv/bin/python -m pytest -q -o addopts='' tests/test_script_14_moment_experiment.py`
  → **25 passed** in 62 s (run on this machine, 2026-08-04, at `12cb822`).
- Every structural claim in `HANDOFF.md` about `zeta/moments.py` checked out at
  the source: full degree-k² polynomials for k=1..4 with enforced coefficient
  counts (`zeta/moments.py:1169-1238`, `615-629`); per-term exact-antiderivative
  window averaging in `moment_polynomial_mean` (`1303-1338`); scorecard
  calibration on theorem rows before releasing conjectural rows (`1341-1523`);
  no use of "certified" except in negation.
- Pinned tables in `HANDOFF.md` match regression pins in
  `tests/test_script_14_moment_experiment.py`: full-polynomial ratios (`:286-289`),
  block CVs (`:302-307`), multi-height ratio table and 768,001 sample count
  (`:326-339`), pooled-attack table with the 0.5831–1.4362 range and 99.12%
  median concentration (`:431-452`). Mutation coverage forces each of the three
  gate paths to fail individually (`:407-427`).
- `HANDOFF.md` / `ROADMAP.md` / `docs/13-moments.md` are mutually consistent,
  including the honest-scope framing.
- Commit `9bd6dd3` was reviewed: it accurately relabels the attack as
  retrospective and strips the falsification claim from docstrings, docs, and
  dataclass names' documentation. The numerical tables are unchanged, which is
  correct, the data was never the problem.

Two minor pin gaps (cheap to close, optional):

1. Of the top-1% share row 25.81/67.06/88.67/96.49, only the 8th-moment value
   is numerically pinned (`:320-322`); the other three are only ordered.
2. Of the multi-height 8th-moment concentration column 90.25/96.52/98.96, only
   the 10⁶ value is pinned (`:353-355`).

One bracket-only check: the `<1.1e-6` grid drift and `18.05%` window drift are
bounded by tests (`:273`, `:277`) but not pinned; `HANDOFF.md` never claimed
they were.

---

## 2. Weaknesses, ranked

Severity is about how much the weakness limits what may be inferred, not about
code quality. "Status" reflects the tree at `9bd6dd3`.

### W1 (high, open): the pattern is expected, not anomalous

Selberg's central limit theorem makes log|ζ(½+it)| approximately
N(0, ½·log log T), so |ζ|^{2k} is approximately log-normal, and moments of a
log-normal field are tail-dominated: the 2k-th moment is carried by values near
exp(2kσ²) occupying measure (log T)^{−k²+o(1)}, precisely Soundararajan's
(2009) measure-of-large-values heuristic and the Keating–Snaith /
Fyodorov–Hiary–Keating picture. Both halves of the candidate pattern,
concentration rising with k and height, *and* pooled windows recovering the
aggregate, are generic to any heavy-tailed integrand with a finite mean
(concentration = large variance; pooled recovery = law of large numbers). No
zeta-specific content has been demonstrated.
**Fix:** reframe as instrument calibration against known theory. The only
defensible object is a *residual relative to a matched null* (§3, A1). Nothing
enters the `conjectures/` ledger unless it deviates quantitatively from that
null.

### W2 (high, addressed in `9bd6dd3`): pre-registration was contaminated

Window 0 at each attack height reproduces the `--replicate` window measured
before the gates were fixed (`scripts/14_moment_experiment.py`, window layout in
`multi_offset_attack`); the concentration-trend gate was chosen after observing
90.25→96.52→98.96 in those same windows, and the 5%/15% tolerances after
observing ~0.6%/6.4% maximum deviations. Given the seen data the pass
probability was near 1.
**Status:** the verdict withdrawal in `9bd6dd3` is the right remediation at the
documentation level. The protocol fix below still applies to any *future*
attack.
**Fix:** evaluation windows disjoint from every previously computed window;
thresholds derived from theory or a held-out calibration set; report each
gate's estimated pass probability under the boring null as part of the
protocol.

### W3 (high, open): the monotonicity gate has almost no power

Strict increase of a median across 3 heights passes an exchangeable
no-height-effect null with probability 1/6 per moment (see §4), and passes the
*theoretically expected* null (Selberg variance growing like ½·log log T) with
probability near 1, so passing carries almost no information under either
hypothesis. The statistic also saturates (96.5→99.0→99.1): the information
lives in the complement, and each median is the midpoint of 4 correlated
windows.
**Fix:** replace with a quantitative slope test on log(1 − share) against
log log T with null-calibrated bands, over more heights and windows, or drop
the gate.

### W4 (high, open): pooled-ratio gates are simultaneously underpowered and miscalibrated

At 10⁶, individual 8th-moment window ratios span 0.5831–1.4362 over 4 windows.
A pooled-of-4 ratio then fluctuates enough that the 15% gate would reject
CFKRS-exactly-true a substantial fraction of the time by window luck (rough
estimate ~40%, see §4), while being unable to detect any genuine deviation
smaller than ~15–30%. A meaningful 15% test at 10⁶ needs on the order of
(window-CV / tolerance)² ≈ 50 windows, not 4.
**Fix:** block-bootstrap intervals respecting the correlation length; state
power against a specified alternative; scale windows-per-height accordingly.

### W5 (high, open): no matched null model, and the repo's own DH control was skipped

The identical pipeline has not been run on (a) a log-correlated Gaussian
surrogate, (b) CUE characteristic polynomials, or (c) the Davenport–Heilbronn
`Z_dh`: despite the standing counterexample-battery rule (AGENTS.md; docs/09
gate #3). Note: a naive *iid* log-normal prediction over-predicts concentration
(top-1% share ≈ 0.98 for k=2 at 10⁵ vs. measured 0.67), which proves grid
correlation and finite-window truncation matter, so only a simulated,
covariance-matched null run through the same code can settle whether the
numbers are fully explained.
**Fix:** run A1–A3 of §3.

### W6 (medium, open): consecutive windows barely probe window luck

The 4 "offset" windows per height are consecutive, covering one contiguous
stretch. log|ζ| is log-correlated, so adjacent windows share low-frequency
modes: pooled variance is larger than independent-windows intuition suggests,
and the attack samples one neighborhood per height, not the height band.
**Fix:** randomized or decade-spread offsets (anchors c·10^j for several random
c ∈ [1,10)); quantify inter-window correlation from the null simulation.

### W7 (medium, partially addressed): the 10⁴ pooled row is suspiciously perfect, and its exposure normalization drifts

All four pooled ratios at 10⁴ sit within 6×10⁻⁴ of one despite ~18% block CV
for the 8th moment at that height; each such agreement is roughly a 10⁻² –10⁻³
event under honest pooling, and all four jointly is implausible without a
correlating cause. House rule applies: a result that looks too good is first
treated as a bug. Separately, the 4-window span at 10⁴ reaches ≈3.05×10⁴, where
the local mean gap is ~15% smaller than at the anchor, so actual zero exposure
exceeds nominal and effective resolution falls from 128 to ~111 points/gap.
**Fix:** audit for accidental data/prediction reuse at 10⁴; re-run at shifted
anchors (e.g. 1.5×10⁴) reporting per-window ratios; define windows by
increments of N(T) (exactly 6,000 zeros) instead of the asymptotic gap at the
window start.
**Status after delivery:** the implementation audit and shifted-anchor run are
complete with no bug found; see §6. Exact-zero exposure remains open.

### W8 (medium, open): "top 1% of grid intervals" is not a peak count

One physical peak spans ~20–60 grid intervals at 128 points/gap, so the top 1%
of intervals (7,680 at replicate resolution) is a few hundred clustered runs
inside perhaps 10–100 peaks. The quantity that actually governs 8th-moment
estimator stability, the number of dominating peaks per window, plausibly
under 10, is never reported. An 8-block sample CV of a heavy-tailed quantity
is itself extremely noisy; "76.81%" mostly encodes which block held the big
spike and its decimals are false precision.
**Fix:** count actual local maxima above a threshold (e.g. |Z| > (log T)^θ);
report effective dominating-peak counts and top-m-peak shares; bootstrap the
block CV or drop its decimals.

### W9 (low, open): quadrature/evaluator audits miss the regime that carries the result

Nested-grid drift <1.1e-6 was established on one window at 10⁵, but the 8th
moment at 10⁶ is carried almost entirely (99.12% median top-1%) by intervals
whose neighborhoods were never re-audited at finer spacing; the evaluator's
pointwise relative error, amplified 8× in the 8th power, was not
characterized across 10⁴–10⁶. Related: the k=1,2 "theorem controls" are not
peak-dominated, so they validate normalization only and cannot catch
high-moment-specific failure modes; passing them lends the protocol specious
credibility.
**Fix:** re-evaluate the top ~100 contributing neighborhoods at 10⁶ at 8×
resolution; run the accuracy probe at each height and propagate the amplified
error into a stated (non-certified) error term; say explicitly what the k=1,2
gates do and do not control.

---

## 3. Ranked attacks (strongest first)

**A1, matched log-correlated Gaussian null (do this before anything else
computational).** Simulate a stationary Gaussian log-field with variance
½·log log T and a log-decaying covariance calibrated to log|ζ|, exponentiate,
and run the *identical* grid/window/block/gate pipeline. If the null reproduces
top-1% shares, block CVs, window-ratio spreads, and pooled recovery within its
own simulation bands, the observation is fully explained: record that and stop.
Byproduct: exact pass probabilities for every gate, replacing hand-set
tolerances and superseding the estimates in §4.

**A2: CUE characteristic-polynomial null.** Sample |Λ_N(θ)| at
N = round(log(T/2π)) matched to each height, same pipeline. The A1/A2
comparison separates RMT-generic behavior from arithmetic content (the a_k
factor's tail effect), the only place a zeta-specific signal could live.

**A3: Davenport–Heilbronn control via `zeta.epstein`.** Run the
concentration/block half of the pipeline on `Z_dh` (no CFKRS polynomial exists,
so test concentration and pooling stability). If the pattern appears for a
function that violates RH, it almost certainly will, it distinguishes nothing
structural. This is the repo's own mandatory gate and is currently skipped.

**A4, quantitative pre-registered prediction on held-out windows.** From
Selberg/Soundararajan plus the A1 simulation, derive *numeric* predictions with
bands for (a) 1 − (top-1% share) as a function of (k, log log T, window length)
and (b) window-ratio variance; pre-register the numbers; evaluate on fresh,
randomly-offset, never-touched windows. Predicting values is a severe test;
predicting a monotone ordering across 3 heights is not.

**A5, direct distributional test of the mechanism.** Anderson–Darling/KS of
sampled log|Z| against N(0, ½·log log T) per window, plus the empirical measure
of {t : |ζ| > V} against Soundararajan's heuristic, tests log-normality at
every quantile instead of one coarse monotone summary.

**A6, block-bootstrap calibration of the existing statistics.** Honest
intervals on pooled ratios and CVs, stated gate power, and the required
windows-per-height (~(CV/tolerance)²) for a decisive 8th-moment test at 10⁶,
quantifying exactly how far the 4-window diagnostic falls short.

**A7, randomized-offset replication; exposure scaling last.** Random offsets
across each decade genuinely test window luck. The originally planned
exposure-scaling attack goes last if at all: its expected outcome (pooled error
shrinking roughly like inverse square root of exposure past the tail-dominance
scale, slower before) is predicted by *every* heavy-tailed null, so without A1
it is another descriptive curve, not a test.

---

## 4. Unverified quantitative side-claims (flagged, with derivations)

These two numbers were quoted in review discussion. Neither is verified; both
are back-of-envelope and are *superseded by A1*, which yields exact gate pass
probabilities by simulation.

**"Gate 3 passes by luck 1-in-6."** Under an exchangeable no-height-effect
null, strict increase of 3 exchangeable values has probability 1/3! = 1/6 per
moment. The 6th- and 8th-moment shares come from the same windows and peaks, so
the joint two-moment pass rate is between 1/6 (perfect correlation) and 1/36
(independence), plausibly ~10–17%. Heuristic only; and under the *expected*
null (variance growing with height) the pass probability is near 1, which is
the deeper reason the gate is uninformative either way.

**"The 15% gate would reject true-CFKRS ~40% of the time."** From the pinned
10⁶ range 0.5831–1.4362 over n=4 windows: E[range]/σ ≈ 2.06 for n=4 (normal
approximation) gives per-window σ ≈ 0.85/2.06 ≈ 0.41; pooled-of-4 σ ≈ 0.21 if
windows were independent (they are consecutive, so effective σ is larger);
P(|pooled − 1| > 0.15) ≈ 2Φ(−0.15/σ_pooled) ≈ 0.4–0.5. Every step (normality,
independence, range-based σ from one 4-window sample) is questionable in a
known direction or an unknown one; treat "~40%" as "large, order one-third to
one-half", pending A1/A6.

---

## 5. Recommended order of operations

1. **Literature audit** (unchanged from HANDOFF step 2): finite-height
   high-moment concentration, block/window variance, CFKRS vs. extreme-value
   tails: Selberg CLT, Soundararajan 2009, Keating–Snaith,
   Fyodorov–Hiary–Keating, Radziwiłł–Soundararajan, Arguin et al. Expected
   outcome given W1: "known heuristic, illustrated at finite height."
2. **A1** (Gaussian null) → **A3** (DH control) → **A2** (CUE), all through the
   unchanged pipeline code.
3. Only if a quantitative residual survives A1–A3: **A4** on held-out windows,
   with gates and bands registered in code before evaluation, mutation tests
   included, and windows never previously touched.
4. Cheap hygiene, any time: close the two pin gaps (§1); investigate the 10⁴
   pooled row (W7); report dominating-peak counts (W8).
5. Ledger decision comes after 1–3, per HANDOFF step 5. Under W1 the default
   expectation is "explained by known theory, no entry."

Standing framing (unchanged): nothing above is evidence for or against RH;
agreement with CFKRS proves neither CFKRS nor novelty; any apparent RH
consequence is treated as a bug first.

---

## 6. Post-report W7 audit

Codex investigated the suspicious `10^4` pooled row before beginning A1.

- The two minor regression-pin gaps from §1 were closed, and the shifted-anchor
  table below was pinned by a new regression test.
- Source tracing found no measured/predicted data reuse. Measured integrals are
  accumulated from `riemann_siegel_z`; predicted integrals are independently
  evaluated from the published/theorem moment polynomials.
- In a one-off diagnostic (not a regression bound), comparison against
  `mpmath.siegelz` at 24 spread points in each original window observed largest
  absolute discrepancies of `4.33e-11`, `1.52e-10`, `1.58e-10`, and `1.47e-10`.
- Another one-off diagnostic repeated window zero on nested grids of 128, 64,
  and 32 points per nominal gap; its ratios changed by at most `3.5e-9` (second
  moment) and much less for the higher moments.
- A fresh four-window run anchored at `1.5e4` gave the following ratios:

| window | 2nd | 4th | 6th | 8th |
| ---: | ---: | ---: | ---: | ---: |
| 0 | `0.998992` | `0.992625` | `0.984079` | `0.972911` |
| 1 | `1.002209` | `1.011846` | `1.027001` | `1.044684` |
| 2 | `0.999394` | `0.993951` | `0.987101` | `0.975328` |
| 3 | `1.000177` | `1.002749` | `1.004286` | `1.009597` |
| pooled | `1.000191` | `1.000374` | `1.000942` | `1.001560` |

**Finding:** no implementation bug was found, and near-unity pooling repeated
at the shifted anchor. This does not establish the probability of the event:
the four moment orders are strongly dependent, so multiplying four marginal
tail probabilities would be invalid. A1 must calibrate the joint behavior.
The separate exposure-normalization drift in W7 remains open.
