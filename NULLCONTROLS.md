# Null controls for the moments concentration pattern

**Date:** 2026-08-04
**Code:** `zeta/surrogate.py`, `scripts/15_null_control.py`, `tests/test_surrogate.py`
**Commits:** `18967ff`, `61e3cbf`, `bb634a8`, `e248d15`
**Answers:** attacks A1–A3 of `REDTEAM.md` §3.

**Verdict:** the candidate pattern is explained. Concentration rising with
moment order and with height is reproduced by controls carrying no arithmetic
input, and it is present in a function that violates the Riemann Hypothesis.
Per the repository's standing gate, a property the counterexample also has
distinguishes nothing. Nothing here is evidence for or against RH.

## What was measured

The statistic under audit is the share of the `2k`-th moment integral carried
by the largest one percent of grid intervals, plus the dispersion of disjoint
block integrals. `zeta.surrogate.interval_statistics` re-expresses the interval
algorithm of `scripts/14_moment_experiment.py` so it accepts any value array;
it reproduces `block_peak_sweep` on real zeta data to **1.7e-16**, so every
column below runs the same code path. That check also independently reproduced
the three top-one-percent shares that `REDTEAM.md` §1 flagged as unpinned
(25.81 / 67.06 / 88.67 percent).

Grid throughout: 750 nominal zero gaps, 64 points per gap, 48,000 intervals,
8 blocks, seed 20260804.

## Three controls

**A1, first-order log-correlated surrogate.** `X(t) = sum_{p<=T} p^{-1/2}
cos(t log p + theta_p)`, intensity `exp(2X)`. Variance `(1/2) sum 1/p` and
exact moments `prod_p I_0(2k p^{-1/2})`, both derived in code and measured
against sampling rather than assumed.

**A2, full random Euler product.** `Z(t) = prod_p (1 - p^{-1/2}
e^{i(theta_p - t log p)})^{-1}`, which keeps the higher prime-power terms the
first-order model drops. Its exact intensity moment `prod_p sum_m d_k(p^m)^2
p^{-m}` reproduces the arithmetic factor `a_k` for k=1..4 to ten digits against
the repository's independently computed `arithmetic_factor`.

**A3, CUE characteristic polynomial.** `|Lambda_N(theta)|` at
`N = round(log(T/2pi))`, fixed by the height and not fitted. Exact moments from
the Keating–Snaith product. Unlike both Euler surrogates this field has zeros
on its own contour.

**A3b, Davenport–Heilbronn.** `Z_dh` from `zeta/epstein.py`; the mandatory
counterexample gate. No CFKRS-style polynomial exists for it, so only shape
statistics are computed.

## Results

Top-one-percent share at t=1e6, with zeta for comparison:

| 2k | zeta | CUE | Euler | first-order |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 30.26% | 31.58% | 46.22% | 50.27% |
| 4 | 78.26% | 76.25% | 93.76% | 94.36% |
| 6 | 95.75% | 93.68% | 99.64% | 99.58% |
| 8 | 99.26% | 98.39% | 99.98% | 99.97% |

Davenport–Heilbronn, its own heights, 150 gaps:

| 2k | t=200 | t=2000 |
| ---: | ---: | ---: |
| 2 | 7.28% | 9.18% |
| 4 | 18.60% | 24.60% |
| 6 | 31.14% | 40.59% |
| 8 | 42.79% | 54.21% |

Tail profile of `log|f|`, t=1e6:

| field | variance | p99 | p99.9 | max |
| --- | ---: | ---: | ---: | ---: |
| zeta | 1.9532 | 2.6610 | 3.3605 | 3.4833 |
| CUE | 2.1597 | — | 3.3707 | — |
| Euler | 1.5164 | 2.8678 | 3.6647 | 4.3138 |
| first-order | 1.4571 | 2.8643 | 3.6623 | 4.2109 |

Selberg's asymptotic variance at this height is 1.3129; zeta overshoots it and
both Euler surrogates undershoot it.

## What each control settled

1. **Concentration is generic.** Both Euler surrogates produce the rise with
   `k` and with height using no arithmetic input at all. The qualitative
   observation therefore carries no zeta-specific content.

2. **The arithmetic factor is not the explanation.** Adding `a_k` left
   concentration essentially unchanged (93.76% against 94.36% at the eighth
   moment) — as it must, since the share is a ratio of integrals and any scale
   factor cancels exactly.

3. **Neither is the variance.** Zeta has a *larger* variance than both Euler
   surrogates but a *smaller* upper tail at every quantile. The excess variance
   is left-tail: `log|zeta|` diverges at every zero, and both Euler surrogates
   are zero-free by construction. Calibrating a zero-free null to zeta's
   variance would therefore widen its upper tail and worsen the fit — the
   opposite of the obvious move.

4. **Random-matrix structure is the explanation.** The CUE control, whose only
   free quantity `N` is fixed by the height, matches zeta within a couple of
   points at every moment order and matches the p99.9 tail to 3.3707 against
   3.3605. Agreement improves with height, the direction random-matrix theory
   predicts.

5. **The counterexample has the property too.** Davenport–Heilbronn shows the
   same rise with moment order and with height, so under the repository's
   standing gate the pattern distinguishes nothing structural.

A byproduct worth keeping: `a_k` from the random Euler product times `g_k` from
the Keating–Snaith product converges to the CFKRS leading coefficient that
`scripts/14_moment_experiment.py` derives independently (ratio 1.0016 at
N=40000, falling by a factor of ten per decade of `N`). Each control supplies
one factor of the constant, and neither is read from a table.

## Limits of these controls

- Concatenated CUE matrices carry no correlation beyond one matrix (about 12
  gaps at t=1e6), so the CUE block-dispersion column is the weakest number here
  and should not be read as a window-variance model.
- The Davenport–Heilbronn heights (200, 2000) are far below the zeta heights
  and the two are not calibrated to each other; only the qualitative rise is
  being compared.
- One seed per configuration in the tables, with a separate five-seed check on
  the Euler surrogates confirming the ordering is not seed luck. The CUE and DH
  rows have not been seed-replicated.
- None of these dispersions or ranges is a confidence interval, an error bound
  or a certificate.

## Consequence for the programme

`REDTEAM.md` §5 ordered the work as literature audit, then A1–A3, then a
held-out quantitative test only if a residual survived. No residual survived:
the pattern is generic, present in the counterexample, and quantitatively
reproduced by CUE. The recommendation is to record the observation as explained
and to make no entry in the `conjectures/` ledger.

## Follow-up: the rate of approach to CUE

The one question the controls left open was the finite-height rate at which
zeta's concentration approaches its random-matrix counterpart. Measured across
six heights with 200 CUE seeds each, so the comparison band is the empirical
CUE distribution rather than a chosen threshold (`--approach`):

| height | 8th-moment gap to CUE median | inside central 95% |
| ---: | ---: | :--- |
| `1e3` | `-19.03%` | no |
| `1e4` | `-7.26%` | yes |
| `1e5` | `-2.01%` | yes |
| `1e6` | `+0.84%` | yes |
| `1e7` | `-0.23%` | yes |
| `1e8` | `+0.63%` | yes |

The gap shrinks monotonically in magnitude through `1e6` and then oscillates
about zero. Zeta sits outside the CUE band only at `1e3`, and only for the 6th
and 8th moments. The residual closes.

Two honest limits on that table. The CUE band is wide — at `1e6` the central
95% for the 8th moment spans `88.69%` to `99.96%` — so "inside" is a weak
test and the 2nd and 4th moments are inside at every height including `1e3`,
which is a statement about low power, not about agreement. And each zeta row is
a single window: the 2nd and 4th moments drift *above* the CUE median at `1e7`
and `1e8` (`+7.73%`, `+10.64%`), still comfortably inside the band, which on
one realisation is window luck until replicated.

With that, the programme has no live residual. The candidate pattern is
explained, the counterexample shares it, and the quantitative gap to the
random-matrix control closes with height.
