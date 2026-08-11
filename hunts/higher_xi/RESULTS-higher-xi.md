# Higher xi derivatives: an exact thesis obstruction and two numerical oracles

## Status

The 2008 discrepancy is resolved at source level. Ji Bian's Figure 10.1
coefficient rows, inserted into equation (11.5), do not yield the reported
`0.9544` and `0.9774` proportions for simple zeros of the second and third
derivatives of xi. Page 93 first changes three signs and then reports numbers
produced by neither coefficient row.

Two independent discovery routes then pointed to the same replacement picture:

1. angular derivatives of completed Haar-unitary characteristic polynomials;
2. a direct finite Dirichlet recurrence for successive logarithmic derivatives.

The CUE route matches the known first-derivative curve within its fixed-size
Monte Carlo error. The direct recurrence has the right scale but retains a
`14.7%` finite-`ell` deficit at its last rung. Both place the measured
second-derivative form factor below Bian's eleven-term polynomial over the
tested band. The direct recurrence's observed window ladder decreases

```text
0.9342893, 0.9329638, 0.9319386, 0.9311081
```

on the tested `ell = 8,10,12,14` ladder. Four rungs do not determine its limit.

Only the internal inconsistency is an exact finite statement. The CUE and
Dirichlet outputs are measured discovery objects. No higher-derivative zeta
constant, conditional or unconditional, is claimed here.

## Pinned primary source

Ji Bian, *The Pair Correlation of Zeros of Derivatives of Riemann's
Xi-Function*, University of Rochester PhD thesis, 2008, repository item 5500:

```text
https://urresearch.rochester.edu/institutionalPublicationPublicView.action?institutionalItemId=5500
PDF SHA-256:
ec1143f4f6c83288b717cfd4cd0aa6cc620f8c68b892f510a2a8d1708f36bfb7
```

The load-bearing pages were visually inspected in the rendered PDF:

- page 70: equation (7.8), the combinatorial coefficient definition;
- page 77: Figure 10.1, the exact coefficient table;
- page 92: equation (11.5), the simplicity expression;
- page 93: the repeated coefficient rows and the `0.9544`, `0.9774` claims;
- pages 99-148: the Mathematica implementation.

The `kappa=1` normalization is independently pinned by Farmer and Gonek's
closed form, arXiv:0803.0425, later published with Yoonbok Lee.

## Exact obstruction

Equation (11.5) gives the eleven-term endpoint expression

```text
1 - 2 sum_(i=1)^11 C[kappa,i]/((i+1)(i+2)).
```

Figure 10.1 gives

```text
C[2,i] =
1, -4, 4, -16, 28, 16, 544/45, -512/45,
-104/63, -416/945, 6688/1575.
```

Exact rational substitution gives

```text
sum C[2,i]/((i+1)(i+2)) = 37057/73710
equation (11.5)                  = -202/36855
                                 = -0.005480938814272...
reported value                  = 0.9544.
```

For `kappa=3`, the same calculation gives

```text
equation (11.5) = -10284002/1216215
                = -8.455743433521212...
reported value = 0.9774.
```

There is a second inconsistency. Page 93 repeats the `kappa=2` row but drops
the minus signs on columns 8, 9, and 10. Using that page's signs gives

```text
-107714/184275 = -0.584528557861891...,
```

which still does not give `0.9544`.

This is not a global factor or equation transcription error. The same equation
and the `kappa=1` Figure 10.1 row give

```text
348002/405405 = 0.858405791739125...,
```

matching the thesis's known `0.8584` control. The exact checker is
`bian_audit.py`.

The source-level diagnosis is a chapter-11 calculation error. An unprinted tail
cannot reconcile the claim under the page's own premise: obtaining the reported
values would require omitted weighted tails canceling `95.46%` and `99.76%` of
the displayed `kappa=2` and `kappa=3` sums. The exact resolution, including the
required tail fractions, is in `RESOLUTION-2008-DISCREPANCY.md`.

## Oracle 1: completed CUE derivatives

For even `N`, sample Haar `U(N)` and form the real completed characteristic
polynomial

```text
Z_U(theta) = phase * exp(-i N theta/2) det(exp(i theta) I-U).
```

The ordinary complex roots of `P'_U` are the wrong object. `cue_oracle.py`
instead differentiates the real trigonometric polynomial in its Fourier basis.
Cyclic Rolle interlacing locates exactly one next zero in every interval.

For derivative level `k`, it measures

```text
K[k,N](m/N) = E |sum_j exp(i m theta_j[k])|^2/N.
```

The fixed-seed ladder used `1000` Haar samples at `N=32` and `600` at `N=48`.
The controls passed at `N=48`:

| alpha | CUE level 0 | exact level 0 | CUE level 1 | FGL level 1 |
|---:|---:|---:|---:|---:|
| 0.125 | 0.12327 | 0.125 | 0.06936 | 0.07035 |
| 0.250 | 0.24814 | 0.250 | 0.06324 | 0.06382 |
| 0.375 | 0.38533 | 0.375 | 0.03419 | 0.03371 |
| 0.500 | 0.50244 | 0.500 | 0.04405 | 0.04460 |

An independent product-rule implementation, which never uses the Fourier
coefficients, reproduces the first two derivative root sets to at most
`3.3e-13` on the permanent irregular-angle control.

The second derivative does not follow Bian's polynomial:

| alpha | CUE level 2 | Monte Carlo SE | Bian 11-term polynomial | discrepancy |
|---:|---:|---:|---:|---:|
| 0.125 | 0.0390741 | 0.0015469 | 0.0673269 | 18.3 standard errors |
| 0.250 | 0.0168759 | 0.0006834 | 0.0318085 | 21.9 standard errors |

The integrated comparison is sharper because it averages every Fourier mode:

| alpha | CUE level-2 integral | Monte Carlo SE | Bian 11-term integral |
|---:|---:|---:|---:|
| 0.125 | 0.00416734 | 0.00007207 | 0.00537379 |
| 0.250 | 0.00751939 | 0.00009420 | 0.01249484 |
| 0.500 | 0.00904672 | 0.00011187 | 0.01494643 |

The first two integrated discrepancies are `16.7` and `52.8` Monte Carlo
standard errors at fixed `N=48`. These measurements are strongly inconsistent
with the eleven-term polynomial at the tested sizes. Their error bars do not
include finite-`N` bias, model error in the CUE analogy, or polynomial
evaluation error. This is not a derivation of the arithmetic form factor.

## Oracle 2: direct Dirichlet recurrence

Freeze

```text
L_* = ell/2 + i*pi/4,
r_0(1)=L_*,
r_0(n)=-Lambda(n),
D(a)(n)=-log(n)a(n).
```

Successive logarithmic derivatives satisfy the finite coefficient recurrence

```text
r_(j+1) = r_j + D(r_j) * inverse(r_j)
```

under Dirichlet convolution. Level one is the same coefficient mechanism as
the known first-derivative calculation. Level two is obtained without Bian's
large partition sum.

The cumulative discovery measure is

```text
sum_(2<=n<=exp(alpha ell)) |r_j(n)|^2/(n ell^2).
```

At `alpha=0.25`:

| ell | cutoff | level 1 | known FGL integral | level 2 | Bian integral |
|---:|---:|---:|---:|---:|---:|
| 8 | 2,980 | 0.0123678 | 0.0143779 | 0.0059101 | 0.0124948 |
| 10 | 22,026 | 0.0115317 | 0.0143779 | 0.0057867 | 0.0124948 |
| 12 | 162,754 | 0.0123121 | 0.0143779 | 0.0061021 | 0.0124948 |
| 14 | 1,202,604 | 0.0122630 | 0.0143779 | 0.0061603 | 0.0124948 |

The known level-one control still has a `14.7%` finite-`ell` deficit at the
last rung. Dividing the level-two value by that control ratio gives `0.00722`,
nearer the independent CUE value `0.00752` than the unadjusted `0.00616`.
This rescaling is ad hoc and diagnostic only. The raw oracle values differ by
`18.1%`, so their agreement is directional rather than quantitative.

## Weighted-window experiment

The August 2026 method does not need a pointwise closed form if the positive
coefficient measure can be inserted directly into its autocorrelation
quadratic form. `window_probe.py` does exactly that in an even Legendre basis.

| ell | known-level reconstruction | level-2 discovery value |
|---:|---:|---:|
| 8 | 0.8831668 | 0.9342893 |
| 10 | 0.8815406 | 0.9329638 |
| 12 | 0.8799970 | 0.9319386 |
| 14 | 0.8786285 | 0.9311081 |
| limiting known level | 0.8686415 | unknown |

The known level is above its known limit at every tested rung. No bias direction
for level two follows from that control. The observed level-two ladder has
already fallen below Conrey's quoted unconditional comparator `0.93469`, but
it is not a limit and the two statements live in different certainty regimes.

At `ell=12`, varying the basis size from 8 to 12, the bin count from 600 to
2400, and quadrature from 80 to 120 moved the level-two value only between

```text
0.9319371667 and 0.9319397045,
```

a spread of `2.54e-6`. The visible drift is from the arithmetic cutoff, not
the window discretization.

As a factor-of-two and objective control, feeding the known Farmer-Gonek-Lee
curve directly into the same window optimizer gives `0.8686409279` with 600
bins, within `5.8e-7` of the independently known sharp value
`0.8686415005`.

## What is new, what is not

The primary-source search found no later paper resolving Bian's tail or
correcting the two higher-derivative percentages. The University repository
page and the available thesis copy still present them unchanged.

The exact contribution here is the countercalculation showing that the
reported values do not follow from the displayed coefficients and formula.
The directional agreement between the two in-repository numerical oracles is a
candidate route toward the actual `F_2`, not a closed form and not a tail bound.

No unconditional consequence follows automatically. A real application to
the August 2026 rank-trace machinery would separately require:

1. the explicit formula and prime-side asymptotic for `xi'''/xi''`;
2. a one-sided tail bound for the direct coefficient measure;
3. a fresh symbolic zero-side transpose audit, including off-line blocks.

The next exact target is the window-weighted tail

```text
sum_i C[2,i] lambda^i M_i(v)
```

at rational `lambda<1`, where geometric and autocorrelation damping may make
control possible even if the pointwise series at `alpha=1` remains inaccessible.

## Reproduction

From the repository root:

```bash
.venv/bin/python hunts/higher_xi/bian_audit.py
.venv/bin/python hunts/higher_xi/cue_oracle.py --sizes 32:1000,48:600
.venv/bin/python hunts/higher_xi/dirichlet_recurrence.py --ells 8,10,12,14
.venv/bin/python hunts/higher_xi/window_probe.py --ells 8,10,12,14
.venv/bin/python -m pytest -q -o addopts='' hunts/higher_xi/test_higher_xi.py
```
