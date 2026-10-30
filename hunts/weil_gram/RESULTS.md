# RESULTS: weil_gram

**Nothing here is a result about the Riemann Hypothesis.** This measures the
bottom of the Weil form on Gaussian subspaces. Grade: **measured**. No proof, no
review, no ball-arithmetic enclosure of the eigenvalues.

## 1. The instrument, and its check

For a real basis `f_1..f_J`,

    M_jk = W(h_jk),  h_jk = f^_j * f^_k,  G_jk = <f_j, f_k>,
    W(|f^|^2) = a^T M a for f = sum a_j f_j.

Gaussian basis, `f_j = N(0, sigma_j^2)`:

    h_jk(r) = exp(-a2 r^2 / 2),  a2 = sigma_j^2 + sigma_k^2,
    g_jk(u) = N(0, a2)(u),       G_jk = sqrt(2 sigma_j sigma_k / a2).

Every entry computed twice: arithmetic side (`explicit_formula_sides`) and zero
side (`2 sum_{gamma>0} h_jk(gamma)`). Residuals, 15 unique entries, dps 50:

| entry | arithmetic | zero side | residual |
| --- | --- | --- | --- |
| (0.10,0.10) | 2.9939602e-1 | 2.9939602e-1 | 6.2e-32 |
| (0.15,0.20) | 3.8882907e-3 | 3.8882907e-3 | 2.7e-33 |
| (0.20,0.45) | 6.0314688e-11 | 6.0314688e-11 | 1.6e-40 |
| (0.45,0.60) | 7.8987861e-25 | 7.8987861e-25 | 8.1e-45 |
| (0.60,0.60) | 1.1610599e-31 | 1.1603496e-31 | **7.1e-35** |

Two things about this table, both of which constrain what can be claimed:

- The residual floor is ~1e-32 absolute, and it is **the zero table's 30-digit
  precision**, not the arithmetic side: raising dps from 50 to 90 changes every
  number in this hunt not at all, including the residuals. So the arithmetic
  side is more accurate than the check, and the check cannot confirm entries
  below ~1e-32.
- `(0.60,0.60)` is the exception that matters: its `prime_tail_bound` is
  **1.2e-33**, comparable to the value 1.16e-31. That entry is 1% uncertain by
  truncation, and that uncertainty is what makes the `plus2` eigenvalue
  meaningless (section 3). The `uncovered` flag written by `gram.py` compares
  the residual against the truncation tails only, which for every other entry are
  `e^{-aR^2}` with `R = 10^4` and therefore absurdly small (`1e-434294`); the
  flag fires on the zero-table floor and is uninformative except near the floor.

## 2. The gap, and what happens when one element is concentrated

| basis | sigmas | lambda_min (arith) | lambda_min (zeros) | eigvec |
| --- | --- | --- | --- | --- |
| broad | 0.10, 0.15, 0.20 | **+3.574e-7** | +3.574e-7 | (+0.013, -0.263, +1.244) |
| plus1 | + 0.45 | **+3.917e-25** | +3.917e-25 | (0, 0, 0, 1) |
| plus2 | + 0.60 | 7.10e-35 (not resolved) | 5.82e-60 | (0, 0, 0, 0, 1) |

The collapse from 3.6e-7 to 3.9e-25 is **the single-element degeneracy**, not a
collective effect: the bottom eigenvector is the coordinate vector of the
concentrated element. That is the same direction `hunts/arch_cover` measured
(depth `= sigma^2 gamma_1^2 / ln 10`), restated at the level of the form.

`plus2` is not a measurement. The (0.60,0.60) entry carries 1% truncation
uncertainty, i.e. ±1e-33, and the eigenvalue is 7e-35: the two sides disagree by
25 orders because the eigenvalue is far below the entry uncertainty. What is
established is only `lambda_min(plus2) < 1e-30`.

## 3. The measured content: the gap is not stable under refinement

The `broad` span alone, with **no concentrated element**, refined by adding
`sigma = 0.05, 0.25, 0.30` in that order (`refine_dps50.json`):

| k | sigmas | lambda_min | from zeros | bottom eigenvector |
| --- | --- | --- | --- | --- |
| 2 | .10 .15 | +2.404e-3 | +2.404e-3 | (-0.344, +1.326) |
| 3 | + .20 | +3.574e-7 | +3.574e-7 | (+0.013, -0.263, +1.244) |
| 4 | + .05 | +2.223e-7 | +2.223e-7 | (+0.018, -0.275, +1.253, -0.001) |
| 5 | + .25 | +2.649e-13 | +2.649e-13 | (0.000, +0.004, -0.141, 0.000, +1.135) |
| 6 | + .30 | **+5.029e-22** | +5.029e-22 | (0.000, 0.000, +0.001, 0.000, -0.075, +1.073) |

Every element here is individually healthy: `W(h_jj)` at `sigma = 0.30` is
`3.10e-8`, and at `sigma = 0.05` it is `2.75`. Nothing in the basis is close to
missing the zeros. Yet the bottom of the form falls by **19 orders** from `k=2`
to `k=6`, and the arithmetic and zero sides agree at every printed digit.

The mechanism is visible in the eigenvector at `k=6`: a combination concentrated
on `sigma = 0.30` with a `-0.075` admixture of `sigma = 0.25`, which cancels
`F = sum a_j f^_j` against the low zeros. At `k=6` the eigenvalue is 14 orders
below the best single element in the span. A `J`-dimensional Gaussian span has
`J` parameters with which to make `F` small at `gamma_1, ..., gamma_J`, and it
uses them: the descent is geometric in the dimension, roughly a factor `1e-6`
per added element at this end of the range.

## 4. What this settles

`W(|f^|^2) = sum_rho |F(rho)|^2`, so `lambda_min` on a span is exactly the
squared distance from that span to the space of functions vanishing at the
zeros. The measurement says that distance falls geometrically with the dimension
of a perfectly ordinary approximation space.

Consequence for strategy, and it is a negative one: **"establish a positive gap on
a growing subspace, then pass to the limit" cannot work.** The gap is not a
property of the form that survives enlargement; it is created by the choice of
subspace and destroyed by adding dimensions. Any proof through this functional
must handle the degeneracy explicitly (an identity, or a decomposition whose
constant degenerates in step with the test function), which is the same
conclusion `hunts/arch_cover` reached from the other direction, with a
one-parameter family instead of a subspace.

It is not evidence about RH in either direction. `lambda_min > 0` at every `k`
is consistent with RH and with its negation on other spaces.

## 5. Defects and scope

- Eigenvalues are computed in mpmath, **not enclosed** in ball arithmetic. The
  `(M, G)` problem is badly conditioned by construction (entries span 1e-31 to
  1), and nothing here is enclosed.
- Entry residuals sit at the zero table's 30-digit floor; the arithmetic side
  agrees at dps 50 and 90 to all printed digits, so the dps-90 run is a null
  test of the arithmetic and a positive test only of the zero table's limit.
- `plus2` is unresolved, as stated. Do not quote its 7.1e-35 or 5.8e-60.
- The basis is Gaussian and centred at the origin. Shifts and non-Gaussian
  elements are not measured here.
- The archimedean term still has no second backend in this tree.
- No human has reviewed any of this.
