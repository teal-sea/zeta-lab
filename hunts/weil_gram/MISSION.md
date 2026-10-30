# MISSION: the Gram matrix of the Weil form, and its bottom eigenvalue

**Scope:** `hunts/weil_gram/` only. Nothing outside this directory is modified.
**Status:** exploratory. Nothing here is a result about the Riemann Hypothesis.

## The object

`W` is linear in `h`, so for a real basis `f_1..f_J` and `f = sum a_j f_j`,

    W(|f^|^2) = a^T M a,   M_jk = W(h_jk),   h_jk = f^_j * f^_k,
    G_jk = <f_j, f_k>,     lambda_min = min_a a^T M a / a^T G a.

RH says `lambda_min >= 0` for every admissible subspace. The useful question is
not the sign (the answer is known) but the *size*: whether the bottom of the
form is bounded away from zero on a subspace, or sits at the numerical floor.

## Basis used here

Normalised Gaussians `f_j(x) = N(x_j, sigma_j^2)`. Then

    h_jk(r) = exp(-(sigma_j^2+sigma_k^2) r^2 / 2) * cos(r (x_j + x_k)),
    g_jk(u) = N(x_j + x_k, sigma_j^2 + sigma_k^2),

because the Fourier partner of `h_jk` is the convolution `f_j * f_k`. Both are
closed form and `W(h_jk)` is the repository's `zeta.weil.weil_functional`. The
`sigma_j` control the width of `h` in `r`: large `sigma` means `h` is narrow and
misses the zeros, which is the degenerate direction measured in
`hunts/arch_cover` (depth `= sigma^2 (gamma_1^2 + 1/4) / ln 10`; first written without the `+ 1/4` from the pole term, corrected 2026-10-30).

## What is measured

1. **Entrywise agreement.** Every `M_jk` computed twice: from the arithmetic
   side (`weil_functional`) and from the zero side (`2 sum_gamma h_jk(gamma)`).
   If these disagree the instrument is wrong and nothing else on the page counts.
2. **`lambda_min` on a broad subspace** (`sigma <= 0.2`), where `h` has mass on
   many zeros. Expected: bounded away from zero.
3. **`lambda_min` after adding one concentrated element** (`sigma = 0.45`).
   Expected: collapses to the floor, because the subspace now contains the
   direction `hunts/arch_cover` showed to be degenerate. This is the control: an
   instrument that still reports a positive gap here is lying.

## What this may not claim

- Not evidence for RH, and not a proof of anything: `lambda_min >= 0` on finitely
  many subspaces is what it says.
- `lambda_min` is computed in mpmath at finite precision and is **not enclosed**
  in ball arithmetic. The eigenvalues below ~1e-25 are noise, and are labelled so.
- The basis is Gaussian and centred at the origin; no statement survives outside
  it.

## HuntSpec

```huntspec
id: weil_gram
question: Does the bottom eigenvalue of the Weil form stay bounded away from zero as the subspace grows?
frontier: measured here, lambda_min falls from 2.4e-3 to 5.0e-22 as the Gaussian span grows from 2 to 6 elements, with every entry checked against the zero side
proposed_attack: assemble the bilinear Gram matrix of W on a Gaussian basis and solve the generalized eigenproblem against the L2 Gram matrix
dead_routes:
  - establish a gap on a finite subspace and pass to the limit, killed here because the gap is created by the subspace choice and destroyed by enlargement
required_oracles:
  - zero side evaluation of every entry, independent of the arithmetic side
  - closed form Gaussian pair with exact inner products
kill_conditions:
  - an entry disagrees with the zero side beyond the table precision
  - an eigenvalue lies below the entry uncertainty and is nevertheless quoted
  - the bottom eigenvector is not reproducible under refinement
agents_may:
  - assemble
  - diagonalise
  - compare
  - code
agents_may_not:
  - declare a bound
  - promote an observation to a result
  - use the reserved vocabulary of zeta/rigor.py
```
