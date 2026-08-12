# Lean frontier for URMS2-051

## Status

`lean/ZetaLean/HigherXi.lean` is the first formal slice of the rebuilt
level-two bridge. The Lean kernel accepts it with no `sorry` declarations.

This is not yet a Lean derivation of URMS2-051. The module intentionally stops
before the analytic inputs which remain absent from the formal tree.

## What is in the kernel

The module contains:

1. The exact rational witness

   \[
   \alpha=51/100,\quad \delta=3/4,\quad
   \gamma=21/20,\quad \epsilon=1/100,
   \]

   including the margins `6/25`, `9/1000`, `1/4`, and `7399/10000`, and the
   far-cutoff coefficient ratio `14/5`.

2. The logarithmic frequency estimate

   \[
   \frac1{n+1}\leq \log(n+1)-\log n,
   \qquad
   \bigl(\log(n+1)-\log n\bigr)^{-1}\leq 2n.
   \]

3. Unit Fourier atoms and their conjugation and multiplication laws.

4. The finite Dirichlet polynomial

   \[
   P(t)=\sum_{n\in S}c_n e^{-it\lambda_n}
   \]

   and its exact pre-inequality expansion

   \[
   \overline{P(t)}P(t)
   =\sum_{m,n\in S}\overline{c_m}c_n
      e^{-it(\lambda_n-\lambda_m)}.
   \]

5. The corresponding integrated sharp-block identity. This identity retains
   every lower/upper cross term automatically.

6. The multiplicity inequality, both pointwise and summed over a finite zero
   set:

   \[
   N_{2,\mathrm{simple}}
   \geq 2N_2-\sum_jm_j^2.
   \]

7. Positivity of the exact rational downstream value and its enclosure

   \[
   0.01477 < L < 0.01478.
   \]

The final rational is currently an input numeral to Lean. Its reconstruction
from all 40 corrected coefficients and the analytic tail allowance remains a
separate formal obligation.

## First missing analytic inputs

The exact dependency boundary is now:

1. A Lean version of the spacing-sensitive Montgomery--Vaughan inequality for
   a finite family of distinct real frequencies.
2. The RAMS2 connected-cluster square-density asymptotic, including uniformity
   on the fixed ratio band through `14/5`.
3. The marked-cluster derivative estimate used for height freezing.
4. The smoothed contour transfer from the level-two arithmetic resolvent to
   the zero statistic.
5. Reconstruction of the exact downstream rational from the 40 coefficient
   data and its tail bound inside Lean.

The first item is the narrowest new general-purpose theorem. The polynomial
and kernel it must act on are already present in the formal tree.

## Reproduction

```bash
cd lean
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.HigherXi
PATH="$HOME/.elan/bin:$PATH" lake build
```
