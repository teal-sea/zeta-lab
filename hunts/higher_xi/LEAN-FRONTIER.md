# Lean frontier for URMS2-051

## Status

`lean/ZetaLean/HigherXi.lean` and `lean/ZetaLean/LogMeanValue.lean` are the
first formal slices of the rebuilt level-two bridge. The Lean kernel accepts
both with no `sorry` declarations.

This is not yet a Lean derivation of URMS2-051. The module intentionally stops
before the analytic inputs which remain absent from the formal tree.

## What is in the kernel

The modules contain:

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

8. The exact sharp-block kernel bound

   \[
   |K_U(\theta)|\leq 2/|\theta| \qquad (\theta\ne0),
   \]

   and the arbitrary positive-integer logarithmic gap estimate

   \[
   \frac{n-m}{n}\leq \log n-\log m \qquad (1\leq m<n).
   \]

9. An elementary application-specific substitute for the general weighted
   Montgomery--Vaughan theorem. For real coefficient magnitudes it gives

   \[
   \sum_{m<n\leq W}
     \frac{2|c_m||c_n|}{\log n-\log m}
   \leq 3H_W\sum_{n\leq W}n c_n^2.
   \]

   Both orientations in the exact sharp-block expansion therefore cost at
   most

   \[
   6H_W\sum_{n\leq W}n c_n^2.
   \]

   The proof is finite and explicit. It allocates each pair to its two
   endpoint energies, reflects and translates the strict triangular rows,
   and bounds each resulting reciprocal row by `H_W`. Mathlib's bound
   `H_W <= 1 + log W` is also connected to the local definition. The extra
   logarithm is absorbed by the strict power margin in the analytic audit.

## First missing analytic inputs

The exact dependency boundary is now:

1. Specialize the exact complex finite mean-square expansion to logarithmic
   frequencies and discharge its off-diagonal norm with the new six-harmonic
   theorem. The analytic bound is now in the kernel; this remaining step is
   bookkeeping across the complex expansion and the two contour ranges.
2. The RAMS2 connected-cluster square-density asymptotic, including uniformity
   on the fixed ratio band through `14/5`.
3. The marked-cluster derivative estimate used for height freezing.
4. The smoothed contour transfer from the level-two arithmetic resolvent to
   the zero statistic.
5. Reconstruction of the exact downstream rational from the 40 coefficient
   data and its tail bound inside Lean.

The previous first item, the spacing-sensitive mean-value input, is no longer
an open formal dependency for this application. The finite harmonic-loss
theorem is weaker than the sharp general Montgomery--Vaughan inequality, but
it is strong enough for the strict exponent margin recorded in `URMS2-051.md`.

## Reproduction

```bash
cd lean
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.HigherXi
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.LogMeanValue
PATH="$HOME/.elan/bin:$PATH" lake build
```
