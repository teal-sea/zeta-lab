# Independent audit of URMS2-051

## Verdict

URMS2-051 survives the independent internal audit.

The six load-bearing gates are:

| Gate | Result | Independent route |
|---|---|---|
| two-range phase and weights | PASS | symbolic expansion from the contour exponents |
| weighted mean value | PASS | Montgomery-Vaughan weighted Hilbert inequality |
| upper-length independence | PASS | separate Stieltjes bounds below and above `x` |
| height freezing at ratio `14/5` | PASS | differentiated connected-cluster majorant |
| multiplicity normalization | PASS | integer inequality for every multiplicity |
| `0.51` window functional | PASS | JSON coefficient fixture and rebuilt tail sum |

This is an internal mathematical audit.  Independent external review remains
separate work.

## 1. Source theorem and exact hypothesis map

The primary analytic input is H. L. Montgomery and R. C. Vaughan,
[*Hilbert's Inequality*](https://doi.org/10.1112/jlms/s2-8.1.73), Journal of
the London Mathematical Society (2) 8 (1974), 73-82.

Its weighted form gives, for distinct real frequencies `lambda_n`,

\[
 \int_A^{A+U}\left|\sum_n c_ne^{-it\lambda_n}\right|^2dt
 =U\sum_n|c_n|^2
 +O\left(\sum_n\delta_n^{-1}|c_n|^2\right),
\]

where `delta_n` is the nearest-neighbor frequency spacing.  Translation of
the interval from `[0,U]` to `[A,A+U]` changes each coefficient by a unit
complex phase and does not change the estimate.

For `lambda_n=log n`, the frequencies are distinct.  Since

\[
 \log(n+1)-\log n=\log(1+1/n)\geq\frac1{n+1},
\]

one has `delta_n^-1<=2n` for `n>=2`.  The `n=1` term has fixed spacing
`log 2` and is absorbed in the same absolute constant.  Therefore

\[
 \int_U^{2U}\left|\sum_{n\leq W}c_nn^{-it}\right|^2dt
 =U\sum_{n\leq W}|c_n|^2
 +O\left(\sum_{n\leq W}n|c_n|^2\right).
\]

No condition `W<U` occurs in this theorem.

## 2. Independent phase reconstruction

At `sigma=3/2`, the lower contour exponent is `-1/2+it` and the upper
exponent is `3/2+it`.  Including the outside factor `x^-1/2` gives

\[
 x^{-1/2}(x/n)^{-1/2+it}
 =\frac{\sqrt n}{x}(x/n)^{it},
\]

and

\[
 x^{-1/2}(x/n)^{3/2+it}
 =\frac{x}{n^{3/2}}(x/n)^{it}.
\]

After the common unit phase `x^it` is removed, both ranges have frequency
`log n` with the same sign.  `exact_two_range_phase_defects()` returns two
symbolic zeros.

The reflected level-two logarithmic derivative causes no magnitude mismatch.
Differentiating `xi(1-s)=xi(s)` three times gives

\[
 \frac{\xi'''(1-s)}{\xi''(1-s)}
 =-\frac{\xi'''(s)}{\xi''(s)}.
\]

The reflection changes a sign and conjugates at the paired point.  The
weighted Hilbert inequality permits arbitrary complex coefficients, so both
operations preserve every square estimate.

## 3. Diagonal and off-diagonal weights

With the frozen level-two coefficients, put

\[
 |c_n|^2=
 \begin{cases}
 x^{-2}|a_2(n)|^2n,&n\leq x,\\
 x^2|a_2(n)|^2n^{-3},&x<n\leq W.
 \end{cases}
\]

The diagonal is `U sum |c_n|^2`.  It is the weighted RAMS2 Stieltjes object
whose limit is the corrected `F2`.

The weighted off-diagonal cost below `x` is

\[
 x^{-2}\sum_{n\leq x}|a_2(n)|^2n^2.
\]

If `A(y)=sum_(n<=y)|a_2(n)|^2<=C y log y`, partial summation gives

\[
 x^{-2}\int_{1-}^{x}u^2dA(u)
 \leq Cx(3\log x+2).
\]

Above `x`, the cost is

\[
 x^2\sum_{x<n\leq W}|a_2(n)|^2n^{-2}.
\]

The same calculation gives

\[
 x^2\int_x^W u^{-2}dA(u)
 \leq Cx(3\log x+2).
\]

The bound is independent of `W`; the decreasing weight makes the lower
endpoint dominant.  Thus the full off-diagonal error is `O(x log x)`.  On
`U>=H^delta`, division by the main scale `U log U` leaves
`O(H^(alpha-delta))`.

This also resolves the lower/upper cross terms.  They are entries of the same
arbitrary-coefficient polynomial and are already included in the weighted
Hilbert inequality.  No separate shifted-correlation hypothesis is used.

## 4. Height-freezing gate

The earlier reports documented height freezing only inside the old elementary
pointwise radius.  The `0.51` witness uses the larger fixed ratio `14/5`, so
this gate needed a new argument.

Differentiate the Borel monomer-dimer representation with respect to the
frozen parameter `z`.  A derivative marks one monomer or dimer factor.  In the
Hadamard square, a marked connected component gains at most a polynomial
factor in its support size.  The unmarked support majorant has successive
ratio `O(1/r)`, so every polynomially marked series is still summable on a
fixed compact `rho` band.

For powerful supports, choose the tail-prime Cauchy radius for a slightly
larger compact band than `14/5`.  Cauchy's derivative estimate changes only
the fixed constant.  The finitely peeled primes again contribute a finite
factor.  The differentiated powerful-squarefree majorant is therefore
summable.

The resulting marked-cluster estimate is

\[
 \sum_{n\leq y}|\partial_z a_{2,z}(n)|^2
 \ll_{\rho_0}y(\log y)^3.
\]

Across one dyadic height block,

\[
 |z(t)-z_U|\ll(\log U)^{-2}.
\]

For `log y` bounded by a fixed multiple of `log U`, the mean-value theorem in
`z` gives

\[
 \sum_{n\leq y}|a_2(n,t)-a_{2,U}(n)|^2
 \ll_{\rho_0}\frac{y}{\log U}.
\]

Applying the two contour weights gives frozen-difference diagonal
`O(1/log U)` and spacing cost `O(x/log U)`.  Cross terms with the main
coefficient family are smaller by Cauchy-Schwarz.  The `L'` and `L''` pieces
carry additional factors `U^-1` and `U^-2` and are smaller.

Thus height freezing remains negligible at the far-cutoff ratio `14/5`.

## 5. Infinite remainder

For `Re(s)=1+epsilon`, the exact inverse has a uniformly bounded weighted
Wiener norm.  Therefore

\[
 \sum_{n>W}|a_2(n,s)|n^{-3/2}
 \leq W^{-1/2+\epsilon}
 \sum_{n>W}|a_2(n,s)|n^{-1-\epsilon}.
\]

This is a pointwise bound before the height integral.  After multiplication
by `x` and squaring,

\[
 |R_{U,x,W}(t)|^2\ll x^2W^{-1+2\epsilon}.
\]

The rational witness

\[
 \alpha=51/100,\quad \gamma=21/20,\quad\epsilon=1/100
\]

has exponent margin

\[
 \gamma(1-2\epsilon)-2\alpha=9/1000.
\]

The cross term between the finite polynomial and this remainder is negligible
by Cauchy-Schwarz.

## 6. Independent window computation

`independent_window_bound()` does not call `constant_window_bound`.  It:

1. reads the 40 rational coefficients from `C2_EXTENDED.json`;
2. integrates the triangular autocorrelation term by term;
3. rebuilds indices 41 through 101 from the Fock majorants;
4. rebuilds the two residue-class tails from the coarse ratio;
5. doubles the full absolute tail allowance.

It returns the same exact rational denominator upper bound as the theorem
code and the positive lower value

\[
 0.0147728663285376\ldots.
\]

This agreement uses a stored coefficient artifact rather than calling the
coefficient derivation used by the first route.

## 7. Multiplicity and normalization

Let the distinct zeros have multiplicities `m_j`.  The zero count with
multiplicity is `N_2=sum m_j`, and the diagonal of the pair sum is
`sum m_j^2`.  For every positive integer `m`,

\[
 \mathbf1_{m=1}\geq2m-m^2.
\]

Summing gives

\[
 N_{2,\mathrm{simple}}
 \geq2N_2-\sum_jm_j^2.
\]

The squared-sinc physical kernel is nonnegative, bounded by one, and equals
one on the diagonal.  Hence the full pair sum bounds `sum m_j^2` from above.
After division by `N_2`, the lower proportion is exactly `2-D_beta(v)`.

The spike at `alpha=0` supplies `A_v(0)`.  URMS2 is used for the regular
part away from zero, with dominated passage supplied by the existing uniform
RAMS2 majorant.  The triangular autocorrelation vanishes at `|alpha|=0.51`,
so no endpoint atom is omitted.

## 8. Remaining trust boundary

The audit found and closed the missing marked-cluster freezing argument.  It
also corrected a stale sentence in `URMS1-CLOSURE.md` that described the
cross-range phase as `log(mn)`; after the exact two-range transform, all finite
terms belong to one `log(m/n)` polynomial.

The theorem package is now internally self-consistent and source-grounded.
It has not received independent external mathematical review.  That is the
next promotion gate, not further bandwidth optimization.

## Reproduction

```bash
.venv/bin/python hunts/higher_xi/urms2_051_audit.py
.venv/bin/python -m pytest -q hunts/higher_xi/test_higher_xi.py -n0
```
