# URMS2 attack: the resummed mean-square bridge

## Disposition

This attack closes at **Outcome D, resummed barrier sharpened**.

No positive zero-statistics band is obtained, including at level one. The
largest band currently promoted is therefore `alpha_0=0`.

The failure is narrower than in the historical argument. The exact inverse is
bounded in a natural weighted Wiener algebra, acts boundedly on the companion
Dirichlet Hilbert space, has a controlled height derivative, and has a
convergent reflected coefficient envelope for `alpha<1/2` at level one and
`alpha<1/4` at level two. Montgomery-Vaughan controls the ordinary
off-diagonal mean-value error once the coefficients are frozen.

What remains missing is one full logarithm in the resummed diagonal square
sum, together with an early-smoothed contour comparison for the full inverse.
The elementary estimate is of size

\[
 x(\log x)^2,
\]

while the required scale is

\[
 x\log x.
\]

This is already a barrier for URMS1. The higher nonlinear denominator is not
yet the first unresolved difference between levels one and two.

## 1. Three precise targets

For `kappa=1,2`, let

\[
 G_\kappa(s)=\frac{\xi^{(\kappa+1)}(s)}
 {\xi^{(\kappa)}(s)}
\]

and let `gamma^(kappa)` denote the ordinates of the zeros of
`xi^(kappa)`, with multiplicity. Assume RH throughout this section. Fix
`5/4<sigma<2`, put `s=sigma+it`, and use the pinned Cauchy kernel

\[
 k(w,s)=\frac{2\sigma-1}
 {(w-(s-1/2))(w-(1/2-\bar s))}.
\]

Define

\[
 Z_{\kappa,x}(s)=
 (2\sigma-1)\sum_{\gamma^{(\kappa)}}
 \frac{x^{i\gamma^{(\kappa)}}}
 {(\sigma-1/2)^2+(t-\gamma^{(\kappa)})^2}.
\]

Let `a_kappa(n,s)` be the exact height-dependent coefficient family of
the untruncated right-half-plane inverse. Its two-range transform is

\[
 \begin{split}
 \mathcal D_x[a_\kappa](s)=x^{-1/2}\bigg(&
 \sum_{n\le x}a_\kappa(n,1-\bar s)(x/n)^{1-\bar s}\\
 &+\sum_{n>x}a_\kappa(n,s)(x/n)^s\bigg).
 \end{split}
\]

Let `P_kappa,x(s)` be the explicit diagonal, archimedean, and crossed-pole
terms from the same Cauchy transform. The error to be controlled is

\[
 E_{\kappa,x}(s)=Z_{\kappa,x}(s)-P_{\kappa,x}(s)
 -\mathcal D_x[a_\kappa](s).
\]

This definition prevents the spike and archimedean main term from being
misclassified as an error.

### A. Pointwise-band URMS2

For every compact `K subset (0,1)`, with `x=T^alpha`, prove

\[
 \sup_{\alpha\in K}\frac1{T\log T}
 \int_T^{2T}|E_{2,T^\alpha}(\sigma+it)|^2dt\longrightarrow0.
\]

Local uniformity, rather than endpoint uniformity, is the requested mode.

### B. Weighted URMS2

Let

\[
 A_v(\alpha)=\int_{\mathbb R}v(u)v(u-\alpha)du
\]

for the exact rational window in `window_certificate.py`. The smaller target
is

\[
 \frac1{T\log T}\int_0^1 A_v(\alpha)
 \int_T^{2T}|E_{2,T^\alpha}(\sigma+it)|^2dt\,d\alpha
 \longrightarrow0.
\]

The alpha integral is inside the analytic statement. No pointwise contour
bound is inserted first.

### C. Narrow-band URMS2

For one fixed `alpha_0>0`, prove

\[
 \sup_{0\le\alpha\le\alpha_0}\frac1{T\log T}
 \int_T^{2T}|E_{2,T^\alpha}(\sigma+it)|^2dt\longrightarrow0,
\]

after the explicit `P_2,x` subtraction at `alpha=0`. The natural first target
from the exact coefficient algebra is any `alpha_0<1/4`.

The same three statements with subscript one define URMS1. Its natural
coefficient-algebra target is `alpha_0<1/2`.

## 2. Exact convolution inverse

For `sigma>1`, define the weighted Wiener norm

\[
 \|a\|_{1,\sigma}=\sum_{n\ge1}|a(n)|n^{-\sigma}.
\]

Dirichlet convolution makes this a Banach algebra. Put

\[
 M_j(\sigma)=\sum_{n\ge2}
 \frac{\Lambda(n)(\log n)^j}{n^\sigma}.
\]

Every `M_j(sigma)` is finite. For level two, write

\[
 A_0=L^2+L',\qquad A_+=2LD+D^2+D'.
\]

Then

\[
 \|A_+\|_{1,\sigma}
 \le 2|L|M_0+M_0^2+M_1.
\]

Whenever

\[
 \delta_2=
 \frac{2|L|M_0+M_0^2+M_1}{|L^2+L'|}<1,
\]

the full inverse exists in the Wiener algebra and satisfies

\[
 \|b\|_{1,\sigma}
 \le\frac1{|L^2+L'|-2|L|M_0-M_0^2-M_1}.
\]

Since `|L(s)|` grows like one half of `log |t|`, this condition holds
uniformly on the right contour line above an epsilon-dependent height. It is
an estimate for the full inverse, not a finite Taylor polynomial.

For

\[
 N_+=2LD'+2DL'+2DD'+D'',
\]

one has

\[
 \|N_+\|_{1,\sigma}
 \le2|L|M_1+2|L'|M_0+2M_0M_1+M_2.
\]

Together with `N_0=2LL'+L''`, this gives

\[
 \|a_2\|_{1,\sigma}
 \le M_0+(|N_0|+\|N_+\|_{1,\sigma})\|b\|_{1,\sigma}.
\]

Level one is simpler:

\[
 \|(L+D)^{-1}\|_{1,\sigma}\le(|L|-M_0)^{-1}
\]

once `|L|>M_0`.

### Support and multiplicativity

The recursion

\[
 b(n,s)=-A_0(s)^{-1}
 \sum_{\substack{d\mid n\\d>1}}a_+(d,s)b(n/d,s)
\]

is finite at every `n`. Since `D` is supported on prime powers and `D^2`
on products of two prime powers, repeated convolution gives the inverse
unbounded almost-prime support.

The normalized inverse is not multiplicative. For the first coprime pair
`2,3`, the frozen level-two denominator gives the exact defect

\[
 b(6)-b(2)b(3)
 =\ell_2\ell_3z^2
 (\ell_2\ell_3z^2-2\ell_2z-2\ell_3z+2),
\]

which is not the zero polynomial. Thus Euler-product methods do not apply to
the inverse sequence without additional structure.

### Height derivative

Differentiating the convolution identity `A*b=1` gives

\[
 \partial_t b=-b*(\partial_t A)*b
\]

and hence

\[
 \|\partial_t b\|_{1,\sigma}
 \le\|b\|_{1,\sigma}^2
 \|\partial_t A\|_{1,\sigma}.
\]

For two heights, the resolvent identity similarly gives

\[
 \|b_t-b_u\|_{1,\sigma}
 \le\|b_t\|_{1,\sigma}\|A_t-A_u\|_{1,\sigma}
 \|b_u\|_{1,\sigma}.
\]

These identities isolate height dependence without differentiating a
coefficient-order expansion.

## 3. Natural Hilbert space

The mean-square companion is

\[
 \mathcal H^2_\sigma=
 \left\{a:\|a\|_{2,\sigma}^2
 =\sum_{n\ge1}|a(n)|^2n^{-2\sigma}<\infty\right\}.
\]

Young's inequality on the multiplicative semigroup gives

\[
 \|a*c\|_{2,\sigma}
 \le\|a\|_{1,\sigma}\|c\|_{2,\sigma}.
\]

Therefore the exact inverse acts as a bounded multiplier on
`H^2_sigma`, with operator norm at most its Wiener norm. Multiplication by
`D,D',D''` is controlled by `M_0,M_1,M_2`, respectively.

This space solves the right-half-plane resolvent problem. It does not by
itself evaluate the reflected polynomial in the first range `n<=x`, where the
coefficient weights grow with `log n/L`. The Hilbert multiplier theorem and
the arithmetic square-density theorem are different obligations.

## 4. The narrow-band base camp

Put

\[
 \lambda_T=\frac12\log\frac{T}{2\pi},
 \qquad r=\frac{\log n}{\lambda_T}.
\]

For an operator word `beta`, the elementary convolution bound is

\[
 |W_\beta(n)|
 \le(\log n)^{\operatorname{length}(\beta)+|\beta|}.
\]

Every word in `q_j` has length plus logarithmic degree `j+1`.

At level one, the absolute word mass is one at every order, so the full
coefficient envelope is

\[
 |a_{1,T}(n)|\le(\log n)G_1(r),
 \qquad G_1(r)=\frac1{1-r},\quad r<1.
\]

For `n<=T^alpha`, this is available on every compact
`alpha<1/2`.

At level two, the exact word masses are

\[
 1,2,3,6,12,\ldots,
\]

and give

\[
 |a_{2,T}(n)|\le(\log n)G_2(r),
\]

where

\[
 G_2(r)=1+2r+\frac{3r^2}{1-2r},\qquad r<\frac12.
\]

Thus the exact coefficient sequence is pointwise resummed on every compact
`alpha<1/4`.

This does not complete the mean square. Summing the pointwise bound over all
integers gives only

\[
 \mathcal A_{\kappa,T}(x)
 :=\sum_{n\le x}|a_{\kappa,T}(n)|^2
 \le x(\log x)^2G_\kappa(r_x)^2.
\]

The target scale is `x log x`. After division by that scale, the available
bound is

\[
 (\log x)G_\kappa(r_x)^2,
\]

which diverges on every fixed positive alpha band. The exact coefficient
threshold therefore does not by itself imply narrow-band URMS2.

## 5. The missing logarithm

Let `F_kappa(alpha)` denote the regular coefficient-generated form-factor
object and define its square-density function by

\[
 \Phi_\kappa(r)=\frac{2}{r}F_\kappa(r/2),
\]

with the value at zero given by continuity. The arithmetic estimate needed by
the two-range Stieltjes calculation is

### RAMS-kappa(alpha_0)

For `x=T^alpha`, uniformly on `0<=alpha<=alpha_0`,

\[
 \mathcal A_{\kappa,T}(x)
 =x\log x\,\Phi_\kappa(\log x/\lambda_T)
 +o(x\log x).
\]

A directly weighted version, sufficient for the mean square, is

\[
 x^{-2}\int_{1-}^{x}u\,d\mathcal A_{\kappa,T}(u)
 +x^2\int_x^\infty u^{-3}\,d\mathcal A_{\kappa,T}(u)
 =\log x\,\Psi_\kappa(\alpha)+o(\log T),
\]

where `Psi_kappa` is the exact Stieltjes transform of `Phi_kappa`.

The second statement is smaller because it asks only for the quadratic form
used downstream. Either statement must save exactly one logarithm over the
current elementary estimate.

Farmer-Gonek-Lee establish the corresponding coefficient pairings at every
fixed order. Their estimates do not state constants uniform in a growing
order, so they do not imply RAMS1 for the full inverse. The corrected
level-two coefficient derivation has the same limitation.

## 6. A slowly growing projection is sufficient but not yet available

Fix `alpha_0<1/4` and put

\[
 \rho=4\alpha_0<1.
\]

The elementary square tail beyond operator order `J` has normalized scale

\[
 O((\log T)\rho^{2(J+1)}).
\]

It is enough to take

\[
 J(T)>\frac{\log\log T}{|\log\rho|}+O(1).
\]

This does not redefine the full inverse as a finite expansion. It is a
Hilbert-space projection used only to estimate its tail.

For example, when `rho=4/5` and the numerical value of `log T` is `10^6`,
the smallest integer selected by the exact inequality

\[
 (\log T)\rho^{2(J+1)}\le(\log T)^{-1}
\]

is `J=61`.

Closing the argument this way requires the almost-prime square-mean errors to
remain summable uniformly through `J(T)`. The pinned source supplies only
fixed-order constants. Sathe-Selberg type counting controls the number of
almost primes in a growing-order range, but no located theorem supplies the
log-weighted, correlated operator-word square asymptotic RAMS1 or RAMS2.

## 7. Mean-value and off-diagonal terms

Once the height-dependent coefficients are replaced by a frozen sequence, the
Montgomery-Vaughan mean-value theorem gives, schematically,

\[
 \int_T^{2T}\left|\sum_{n\le x}c_n n^{-it}\right|^2dt
 =T\sum_{n\le x}|c_n|^2
 +O\left(x\sum_{n\le x}|c_n|^2\right).
\]

For `x=T^alpha`, the error is smaller than the diagonal by `T^(alpha-1)`
throughout every compact `alpha<1`. Applying this theorem to the full frozen
coefficient sequence avoids the historical factor `(log x)^(4B)`.

Thus the ordinary Dirichlet-polynomial off-diagonal is not the narrow-band
barrier. The missing input is the arithmetic size and asymptotic shape of
`sum |c_n|^2` itself.

## 8. Archimedean freezing

Across `t in [T,2T]`,

\[
 L(\sigma+it)-\lambda_T=O(1),
 \qquad L'=O(T^{-1}),\qquad L''=O(T^{-2}).
\]

Inside the strict coefficient radii, differentiating the resummed envelopes
gives

\[
 |a_\kappa(n,L(t))-a_\kappa(n,\lambda_T)|
 \le C_{\kappa,\alpha_0}\frac{\log n}{\lambda_T}.
\]

The square of this difference sums to `O(x)` by the elementary pointwise
bound. If RAMS-kappa supplies `sum |a_kappa|^2=O(x log x)`, Cauchy-Schwarz
makes the cross term `o(x log x)`. The `L'` and `L''` terms are smaller.

Therefore freezing introduces no additional power loss once the missing
one-log square-mean bound is available. Without RAMS-kappa, the current
pointwise estimate cannot make the cross term negligible. Freezing is not
silently counted as closed before that input exists.

## 9. Long Dirichlet tail

On `Re(s)=1+epsilon`, the exact inverse belongs to the Wiener algebra. Hence

\[
 \sum_{n>X}|a_\kappa(n,s)|n^{-1-\varepsilon}\longrightarrow0
\]

uniformly in height after the right-line inverse gap is fixed. The same holds
in `H^2_(1+epsilon)`.

This controls a tail beyond a freely chosen `X`, not the entire second range
`n>x`, which contributes to the main Stieltjes quadratic form. A valid proof
must first retain that range and then let `X/x` grow. The Wiener result
prevents an uncontrolled infinite coefficient tail, but it does not evaluate
the main two-range mean square.

## 10. URMS1 calibration

Level one has all the structural advantages expected:

- inverse denominator `L+D` rather than `U^2+U'`;
- coefficient envelope radius `alpha<1/2`;
- word mass one at every order;
- the same Wiener and Hilbert multiplier bounds;
- the same Montgomery-Vaughan reduction after freezing.

Nevertheless, the elementary square sum is still only

\[
 x(\log x)^2G_1(2\alpha)^2,
\]

and the required RAMS1 scale is `x log x`. No independent uniform
almost-prime square asymptotic was located. URMS1 is therefore not obtained,
and Outcome B is not claimed.

This identifies the present ordering of difficulties:

1. uniform resummed almost-prime square density, already at level one;
2. exact early-smoothed contour transfer;
3. the additional level-two nonlinear numerator and denominator.

## 11. Exact contour target

The old false estimate is not repaired or reused. The replacement contour
target is

### RC-kappa(alpha_0)

For the exact full inverse and `x=T^alpha`,

\[
 \sup_{0\le\alpha\le\alpha_0}
 \frac1{T\log T}\int_T^{2T}
 |E_{\kappa,T^\alpha}(\sigma+it)|^2dt=o(1).
\]

The high right contour line is controlled by the Wiener inverse. What remains
is an early-smoothed passage through the Cauchy transform that retains
cancellation, handles the reflected finite range, and sums the residues of
the coefficient functions without a pointwise absolute tail estimate.

The permanent planted failure remains

\[
 \int_V^\infty\frac{dv}{1+(v-t)^2}\ge\frac12
 \quad(t\ge V).
\]

Nothing in the Wiener or Hilbert argument implies decay for this integral.
The new architecture therefore does not reproduce the known false step.

## 12. Smallest sufficient package

For any fixed `alpha_0<1/4`, the following two estimates would give narrow-band
URMS2:

1. `RC-2(alpha_0)`, the exact early-smoothed contour comparison;
2. the weighted RAMS2 Stieltjes asymptotic with error `o(log T)`.

The existing exact inverse, Hilbert multiplier, long-tail, projection, and
freezing bounds then control every remaining passage. For URMS1, replace
`1/4` by `1/2` and use the level-one versions of the same two estimates.

Current estimates miss RAMS-kappa by exactly the exponent change

\[
 x(\log x)^2\quad\hbox{to}\quad x\log x.
\]

They miss RC-kappa qualitatively: right-line norm control is available, but no
published result located here turns it into the required reflected,
early-smoothed `L2` comparison.

## 13. Falsification controls

`urms2_attack.py` records:

- exact finite convolution inversion;
- the smallest multiplicativity defect at `2,3`;
- Wiener inverse, resolvent-difference, and height-derivative bounds;
- the level-one and level-two coefficient envelopes;
- the one-log square-loss calculation;
- the `J(T)` projection scale;
- an independent finite comparison between the exact level-two recurrence and
  the corrected operator-word projections.

In the default finite comparison, the maximum coefficient error falls
monotonically from about `1.70` at order zero to below `1e-12` at order ten.
This checks the resummation normalization. It is not an asymptotic input.

The level-one reduction and the old contour-kernel counterexample remain in
`test_higher_xi.py`.

## 14. Literature boundary

| Source | Applicable result | Remaining mismatch |
|---|---|---|
| [Montgomery-Vaughan, Hilbert's inequality](https://doi.org/10.1112/jlms/s2-8.1.73) | off-diagonal control for frozen Dirichlet polynomials | does not evaluate the resummed diagonal coefficient square sum |
| [Hedenmalm-Lindqvist-Seip, arXiv:math/9512211](https://arxiv.org/abs/math/9512211) | Hilbert space of square-summable Dirichlet coefficients and multipliers | supplies functional-analytic structure, not the almost-prime asymptotic |
| [Stetler, arXiv:1401.3286](https://arxiv.org/abs/1401.3286) | multipliers on weighted Dirichlet-series Hilbert spaces | no height-dependent arithmetic square-density theorem |
| [Farmer-Gonek-Lee-Lester, QJM 64](https://academic.oup.com/qjmath/article/64/4/1057/1567887) | mean values and correlations for fixed products of `zeta'/zeta` | fixed product count, no full reciprocal uniformly in order |
| [Banks-Sinha, arXiv:2209.11768](https://arxiv.org/abs/2209.11768) | twisted sums for fixed generalized von Mangoldt order | not the growing-order correlated square sum RAMS-kappa |

No located source supplies RC1, RAMS1, RC2, or RAMS2 as stated.

## 15. Trust boundary

Exact algebra and deterministic computation cover the convolution recurrence,
nonmultiplicativity witness, norm identities, envelope sums, projection scale,
and finite resummation comparison.

Classical analysis is still required for RC-kappa and RAMS-kappa. Numerical
CUE and finite-height recurrence data do not enter the disposition.

No simplicity percentage, zeta transfer, or higher derivative is opened.

## Pinned state

- Repository state at the start of this attack:
  `64679e742dd74af9589212ba176c2604fd1c1b13`.
- Farmer-Gonek-Lee source:
  [arXiv:0803.0425](https://arxiv.org/abs/0803.0425).
- Bian thesis PDF SHA-256:
  `ec1143f4f6c83288b717cfd4cd0aa6cc620f8c68b892f510a2a8d1708f36bfb7`.

## Reproduction

```bash
.venv/bin/python hunts/higher_xi/urms2_attack.py
.venv/bin/python -m pytest -q -n0 hunts/higher_xi/test_higher_xi.py
```
