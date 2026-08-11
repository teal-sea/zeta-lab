# Resummed bridge audit for the xi-double-prime form factor

## Disposition

This audit closes at **Outcome D, current technology barrier**.

It also classifies the pinned Farmer-Gonek-Lee level-1 precedent as
**Classification C, a genuine gap in the printed proof with no repair located**.
This classification concerns the proof, not the truth of its limiting
prediction. No contradictory zero statistic is known here.

The positive result of this audit is a changed representation. The corrected
`Q(z)` object is the Taylor expansion of an exact, untruncated resolvent for
`xi'''/xi''`. Thus geometric order `B` is not intrinsic to the arithmetic
object. The remaining obstacle is a uniform mean-square theorem for that full
resolvent.

## 1. Level-1 precedent

The pinned source is Farmer, Gonek, and Lee,
*Pair correlation of the zeros of the derivative of the Riemann xi-function*,
arXiv:0803.0425. The journal version is JLMS 90 (2014), 241-269.

The dependency chain in the source is:

1. Equation (7.1) writes `xi''/xi'` exactly in terms of `L` and
   `zeta'/zeta`.
2. Equations (7.5)-(7.6) replace the reciprocal by a geometric expansion of
   fixed order `K` with a right-half-plane remainder.
3. Equations (7.19)-(7.22) pass that remainder through the Cauchy kernel in the
   explicit formula.
4. The resulting explicit-formula error is squared and integrated in the
   mean-square calculation used for Theorem 1.1.

At step 3 the source obtains

\[
 E_3=O\left(\frac{x^{1/2+\varepsilon}}{\varepsilon 2^K}
 \int_{T_\varepsilon}^{\infty}
 \frac{dv}{1+(v-t)^2}\right)
\]

and then assigns it decay in `|t|`. For `t>=T_epsilon`, however, the integral
is at least `1/2`, as preserved by `bridge_obstruction.py`. This term is the
only stated source of the later decaying geometric-tail error. It is therefore
load-bearing in the printed argument.

There is a second local endpoint issue in the same passage: terms containing
`1/(|t-T_epsilon|+2)` are replaced by `1/(|t|+2)`. That replacement is also
invalid near `t=T_epsilon`. The nondecaying `E_3` term already stops the chain,
so the classification does not depend on the second issue.

The fixed-order statements provide an internal control. At `alpha=1/2`, the
printed order-1 and order-2 regular polynomials differ by exactly `1/24`.
They cannot both be one common pointwise limit with a remainder tending to
zero at each fixed order. This shows that a nonvanishing truncation remainder
is missing from the printed family of formulas. It does not determine the
true limiting value.

No later erratum or independent RH-only derivation repairing this operation
was located. Sodin derives critical-point limits under RH plus convergence of
the full zeta-zero point process, which is a stronger statistical hypothesis,
not a repair of the arithmetic theorem. Later mean-value work on fixed
products of `zeta'/zeta` does not supply uniform control of the nonlinear
reciprocal used here.

Consequently:

- the exact logarithmic-derivative identities survive;
- the fixed-order coefficient calculations survive as fixed-order arithmetic;
- the printed finite-height to infinite-form-factor passage has a gap;
- this audit does not classify the level-1 limiting prediction as false.

## 2. Exact representation without geometric order

Put

\[
 U=\frac{\xi'}\xi=L+D,
 \qquad D=\frac{\zeta'}\zeta.
\]

Direct differentiation gives

\[
 \frac{\xi'''}{\xi''}
 =\frac{U^3+3UU'+U''}{U^2+U'}
 =U+\frac{2UU'+U''}{U^2+U'}.
\]

This identity contains no coefficient-order cutoff. Split its denominator as

\[
 U^2+U'=A_0+A_+,
\]

where

\[
 A_0=L^2+L',
 \qquad
 A_+=2LD+D^2+D',
\]

and split the numerator after the leading `U` as

\[
 2UU'+U''=N_0+N_+,
\]

with

\[
 N_0=2LL'+L'',
 \qquad
 N_+=2LD'+2DL'+2DD'+D''.
\]

On `Re(s)>=1+epsilon`, the series for `D,D',D''` converge absolutely. At
sufficient height, `A_0` is nonzero and `A_0+A_+` can be inverted in the
weighted Dirichlet algebra. If `a_+(n,s)` denotes the coefficient sequence of
`A_+`, its inverse `b(n,s)` is determined without a finite order by

\[
 b(1,s)=A_0(s)^{-1},
\]

and, for `n>1`,

\[
 b(n,s)=-A_0(s)^{-1}
 \sum_{\substack{d\mid n\\d>1}}a_+(d,s)b(n/d,s).
\]

The full arithmetic coefficients of the resolvent are then

\[
 a_2(\cdot,s)
 =D(\cdot)+[N_0(s)\mathbf 1+N_+(\cdot,s)]*b(\cdot,s).
\]

This is an exact, height-dependent Dirichlet object on the right half-plane.
It packages every `q_j` before the finite-height limit.

## 3. The corrected Q object is the frozen exact resolvent

Freeze `L'=L''=0`, put `z=1/L`, and use

\[
 D=-A,\qquad D'=B,\qquad D''=-C,
\]

where `A=Lambda`, `B=Lambda log`, and `C=Lambda log^2`. The arithmetic part
of the exact resolvent becomes

\[
 -A+\frac{2(L-A)B-C}{(L-A)^2+B}
 =-A+\frac{2Bz-(2A*B+C)z^2}
 {(1-Az)^2+Bz^2}.
\]

The right side is exactly the corrected generating object `Q(z)` in
`CORRECTED-F2.md`. `resummed_bridge.py` checks this symbolic identity, the
two numerator/denominator splits, and the original resolvent identity.

This connection is stronger than matching forty Taylor coefficients. It
identifies what must be treated in mean square: the whole convolution inverse,
not a geometric polynomial whose order later has to grow.

## 4. What elementary absolute resummation can and cannot do

Let `S_j` be the sum of the absolute coefficients of the operator words in
`q_j`. The closed formula gives exactly

\[
 S_0=1,\qquad S_1=2,\qquad S_j=3\,2^{j-2}\quad(j\ge2).
\]

For `j>=2`, the two numerator families in the closed formula contribute
`2 sum_k binom(j-1,2k)=2^(j-1)` and
`sum_k binom(j-1,2k+1)=2^(j-2)`, respectively. The deterministic control
checks the resulting formula through order 19. Each word in `q_j`
has word length plus total logarithmic degree equal to `j+1`. The elementary
bound for `n<=T^alpha` therefore has asymptotic order ratio `4 alpha` after
division by `L^j`, where `L` is asymptotic to one half of `log T`.

Thus termwise absolute resummation is directly available only for

\[
 \alpha<\frac14.
\]

At `alpha=1/4` this majorant loses decay. This is a boundary of the elementary
absolute argument, not a singularity of the corrected coefficient series and
not a zero-statistics theorem. Even below `1/4`, it does not control the
contour comparison, archimedean freezing, the long Dirichlet tail, or the
uniform arithmetic mean square. Those are separate obligations.

## 5. Early smoothing and direct L2 control

The source Cauchy kernel should not be estimated pointwise after taking an
absolute value. Define

\[
 Z_{2,x}(s)=\sum_{\gamma^{(2)}}k(i\gamma^{(2)},s)x^{i\gamma^{(2)}}
\]

with the same `k` as the pinned source. For any right-half-plane coefficient
family `a(n,s)`, define its two-range transform by

\[
 \begin{split}
 \mathcal D_x[a](s)=x^{-1/2}\bigg(&
 \sum_{n\le x}a(n,1-\bar s)(x/n)^{1-\bar s}\\
 &+\sum_{n>x}a(n,s)(x/n)^s\bigg).
 \end{split}
\]

This is the arithmetic object appearing after the source contour split, but
here `a=a_2` is the exact convolution-inverse sequence rather than `a_K` from
a finite geometric expansion.

The natural replacement is to compare `Z_{2,x}` and
`mathcal D_x[a_2]` directly in `L2`, after subtracting the explicit
archimedean and diagonal terms. Parseval or Montgomery-Vaughan then has a
chance to preserve cancellation that the failed pointwise bound destroyed.

No searched source provides that comparison for this height-dependent
nonlinear coefficient family. Existing theorems cover fixed Dirichlet
polynomials, fixed products of logarithmic derivatives, or smoothed linear
statistics of the original zeta zeros. None gives a coefficient-order-uniform
mean square for this convolution inverse.

## 6. Minimal new analytic target

The smallest replacement target found here is the following named lemma.

### Uniform Resummed Mean-Square Lemma at level two, URMS2

Assume RH. Fix `epsilon>0` and a compact interval
`K subset (0,1-epsilon)`. Let `x=T^alpha`, `alpha in K`, and let `a_2(n,s)` be
the exact coefficient family above. Let `A_x(s)` denote the explicit
archimedean and diagonal terms obtained from the poles crossed in the same
Cauchy transform.

The lemma has two parts, uniform for `alpha in K`:

\[
 \frac1{T\log T}\int_T^{2T}
 |Z_{2,x}(\sigma+it)-A_x(\sigma+it)
 +\mathcal D_x[a_2](\sigma+it)|^2dt=o(1),
\]

for one, hence every, fixed `5/4<sigma<2`; and

\[
 \frac1{T\log T}\int_T^{2T}
 |\mathcal D_x[a_2](\sigma+it)|^2dt
 =\mathcal F_2(\alpha)+o(1),
\]

after the source's exact diagonal normalization. The second equality includes
all prime powers, unequal convolution lengths, off-diagonal terms, and the
variation of `L,L',L''` across the height interval.

The required convergence is local uniformity in `alpha`. A weighted variant
may replace both suprema by integration against the fixed autocorrelation
`A_v(alpha)` from `window_certificate.py`. That weaker form would be enough
for the downstream window functional.

URMS2 implies the bridge as follows:

1. the first part replaces the invalid pointwise contour tail by an `L2`
   comparison of the full objects;
2. the second part evaluates the resummed arithmetic side without a geometric
   order `B`;
3. Cauchy-Schwarz transfers the first comparison to the smoothed pair
   statistic;
4. the already bounded corrected coefficient tail identifies the resulting
   regular function with `mathcal F_2`.

The most concrete arithmetic subproblem inside URMS2 is a uniform quadratic
mean for `a_2(n,s)`. Montgomery-Vaughan handles the standard off-diagonal
geometry once one has a uniform leading asymptotic and summable error for the
height-dependent diagonal sums. Current fixed-word prime-number-theorem
estimates do not provide that summability.

## 7. Literature mechanism audit

| Source | Mechanism inspected | Why it does not close URMS2 |
|---|---|---|
| [Farmer-Gonek-Lee, arXiv:0803.0425](https://arxiv.org/abs/0803.0425) | fixed geometric expansion, Cauchy explicit formula, Dirichlet-polynomial mean square | contains the nondecaying contour-tail gap and no full-resolvent estimate |
| [Farmer-Gonek-Lee-Lester, QJM 64 (2013)](https://academic.oup.com/qjmath/article/64/4/1057/1567887) | mean products of `zeta'/zeta`, almost-prime coefficient correlations | treats fixed products, not the height-dependent convolution inverse uniformly |
| [Chirre, arXiv:2107.13636](https://arxiv.org/abs/2107.13636) | moments of fixed derivatives of `zeta'/zeta` and pair-correlation equivalences | fixed derivative order does not control the nonlinear denominator |
| [Bourgade-Kuan, arXiv:1203.5328](https://arxiv.org/abs/1203.5328) | early-smoothed explicit formula and mesoscopic linear statistics | the statistic is linear in original zeta zeros and is not the microscopic derivative-zero resolvent |
| [Sodin, arXiv:1611.10037](https://arxiv.org/abs/1611.10037) | critical-point process from convergence of the zeta-zero point process | assumes stronger zero-process convergence and is not an RH-only arithmetic bridge |
| [Fazzari, arXiv:2310.15918](https://arxiv.org/abs/2310.15918) | shifted `zeta'/zeta` mean values with a zeta weight | does not estimate the exact `xi'''/xi''` convolution inverse |
| [Arias de Reyna-Rodgers, arXiv:2311.13441](https://arxiv.org/abs/2311.13441) | equivalences for zeta-zero point-process convergence | supplies no resummed prime-side mean square for derivative zeros |

This search found useful analogies for early smoothing and mean-square
organization, but no lemma with the hypotheses and uniformity above. The
absence of a located repair is a literature-search result, not a claim that no
repair exists.

## 8. Trust boundary and final status

Exact algebra and deterministic computation now cover:

- the untruncated resolvent identity;
- its convolution-inverse coefficient recurrence;
- its reduction to the corrected `Q(z)` object;
- the operator-word mass formula;
- the `4 alpha` elementary absolute-majorant boundary;
- the counterexample to the printed contour-tail estimate.

Classical analysis is still required for:

- the full-resolvent Cauchy transform in `L2`;
- uniform freezing or retention of the archimedean factors;
- the resummed diagonal arithmetic asymptotic;
- prime-power and unequal-length contributions;
- the off-diagonal mean square uniformly in `alpha`.

No completed-CUE or finite-ell output enters this disposition. No corrected
simplicity percentage or zeta rank-trace transfer is opened.

The next named target is URMS2. Reverting to a larger fixed geometric order
would not address it.

## Pinned inputs

- Repository state at audit start:
  `1d850e5838b2226c1948c87ddd3c69e039901c87`.
- Farmer-Gonek arXiv archive SHA-256:
  `f6cdc7b71db06187dac655647e24312843441aa2598e41a3b53834dd1b36822f`.
- Farmer-Gonek main TeX SHA-256:
  `a3a9ac955a9c95d10d36d6b05aae05a79c6408f6e1cdcb8c14fd79f000144fb1`.
- Bian thesis PDF SHA-256:
  `ec1143f4f6c83288b717cfd4cd0aa6cc620f8c68b892f510a2a8d1708f36bfb7`.

## Reproduction

```bash
.venv/bin/python -m pytest -q -n0 hunts/higher_xi/test_higher_xi.py
.venv/bin/python hunts/higher_xi/resummed_bridge.py
```
