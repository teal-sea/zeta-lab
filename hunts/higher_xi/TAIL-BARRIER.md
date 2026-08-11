# Tail status after the corrected level-2 extension

## Split result

The old coefficient-tail barrier is closed. `CORRECTED-F2.md` gives an exact
majorant for the infinite corrected series and the uniform bandwidth-one bound

\[
\sum_{i>40}|C_{2,i}||\alpha|^i<3.279\mathbin{\cdot}10^{-9},
\qquad |\alpha|\le1.
\]

A different barrier remains: the available source does not justify identifying
that entire coefficient-generated object with the limiting pair form factor of
the zeros of `xi''`. `BRIDGE-CLOSURE.md` identifies the first failed estimate,
not merely an absent uniformity argument.

## First exact obstruction to the bridge

On thesis pages 32-33, the geometric truncation remainder contains

\[
\int_{T_\varepsilon}^{\infty}\frac{dv}{1+(v-t)^2}.
\]

For `t>=T_epsilon` this is at least `1/2`, but the source assigns it
`O((t+2)^-2)`. The unit interval `[t,t+1]` is the smallest obstruction. This
invalidates the explicit-formula remainder used by the later mean square.

Correcting the absolute bound forces geometric order `B=Omega(log T)` on any
fixed positive alpha. The source's fixed-order mean-square error can vanish
only with `B=O(log T/log log T)`. No single order selection satisfies both.

There is also a uniqueness symptom at level one:

Bian's Theorem 1 is stated for every fixed positive integer `B`, with only an
`o_(kappa,B)(1)` remainder, uniformly on `0<|alpha|<1`. At level one, `B=1`
gives

\[
\alpha-4\alpha^2+4\alpha^3,
\]

while `B=2` adds the nonzero term `4\alpha^5/3`. Two distinct polynomials
cannot both be the same limiting function on an open interval with errors that
vanish as `T` tends to infinity. Thus the printed fixed-`B` statement is not a
valid limit-exchange theorem for the infinite series.

The issue is separate from the missing multiplicity factors in the level-2
coefficient table. The level-1 control already exposes it.

## Sharpest current statement

The exact arithmetic now supplies:

1. a rational generating function for every `q_j`;
2. exact `C[2,i]` through index 40 by independent routes;
3. strict sign alternation for every coefficient;
4. an explicit entire majorant for the full coefficient series;
5. a bandwidth-one window tail bound applying to every integrable window.

For the explicit rational window in `window_certificate.py`, the
coefficient-generated object gives the exact conditional inequality

\[
2-D>0.923401526388517\ldots>0.9234015.
\]

It is not a result about zeros of `xi''` until an analytic bridge controls the
terms discarded before or during the explicit-formula and mean-square passage.

## Exact sufficient bridge

Let `A_v` be the autocorrelation of an admissible window. It would suffice to
derive, directly from `xi'''/xi''`, a bound of the form

\[
\limsup_{T\to\infty}
\left|\int A_v(\alpha)
\left(F_2(\alpha,T)-\sum_{i=1}^{J}C_{2,i}|\alpha|^i\right)d\alpha\right|
\le E_J(1)\|v\|_1^2.
\]

At `J=40`, the available coefficient allowance is below `3.279e-9`. The
missing input is therefore not a coefficient-growth estimate. It is a uniform
analytic remainder connecting the arithmetic expansion to the zero statistic.

This is Outcome C at the form-factor bridge, with the coefficient-series part
of the directive completed and the first failed analytic estimate pinned.
