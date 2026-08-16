# Pub 1 source-admissible strong closure

**Status:** exact-rational evidence package for independent review.  This file
strengthens the ambient variational result in
`RESULTS-xiprime-global-optimality.md`.  It does not edit or replace the
publication manuscript.

## Theorem

Let

\[
I=[-1/2,1/2],\qquad
\mathcal H=L^2_{\mathrm{even}}(I;\mathbb R),\qquad
A=I+T_{F_1},
\]

with (F_1), (T_{F_1}), and (c^*) as in
`RESULTS-xiprime-global-optimality.md`.  Thus

\[
c^*=\langle\mathbf1,A^{-1}\mathbf1\rangle,
\qquad w=A^{-1}\mathbf1.
\]

Let \(\mathcal A_{\mathrm{source}}\) be the scalar profiles induced by the
physical windows used in Section 7.1 of the cited source paper, in the
asymptotic sense made explicit below.  Then

\[
\boxed{
\sup_{v\in\mathcal A_{\mathrm{source}}}
\frac{\langle\mathbf1,v\rangle^2}{\langle Av,v\rangle}
=\langle\mathbf1,A^{-1}\mathbf1\rangle=c^*.}
\]

Equivalently, for the reciprocal quotient,

\[
\boxed{
\inf_{v\in\mathcal A_{\mathrm{source}}}
\frac{\langle Av,v\rangle}{\langle\mathbf1,v\rangle^2}
=\frac1{c^*}.}
\]

The quotient orientation is load-bearing.  The maximizing quotient is
\(\langle\mathbf1,v\rangle^2/\langle Av,v\rangle\); its reciprocal is
minimized, not maximized.

## Exact source class

The exact cited version is:

> *More than two thirds of the zeros of the Riemann zeta function lie on the
> critical line*,
> <https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf>.

The relevant locations are:

1. **Proposition 2.1, p. 7, equation (2.7).**  The explicit formula takes
   (C_c^2(\mathbb R)) test functions supported in \([-L/2,L/2]\).
2. **Section 2.2, pp. 7-8, equations (2.11)-(2.14).**  The initial convenient
   realization fixes a nondecreasing (C^3) ramp \(\varrho\), chooses
   (1\leq r\leq L/8\), and sets
   \(\phi(u)=\varrho((L/2-|u|)/r)\).  This produces an even, flat-topped
   endpoint taper with (0\leq\phi\leq1\).
3. **Section 7.1, p. 20, paragraph before (7.1).**  This is the generalized,
   load-bearing class.  It requires
   \[
   \phi\in C_c^2(\mathbb R),\quad \phi\text{ even},\quad 0\leq\phi\leq1,
   \quad\operatorname{supp}\phi=[-L/2,L/2],
   \]
   with \(\phi\) nonincreasing in \(|u|\), and with
   \(\|\phi''\|_1\) and \(\|(\phi^2)''\|_1\) uniformly (O(1)).  Radial
   monotonicity gives \(\|\phi'\|_1,\|(\phi^2)'\|_1\leq2\).
4. **Section 7.1, p. 20, equation (7.3).**  The scalar profile is defined by
   \(\phi^2(u)=v(u/L)\).  There is no integral, peak, or (L^p)
   normalization beyond (0\leq\phi\leq1\).
5. **Theorem D, p. 21, proof after (7.4).**  The ideal profile is realized in
   the limit by multiplying its square root by the fixed-width endpoint ramp
   from Section 2.2.  The change in the scale-free constants is (O(1/L)).
6. **Remark 7.1(iii), p. 22.**  A sharp cutoff makes Proposition 4.2 fail; a
   fixed-width ramp is the minimal repair and costs (O(1/L)).
7. **Remark 7.3, p. 23.**  The same window mechanism is applied to \(\xi'\),
   with the flat and quartic profiles displayed there.

Thus (C^\infty), a flat top, and a particular ramp are not requirements.
The nontrivial source constraint is radial monotonicity.

## Exact strict-concavity bound

Use the exact rational trial polynomial

\[
u(s)=\sum_{j=0}^5c_js^{2j},\qquad
(c_0,\ldots,c_5)=
\left(
\frac{427163}{446844},
-\frac{205089}{684401},
-\frac{2976898}{824779},
-\frac{13369}{15690},
-\frac{104561}{672519},
-\frac{32375}{630751}
\right).
\]

Let (A_0) use the (M=20) kernel truncation, let (E=A-A_0), and put

\[
r_0=\mathbf1-A_0u,\qquad z=w-u.
\]

The existing tail bound is

\[
\rho=\|E\|_{2\to2}\leq
\frac{45088768}{2828846926917599723269509375}
<1.6\times10^{-20}.
\]

The executable evidence reconstructs (A_0u) and (r_0) as exact rational
polynomials.  On \(|s|\leq1/2\), the coefficient absolute-sum bound gives,
with every decimal below interpreted as an outward rational bound,

\[
\|r_0\|_2<7.8749770\times10^{-10},\qquad
\|r_0\|_\infty<2.1710808\times10^{-5},
\]

\[
\|r_0''\|_\infty<0.005982627,qquad
\|u\|_2<0.887972.
\]

Since (Az=r_0-Eu\) and \(\|A^{-1}\|_{2\to2}\leq9/5\),

\[
\|z\|_2
\leq\frac95(\|r_0\|_2+\rho\|u\|_2)
<1.417496\times10^{-9}.
\]

The row bound \(\|T_{F_1}\|_{\infty\to\infty}\leq4/9\) and
\(z=(r_0-Eu)-T_{F_1}z\) similarly give

\[
\|z\|_\infty
\leq\frac95(\|r_0\|_\infty+\rho\|u\|_2)
<3.907946\times10^{-5}.
\]

Distributionally,

\[
F_1''=2\delta_0+q,
\qquad
q(x)=-8+\sum_{k\geq1}d_k|x|^{2k-1},
\qquad d_k=a_k(2k)(2k+1).
\]

The coefficient ratio is exact:

\[
\frac{d_{k+1}}{d_k}=\frac{2(2k+3)}{(2k+1)^2}.
\]

It decreases on the relevant tail.  Hence

\[
\sum_{k>20}d_k
\leq
\frac{666953056256}{23065890935073171953452059375}
<2.90\times10^{-17},
\]

and exact summation gives

\[
8+\sum_{k\geq1}d_k
\leq
\frac{622490816315301203923339889968}
{7688630311691057317817353125}
<80.963.
\]

The delta mass must not be dropped.  Differentiating (Az=r_0-Eu\) twice
gives the pointwise identity

\[
z''=r_0''-(Eu)''-2z-q*z.
\]

The bounds above imply, entirely in rational arithmetic,

\[
\boxed{\|z''\|_\infty
<0.006060899845<\frac{6061}{10^6}.}
\]

All five nonconstant coefficients of (u) are negative, so

\[
u''(s)\leq2c_1=-\frac{410178}{684401}
<-0.5993240804.
\]

Therefore

\[
\boxed{w''(s)=u''(s)+z''(s)<-0.59326318<-\frac{593}{1000}}
\qquad(s\in I).
\]

The kernel equation and the already established positivity give

\[
\frac15\leq w(s)\leq1.
\]

Indeed, the lower bound is the row-bound argument in the ambient theorem;
the upper bound follows from (w=1-T_{F_1}w\), (F_1\geq0\), and (w\geq0\).
Evenness gives (w'(0)=0\).  Strict concavity then gives (w'(s)<0\) for
\(0<s\leq1/2\), so (w\) is strictly decreasing in \(|s|\).

## Explicit source-admissible sequence

Define

\[
\eta(x)=
\begin{cases}
0,&x\leq0,\\
35x^4-84x^5+70x^6-20x^7,&0<x<1,\\
1,&x\geq1.
\end{cases}
\]

On \((0,1)\),

\[
\eta'(x)=140x^3(1-x)^3\geq0.
\]

The first three derivatives glue to zero at both endpoints, so
\(\eta\in C^3(\mathbb R)\).  Exact integration gives

\[
\|\eta''\|_1=\frac{35}{8},\qquad
\int_0^1\eta'(x)^2\,dx=\frac{700}{429},
\]

and therefore

\[
\|(\eta^2)''\|_1
\leq2\int_0^1\eta'(x)^2\,dx+2\|\eta''\|_1
=\frac{20615}{1716}.
\]

For (L\geq8\), set

\[
\phi_L(u)=
\begin{cases}
\sqrt{w(u/L)}\,\eta(L/2-|u|),&|u|\leq L/2,\\
0,&|u|>L/2.
\end{cases}
\]

Every source condition is preserved:

1. (w\in C^2(I)\) follows from the displayed distributional identity and
   the uniformly convergent ordinary part (q\).  Since (w\geq1/5\),
   \(\sqrt w\in C^2(I)\).  Fourth-order endpoint vanishing of \(\eta\) gives
   \(\phi_L\in C_c^2(\mathbb R)\).
2. Both factors are even and nonincreasing in \(|u|\), so the same holds for
   \(\phi_L\).
3. (0\leq\phi_L\leq1\), because (1/5\leq w\leq1\) and
   (0\leq\eta\leq1\).
4. \(\eta(x)>0\) for (0<x<1\), and (w>0\), so
   \(\operatorname{supp}\phi_L=[-L/2,L/2]\) exactly.
5. Radial monotonicity gives
   \(\|\phi_L'\|_1=2\phi_L(0)\leq2\) and
   \(\|(\phi_L^2)'\|_1=2\phi_L(0)^2\leq2\).
6. Put (p=\sqrt w\).  Product-rule estimates give
   \[
   \|\phi_L''\|_1
   \leq\frac{\|p''\|_\infty+4\|p'\|_\infty}{L}
       +\frac{35}{4},
   \]
   and
   \[
   \|(\phi_L^2)''\|_1
   \leq\frac{\|w''\|_\infty+4\|w'\|_\infty}{L}
       +\frac{20615}{858}.
   \]
   The right sides are uniform for (L\geq8\).

The induced scalar profile is

\[
v_L(s)=\phi_L(Ls)^2
=w(s)\eta(L(1/2-|s|))^2.
\]

It differs from (w\) only in two endpoint strips of total length (2/L\).
Since (0\leq w\leq1\),

\[
\boxed{\|v_L-w\|_2^2\leq\frac2L,\qquad v_L\to w\text{ in }L^2(I).}
\]

## Closing the quotient

Boundedness of (A\) gives

\[
|\langle Av_L,v_L\rangle-\langle Aw,w\rangle|
\leq
\|A\|\,\|v_L-w\|_2(\|v_L\|_2+\|w\|_2)\to0.
\]

Also

\[
|\langle\mathbf1,v_L-w\rangle|
\leq\|v_L-w\|_2\to0.
\]

Since \(\langle\mathbf1,w\rangle=\langle Aw,w\rangle>0\),

\[
\frac{\langle\mathbf1,v_L\rangle^2}{\langle Av_L,v_L\rangle}
\longrightarrow
\frac{\langle\mathbf1,w\rangle^2}{\langle Aw,w\rangle}
=\langle\mathbf1,w\rangle=c^*.
\]

The ambient variational theorem supplies the upper bound (c(v)\leq c^*\)
for every source-admissible (v\).  The sequence supplies the reverse
inequality for the supremum.  This proves the theorem.

## Executable evidence and lesions

- `admissible_closure.py` reconstructs the rational trial, residual, kernel
  tails, (L^2\), (L^\infty\), and second-derivative bounds using
  `fractions.Fraction` and exact SymPy polynomials.
- `tests/test_pub1_admissible_closure.py` pins every displayed target, the
  endpoint ramp identities, the uniform product-rule bounds, and the
  (2/L\) convergence rate.
- **Delta lesion:** replacing the coefficient (2\) of \(\delta_0\) by zero
  is rejected before a verdict can be produced.
- **Residual lesion:** multiplying every residual-derived bound by (101\)
  changes the concavity margin from (+0.59326318\) to
  (-0.01282680\), and the verdict becomes false.

Run:

```bash
.venv/bin/python hunts/wide_search/admissible_closure.py
.venv/bin/python -m pytest -q tests/test_pub1_admissible_closure.py
```
