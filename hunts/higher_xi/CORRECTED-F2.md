# The corrected level-2 coefficient object and its remaining bridge

## Result

The corrected coefficients define an absolutely convergent power series on
`|alpha|<=1`. In fact, the majorant below has infinite radius. The first 40
coefficients are exact, and the regular series after index 40 satisfies

\[
 \sum_{i>40}|C_{2,i}|\,|\alpha|^i
 \le E_{40}(\alpha)
 \le E_{40}(1)
 <3.279\mathbin{\cdot}10^{-9}.
\]

The exact value of `E_40(1)` is emitted by `corrected_form_factor.py` and stored
as an exact rational in the window check. Thus the coefficient-generated
object

\[
 \mathcal F_2(\alpha)=\sum_{i\ge1}C_{2,i}|\alpha|^i
\]

is rigorously controlled on the full bandwidth. Its endpoint lies in

\[
4.76344632220668 < \mathcal F_2(1) < 4.76344632876331.
\]

This closes the coefficient-series tail problem. It does not by itself identify
`mathcal F_2` with the limiting pair form factor of the zeros of `xi''`. The
uniform analytic passage missing from the source remains a separate bridge.

## Exact generating mechanism

Use the commutative Dirichlet-convolution atoms

\[
A=\Lambda,\qquad B=\Lambda\log,\qquad C=\Lambda\log^2.
\]

If `q_j` denotes the coefficient of `L^(-j)` in the arithmetic part of
`xi'''/xi''`, then the formal object

\[
Q(z)=\sum_{j\ge0}q_jz^j
\]

has the rational expression

\[
Q(z)=-A+
\frac{2Bz-(2A*B+C)z^2}{(1-Az)^2+Bz^2}.
\]

Equivalently, for `n>=1`,

\[
\begin{split}
q_n={}&2\sum_{j=0}^{\lfloor(n-1)/2\rfloor}
(-1)^j {n-1\choose2j}A^{*(n-1-2j)}*B^{*(j+1)}\\
&-\sum_{j=0}^{\lfloor(n-2)/2\rfloor}
(-1)^j {n-1\choose2j+1}A^{*(n-2-2j)}*B^{*j}*C.
\end{split}
\]

`exact_c2.py` regenerates this sequence in three independent ways: the
successive logarithmic-derivative recurrence, the direct operator-word
expansion, and this closed binomial expression. They agree exactly through
index 40. Two separate compressed mean-square calculations also agree exactly.

Every word `beta` in `q_n` has entries in `{0,1,2}` and satisfies

\[
\operatorname{len}(\beta)+|\beta|=n+1,
\qquad
\operatorname{sgn}[q_n(\beta)]=(-1)^{n-\operatorname{len}(\beta)}.
\]

In a nonzero pairing contributing to `C[2,i]`, the two words have equal
length and their powers sum to `i-1`. Hence every summand has the same sign,

\[
\operatorname{sgn} C_{2,i}=(-1)^{i-1}.
\]

This is an exact structural statement, not an observed sign pattern.

## Exact coefficient fixture

The formula is

\[
C_{2,i}=2^{i-1}\sum_{p+q=i-1}\langle q_p,q_q\rangle.
\]

For paired words `beta,delta` of equal length `r`, the weighted-degree
identity reduces the denominator in the mean-square constant to exactly `i!`:

\[
2r+|\beta|+|\delta|-1=i.
\]

`C2_EXTENDED.json` stores indices 1 through 40 as reduced rationals. It also
stores the integers

\[
C_{2,i}\,i!/2^{i-1},
\]

which give a compact independent serialization check. Indicative generation
cost on the recorded machine was `0.08 s, 2.13 MB` through index 20 and
`1.40 s, 34.15 MB` through index 40. These timings are not part of the
mathematical claim.

## Tail majorant

For exponents `a,b` in `{0,1,2}`, set

\[
w_0=1,\qquad w_1=5/2,\qquad w_2=11.
\]

All nine inequalities

\[
(a+b+1)!\le w_aw_b
\]

hold by direct rational comparison. Therefore the factorial permanent for two
length-`r` words is at most

\[
r!\,w(\beta)w(\delta).
\]

The checker retains the exact word length in this bound through index 101.
For the remainder, put `n=i-1`,

\[
R=\lfloor n/2\rfloor,\quad
L=\lceil n/4\rceil,\quad
M=R-L+1,\quad a=5/2,\quad K=47/4.
\]

The binomial formula, `binom(n,j)<=2^n`, and monotonicity of `r!a^(-2r)`
give, for `i>=26`,

\[
|C_{2,i}|\le B_i=
\frac{(n-1)M4^nK^2a^{n-2-2R}R!}{(n+1)!}.
\]

The two-step ratio `B_(i+2)/B_i` splits into four exact rational expressions
according to `n mod 4`. Their successive differences have numerators

\[
\begin{array}{c|l}
0&-32\\
1&-2(16m^4+64m^3+88m^2+46m+7)\\
2&-8(16m^3+100m^2+176m+87)\\
3&-32(8m^3+36m^2+52m+25),
\end{array}
\]

over positive denominators. Each residue-class ratio therefore decreases. The
largest starting value for `n>=101` is

\[
\rho=\frac{5202}{64375}<0.081.
\]

The two parity tails are consequently geometric. The exact bound used by the
checker is

\[
E_{40}(\alpha)=
\sum_{i=41}^{101}U_i\alpha^i+
\frac{B_{102}\alpha^{102}+B_{103}\alpha^{103}}
{1-\rho\alpha^2},
\]

where `U_i` is the exact length-retaining permanent majorant. The same ratio
tends to zero, so the regular coefficient series is entire as a complex power
series.

## Direct weighted consequence

For an integrable window `v` with autocorrelation `A_v`, the bandwidth-one
tail contributes at most

\[
E_{40}(1)\int_{-1}^{1}|A_v(u)|\,du
\le E_{40}(1)\|v\|_1^2.
\]

`window_certificate.py` uses the exact rational window

\[
v(s)=P_0(2s)-\frac{185616}{10^6}P_2(2s)
-\frac{111471}{10^6}P_4(2s)
-\frac{20783}{10^6}P_6(2s).
\]

Since `|P_j(x)|<=1`, this window has the exact positive floor
`68213/100000`, integral one, and `L1` norm one. Exact polynomial integration
of the first 40 terms gives

\[
D_{40}=1.0765984703331668\ldots.
\]

Adding the full tail allowance gives

\[
D<1.076598473611483\ldots,
\qquad
2-D>0.923401526388517\ldots>0.9234015.
\]

The floating window optimizer finds `0.923401531890862`; its gap above the
exact rational lower calculation is `5.51e-9`, split between window rounding
and the uniform tail allowance.

This is an exact conditional calculation for the coefficient-generated
object. It is not yet a ξ'' simplicity result because the bridge in the next
section remains open.

## The remaining analytic bridge

Bian's printed fixed-`B` statement cannot be used as a uniform tail theorem.
For level one, `B=1` already gives the polynomial

\[
\alpha-4\alpha^2+4\alpha^3,
\]

while `B=2` adds the nonzero term `4\alpha^5/3`. Both cannot equal the same
limiting form factor with only an `o_B(1)` error on a fixed open alpha
interval. This inconsistency exists before the level-2 coefficient correction.

What is still required is one of the following:

1. a corrected explicit-formula theorem with a remainder uniform in `B`;
2. a direct mean-square derivation whose discarded arithmetic terms are
   bounded by the coefficient majorant above;
3. a weighted version of that derivation controlling the full admissible
   window functional.

A sufficient theorem schema is

\[
\limsup_{T\to\infty}
\left|\int r(\alpha)
\left(F_2(\alpha,T)-\sum_{i=1}^{J}C_{2,i}|\alpha|^i\right)d\alpha\right|
\le E_J(1)\|v\|_1^2,
\]

for the autocorrelation kernel generated by every admissible `v`. At `J=40`,
the right side for the explicit rational window is below `3.279e-9`.

Until such a bridge is derived, the strict `0.9234015` number remains a
conditional consequence of identifying the actual form factor with
`mathcal F_2`, not a promoted statistic for zeros of `xi''`.

## Independent numerical falsifiers

The corrected object was compared without rescaling to both existing oracles.
For completed CUE at `N=48`, 200 fresh fixed-seed samples gave:

| alpha | corrected object | CUE level 2 | Monte Carlo SE |
|---:|---:|---:|---:|
| 0.125 | 0.03964415 | 0.03902832 | 0.00264343 |
| 0.250 | 0.01706969 | 0.01723648 | 0.00127582 |
| 0.375 | 0.00518741 | 0.00492219 | 0.00035914 |
| 0.500 | 0.00252579 | 0.00252449 | 0.00021506 |

All four raw discrepancies are below one reported Monte Carlo standard error.
The same run includes level-0 and Farmer-Gonek-Lee level-1 controls.

For the direct Dirichlet recurrence at `ell=14`, the raw cumulative values are
still below their limiting controls:

| alpha | corrected integral | direct level 2 | FGL integral | direct level 1 |
|---:|---:|---:|---:|---:|
| 0.125 | 0.00388600 | 0.00305029 | 0.00545332 | 0.00443256 |
| 0.250 | 0.00749860 | 0.00616034 | 0.01437786 | 0.01226302 |
| 0.375 | 0.00870748 | 0.00729079 | 0.02041118 | 0.01801370 |
| 0.500 | 0.00917264 | 0.00776788 | 0.02448689 | 0.02211235 |

No ad hoc rescaling is applied. The finite-`ell` deficit remains visible in
both levels. These comparisons do not supply the missing analytic bridge.

## Reproduction

```bash
.venv/bin/python hunts/higher_xi/exact_c2.py --max-index 40
.venv/bin/python hunts/higher_xi/corrected_form_factor.py
.venv/bin/python hunts/higher_xi/window_certificate.py
.venv/bin/python hunts/higher_xi/cue_oracle.py --sizes 24:200,32:200,48:200
.venv/bin/python hunts/higher_xi/dirichlet_recurrence.py --ells 8,10,12,14
.venv/bin/python -m pytest -q hunts/higher_xi/test_higher_xi.py -n0
```
