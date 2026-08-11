# URMS1 closure: a positive-band level-one bridge

## Disposition

This phase reaches **Outcome B: level one repaired, level two blocked**.

Assuming RH, the exact resummed level-one arithmetic square density has the
`x log x` scale on every compact coefficient band `r<1`. An early-smoothed
right-line contour argument then gives the level-one zero-statistics bridge on
every compact

\[
 0<|\alpha|<\frac14.
\]

The limiting regular expression agrees with the infinite Farmer-Gonek-Lee
coefficient object. The printed finite-order contour argument is not used.

The level-two lift stops at a new, exact obstruction. Its frozen denominator

\[
 (1-Az)^2+Bz^2
\]

contains the connected two-prime atom `A*A` already at `n=6`. The level-one
Borel transform is multiplicative; the level-two transform is not. A uniform
Hadamard cluster estimate for this connected atom is the named missing input
`RAMS2-Cluster`. No URMS2 or statement about actual zeros of `xi''` is claimed.

## 1. Normalization

Put

\[
 \lambda_T=\frac12\log\frac{T}{2\pi},\qquad z_T=\lambda_T^{-1},
\]

and define the full frozen level-one coefficient family

\[
 a_T(n)=-\Lambda(n)+
 \sum_{k\geq1}z_T^k\alpha_k(n),
 \qquad
 \alpha_k=\Lambda_{k-1}*(\Lambda\log).
\]

The sum terminates at `k=Omega(n)`. No geometric order is chosen.

For `y>=2`, write

\[
 \mathcal A_T(y)=\sum_{n\leq y}|a_T(n)|^2,
 \qquad r_y=\frac{\log y}{\lambda_T}.
\]

The coefficient band `r_y<1` corresponds to `y<T^(1/2+o(1))`.

## 2. RAMS1 theorem

For every fixed `0<r_min<=r_0<1`, uniformly for
`r_min<=r_y<=r_0`,

\[
 \boxed{
 \mathcal A_T(y)=
 y\log y\,\Phi_1(r_y)+o(y\log y),
 }
\]

where

\[
 \Phi_1(r)=1-2r+
 2\sum_{j\geq1}\frac{(j-1)!}{(2j)!}r^{2j}.
\]

The series is entire in `r`. The restriction `r_0<1` enters the uniform
resolvent bounds, not the limiting coefficient series.

### 2.1 Exact coefficient symmetry

The algebraic starting point is

\[
 \alpha_k(n)=\frac{\log n}{k}\Lambda_k(n).
\]

It follows by marking one of the `k` identical convolution positions. This
identity is checked independently by formal polynomials in `rams1.py`.

### 2.2 Unique support split

Every integer has a unique factorization

\[
 n=qm,
\]

where `q` is powerful, every prime exponent in `q` is at least two, `m` is
squarefree, and `(q,m)=1`. Put `j=omega(m)`.

Let

\[
 B_{q,j}(z)=
 \sum_{h\geq0}\binom{j+h-1}{h}z^h\Lambda_h(q).
\]

This is the coefficient at `q` in `(1-zA)^(-j)`, with
`A(s)=sum Lambda(n)n^(-s)`. For `j>=1`, the positive part of `a_T(qm)` factors
exactly as

\[
 \boxed{
 \sum_{k\geq1}z^k\alpha_k(qm)
 =(j-1)!z^j\log(qm)
 \prod_{p\mid m}\log p\,B_{q,j}(z).
 }
\]

`powerful_split_coefficient_defects()` checks this formula on every eligible
integer through 55.

### 2.3 Squarefree main term

For `q=1`, `B_(1,j)=1`. The weighted squarefree prime-simplex asymptotic is

\[
 \sum_{\substack{m\leq y\\m\text{ squarefree}\\\omega(m)=j}}
 (\log m)^2\prod_{p\mid m}(\log p)^2
 \sim
 \frac{y(\log y)^{2j+1}}{j!(2j-1)!}.
\]

After multiplication by `(j-1)!^2 z^(2j)`, this gives

\[
 2\frac{(j-1)!}{(2j)!}y\log y\,r_y^{2j}.
\]

Chebyshev's estimate for `sum_(p<=e^u)(log p)^2` gives the order-uniform
majorant

\[
 \frac{D^j y(\log y)^{2j+1}}{j!(2j-1)!}
\]

for an absolute `D`. Its normalized successive-term ratio is asymptotic to
`D r_0^2/(4j)`. Dominated convergence therefore sums all depths uniformly.

The `j=1` prime stratum includes the explicit `-Lambda` term and gives

\[
 y\log y(1-2r_y+r_y^2)+O(y).
\]

### 2.4 Mixed repeated-prime strata vanish

For `q<=y` and `r_y<=r_0<1`, the elementary convolution bound gives

\[
 0\leq B_{q,j}(z)
 \leq\sum_{h\geq0}\binom{j+h-1}{h}r_0^h
 =(1-r_0)^{-j}.
\]

For each fixed powerful `q>1`, `B_(q,j)(z_T)` tends to zero because its
constant coefficient vanishes.

Every powerful integer has a representation

\[
 q=a^2b^3,
\]

with `b` squarefree. Consequently

\[
 \sum_{q\text{ powerful}}\frac1q
 \leq\zeta(2)\zeta(3)<\infty.
\]

The squarefree prime-measure majorant and dominated convergence now give

\[
 \sum_{\substack{qm\leq y\\q>1,\ j\geq1}}
 |a_T(qm)|^2=o(y\log y)
\]

uniformly on the compact band. The remaining `j=0` powerful integers are at
most `O(sqrt(y))` in number, while

\[
 |a_T(q)|\leq C_{r_0}\log q.
\]

Their total is `O_(r_0)(sqrt(y)(log y)^2)=o(y log y)`.

This completes the full frozen arithmetic asymptotic. The extra logarithm in
the old majorant came from charging a prime-supported logarithmic envelope to
all integers.

### 2.5 Height-dependent coefficients

On `t in [T,2T]`, the archimedean logarithm differs from `lambda_T` by `O(1)`
and its reciprocal differs by `O(lambda_T^(-2))`. Inside `r<=r_0`,
differentiating the exact resolvent gives

\[
 |a_1(n,t)-a_T(n)|\leq C_{r_0}.
\]

The square sum of this difference is `O(y)`. Cauchy-Schwarz with the frozen
RAMS1 bound makes the cross term `O(y sqrt(log y))=o(y log y)`. RAMS1 therefore
holds for the exact height-dependent family as well.

## 3. RC1 without the false contour tail

Assume RH. Fix `5/4<sigma<2`, put `s=sigma+it`, and choose the right contour
line `w=c+iv` with `c=1/2+epsilon` and `0<epsilon<1/8`.

The exact zero-side contour identity is retained before inserting any
Dirichlet expansion. Its right-line arithmetic term contains

\[
 k(w,s)=\frac{2\sigma-1}
 {(w-(s-1/2))(w-(1/2-\bar s))}.
\]

Put

\[
 A=\sigma-\frac12-c,
 \qquad B=\sigma-\frac12+c.
\]

For `u=v-t`, the exact partial fraction is

\[
 k(c+i(t+u),s)=
 \frac1{-A+iu}-\frac1{B+iu}.
\]

The Fourier transforms of these two terms are one-sided exponentials. After
the extra `n^(-1/2)` in the logarithmic-derivative series is included, they
select exactly

\[
 (x/n)^{1-\bar s}\quad(n\leq x),
 \qquad
 (x/n)^s\quad(n>x).
\]

The symbolic defects of the partial fraction and both exponents are zero in
`rams1.py`.

Thus the two-range transform is obtained by Fourier localization on the
original right line. No coefficient is continued across the strip, no finite
geometric polynomial is introduced, and no artificial poles at zeros of `L`
are crossed.

## 4. RC1 error decomposition

Let

\[
 \mathcal D_{T,x}(s)=x^{-1/2}\left(
 \sum_{n\leq x}a_T(n)(x/n)^{1-\bar s}
 +\sum_{n>x}a_T(n)(x/n)^s
 \right).
\]

After the explicit archimedean and pole contribution `P_(T,x)` is removed,
the early-smoothed contour identity gives

\[
 Z_{1,x}(s)=P_{T,x}(s)+\mathcal D_{T,x}(s)+E_{T,x}(s).
\]

For every compact `0<alpha_min<=alpha<=alpha_0<1/4`, with `x=T^alpha`,

\[
 \boxed{
 \int_T^{2T}|E_{T,x}(\sigma+it)|^2dt=o(T\log T)
 }
\]

uniformly in `alpha`. The error classes are as follows.

### 4.1 Central right-line segment

The exact resolvent is used on the bounded central segment where its
Dirichlet series is not inserted. Since `t` is of size `T`, the Cauchy kernel
has quadratic separation. Its contribution is

\[
 O_\epsilon(x^{1/2+\epsilon}/T)
\]

pointwise, hence negligible in the displayed square mean.

### 4.2 Height-freezing commutator

The exact weighted Wiener derivative of the right-line inverse is `O(1/T)` on
`[T/2,3T]`. Before taking absolute values, subtract the frozen coefficient
inside the Cauchy integral. The local first-moment kernel mass is exactly

\[
 \int_{-R}^{R}\frac{|u|}{1+u^2}du=\log(1+R^2).
\]

With `R` proportional to `T`, the commutator is

\[
 O_\epsilon(x^{1/2+\epsilon}\log T/T)
\]

pointwise. The complement of the local height interval uses the quadratic
Cauchy tail and is smaller. This is the cancellation lost by the historical
absolute contour estimate.

### 4.3 Archimedean derivative

The omitted `L'/(L+g)` part has weighted Wiener norm
`O(1/(T log T))`. Its convolution satisfies the same commutator estimate and
is negligible separately.

### 4.4 Infinite upper Dirichlet range

Choose constants

\[
 2\alpha_0<\beta<\frac12
\]

and then choose `epsilon>0` small enough that

\[
 2\alpha_0<\beta(1-2\epsilon).
\]

RAMS1 applies through `Y=T^beta`. On the fixed right line, the full inverse has
bounded weighted Hilbert norm. Therefore

\[
 \sum_{n>Y}|a_T(n)|^2n^{-3}
 \ll_\epsilon Y^{-1+2\epsilon}.
\]

After multiplication by `x^2`, this is `o(log T)` by the displayed choice of
parameters. This is the step that currently restricts the clean RC1 band to
`alpha<1/4` rather than the full RAMS1 coefficient band `alpha<1/2`.

### 4.5 Dirichlet mean-value off-diagonal

Truncate the upper range at `Y`. Montgomery-Vaughan applies to both finite
ranges. The lower-range relative error is `O(x/T)` and the upper-range error
is `O(Y/T)`. Both vanish. The cross-range phase contains `log(mn)` rather than
`log(m/n)` and integration by parts makes it smaller. No fixed convolution
depth enters these estimates.

### 4.6 From dyadic height to the source normalization

The local estimate above is stated on `[T,2T]`, while the source statistic
counts ordinates up to one height `H`. Fix `alpha_0<1/4` and choose

\[
 4\alpha_0<\delta<1,
 \qquad
 2\alpha_0<\beta<\frac\delta2.
\]

Then take `epsilon>0` small enough that
`2 alpha_0<beta(1-2 epsilon)`.

The interval `[H^delta,H]` is partitioned dyadically. On a block of height
`U>=H^delta`, with `x=H^alpha`, both required coefficient ratios satisfy

\[
 \frac{\log x}{\tfrac12\log U}
 \leq\frac{2\alpha_0}{\delta}<1,
 \qquad
 \frac{\log H^\beta}{\tfrac12\log U}
 \leq\frac{2\beta}{\delta}<1.
\]

Thus the same RAMS1 and upper-tail bounds hold on every block, and their
geometric sum has the stated `o(H log H)` size. The omitted initial interval
`[0,H^delta]` contributes `O(H^delta(log H)^3)` by the standard local zero
count and the integrability of the Cauchy weight. This is `o(H log H)`.

The main terms have the top-height normalization as well. For each fixed
dyadic offset, `U=H/2^j` satisfies `log U/log H -> 1`, so its coefficient
ratio tends to `2 alpha`. Blocks with unbounded offset have geometrically
vanishing total length. The uniform RAMS1 majorant permits dominated summation
over the blocks. Hence the assembled regular term is `mathcal F_1(alpha)`, not
a block-dependent average.

The inequalities selecting `delta,beta` are simultaneously feasible exactly
for the present argument when `alpha_0<1/4`. This supplies the source's
`0<gamma,gamma'<=H` normalization rather than only a dyadic surrogate.

## 5. Rebuilt level-one bridge

Combining RAMS1 and RC1 with the standard zero-side square identity gives the
following independent level-one statement.

### URMS1 theorem

Assume RH. For every compact `K subset (0,1/4)`, locally uniformly for
`alpha in K`,

\[
 F_1(\alpha,T)=
 (1+o(1))T^{-2\alpha}\log T+\mathcal F_1(\alpha)+o(1),
\]

where

\[
 \boxed{
 \mathcal F_1(\alpha)=
 \alpha-4\alpha^2+
 \sum_{j\geq1}\frac{(j-1)!}{(2j)!}(2\alpha)^{2j+1}.
 }
\]

Symmetry supplies negative `alpha`. The convergence mode is local uniformity
away from the spike at zero. The spike comes from the explicit archimedean
term; the regular expression is the Stieltjes transform of `Phi_1`.

This agrees exactly with the infinite Farmer-Gonek-Lee coefficient
prediction. It does not validate their printed fixed-order remainder. The new
argument uses the full resolvent throughout.

## 6. Why the lift stops at level two

The frozen level-two arithmetic resolvent is

\[
 -A+\frac{2Bz-(2A*B+C)z^2}
 {(1-Az)^2+Bz^2}.
\]

At level one, the Borel family

\[
 E_\tau=\exp(\tau A)
\]

is multiplicative, and the powerful-squarefree split isolates every repeated
prime correction in a finite harmonic-mass kernel.

At level two the denominator contains

\[
 A*A+B.
\]

The `A*A` coefficient at `6=2*3` is nonzero. It couples two distinct primes
inside one denominator atom. Consequently the exponential or Laplace
resummation is not multiplicative even on coprime inputs. The smallest exact
defect is already recorded by `level_two_multiplicativity_defect()`.

The missing level-two theorem is:

### RAMS2-Cluster

Construct a connected-cluster expansion for the Hadamard square of the full
inverse of `(1-Az)^2+Bz^2` and show that every connected cluster containing a
repeated or coupled-prime atom contributes `o(x log x)` uniformly on one fixed
band `0<alpha<=alpha_0<1/4`.

Equivalently, produce a summable majorant for the connected two-prime local
kernel which replaces the multiplicative powerful-number harmonic bound used
at level one.

No searched fixed-product mean-value theorem supplies this resummed connected
cluster estimate. RC2 can reuse the early-smoothed Cauchy architecture once
RAMS2-Cluster is available, but the arithmetic gate comes first.

## 7. Hostile controls

The closure passes the following separations:

1. Replacing the Cauchy convolution by the historical pointwise tail estimate
   still fails on the permanent unit-interval counterexample.
2. Taking absolute values before the height commutator loses the
   `log(T)/T` factor.
3. The dense-support toy retains true `x(log x)^2` growth.
4. Removing prime powers changes only a lower-order stratum.
5. Truncating convolution depth is unnecessary and is not used.
6. The upper Dirichlet tail exposes the `alpha=1/4` endpoint rather than
   silently extending the theorem to `alpha=1/2`.
7. The level-two coprime defect prevents reuse of the multiplicative proof.

## 8. Trust boundary and commands

Exact algebra and finite combinatorics are checked by:

```bash
.venv/bin/python -m pytest -q hunts/higher_xi/test_higher_xi.py -n0
```

The exact layer identities, powerful-squarefree decomposition, Borel
multiplicativity, Cauchy partial fraction, two-range exponents, and planted
failures are in that suite.

The prime-measure asymptotic, dominated-convergence passage, contour edge
bounds, and Montgomery-Vaughan estimate are classical analytic inputs. The
argument above states where each enters and does not ask Python to supply an
asymptotic limit.

## 9. Pinned sources

- Repository state at the start of this closure: `08a61240e7dc1008ffb67e30bf05f23fe9ed45b4`.
- [Farmer, Gonek, and Lee, arXiv:0803.0425](https://arxiv.org/abs/0803.0425), used for the finite-height normalization, zero-side square identity, and fixed-depth prime asymptotics, not for its disputed contour remainder.
- [Montgomery and Vaughan, Hilbert's inequality](https://doi.org/10.1112/jlms/s2-8.1.73), used for the frozen finite Dirichlet-polynomial mean value.
- Farmer-Gonek source archive SHA-256: `f6cdc7b71db06187dac655647e24312843441aa2598e41a3b53834dd1b36822f`.
- Farmer-Gonek TeX SHA-256: `a3a9ac955a9c95d10d36d6b05aae05a79c6408f6e1cdcb8c14fd79f000144fb1`.

No higher-derivative percentage or zeta rank-trace transfer is opened by this
result.
