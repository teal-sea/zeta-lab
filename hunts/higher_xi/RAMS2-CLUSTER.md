# RAMS2-Cluster: the level-two connected expansion

## Disposition

**Bandwidth update.** `BANDWIDTH-FORENSICS.md` audits the constants used below.
The `rho<=1/10` and `|alpha|<1/100` values in this report are the first
explicit promotion, not final endpoints. A finite-prime peel permits an
arbitrarily small Cauchy radius on the tail-prime Euler product. RAMS2 then
holds on every fixed compact `rho` band, and the current contour architecture
reaches every compact band inside `|alpha|<1/2`.

The level-two arithmetic obstruction has a smaller exact structure than a
general graph gas.

After Borel transformation in Neumann order, the denominator inverse is a
rank-one monomer-dimer model.  Its only non-singleton squarefree atom is the
two-prime term from `A*A`.  After taking the Hadamard square, two matchings are
superposed.  Every connected component is therefore one of:

1. an isolated vertex;
2. an alternating path;
3. an even alternating cycle, with a doubled edge as the size-two cycle.

No other connected graph occurs.  This classification is exact at every
support size.

The resulting all-support-size squarefree majorant is summable.  Repeated
prime supports are handled by the same Gaussian mixture, followed by the
powerful-squarefree split used at level one.  On the explicit coefficient
band

\[
 0<\rho=\frac{\log x}{\lambda_T}\leq \frac1{10},
 \qquad
 \lambda_T=\frac12\log\frac{T}{2\pi},
\]

the frozen level-two square density has scale `x log x`.  The connected term
changes the coefficient, beginning at `pq`; it does not change the logarithmic
order.  Its coefficient is the existing corrected infinite `F2` object,
because the cluster expression is algebraically identical to the rational
`Q(z)` before either side is expanded.

This supplies `RAMS2-Cluster` on a fixed positive band.  Combining it with the
right-line estimates already isolated in `URMS2-ATTACK.md` and the
early-smoothed transfer of `URMS1-CLOSURE.md` gives the same bridge architecture
for level two on every compact `0<|alpha|<1/100`.  The endpoint is deliberately
not optimized.

The band is far too narrow for the existing simplicity window, whose support
reaches about `0.68213`.  No higher-xi percentage follows from this closure.

## 1. Exact inverse without coefficient-order truncation

Use the convolution atoms

\[
 A=\Lambda,\qquad B=\Lambda\log,
\]

and put

\[
 D(z)=(1-Az)^2+Bz^2=1-X(z),
 \qquad
 X(z)=2Az-z^2(A*A+B).
\]

Every coefficient at a fixed integer receives only finitely many convolution
terms.  Hence the formal inverse is exact:

\[
 D(z)^{-1}=\sum_{m\geq0}X(z)^{*m}.
\]

Separating `B` from `(1-Az)^2` gives the first useful closed expansion:

\[
 \boxed{
 D(z)^{-1}
 =\sum_{j,k\geq0}(-1)^j
 {2j+k+1\choose k}z^{2j+k}A^{*k}*B^{*j}.
 }
\]

This is an identity of formal Dirichlet series, not a geometric cutoff.  It
follows from

\[
 \frac1{(1-Az)^2+Bz^2}
 =\sum_{j\geq0}(-1)^jB^{*j}z^{2j}(1-Az)^{-2j-2}.
\]

For distinct primes `p_1,...,p_r`, write `ell_i=log p_i`.  Evaluating the
convolution powers on squarefree support gives

\[
 \boxed{
 b(p_1\cdots p_r)
 =\Bigl(\prod_i\ell_i\Bigr)
 \sum_{j=0}^r(-1)^j
 \frac{j!(r+j+1)!}{(2j+1)!}
 e_j(\ell_1,\ldots,\ell_r)z^{r+j}.
 }
\]

The direct formula, subset-convolution inversion, and the cluster formula in
the next section have zero symbolic defect through five independent prime
labels in `rams2_cluster.py`.

## 2. The correct Borel transform

The level-one mechanism Borel-transforms the Neumann order before taking a
Hadamard square.  The same operation at level two is

\[
 \widehat b_t(z)
 =\sum_{m\geq0}\frac{t^m}{m!}X(z)^{*m}
 =\exp_*(tX(z)),
\]

with the inverse recovered by

\[
 D(z)^{-1}=\int_0^\infty e^{-t}\widehat b_t(z)\,dt.
\]

On a squarefree prime label `p`, define the monomer weight

\[
 m_p(t)=tz\ell_p(2-z\ell_p),
\]

and on two distinct labels define the dimer weight

\[
 d_{pq}(t)=-2tz^2\ell_p\ell_q.
\]

Then, for any finite set `S` of distinct primes,

\[
 \boxed{
 \widehat b_t(S)
 =\sum_{M\text{ matching on }S}
 \prod_{\{p,q\}\in M}d_{pq}(t)
 \prod_{p\notin V(M)}m_p(t).
 }
\]

The formula is immediate from the convolution exponential.  The generator
`X` has squarefree support of size at most two, and the size-two part is
exactly `-z^2 A*A`.

Laplace integration gives an equivalent finite formula:

\[
 \boxed{
 b(S)=z^{|S|}\prod_{p\in S}\ell_p
 \sum_{M}
 (|S|-|M|)!(-2)^{|M|}
 \prod_{p\notin V(M)}(2-z\ell_p).
 }
\]

This is the requested replacement for level-one multiplicativity.  The
disconnected background is the monomer product.  The new connected object is
a dimer.  Larger connected supports arise only after two matching systems are
superposed in the Hadamard square.

There is also a useful rank-one Gaussian form.  With a standard real Gaussian
`G`, formal Gaussian moments give

\[
 \boxed{
 \widehat b_t(z)
 =\mathbb E_G\exp_*\left(
 [2tz+i\sqrt{2t}\,zG]A-tz^2B
 \right).
 }
\]

For each fixed `G`, the exponent is supported on prime powers and its
Dirichlet coefficients are multiplicative.  The entire failure of the
level-one Borel factorization is therefore one rank-one Gaussian covariance.

## 3. The unit test at 6

Let `ell_p=log p` and `ell_q=log q`.  In the squarefree quotient, write

\[
 D=1+f_px_p+f_qx_q+f_{pq}x_px_q,
\]

where

\[
 f_p=-2z\ell_p+z^2\ell_p^2,
 \quad
 f_q=-2z\ell_q+z^2\ell_q^2,
 \quad
 f_{pq}=2z^2\ell_p\ell_q.
\]

### Route 1: direct resolvent

The `x_p x_q` coefficient of `D^-1` is

\[
 -f_{pq}+2f_pf_q.
\]

Thus

\[
 \boxed{
 b(pq)=6z^2\ell_p\ell_q
 -4z^3\ell_p\ell_q(\ell_p+\ell_q)
 +2z^4\ell_p^2\ell_q^2.
 }
\]

### Route 2: convolution recurrence

The exact recurrence

\[
 b(n)=-\sum_{\substack{d\mid n\\d>1}}(D-1)(d)b(n/d)
\]

gives

\[
 b(p)=-f_p,\qquad b(q)=-f_q,
\]

and then the same `-f_pq+2f_pf_q` expression at `pq`.

### Route 3: Borel clusters

Before Laplace integration,

\[
 \widehat b_t(pq)=m_p(t)m_q(t)+d_{pq}(t).
\]

The Borel connected defect is therefore exactly

\[
 \boxed{
 \widehat\kappa_t(p,q)=-2tz^2\log p\log q.
 }
\]

After the common `t` parameter is integrated,

\[
 \boxed{
 \kappa(p,q)=b(pq)-b(p)b(q)
 =z^2\ell_p\ell_q
 \left[2-2z(\ell_p+\ell_q)+z^2\ell_p\ell_q\right].
 }
\]

At `p=2,q=3`, this is the existing `n=6` defect.  The decomposition matters:

\[
 \kappa(p,q)
 =z^2\ell_p\ell_q(2-z\ell_p)(2-z\ell_q)
 -2z^2\ell_p\ell_q.
\]

The first term is covariance from sharing the Laplace parameter.  That effect
already exists in the level-one control and is handled by retaining the Borel
parameters.  The second term is the new `A*A` connected atom.  Treating their
sum as one undifferentiated failure hides the actual level-two obstruction.

## 4. The exact `Q` matching formula

Let `mathcal L` be the coefficient derivation

\[
 (\mathcal Lf)(n)=\log(n)f(n).
\]

It satisfies the convolution Leibniz rule, and

\[
 \mathcal L X=2zB-z^2(2A*B+C),
 \qquad C=\Lambda\log^2.
\]

Hence the corrected arithmetic object can be written

\[
 \begin{aligned}
 Q(z)
 &=-A+(\mathcal LX)D^{-1}\\
 &=-A-\mathcal L\log_*D.
 \end{aligned}
\]

This is the same rational object already stored in `CORRECTED-F2.md`:

\[
 Q(z)=-A+
 \frac{2Bz-(2A*B+C)z^2}{(1-Az)^2+Bz^2}.
\]

Since

\[
 \mathcal L\exp_*(tX)=t(\mathcal LX)\exp_*(tX),
\]

the squarefree coefficient has the finite rooted matching formula

\[
 \boxed{
 Q(S)=-A(S)+\log\!\left(\prod_{p\in S}p\right)
 z^{|S|}\prod_{p\in S}\ell_p
 \sum_M(|S|-|M|-1)!(-2)^{|M|}
 \prod_{p\notin V(M)}(2-z\ell_p).
 }
\]

For `|S|>1`, the `-A(S)` term vanishes.  This formula shows directly why the
full arithmetic coefficient has one global logarithmic mark, just as the
level-one identity `alpha_k(n)=log(n)Lambda_k(n)/k` does.

## 5. Connected graphs in the Hadamard square

Use independent Borel parameters `t,u`.  A term in

\[
 \widehat b_t(S)\widehat b_u(S)
\]

is a pair `(M_t,M_u)` of matchings.  Color their edges by the parameter.  Each
vertex has degree at most two, with at most one incident edge of each color.
Consequently every nontrivial connected component is an alternating path or
an even alternating cycle.

Put

\[
 h_p=2-z\ell_p,
 \qquad
 \mu(C)=z^{2|C|}\prod_{p\in C}\ell_p^2.
\]

For a fixed labelled prime set `C` of size `r`, the sum of every connected
two-color configuration is as follows.

For odd `r>=3`, only paths occur:

\[
 K(C)=(-2)^{r-1}2(r-2)!(tu)^{(r+1)/2}\mu(C)
 \sum_{\{p,q\}\subset C}h_ph_q.
\]

For even `r>=2`, paths contribute

\[
 K_{\rm path}(C)=(-2)^{r-1}(r-2)!(tu)^{r/2}(t+u)\mu(C)
 \sum_{\{p,q\}\subset C}h_ph_q,
\]

and cycles contribute

\[
 K_{\rm cycle}(C)=2^r(r-1)!(tu)^{r/2}\mu(C).
\]

The size-two cycle is the doubled edge selected in both matchings.  Direct
enumeration of all matching pairs agrees symbolically with these formulas for
every labelled support size through six.  This includes a nonzero size-three
path, so discarding clusters above size two is not an admissible simplification.

The decomposition of a pair of matchings into union components is unique.
It supplies the linked-cluster functional without importing a generic graph
ansatz.  A Mayer expansion can be applied after singleton components are
factored, but it is unnecessary for the square-density bound because the
matching pair can be summed directly.

## 6. Uniform squarefree cluster bound

Assume `0<=z log n<=rho_0`.  On the present positive band,

\[
 |2-z\log p|\leq2.
\]

For support size `r`, the number of matchings with `a` edges is

\[
 N(r,a)=\frac{r!}{2^a a!(r-2a)!}.
\]

The absolute one-color rooted matching mass in `Q(S)` is bounded by

\[
 2^rS_r,
 \qquad
 S_r=\sum_{0\leq a\leq r/2}
 N(r,a)2^{-a}(r-a-1)!.
\]

The ratio of consecutive summands is

\[
 \frac{(r-2a)(r-2a-1)}{4(a+1)(r-a-1)}
 \leq\frac{r}{4(a+1)}.
\]

Therefore

\[
 S_r\leq(r-1)!e^{r/4}.
\]

The order-uniform prime-simplex majorant used in `URMS1-CLOSURE.md` gives, for
an absolute `D`,

\[
 \sum_{\substack{p_1\cdots p_r\leq x\\p_i\text{ distinct}}}
 \left(\log(p_1\cdots p_r)\right)^2
 \prod_i(\log p_i)^2
 \leq
 \frac{D^r x(\log x)^{2r+1}}{r!(2r-1)!}.
\]

Combining the last three displays bounds the complete squarefree support-size
`r` contribution by

\[
 x\log x\;c_r(D\rho^2)^r,
\]

where the exact finite matching coefficient is

\[
 \boxed{
 c_r=\frac{4^rS_r^2}{r!(2r-1)!}
 }
\]

and the simpler bound is

\[
 c_r\leq
 \frac{4^re^{r/2}(r-1)!}{r(2r-1)!}.
\]

The successive ratio of the right side is

\[
 4e^{1/2}\frac{r}{2(r+1)(2r+1)}=O(r^{-1}).
\]

Thus

\[
 \sum_{r\geq1}c_r(D\rho^2)^r
\]

converges for every fixed `rho`; in particular it is uniform on the stated
band.  The first exact `c_r` values are

\[
 4,\ 3,\ \frac{49}{45},\ \frac{289}{840},\
 \frac{1681}{18900},\ \frac{11}{560},\ldots
\]

and are emitted by `rams2_cluster.py`.

This bound sums all pairs of matchings.  It does not rely on cancellation of
their signs.  Taking absolute values is safe after the prime-support density
has been retained; taking them before that support split recreates the false
`x(log x)^2` dense-support bound.

## 7. Repeated primes

The Gaussian representation keeps prime powers local.  At one prime, put
`ell=log p`.  Conditional on `G`, the local Euler series is

\[
 \boxed{
 \sum_{e\geq0}\widehat b_t(p^e)u^e
 =\exp\left(
 [2tz+i\sqrt{2t}\,zG]\ell\frac{u}{1-u}
 -tz^2\ell^2\frac{u}{(1-u)^2}
 \right).
 }
\]

Coefficient extraction, Gaussian moments, and the Laplace integral reproduce
the direct `Q(z)` local series at `p^e` for `1<=e<=4` symbolically in the
control code.  The identity itself holds for every `e` by the displayed local
Euler series.

Write each integer uniquely as `n=qm`, where `q` is powerful, `m` is
squarefree, and `(q,m)=1`.  The conditional Gaussian coefficient factors as

\[
 \widehat b_t(qm;G)=\widehat b_t(q;G)
 \prod_{p\mid m}\widehat b_t(p;G).
\]

For the local coefficient at `q`, Cauchy's estimate on `|u|=3/4` gives

\[
 |\widehat b_t(q;G)|
 \leq
 \left(\frac43\right)^{\Omega(q)}
 \exp\left(
 3|2tz+i\sqrt{2t}zG|\log q
 +12tz^2(\log q)^2
 \right).
\]

When `z log q<=rho<=1/10`, averaging the Gaussian absolute exponential costs
at most `2 exp(9rho^2 t)`.  The remaining Laplace exponent is bounded by

\[
 (6\rho+21\rho^2)t\leq0.81t.
\]

The residual `e^{-0.19t}` supplies the same factorial moment bounds as in the
squarefree matching calculation, with a larger absolute constant per support
vertex.  For two Hadamard copies, the powerful weight is dominated by

\[
 \left(\frac{16}{9}\right)^{\Omega(q)}.
\]

Its harmonic mass is finite:

\[
 \sum_{q\text{ powerful}}
 \frac{(16/9)^{\Omega(q)}}q
 =\prod_p\left(
 1+\sum_{e\geq2}\frac{(16/9)^e}{p^e}
 \right)<\infty.
\]

For every fixed `q>1`, the local coefficient tends to zero with `z`, because
each prime in its support requires at least one factor from the exponent.
Dominated convergence against the last harmonic majorant makes every mixed
`q>1,m>1` stratum `o(x log x)`, uniformly on compact subbands of
`rho<=1/10`.

The pure powerful stratum `m=1` is smaller directly.  Powerful integers up to
`x` are `O(sqrt(x))`, and the existing exact level-two envelope on
`rho<1/2` gives `|Q(q)|<=C_rho log q`.  Its square mass is

\[
 O_\rho(\sqrt{x}(\log x)^2)=o(x\log x).
\]

Thus repeated primes do not create a second main logarithm.

The displayed `R=3/4` estimate is not a radius barrier.  Fix any finite
`rho_0`.  Choose a tail radius `0<R<1` for which

\[
 2\frac{R}{1-R}\rho_0
 +\left(\frac{R}{(1-R)^2}+\frac{R^2}{(1-R)^2}\right)\rho_0^2<1/2.
\]

Peel off the finitely many primes `p<=R^-2`.  For `p>R^-2`, the powerful
Hadamard mass

\[
 \prod_{p>R^{-2}}\left(1+
 \sum_{e\geq2}\frac{R^{-2e}}{p^e}\right)
\]

converges.  Give each peeled prime its own radius `R_p>p^-1/2`; its exponent
sum converges, and the total logarithm of the peeled set is fixed.  Since
`z` tends to zero, its extra Laplace rate is `o(1)` and fits in the remaining
half-gap.  The preceding dominated-convergence argument therefore holds on
every fixed compact `rho` band.

## 8. RAMS2-Cluster

For every fixed finite

\[
 0<\rho_{\min}\leq\rho\leq\rho_0,
\]

the frozen exact level-two coefficient family satisfies

\[
 \boxed{
 \mathcal A_{2,T}(x)
 =\sum_{n\leq x}|a_{2,T}(n)|^2
 =x\log x\,\Phi_2(\rho)+o(x\log x),
 }
\]

locally uniformly in `rho`.

For each fixed support size, the prime-simplex asymptotic gives the
corresponding coefficient of `Phi_2`.  The summable `c_r` majorant permits the
support-size limit to pass through the series.  The powerful strata vanish by
the preceding dominated-convergence argument.

The cluster representation and the rational `Q(z)` are the same formal
Dirichlet object.  Therefore the resulting main series is

\[
 \boxed{
 \Phi_2(\rho)=\frac2\rho\,\mathcal F_2(\rho/2),
 }
\]

with the value at zero taken by continuity.  This is an identity of the exact
coefficient mechanisms, not a fit to finite data.  Expanding it recovers the
corrected coefficient fixture through all 40 stored orders; coefficient two
is the corrected value already pinned by `C2_EXTENDED.json`.

The connected `A*A` term enters this `Phi_2`.  It is a leading-coefficient
correction, not an `o(x log x)` term.  What vanishes is the repeated-prime
part after the powerful-squarefree split.

## 9. RC2 parameter choice and the resulting band

The right-line Wiener inverse, Hilbert multiplier, height derivative, and
long-tail estimates for the full level-two resolvent are already recorded in
`URMS2-ATTACK.md`.  The early-smoothed Cauchy transfer in
`URMS1-CLOSURE.md` depends only on those estimates and on a uniform RAMS
input through the upper cutoff `Y=H^beta`.

One explicit non-endpoint choice is

\[
 \alpha_0=\frac1{100},\qquad
 \delta=\frac12,\qquad
 \beta=\frac{11}{500}.
\]

It satisfies

\[
 \frac{2\alpha_0}{\delta}=0.04<0.1,
 \qquad
 \frac{2\beta}{\delta}=0.088<0.1,
 \qquad
 2\alpha_0=0.02<\beta=0.022.
\]

Choosing any sufficiently small positive contour epsilon also gives

\[
 2\alpha_0<\beta(1-2\epsilon).
\]

These are exactly the three inequalities used in the level-one dyadic
assembly: RAMS at the target range, RAMS at the upper cutoff, and decay of the
weighted upper tail.  The central segment, height-freezing commutator,
archimedean derivatives, Montgomery-Vaughan off-diagonal terms, cross-range
phase, and initial height interval retain the same bounds.  The level-two
numerator and denominator remain in their exact resummed form.

Under the hypotheses already stated for the zero-side bridge, this gives
local uniformity on

\[
 \boxed{0<|\alpha|<1/100.}
\]

The regular limiting expression is the corrected `mathcal F_2(alpha)`.

## 10. Falsification controls

The permanent controls now include:

- direct inverse, subset-convolution, and Borel-cluster agreement;
- arbitrary symbolic `pq` and the specialization `n=6`;
- isolation of the Borel pair defect `-2tz^2 log(p)log(q)`;
- enumeration of every two-color matching pair through six labelled primes;
- the alternating-path/even-cycle closed formula;
- nonzero size-three connected support;
- repeated-prime local agreement through `p^4`;
- exact all-support-size majorant coefficients and ratios;
- the pre-existing rational `Q(z)` identity and all 40 corrected coefficients.

The requested lesions separate as follows:

- deleting `A*A` sets the Borel `pq` defect to zero;
- forcing multiplicativity misses the displayed `kappa(p,q)`;
- deleting connected supports above size two misses the size-three path;
- taking a dense all-integer envelope before the support split restores the
  extra logarithm;
- a planted family with support coefficient `r!` in place of `c_r` has
  nonsummable fixed-band mass.

Command:

```bash
.venv/bin/python -m pytest -q hunts/higher_xi/test_higher_xi.py -n0
```

## 11. Source boundary

The path/cycle classification and matching bounds are derived directly from
the exact arithmetic weights.  Generic polymer machinery is not needed for
the main estimate.

For comparison, the hard-core polymer log can be expanded with the
Kotecky-Preiss framework, and Penrose tree identities can replace connected
polymer graphs by trees.  Those tools apply only after the arithmetic
activities above are supplied.  They do not create the `z`, prime-simplex, or
powerful-support savings.  The direct matching sum is sharper here because
the rank-one quadratic atom restricts the physical components to paths and
cycles before any tree bound is taken.

Primary references for the generic comparison:

- R. Kotecky and D. Preiss, *Cluster expansion for abstract polymer models*,
  Communications in Mathematical Physics 103 (1986), 491-498,
  DOI `10.1007/BF01211762`.
- R. Fernandez and A. Procacci, *Cluster expansion for abstract polymer
  models. New bounds from an old approach*, Communications in Mathematical
  Physics 274 (2007), 123-140, arXiv `math-ph/0605041`.

Neither reference supplies the arithmetic theorem.  The load-bearing inputs
remain the exact rank-one reduction, the prime-simplex estimate already used
at level one, and the powerful harmonic majorant above.
