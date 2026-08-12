# Level-two bandwidth forensics

**Half-band update.** `URMS2-051.md` retains the individual `log n` spacings
and the exact two-range coefficient weights in the finite mean square. Its
off-diagonal error is `O(x log x)`, independent of the far cutoff length. This
removes `gamma<delta`, reaches bandwidth `0.51`, and opens the first corrected
conditional xi-double-prime simplicity statement.

## Disposition

The promoted endpoint `1/100` was not a theorem boundary.  It was the result
of one convenient dyadic parameter choice.

Four successive ranges are now separated.

1. The proof as written in `RAMS2-CLUSTER.md`, with its tail split unchanged,
   works on every compact band

   \[
   0<|\alpha|<\frac1{40}.
   \]

2. Inserting the already available pointwise coefficient envelope between the
   RAMS2 range and the far Hilbert tail extends the bridge to

   \[
   0<|\alpha|<\frac1{20}.
   \]

3. The repeated-prime estimate in `RAMS2-CLUSTER.md` fixed the local Cauchy
   radius at `3/4`.  Optimizing that radius, without changing the cluster
   representation, extends RAMS2 to every

   \[
   0<\rho<\rho_*,
   \qquad
   \rho_*=0.1454524603084045\ldots,
   \]

   and the bridge to every compact

   \[
   \boxed{0<|\alpha|<\rho_*/2
   =0.0727262301542022\ldots.}
   \]

   The round milestone `|alpha|<0.07` has an entirely rational parameter
   witness.

4. The apparent condition `R>1/sqrt(2)` comes only from applying the same
   Cauchy radius to the prime `2` and the entire Euler product.  Peel off the
   finitely many primes `p<=R^-2`, then use radius `R` on the remaining
   primes.  Since `E_R(rho)` tends to zero with `R`, RAMS2 holds on every
   fixed compact `rho` band.  The current contour architecture consequently
   reaches every compact band

   \[
   \boxed{0<|\alpha|<\frac12.}
   \]

The first requested checkpoint not reached is now `0.50`, as a strict
endpoint.  The binding conditions are `2alpha<gamma` for the far tail and
`gamma<delta<1` for the finite mean value.  The squarefree path/cycle series
and the powerful support no longer bind at any fixed `rho`.

No corrected xi-double-prime simplicity theorem follows on the enlarged
band.  Cauchy-Schwarz, an exact operator-norm bound, and completion of squares
exclude every admissible spectral-factor window through bandwidth `1/2`.  A
constant window works at `0.51`.  Current exact downstream bounds are

\[
 \boxed{\frac12\leq\beta_{\rm useful}
 \leq\frac{51}{100}.}
\]

The upper bound uses the normalized constant window at bandwidth `0.51` and
gives the exact positive conditional lower value

\[
 0.0147728663285376\ldots.
\]

Thus the next useful target is not the historical `0.68213`.  The current
bridge ends exactly where a useful window first becomes possible.  The first
exact candidate is at `0.51`.  Reaching it requires a stronger far-tail norm
or a long-polynomial mean-value replacement, as stated in section 11.

## 1. The map from alpha to rho

Let the source height be `H`, the Fourier scale be

\[
 x=H^\alpha,
\]

and discard the initial interval below `H^delta`, where `0<delta<1`.  On a
dyadic block of height `U>=H^delta`, the frozen archimedean parameter is

\[
 \lambda_U=\frac12\log\frac{U}{2\pi}.
\]

Therefore the coefficient ratio entering RAMS2 is

\[
 \rho_x(U)=\frac{\log x}{\lambda_U}
 =\frac{2\alpha\log H}{\log U+O(1)}.
\]

At top height `U` comparable with `H`, this tends to `2 alpha`.  Uniformly on
all retained dyadic blocks,

\[
 \boxed{\rho_x(U)\leq\frac{2\alpha}{\delta}+o(1).}
\]

There is no factor ten in this identification.  The arithmetic band
`rho<0.1` naturally permits `alpha<0.05` before any tail estimate is imposed.

If an upper arithmetic cutoff is `Y=H^beta`, its coefficient ratio is

\[
 \rho_Y(U)\leq\frac{2\beta}{\delta}+o(1).
\]

If a second envelope cutoff is `W=H^gamma`, its ratio is similarly at most
`2 gamma/delta`.

## 2. Dependency graph

| Obligation | Exact inequality | Proved input | Margin source | Status before this pass |
|---|---:|---:|---|---|
| RAMS2 at `x` | `2 alpha/delta < rho_R` | `rho_R=0.1` | `rho_R-2alpha/delta` | structural |
| RAMS2 at `Y` | `2 beta/delta < rho_R` | `rho_R=0.1` | `rho_R-2beta/delta` | structural |
| old far tail | `2alpha < beta(1-2epsilon)` | `H^2_(1+epsilon)` | `beta(1-2epsilon)-2alpha` | non-sharp |
| intermediate shell | `alpha<beta` | `A(u)<=Cu(log u)^2` for `rho<1/2` | `beta-alpha` | available but unused |
| envelope at `W` | `2gamma/delta<1/2` | level-two pointwise envelope | `1/2-2gamma/delta` | available but unused |
| far tail after `W` | `2alpha<gamma(1-2epsilon)` | `H^2_(1+epsilon)` | `gamma(1-2epsilon)-2alpha` | nonbinding after shell |
| finite mean value | `max(alpha,beta,gamma)<delta` | Montgomery-Vaughan | exponent differences | nonbinding |
| initial interval | `delta<1` | `O(H^delta(log H)^3)` | `1-delta` | strict endpoint only |
| central segment | `alpha(1/2+epsilon)<1` | pointwise kernel separation | exponent difference | nonbinding |
| height commutator | same | `O(x^(1/2+epsilon)log H/H)` | exponent difference | nonbinding |
| archimedean derivatives | same | Wiener norm `O(1/(H log H))` | exponent difference | nonbinding |
| Borel/Laplace core | `E_R(rho)<1`, `p>R^-2` on tail primes | finite-prime peeling | choose `R` for each compact `rho` band | nonbinding after split |
| squarefree clusters | fixed `rho` | matching majorant ratio `O(1/r)` | factorial suppression | nonbinding |
| Hadamard square | same support band | two matching systems | included above | nonbinding |
| contour localization | `epsilon>0`, retained right line | early smoothing | exact Fourier support | nonbinding |

`bandwidth_forensics.py` emits the same graph as machine-readable records.

## 3. Where 0.1 became 0.01

The previous report chose

\[
 \alpha_0=0.01,\qquad \delta=0.5,\qquad \beta=0.022.
\]

The inequalities checked there were

\[
 \frac{2\alpha_0}{\delta}=0.04<0.1,
 \qquad
 \frac{2\beta}{\delta}=0.088<0.1,
 \qquad
 2\alpha_0=0.02<\beta=0.022.
\]

No lemma states `alpha<0.01`.  The first appearance of that number is this
parameter assignment.

Keeping the same old tail split, the existence conditions are

\[
 2\alpha<\beta(1-2\epsilon),
 \qquad
 \beta<\frac{\rho_R\delta}{2},
 \qquad
 \delta<1.
\]

Letting `epsilon` tend to zero shows that parameters exist exactly when

\[
 4\alpha<\rho_R\delta<\rho_R.
\]

For `rho_R=0.1`, the natural endpoint of the unchanged architecture is

\[
 \boxed{\alpha<0.025.}
\]

As a minimal witness that `0.01` was not a boundary, `alpha=0.011` admits

\[
 \delta=\frac{18}{25},\qquad
 \beta=\frac{29}{1000},\qquad
 \epsilon=\frac7{116}.
\]

The exact positive margins are

\[
 \frac5{72},\qquad \frac7{360},\qquad \frac7{2000}
\]

for the target RAMS ratio, cutoff RAMS ratio, and far-tail exponent.

Classification of `1/100`: **D, a safety and convenience choice**.  The
`1/40` endpoint that replaces it in the unchanged proof is produced by **B/C,
a sufficient non-sharp tail inequality obtained by applying the Hilbert norm
immediately after the RAMS cutoff**.

## 4. Continuation scan

The table distinguishes the report as previously promoted, the old lemmas
with parameters reselected, the intermediate-shell improvement, the uniform
Cauchy-radius optimization, and the finite-prime split.

| `alpha` | Promoted | Old lemmas | Shell | Uniform radius | Prime split |
|---:|---|---|---|---|---|
| 0.01 | PROVED | PROVED | PROVED | PROVED | PROVED |
| 0.02 | no | PROVABLE WITH CURRENT LEMMA | PROVED | PROVED | PROVED |
| 0.025 | no | FAILS at strict endpoint | PROVED | PROVED | PROVED |
| 0.05 | no | FAILS | FAILS at `rho_R=0.1` | PROVED | PROVED |
| 0.075 | no | FAILS | FAILS | FAILS | PROVED |
| 0.10 | no | FAILS | FAILS | FAILS | PROVED |
| 0.15 | no | FAILS | FAILS | FAILS | PROVED |
| 0.20 | no | FAILS | FAILS | FAILS | PROVED |
| 0.30 | no | FAILS | FAILS | FAILS | PROVED |
| 0.50 | no | FAILS | FAILS | FAILS | FAILS at strict endpoint |
| 0.68213 | no | FAILS | FAILS | FAILS | FAILS |

The first failed requested checkpoint after every current optimization is
`0.50`.

## 5. The binding RC2 estimate

At the standard smoothing weight

\[
 w(u)=\frac4{4+u^2},
\]

the Cauchy evaluation point is `sigma=3/2`.  The upper Dirichlet range has
square weight `x^2n^-3`.  The old proof placed the Hilbert bound immediately
after `Y`:

\[
 \sum_{n>Y}|a(n)|^2n^{-3}
 \ll Y^{-1+2\epsilon}.
\]

Multiplication by `x^2` forces `Y` beyond `x^2`, which is the condition
`beta>2alpha`.

Changing `sigma` would change the zero-pair smoothing weight.  It is therefore
not a free optimization for the stated `F2`; the standard weight fixes this
part of the calculation.

## 6. The intermediate-shell repair

Insert a second cutoff

\[
 x<Y=H^\beta<W=H^\gamma.
\]

RAMS2 is used only through `Y`.  Between `Y` and `W`, use the already proved
pointwise level-two envelope.  On every compact coefficient band below
`rho=1/2`, it gives

\[
 \mathcal A_{2,U}(u)\leq C u(\log u)^2.
\]

Partial summation gives

\[
 \begin{aligned}
 \int_{Y-}^{W}u^{-3}\,d\mathcal A_{2,U}(u)
 &\leq
 C Y^{-2}\left[
 \frac32(\log Y)^2+rac32\log Y+\frac34
 \right].
 \end{aligned}
\]

After multiplication by `x^2`, this shell is negligible when

\[
 \alpha<\beta,
\]

not only when `2alpha<beta`.

Beyond `W`, retain the Hilbert estimate:

\[
 x^2\sum_{n>W}|a(n)|^2n^{-3}
 \ll x^2W^{-1+2\epsilon}.
\]

It is negligible when

\[
 2\alpha<\gamma(1-2\epsilon).
\]

The pointwise envelope permits `2gamma/delta<1/2`.  This far condition allows
`alpha<delta/8`, so it is nonbinding while RAMS2 has `rho_R=0.1`.

The complete parameter conditions reduce to

\[
 \alpha<\beta<\frac{\rho_R\delta}{2},
 \qquad
 2\alpha<\gamma(1-2\epsilon),
 \qquad
 \frac{2\gamma}{\delta}<\frac12,
 \qquad
 \delta<1.
\]

For `rho_R=0.1`, they are feasible exactly on compact bands

\[
 \boxed{\alpha<0.05.}
\]

At `alpha=0.049`, one exact witness is

\[
 \delta=\frac{99}{100},\quad
 \beta=\frac{197}{4000},\quad
 \gamma=\frac{691}{4000},\quad
 \epsilon=\frac1{16}.
\]

Every bandwidth-bearing margin is positive; the smallest is `1/4000` in
`beta-alpha`.

This is a level-two bridge improvement.  No cluster estimate was changed to
obtain it.

## 7. The apparent next binding estimate: powerful Borel/Laplace mass

After the shell repair, the target RAMS2 condition `2alpha/delta<rho_R` binds.
The squarefree cluster majorant does not.  Its support-size ratio tends to
zero for every fixed `rho`, and the exact low components remain:

- size two: the `pq` connected atom and doubled edge;
- size three: alternating paths;
- size four: alternating paths and cycles.

The restriction comes from the repeated-prime Cauchy estimate.  On a local
circle `|u|=R`, define

\[
 a(R)=\frac{R}{1-R},
 \qquad
 b(R)=\frac{R}{(1-R)^2}.
\]

The powerful local factor has Laplace exponent bounded by

\[
 \boxed{
 \mathcal E_R(\rho)
 =2a(R)\rho+[b(R)+a(R)^2]\rho^2.
 }
\]

If one radius is imposed at every prime, the Hadamard powerful harmonic mass
requires `R^-2<2`, hence

\[
 R>\frac1{\sqrt2}.
\]

The previous report chose `R=3/4`, for which

\[
 \mathcal E_{3/4}(\rho)=6\rho+21\rho^2.
\]

It then selected the convenient subband `rho<=0.1`, where the exponent is at
most `0.81`.  Even at fixed `R=3/4`, the actual strict endpoint is

\[
 \rho<\frac{\sqrt{30}-3}{21}
 =0.1179631226215077\ldots.
\]

Optimizing `R` down to `1/sqrt(2)` gives the limiting rate

\[
 (2+2\sqrt2)\rho+(7+5\sqrt2)\rho^2.
\]

Let `rho_*` be its positive root.  Then every `rho<rho_*` admits some
`R>1/sqrt(2)` with a positive Laplace gap.  Explicitly,

\[
 \rho_*
 =\frac{\sqrt{(2+2\sqrt2)^2+4(7+5\sqrt2)}-(2+2\sqrt2)}
 {2(7+5\sqrt2)}
 =0.1454524603084045\ldots.
\]

This extends RAMS2 and, through section 6, RC2 and URMS2 to

\[
 |\alpha|<0.0727262301542022\ldots.
\]

For the round milestone `alpha=0.07`, choose

\[
 R=\frac{71}{100},\qquad \rho_R=\frac{143}{1000}.
\]

The exact Laplace margin is

\[
 \frac{3854691}{841000000}>0.
\]

Together with

\[
 \delta=\frac{283}{286},\quad
 \beta=\frac{563}{8000},\quad
 \gamma=\frac{11079}{57200},\quad
 \epsilon=\frac1{16},
\]

all RAMS, shell, envelope, far-tail, and dyadic margins are strictly positive.

### Finite-prime peeling removes the fixed-rho endpoint

The last restriction still uses more uniformity than the Euler product needs.
Fix any finite `rho_0` and choose `0<R<1` so small that

\[
 \mathcal E_R(\rho_0)<1/2.
\]

Put `P=R^-2` and split the powerful support into primes at most `P` and primes
larger than `P`.  On the tail-prime product,

\[
 \prod_{p>P}\left(1+\sum_{e\geq2}\frac{R^{-2e}}{p^e}\right)
\]

converges, because each local geometric series converges and its first term
is `O_R(p^-2)`.  The Laplace rate is at most `E_R(rho_0)<1/2`.

There are only finitely many primes at most `P`.  Give each such prime its own
radius `R_p>p^-1/2`.  Its exponent sum converges.  The total logarithm of this
finite prime set is constant, so its contribution to the Laplace rate is
`o(1)` as `z` tends to zero.  It is absorbed by the remaining half of the
Laplace gap.  Dominated convergence on the powerful strata then runs exactly
as before.

This establishes RAMS2 on every compact fixed `rho` band.  For example,
`split_powerful_witness(21/10)` chooses a rational tail radius, a finite prime
cutoff, and a Laplace rate below `1/2` using exact arithmetic.

With RAMS2 available at the target, the intermediate cutoff, and the far
cutoff, choose for any `alpha<1/2`

\[
 \delta=\frac{2\alpha+1}{2},\qquad
 \gamma=\frac{2\alpha+\delta}{2},\qquad
 \beta=\frac{\alpha+\gamma}{2}.
\]

Then

\[
 \alpha<\beta<\gamma<\delta<1,
 \qquad 2\alpha<\gamma.
\]

A sufficiently small positive `epsilon` gives
`2alpha<gamma(1-2epsilon)`.  These are the shell decay, far-tail decay,
finite mean-value, and initial-interval conditions.  Therefore RC2 and URMS2
hold on every compact band `0<|alpha|<1/2`.  The exact witness at
`alpha=0.499` is emitted by `prime_split_parameter_witness`.

## 8. Path and cycle audit

The directive's requested low-order separation is already exact in
`rams2_cluster.py`.

For a labelled support `C`, the path and cycle weights are separate formulas.
Direct enumeration through six prime labels has zero symbolic defect against
those formulas.  The full all-matching support majorant begins

\[
 4,\quad3,\quad\frac{49}{45},\quad\frac{289}{840},\quad
 \frac{1681}{18900},\quad\frac{11}{560},\ldots
\]

and has ratio `O(1/r)`.  Evaluating support sizes two, three, and four exactly
therefore cannot enlarge the present endpoint: those pieces are already kept
without the high-order majorant.  After finite-prime peeling, neither the
powerful core nor the path/cycle enumeration binds on a fixed `rho` band.

Deleting `A*A` still removes the Borel `pq` defect, forcing multiplicativity
still misses `kappa(p,q)`, and removing clusters above size two still misses
the size-three path.  None of these lesions is hidden by the bandwidth
optimization.

## 9. Downstream window obstruction

Let an admissible real spectral factor `v` have support of length `beta` and

\[
 \int v=1.
\]

The physical-space test `|v_hat(u)|^2` is nonnegative and equals one at the
origin.  Its autocorrelation `A_v` is supported on `[-beta,beta]`, but it may
have either sign.  The downstream denominator is

\[
 D_\beta(v)=\int v(s)^2\,ds
 +2\int_0^\beta\mathcal F_2(\alpha)A_v(\alpha)\,d\alpha.
\]

The exact coefficient and tail majorants show

\[
 \mathcal F_2(\alpha)>0
 \qquad(0<\alpha\leq1/2).
\]

The deterministic check forms the rational lower function from the first 40
coefficients, the exact majorants through index 101, and the two-residue
geometric tail.  After multiplying by the positive denominator and dividing
by `alpha`, the resulting degree-102 polynomial has every Bernstein
coefficient positive on `[0,1/2]`.  The smallest coefficient is

\[
 0.0049495354041559\ldots>0.
\]

Cauchy-Schwarz gives

\[
 \int v^2\geq\frac1\beta,
 \qquad
 |A_v(\alpha)|\leq\int v^2.
\]

Put

\[
 I_\beta^+
 =\sum_{i=1}^{40}\frac{C_i\beta^{i+1}}{i+1}
   +\beta\,\mathcal R_{40}(\beta),
\]

where `R_40` is the exact absolute tail majorant.  Positivity on the half-band
and the two inequalities above give, for every such `v`,

\[
 D_\beta(v)
 \geq (1-2I_\beta^+)\int v^2
 \geq\frac{1-2I_\beta^+}{\beta}.
\]

At `beta=1227/2500`, exact rational evaluation gives

\[
 \frac{1-2I_{1227/2500}^+}{1227/2500}
 =2.0002085758065586\ldots>2.
\]

Thus no admissible spectral-factor window of bandwidth at most `0.4908` can
give a positive simplicity expression.  For the exact integral, half-band
positivity makes `1-2beta-2 integral_0^beta F2` decrease with beta, so the
endpoint calculation covers every smaller bandwidth.

The remaining interval closes by retaining the positive interaction of the
constant part.  Write `v=1/beta+w`, with `integral w=0`, and let `T_beta` be
the integral operator with kernel `F2(|s-t|)`.  Schur's bound gives

\[
 \|T_\beta\|\leq2I_{1/2}^+<1.
\]

Completing the square in `w` bounds the possible improvement over the
constant factor by

\[
 \frac{4(I_{1/2}^+)^2}
 {(1227/2500)(1-2I_{1/2}^+)}.
\]

Meanwhile the exact constant interaction at `beta=1227/2500`, with its full
tail allowance, remains a lower bound throughout `[1227/2500,1/2]`.  After
division by the largest possible `beta^2`, the exact difference between this
interaction and the completion correction is

\[
 0.0233227357071382\ldots>0.
\]

Since `1/beta>=2`, every admissible real spectral factor through `beta=1/2`
has `D_beta(v)>2`.  Therefore

\[
 \boxed{\frac12\leq\beta_{\rm useful}.}
\]

This is a mathematical lower barrier for the downstream variational problem,
not a weakness of the chosen Legendre basis.

The unrestricted exploratory quadratic solve uses 400 midpoint cells.  At
`beta=0.499` it returns denominator `2.0287201304...`, hence simplicity value
`-0.0287201304...`; its minimizing spectral factor is still positive.  At
`beta=0.51` it returns `0.0147819191...`, consistent with the exact constant
window below.  This scan finds no candidate inside the newly reached band,
but it is not used as a proof of nonexistence.

## 10. A useful window at 0.51

Take the normalized constant window

\[
 v_\beta(s)=\frac1\beta
 \mathbf1_{[-\beta/2,\beta/2]}(s).
\]

Then

\[
 A_{v_\beta}(\alpha)=\frac{\beta-\alpha}{\beta^2}
 \quad(0\leq\alpha\leq\beta).
\]

This is exactly the triangular transform in Bian's Chapter 11 test.  The
thesis chooses the squared-sinc physical-space kernel immediately before
equation (11.2) and computes its triangular Fourier transform in the paragraph
that follows.  Equation (11.2) is the resulting pair-sum asymptotic.  The
constant `v_beta` above has that triangle as its autocorrelation, so this
candidate does not enlarge the historical admissible class.

For `beta=51/100`, exact integration of the first 40 corrected coefficients,
plus twice the full tail allowance, gives

\[
 2-D_{51/100}(v_{51/100})
 >0.0147728663285376.
\]

The exact rational value is emitted by `constant_window_bound(51/100)`.
Consequently

\[
 \boxed{1/2\leq\beta_{\rm useful}\leq51/100.}
\]

This is a coefficient-side statement.  It becomes an xi-double-prime theorem
only after the zero-statistics bridge reaches that bandwidth.

The primary source used for this comparison is Ji Bian, *The Pair Correlation
of Zeros of Derivatives of Riemann's Xi-Function*, University of Rochester
PhD thesis, 2008.  The audited PDF SHA-256 is

```text
ec1143f4f6c83288b717cfd4cd0aa6cc620f8c68b892f510a2a8d1708f36bfb7
```

## 11. The replacement lemma now required

The current rigorous bridge stops at `alpha=1/2`, exactly where the universal
window obstruction ends.  The current exact candidate is at `0.51`.

RAMS2 is no longer the obstacle at `0.51`: finite-prime peeling supplies every
fixed ratio needed at the target and intermediate cutoffs.  The conflicting
RC2 conditions are instead

\[
 2\alpha<\gamma(1-2\epsilon),
 \qquad
 \gamma<\delta<1.
\]

At `alpha=0.51`, the first demands `gamma>1.02` in the zero-epsilon limit,
while the finite mean-value estimate demands `gamma<1`.  This is the first
binding line.

### Strong far-tail alternative

Establish, for some `eta>1.02`,

\[
 \sum_{n>Y}|a_{2,T}(n)|^2n^{-3}
 \ll Y^{-\eta+o(1)}
\]

outside the RAMS band.  The cutoff condition becomes
`2alpha<eta*beta`, reducing the amount of arithmetic continuation required.

### Long-polynomial mean-value alternative

Replace the current `O(W/U)` relative error by an early-smoothed estimate that
remains `o(1)` for `W=H^gamma` at some `gamma>1.02`.  This permits the existing
quadratic tail decay to start beyond `x^2` without requiring `W<U`.

The present obstruction is therefore a proof-technology barrier: the
far-tail norm or the length range of the finite mean-value theorem.  No
divergent squarefree cluster, powerful-core divergence, or resolvent
singularity has appeared.

## 12. Commands and controls

```bash
.venv/bin/python hunts/higher_xi/bandwidth_forensics.py
.venv/bin/python -m pytest -q hunts/higher_xi/test_higher_xi.py -n0
```

The controls cover:

- the complete inequality graph;
- an exact witness at `alpha=0.011`;
- strict failure of the old endpoint at `1/40`;
- an exact shell witness at `alpha=0.049`;
- an exact optimized-Cauchy witness at `alpha=0.07`;
- a finite-prime split witness at `rho=2.1`;
- an exact contour witness at `alpha=0.499`;
- every requested continuation checkpoint;
- positivity of the corrected regular object on `[0,1/2]`;
- the universal lower bound `beta_useful>=1/2`;
- the exact constant-window upper bound `beta_useful<=0.51`;
- all prior coefficient, cluster, contour-lesion, and level-one controls.
