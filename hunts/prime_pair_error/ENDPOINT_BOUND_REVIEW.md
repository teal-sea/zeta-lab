# Review record for the corrected CHHL endpoint bound

## Provenance

The coordinator supplied the candidate argument directly in the Codex review
request on 2026-09-09. At review time it had no endpoint commit or attached
file. The reviewer checked that supplied text against the cited primary sources
and project dependencies. The exact mathematical version reviewed was then
preserved, without a new mathematical step, in:

```text
f659c8d693fd6dea4cc640b420c7ed862bcaf7a6
hunts/prime_pair_error/ENDPOINT_BOUND.md
```

This record attaches the review to that first durable proof commit. It does not
claim that the proof existed at this commit before the review, and it does not
attach the review retroactively to checkpoint #215.

## Verdict

**PASS.** The proof commit above supports the following statement. There are
fixed constants \(C,c>0\) such that, for every sufficiently large integer
\(N\),

\[
\boxed{E_{\rm corr}(N)\le C N^3
       \exp\!\left(-c(\log N)^{1/10}\right).}
\]

Here \(E_{\rm corr}\) uses the unchanged exceptional correction \(C_N\) from
#212-#215. The assertion is uniform over the exceptional data in Tao and
Teräväinen's source range, including the case in which there are no such data.

This is a review of a handwritten mathematical argument. It is not formal
verification, external peer review, or a novelty determination.

## Checked dependencies

1. Tao and Teräväinen, arXiv:2107.02158v4, Proposition 2.2, equation
   (2.5), gives
   \[
   \sum_{n\in B}(\Lambda(n)-\Lambda_{\rm Siegel}(n))
   \ll N\exp(-\gamma(\log N)^{1/10})
   \]
   for every arithmetic progression \(B\subset[N]\). Its proof writes such a
   progression as a difference of progression prefixes and equation (7.1)
   states the required endpoint form with the model fixed at the ambient
   \(N\). The endpoint exponent is obtained from this proposition. It is not
   obtained by setting \(\kappa=1/10\) in Theorem 2.7.

2. Montgomery and Vaughan, *Multiplicative Number Theory II*, Theorem 17.1
   and equations (17.28)-(17.32), give the stated minor-arc estimate for the
   full von Mangoldt exponential sum and the Type I bound used in the proof.
   The full \(\Lambda\) retains proper prime powers.

3. `SIEGEL_UNIFORMITY.md` at
   `76ed1155d087d9137306d3632f66dba7555aadc3`, equations (18)-(19), gives
   uniformly in \(1\le h\le N\)
   \[
   r_a(h)=C_N(h)+O\!\left(N\exp(-c_m(\log N)^{1/10})\right).
   \]
   That project dependency keeps the sharp endpoint \(N-h\), the original
   infinite singular series, and every exceptional conductor case.

4. `CORRECTED_RH_BRIDGE.md` at
   `cb0189db3863ac43b2314c7df1008636bd4da477` defines the same
   \(E_{\rm corr}\) and proves the separate implication
   \[
   E_{\rm corr}(N)\ll_\epsilon N^{2+\epsilon}
   \text{ for every }\epsilon>0\quad\Longrightarrow\quad\mathrm{RH}.
   \]
   The endpoint estimate reviewed here does not meet that near-quadratic
   hypothesis.

## Complete budget and parameters

The proof takes

\[
\ell=\log N,\quad t=\ell^{1/10},\quad Z=e^t,
\]

\[
m=2\lceil\sqrt\ell\rceil,quad D_0=Z^m,quad
0<\sigma\le\min(\gamma/20,1/20),quad
R=\lfloor e^{\sigma t}\rfloor.
\]

Before absorption, the complete bound is

\[
\begin{aligned}
E_{\rm corr}(N)\ll \ell^{O(1)}\bigl[&
N^3R^7e^{-2\gamma t}+N^3R^{-1/6}
+N^{14/5}+N^2D_0\sqrt Z\bigr]\\
&+N^3e^{-c_d\sqrt\ell}+N^3e^{-2c_mt}.
\end{aligned}
\]

Every displayed term is retained. The first two terms become respectively
\(N^3e^{-(2\gamma-7\sigma)t}\) and \(N^3e^{-\sigma t/6}\). Also

\[
\log(D_0\sqrt Z)=2\ell^{3/5}+O(\ell^{1/10})=o(\ell),
\]

so the remaining polynomial and \(N^{2+o(1)}\) terms are absorbed after
decreasing \(c\). For example, after increasing the lower threshold for
\(N\), one can take a positive \(c\) no larger than
\(\min(\sigma/12,c_m)\).

The review checked the Bonferroni divisor error, the length \(D_0\), all
major-arc powers of \(R\), both exceptional-conductor ranges on the minor
arcs, rational shifts, non-coprime divisors, sharp prefixes, Abel summation,
centering, Parseval normalization, and the final absorption. No
\(N^{3-o(1)}\) remainder was removed from the budget.

## Original error and remaining gap

This endpoint statement is for \(E_{\rm corr}\). For the original CHHL error,
the same proof and the inherited exceptional-energy estimate give

\[
\boxed{\begin{aligned}
E(N)\ll{}&N^3\exp\!\left(-c(\log N)^{1/10}\right)\\
&+1_{q\ {\rm odd}}N^{2\beta+1}\frac{q^2}{\phi(q)^4}
+N^{4\beta-1}\frac{q^2}{\phi(q)^3}.
\end{aligned}}
\]

Both exceptional contributions remain when the source-range exceptional data
exist. They disappear only in the no-exception case.

The improvement over the previous result is precise: it replaces the family

\[
E_{\rm corr}(N)\ll_\kappa
N^3\exp(-c_\kappa(\log N)^\kappa),\qquad\kappa<1/10,
\]

by the endpoint exponent \(\kappa=1/10\), with fixed constants. It does not
produce any fixed \(\eta>0\) in \(E_{\rm corr}\ll N^{3-\eta}\). The remaining
mathematical gap is therefore a fixed power saving, ultimately the
near-quadratic family required by the #214 RH-sufficiency bridge. That is a
separate future research task.
