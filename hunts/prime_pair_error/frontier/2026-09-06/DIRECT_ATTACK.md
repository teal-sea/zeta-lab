# Direct arithmetic attack on the central prime-counting obstruction

**2026-09-06.** This is an attempted proof mechanism, its failure analysis, and a constructive stress test. **No improved upper bound for the real primes, no proof of RH, and no novelty claim is made.** The completed A/B audit is not reopened.

## 1. The exact target

Let `Lambda(p^a)=log p`, with zero elsewhere, and let

\[
 \psi(x)=\sum_{n\le x}\Lambda(n),\qquad R(x)=\psi(x)-x.
\]

CHHL's Theorem 2 and its Section 3 connect the total prime-pair error to this scalar remainder. In particular,

\[
 E(N)\ge 2N\left[R(N)\left(1+\frac{R(N)}{2N}\right)+O(\log N)\right]^2.
\]

Thus better control of peripheral components of the Fourier integral cannot hide an uncontrolled scalar surplus. The previous MULTISCALE.md also contains a *draft* localization inequality for its central interval. The present finite arithmetic identities do not depend on that draft's asymptotic zero-energy estimates.

For RH itself, even the one-sided statement

\[
 R(N)\le C_\epsilon N^{1/2+\epsilon}\quad\text{for every }\epsilon>0
 \quad\text{and all sufficiently large integers }N
\tag{U}
\]

would suffice. This is a standard consequence of the positive oscillation theorem for the prime-number remainder: if a zero existed with real part greater than one half, positive fluctuations would exceed an appropriately smaller exponent. CHHL Section 3 cites the stronger `Omega_+` and `Omega_-` facts. This is a known sufficient criterion, not a new equivalence or a new bound proved here. A fixed epsilon, finite computations, or a correct mean density do not supply (U).

The word "coherent" below means a fluctuation persisting across scales such as the real part of `x^(beta+i gamma)`, not a statistical independence assumption.

## 2. Exact factorization feedback

The established divisor identity is

\[
 \sum_{d\mid n}\Lambda(d)=\log n.
\tag{F0}
\]

It follows immediately by writing the prime factorization of n; every prime power dividing n contributes one copy of the corresponding log p.

Summing (F0) for `n<=N` and changing the order of a finite sum gives

\[
 \sum_{m=1}^N\psi(N/m)=\log(N!).
\tag{F1}
\]

Here `psi` is evaluated at the real argument `N/m`, with its usual integer cutoff. Consequently

\[
 R(N)+\sum_{m=2}^N R(N/m)=\log(N!)-N H_N,
 \qquad H_N=\sum_{m=1}^N\frac1m.
\tag{F2}
\]

**Endpoint warning:** `R(N/m)` is not `R(floor(N/m))`; they differ by the fractional part of `N/m`. The checker retains this distinction.

This looks like a possible feedback relation: an excess at N must be balanced by a known term and values at smaller scales. It is exact, but that alone does not make it a contracting recursion. Indeed an absolute-value treatment of a putative `|R(t)| <= C sqrt(t)` only gives

\[
 \sum_{m=2}^N |R(N/m)|\le C\sqrt N\sum_{m=2}^Nm^{-1/2}=O(CN),
\]

not `O(sqrt N)`. This is a failure of that inequality, not a theorem that no argument from factorization can work.

The compensated identity is particularly accurate:

\[
 \sum_{m=1}^N R(N/m)+(1+\gamma_E)N+\frac12
 =\frac12\log(2\pi N)+\frac1{6N}+O(N^{-3}),
\tag{F3}
\]

by the usual expansions for log(N!) and H_N. `gamma_E` is Euler's constant. Accuracy of the aggregated left side does not, by itself, bound its individual signed terms.

## 3. Test the feedback on an oscillating power

For a *fixed* complex `s`, `0<Re(s)<1`, define `f_s(x)=x^s`, `x>=1`. Directly,

\[
 \sum_{m=1}^N f_s(N/m)=N^s\sum_{m=1}^N m^{-s}.
\]

Euler--Maclaurin (equivalently the large-parameter expansion of the Hurwitz zeta function) gives

\[
 \boxed{\sum_{m=1}^N(N/m)^s-\frac{N}{1-s}-\frac12
 =\zeta(s)N^s-\frac{s}{12N}+O_s(N^{-3}).}
\tag{F4}
\]

The constant in `O_s` is allowed to depend on s. No uniform high-zero estimate is asserted.

The subtracted linear term is natural: `int_1^infinity t^(s-2) dt = 1/(1-s)`.

At an actual zeta zero `rho`, (F4) becomes

\[
 \sum_{m=1}^N(N/m)^\rho-\frac{N}{1-\rho}-\frac12
 =-\frac{\rho}{12N}+O_\rho(N^{-3}).
\tag{F5}
\]

Thus an input with magnitude `N^Re(rho)` has an aggregated oscillatory output of only `O_rho(1/N)` after the linear and boundary terms are accounted for. The identity would have the same effect at a hypothetical off-line zero. There is no assumption here that such a zero exists.

This is the familiar Mellin/Dirichlet-convolution multiplier `zeta(s)`, not a newly discovered phenomenon. The useful lesson for this attempted proof is precise: **small compensated factorization error is not automatically a stable estimate for the original fluctuation.** The leading dangerous mode is multiplied by zero rather than forced to become small.

This does not produce a second exact solution to (F0). The complete divisor identities uniquely determine Lambda. A pure power is a test of an asymptotic feedback estimate, not a replacement for the actual arithmetic sequence.

Finite numerical illustration, using mpmath's approximation to the first critical-line zero:

| N | magnitude of N^rho | magnitude after linear/boundary subtraction |
|---|---:|---:|
| 100 | 10 | 0.0117901573 |
| 1,000 | 31.6227766 | 0.00117863434 |
| 10,000 | 100 | 0.000117863053 |

The controls include `3/4 + i Im(rho_1)` and the real exponent `3/4`. **Neither is asserted to be a zero.** Their outputs contain the nonzero `zeta(s)N^s` term, as expected. The computations are diagnostics; (F4) is justified by Euler--Maclaurin.

## 4. Why cancellation between distinct zeros cannot simply hide an off-line zero forever

For `Re(s)>1`, absolute convergence and partial summation give

\[
 \int_1^\infty R(x)x^{-s-1}\,dx
 =-\frac{\zeta'(s)}{s\zeta(s)}-\frac1{s-1}.
\tag{M}
\]

At a nontrivial zero `rho` of multiplicity m, the meromorphic expression on the right has residue `-m/rho`, which is nonzero. Contributions from poles at other locations cannot cancel this local residue.

If an absolute remainder bound `R(x)=O(x^a)` held with `a<Re(rho)`, the left side would define a holomorphic function on `Re(s)>a`, contradicting that pole after analytic continuation from `Re(s)>1`. This is a standard proof of the connection between prime-counting error and zeros. The one-sided assertion in Section 1 uses the standard oscillation theorem, not absolute convergence of a one-sided estimate.

This is why density/energy information allowing even one unknown right-hand zero does not automatically settle the central remainder. The task is to establish a prime-counting upper bound that **excludes** such zeros, not to assume that their effects cancel in the final count.

## 5. Constructive test of the coarse assumptions

A separate, deliberately counterfeit sequence shows why positivity, the leading density, a prime-sized second moment, and avoiding a fixed set of small prime divisors do not suffice for the desired estimate.

This is **not a counterexample involving real primes**, and it is not claimed to satisfy the zeta-zero energy theorems or all inputs of the earlier band calculation.

Fix

\[
 \beta=3/4,\quad t=3,\quad c=1/10,
 \qquad A(x)=x+c x^\beta\cos(t\log x)+b.
\]

For `x>=10,000`, choose b to make A match an initial cumulative weight. Then A is increasing and its increments over an integer interval are between 1/2 and 3/2, since

\[
 |(c x^\beta\cos(t\log x))'|
 \le c\sqrt{\beta^2+t^2}\,x^{\beta-1}<1/2.
\]

Start with the true Mangoldt weights through `n0=10,000`. Above n0 permit new weights only when `(n,30)=1`. The gaps between permitted integers are at most 6. At a permitted n, add `log n` if doing so will not overshoot A(n); otherwise add zero. At all other n add zero.

Equivalently, with cumulative sum Psi_a, add log n exactly when

`A(n)-Psi_a(n-1) >= log n` and `(n,30)=1`.

After each permitted position the deficit lies in `[0,log n)`: before the next one it increases by at most 9, and `log n > 9` for n>=10,000, so at most one added log is required. Between permitted positions it is at most `log n+9`. Therefore the infinite construction satisfies

\[
 \Psi_a(N)=N+cN^{3/4}\cos(3\log N)+b+O(\log N).
\tag{C1}
\]

In particular it has the correct leading weighted density, `Psi_a(N)~N`, but violates a square-root-with-arbitrarily-small-power error along suitable sequences. Above n0 every nonzero value is exactly `log n` and avoids multiples of 2, 3 and 5.

Also, apart from a finite initial constant,

\[
 \sum_{n\le N}a_n^2=\sum_{n\le N}a_n\log n
 =N\log N-N+O(N^{3/4}\log N+\log^2N),
\tag{C2}
\]

by partial summation using (C1). Hence its second moment is asymptotic to `N log N`, just as for actual prime weights. The number of nonzero positions is asymptotic to `N/log N` by another partial summation.

The script executed this construction through two million. For example:

| N | counterfeit remainder Psi_a(N)-N | tracking error relative to A(N) |
|---|---:|---:|
| 300,000 | +1,358.370443 | 5.148672 |
| 1,000,000 | -2,514.210209 | 8.126829 |
| 2,000,000 | +4,854.985816 | 12.541643 |

These finite values do not establish (C1)'s asymptotic; the greedy-deficit argument does. No comparison with the genuine R(N) is implied.

Crucially, the sequence **fails the exact factorization condition**. The first checked failure is at n=10,007, where its divisor-weight sum minus log n is about -9.21104. Thus this is a falsifier for arguments using only the coarse properties above, not a falsifier for the real prime problem.

## 6. Outcome of this attempt

1. The central target is the real prime-counting surplus, and even a suitable **one-sided upper bound** would suffice for RH. This is known theory.
2. The direct factorization-feedback identity is exact, but its compensated action suppresses modes at zeta zeros. The proposed automatic contraction was not established; the generic argument for it fails at (F4)--(F5).
3. A positive, sparse, locally pre-sieved counterfeit can carry a larger-than-square-root drift while retaining the leading second moment. The generic positivity/local-density strategy therefore has a concrete false-positive test.
4. No new upper bound for R, the central intensity, or total E follows. None of the previous completed results is withdrawn by these tests.

The required new ingredient is an upper-bound argument exploiting the **full arithmetic sequence**, beyond a coarse average of factorization or generic Fourier norms. Merely proving (F1), naming its inverse, or restating (U) is not that ingredient. This note records the actual proof attempt and its first unsupported step; it does not claim a successful route is already available.

## 7. Checks and sources

Run `python check_attack.py` with numpy and mpmath installed. `checks.json` and `checks.log` record the executed outputs.

Checks performed:
- 66 exact integer prime-exponent verifications of the factorial identity, up to N=1,000;
- floating evaluations of all divisor identities through 100,000, maximum residual below 4e-15;
- seven prefix/factorial comparisons, keeping real arguments for R;
- nine 55-digit direct power-sum/Euler--Maclaurin comparisons, including one numerical critical-line zero and two nonzero controls;
- a two-million-step sparse-countermodel construction with deficit and arithmetic-violation checks.

Exact arithmetic checks and floating diagnostics are distinguished in the JSON. There is no asymptotic certification, formal verification, or independent referee claim.

Primary sources:
- Chou, Haag, Huryn, Ledoan, Theorem 2 and Section 3: https://arxiv.org/html/2308.14888v1
- NIST DLMF 27.4.12--13, the von Mangoldt and logarithm Dirichlet series: https://dlmf.nist.gov/27.4
- NIST DLMF 25.11(iii), 25.11(xii), Euler--Maclaurin and the Hurwitz-zeta asymptotic: https://dlmf.nist.gov/25.11
- NIST DLMF 27.2, prime factorization and arithmetic functions: https://dlmf.nist.gov/27.2

The original exact identities and their Mellin interpretation are established mathematics. The counterfeit construction is supplied as a self-contained diagnostic; no priority claim is made for it.
