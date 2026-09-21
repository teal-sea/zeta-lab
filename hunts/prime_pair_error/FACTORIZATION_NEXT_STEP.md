# Dirichlet Hyperbola Factorization of the Full Signed Functional D_N

## 1. Orientation and Purpose

This document records the constructive next step in the arithmetic investigation of the Riemann-Weil signed functional $D_N$.

Following the independent review and author adjudication in `ARITHMETIC_CANCELLATION_REVIEW.md` and `ARITHMETIC_CANCELLATION_CANDIDATE.md`, we depart from the scale-by-scale bilinear sums $\mathcal{T}_{\mathrm{bilinear}}$ and address the full signed functional directly. Rather than postulating separate remainder bounds, we substitute the exact truncated Mobius convolution $\Lambda = \mu * \log$ into the entire functional $D_N$, retain all coupled boundary and principal terms, and establish an exact two-piece Dirichlet hyperbola decomposition without remainder leakage.

The central finding is twofold:
1. The full functional $D_N$ is an exact finite linear combination of $\Lambda(m)$ for $m \le N/2$ plus a completely explicit smooth baseline $\mathcal{S}_{\mathrm{smooth}}(N, K)$.
2. Substituting $\Lambda = \mu * \log$ yields an exact partition $D_N = \mathcal{S}_{\mathrm{smooth}} + \Sigma_1 + \Sigma_2$. The Type I sum $\Sigma_1$ carries the order $N \log N$ and order $N$ scale matching $\mathcal{S}_{\mathrm{smooth}}$, while the Type II inner sums expand explicitly into interval differences of the Mertens function $M(t) = \sum_{a \le t} \mu(a)$ (with empty-interval guards required; see section 4.2). The exact joint target of this route is $|\mathcal{S}_{\mathrm{smooth}} + \Sigma_1 + \Sigma_2| \ll_\epsilon N^{1/2+\epsilon}$. No equivalence is claimed between bounds on individual pieces ($\Sigma_1$ alone, $\Sigma_2$ alone) and RH: only $\zeta(s)$ is involved here (no Dirichlet L-functions), and necessity of Mertens-strength input for any individual piece is not proved. (Corrected 2026-09-20: the draft claimed an equivalence with the Mertens square-root bound and invoked Dirichlet L-functions; both removed.)

---

## 2. Exact Kernel Reduction of the Full Functional

Let $N \ge 4$ be an integer, $K = \lfloor\sqrt{N}\rfloor$, and $Y = N/K$. The full functional is defined by:
$$D_N = N \int_{Y}^\infty \frac{R(u)}{u^2} \, du - \sum_{k=2}^K R(N/k)$$
where $R(u) = \psi(u) - u = \sum_{m \le u} \Lambda(m) - u$.

Using the identity $\int_1^\infty R(u)/u^2 \, du = -(1 + \gamma)$ and evaluating the finite integral on $[1, Y]$, the tail term expands as:
$$N \int_Y^\infty \frac{R(u)}{u^2} \, du = N \log Y - N(1 + \gamma) + K \psi(Y) - N \sum_{m \le Y} \frac{\Lambda(m)}{m}$$
Similarly, the discrete sum expands as:
$$\sum_{k=2}^K R(N/k) = \sum_{k=2}^K \psi(N/k) - N (H_K - 1)$$
where $H_K = \sum_{k=1}^K 1/k$.

Subtracting the two expressions collects the smooth terms into:
$$\mathcal{S}_{\mathrm{smooth}}(N, K) = N (\log Y + H_K - 2 - \gamma)$$
The remaining terms depend purely on the prime powers $m$:
$$\mathcal{A}_N = K \psi(Y) - N \sum_{m \le Y} \frac{\Lambda(m)}{m} - \sum_{k=2}^K \sum_{m \le N/k} \Lambda(m)$$

Interchanging summation over $k$ and $m$ over the range $m \le M = \lfloor N/2 \rfloor$:
- For $1 \le m \le Y$: the number of $k \in [2, K]$ with $k \le N/m$ is exactly $K - 1$. Combining with $(K - N/m) \Lambda(m)$ from the first two terms gives the coefficient $(K - N/m) - (K - 1) = 1 - N/m$.
- For $Y < m \le M$: since $N/m < N/Y = K$ and $N/m \ge N/M \ge 2$, the number of $k \in [2, K]$ with $k \le N/m$ is exactly $\lfloor N/m \rfloor - 1 \ge 1$. The first two terms contribute zero, yielding the coefficient $-(\lfloor N/m \rfloor - 1) = 1 - \lfloor N/m \rfloor$.
- Endpoint notes: $m = 1$ contributes $\Lambda(1) = 0$ regardless of branch; the $m \le Y$ versus $m > Y$ split is over integers against rational $Y$, hence exact with no fractional error; primality of $N$ itself never enters since $m \le M = \lfloor N/2 \rfloor$.

Therefore, the full signed functional admits the exact discrete kernel representation:
$$D_N = \mathcal{S}_{\mathrm{smooth}}(N, K) + \sum_{m=1}^M w_N(m) \Lambda(m)$$
where $M = \lfloor N/2 \rfloor$, and the kernel $w_N(m)$ is defined for $1 \le m \le M$ by:
$$w_N(m) = \begin{cases} 1 - \frac{N}{m}, & 1 \le m \le Y \\ 1 - \lfloor \frac{N}{m} \rfloor, & Y < m \le M \end{cases}$$
This representation is exact: there are no asymptotic remainders, no discarded boundaries, and no floating-point approximations.

---

## 3. Truncated Dirichlet Hyperbola Partition

We substitute the exact Dirichlet convolution:
$$\Lambda(m) = (\mu * \log)(m) = \sum_{a b = m} \mu(a) \log b$$
into the arithmetic sum $\sum_{m=1}^M w_N(m) \Lambda(m)$. Since $\log 1 = 0$, terms with $b = 1$ vanish identically. The sum becomes:
$$\sum_{m=1}^M w_N(m) \Lambda(m) = \sum_{\substack{a b \le M \\ b \ge 2}} \mu(a) \log b \, w_N(a b)$$

We partition the hyperbolic domain $\{ (a, b) : a b \le M, b \ge 2 \}$ using the parameter:
$$U = \lfloor \sqrt{M} \rfloor = \lfloor \sqrt{\lfloor N/2 \rfloor} \rfloor$$

### Lemma (Absence of Remainder Region)
For $U = \lfloor \sqrt{M} \rfloor$, every pair of integers $(a, b)$ satisfying $a b \le M$ satisfies $\min(a, b) \le U$. Consequently, the region $\{ a > U, b > U, a b \le M \}$ is strictly empty.

*Proof.* If $a > U$ and $b > U$, then $a \ge U + 1$ and $b \ge U + 1$. Thus $a b \ge (U + 1)^2$. By definition of the integer square root, $(U + 1)^2 > M$. Hence $a b > M$, which contradicts $a b \le M$. Q.E.D.

By this lemma, the hyperbolic domain splits disjointly into exactly two regions:
1. **Type I Sum ($\Sigma_1$):** $a \le U$ and $2 \le b \le \lfloor M/a \rfloor$.
2. **Type II Sum ($\Sigma_2$):** $2 \le b \le U$ and $U < a \le \lfloor M/b \rfloor$.

The decomposition of $D_N$ is therefore exact:
$$D_N = \mathcal{S}_{\mathrm{smooth}}(N, K) + \Sigma_1(N) + \Sigma_2(N)$$
with:
$$\Sigma_1(N) = \sum_{a=1}^U \mu(a) \sum_{b=2}^{\lfloor M/a \rfloor} \log b \, w_N(a b)$$
$$\Sigma_2(N) = \sum_{b=2}^U \log b \sum_{a=U+1}^{\lfloor M/b \rfloor} \mu(a) w_N(a b)$$
There is no third intersection piece to subtract, and no uncounted region.

---

## 4. Analytical Anatomy and the Mertens Obstruction

### 4.1. Type I Cancellation of Smooth Growth

In $\Sigma_1$, the variable $a \le U \le \sqrt{N/2}$ is small, while the inner variable $b$ runs up to $M/a \asymp N/a$.
The inner sum:
$$S_1(a) = \sum_{b=2}^{\lfloor M/a \rfloor} \log b \, w_N(a b)$$
has the summand $\log b$ weighted by $w_N(a b)$. Formally, for $b \le Y/a$ where $w_N(ab) = 1 - N/(ab)$, Euler-Maclaurin in $b$ suggests main terms of the form $- (N/a) \log(N/a) + C (N/a)$. This is a formal scale reading, not an estimate: $w_N$ has a kink at $b = Y/a$ and a jump at every $ab = N/k$, so Euler-Maclaurin does not apply directly, and no remainder is priced here. (Qualified 2026-09-20.)

Summing against $\mu(a)$ would invoke, in the limit, the classical relations:
$$\sum_{a=1}^\infty \frac{\mu(a)}{a} = 0, \qquad \sum_{a=1}^\infty \frac{\mu(a) \log a}{a} = -1$$
These infinite series do not license uncontrolled finite truncations at $a \le U$: the partial sums converge only with PNT-strength error, and the truncation remainder at scale $U$ is not priced here. What is true exactly is the scale match: the $b$-inner sums carry $-(N/a)\log(N/a)$-scale structure against $\mu(a)$, the same scale as $\mathcal{S}_{\mathrm{smooth}}$. Measured diagnostic only: $|\mathcal{S}_{\mathrm{smooth}} + \Sigma_1|/N^{3/4}$ is $0.17$ at $N = 400$ and $0.75$ at $N = 1000$; finite agreement is not a bound proof and no $O(N^{3/4})$ cancellation is claimed. (Corrected 2026-09-20: the draft presented the infinite-series cancellation and the finite-ratio observation as established.)

### 4.2. Reduction of Type II to the Mertens Function

In $\Sigma_2$, the outer variable $b$ is small ($2 \le b \le U$). For the inner variable $a$, we have integers $a \ge U + 1$ and $b \ge 2$, so $a b \ge 2(U + 1) > 2\sqrt{M}$. Since $Y = N/K \le \sqrt{N} + 1 + 1/(\sqrt{N} - 1)$ (valid upper bound; $Y < \sqrt{N} + 1$ is false, e.g. $N = 8$ and every $N = m^2 - 1$) and $2\sqrt{M} \ge Y$ holds for $N \ge 16$ by direct squaring, with $4 \le N \le 15$ checked by hand ($\Sigma_2$ is empty for $N \le 11$; at $N = 12, 13, 14, 15$ the least product is $6 > Y$), we have $ab > Y$ for every $\Sigma_2$ pair at every $N \ge 4$. Verified computationally: $\min(2(U+1) - Y) = 0.5$ over $4 \le N \le 100000$, and $\min(Kab - N) = 3$ over 30.8M sampled pairs. (Corrected 2026-09-20: the draft chain used the invalid inequality $\sqrt{N} \ge Y$; in fact $Y \ge \sqrt{N}$ always. The conclusion survives via the argument above.)
Consequently, throughout $\Sigma_2$, the product $a b$ strictly exceeds $Y = N/K$. The kernel $w_N(a b)$ therefore takes purely integer values:
$$w_N(a b) = 1 - \lfloor \frac{N}{a b} \rfloor$$

Let $k = \lfloor N/(a b) \rfloor$. Since $a b \le M = \lfloor N/2 \rfloor$, we have $k \ge 2$. Furthermore, since $a b > Y$, we have $k \le K$. The condition $\lfloor N/(a b) \rfloor = k$ is equivalent to:
$$\frac{N}{k+1} < a b \le \frac{N}{k} \iff \frac{N}{b(k+1)} < a \le \frac{N}{bk}$$

The inner sum over $a$ in $\Sigma_2$ is:
$$\mathcal{M}_b(N) = \sum_{U < a \le \lfloor M/b \rfloor} \mu(a) \left( 1 - \lfloor \frac{N}{a b} \rfloor \right)$$
Expanding by the level sets of the floor function:
$$\mathcal{M}_b(N) = \left[ M\left(\lfloor M/b \rfloor\right) - M(U) \right] - \sum_{k=2}^K k \sum_{\substack{U < a \le \lfloor M/b \rfloor \\ N/(b(k+1)) < a \le N/(bk)}} \mu(a)$$
where $M(t) = \sum_{n \le t} \mu(n)$ is the Mertens function.

Each inner sum is a Mertens difference over a clamped interval. With $hi = \min(\lfloor M/b \rfloor, \lfloor N/(bk) \rfloor)$ and $lo = \max(U, \lfloor N/(b(k+1)) \rfloor)$:
$$\sum_{\substack{U < a \le \lfloor M/b \rfloor \\ N/(b(k+1)) < a \le N/(bk)}} \mu(a) = \begin{cases} M(hi) - M(lo), & hi > lo \\ 0, & hi \le lo \end{cases}$$
The guard is load-bearing: clamped endpoints can reverse ($hi \le lo$), and the unguarded $M(hi) - M(lo)$ then returns a nonzero wrong-signed value (e.g. $N = 20$, $b = 2$, $k = 4$: unguarded $1$, correct $0$; two further instances at $b = 3$; see `results_factorization_diagnostic.json`). Level sets with $k > K - 1$ are empty by the $ab > Y$ gate and contribute $0$ under the same guard, so summing $k = 2, \dots, K$ is safe. (Corrected 2026-09-20: the draft omitted the guard.)

### 4.3. Pricing the Implication

We now evaluate the bounds on $\Sigma_2$:
- **Trivial Size Bound:**
  Bounding $|\mu(a)| \le 1$ and $|1 - \lfloor N/(ab) \rfloor| \le N/(ab)$ without sign cancellation yields:
  $$\sum_{U < a \le M/b} |\mu(a)| \left| 1 - \lfloor \frac{N}{ab} \rfloor \right| \ll \frac{N}{b} \sum_{a \le M/b} \frac{1}{a} \ll \frac{N \log N}{b}$$
  Summing over $b \le U$ with $\log b$:
  $$\Sigma_2 \ll N \log N \sum_{b \le U} \frac{\log b}{b} \ll N \log^3 N$$
- **Genuine unconditional baseline (proved):**
  Write the inner sum directly as $\sum \mu(a) - (N/b)\sum \mu(a)/a - \sum \mu(a)\{N/(ab)\}$ over $U < a \le M/b$ (no level sets, so no $k$-weights). The fractional piece costs at most the interval length $M/b$ per $b$; with $\log b$ weights this is $\ll M \sum_{b \le U} (\log b)/b \ll N \log^2 N$. The other two pieces admit Stieltjes partial summation against $M(t) \ll t\exp(-c\sqrt{\log t})$ with logs retained, contributing $\ll N\exp(-c'\sqrt{\log N})\log^3 N$. Hence, honestly derived:
  $$\Sigma_2(N) \ll N \log^2 N \qquad \text{(unconditional; logs retained).}$$
  The draft's $\Sigma_2 \ll N\exp(-c\sqrt{\log N})$ is retracted: inserting $M(t)$ bounds into the $k$-level-set expansion multiplies every cell by its $k$-weight, gaining a factor $\sim K$ per $b$ that wipes out the subexponential saving. (Corrected 2026-09-20.)
- **Priced conditional (Mertens input, classical RH-equivalence):**
  $M(t) \ll_\epsilon t^{1/2+\epsilon}$ for every $\epsilon > 0$ is classically equivalent to RH for $\zeta(s)$ (reference equivalence, not re-proved here; no Dirichlet L-functions enter). Inserted into the same direct split, the smooth pieces fall to $\ll_\epsilon N^{3/4+\epsilon}\log^2 N$, but the fractional-weight piece $\sum \mu(a)\{N/(ab)\}$ is unimproved by this step and still costs $\ll N\log^2 N$. So even full Mertens-strength input does not price $\Sigma_2$ at $N^{1/2+\epsilon}$ through this split; the $N^{1/2}$ claim priced the fractional piece at zero. Reaching it needs oscillation analysis of $\mu$ against $\{N/(ab)\}$, which is not done here.
- **Valid conditional implication for the joint target:**
  RH implies $|R(x)| \ll x^{1/2}\log^2 x$ (von Koch, inherited leaf), whence via the unconditional $D_N = R(N) + O(\sqrt{N})$ the joint bound $|D_N| \ll N^{1/2}\log^2 N$. This implication is proved; it routes through the renewal identity, not through individual $\Sigma_1$/$\Sigma_2$ bounds.

**The Precise Obstruction (restated):**
The weights $w_N(a b) = 1 - \lfloor N/(a b) \rfloor$ are piecewise constant, but partial (Stieltjes) summation against $M(t)$ applies to them regardless: lack of smoothness is not the obstruction. The obstruction is quantitative: the $k$-level-set expansion carries $k$-weights ($\sum_{k \le K} k^{1/2} \asymp K^{3/2}$), and the fractional-weight piece resists both trivial and Mertens-based estimation at the $N^{1/2}$ scale. No necessity claim is made: it is not proved that bounding $\Sigma_2$ individually requires Mertens strength, and no equivalence for individual terms is asserted. The exact joint target is $|\mathcal{S}_{\mathrm{smooth}} + \Sigma_1 + \Sigma_2| \ll_\epsilon N^{1/2+\epsilon}$.

---

## 5. Endpoints, Prime Powers, and Smoothing Costs

1. **Prime Powers at Endpoints:**
   In $D_N$, the arithmetic convolution runs only up to $M = \lfloor N/2 \rfloor$. Thus, whether $N$ itself is a prime or prime power has no direct effect on the summation range of $\Lambda(m)$. The only endpoint sensitivity arises at $Y = N/K$. Because $Y$ is rational, the split between $m \le Y$ and $m > Y$ in $w_N(m)$ is exact and introduces no fractional error.
2. **Smooth Tail Integral:**
   The infinite tail $N \int_Y^\infty R(u)/u^2 \, du$ is completely resolved into $K \psi(Y) - N \sum_{m \le Y} \Lambda(m)/m$ plus smooth terms. There is no truncation error or discarded tail remainder.
3. **Smoothing Cost:**
   The smooth contribution $\mathcal{S}_{\mathrm{smooth}}(N, K) = N (\log Y + H_K - 2 - \gamma)$ is given in closed form and evaluates to high precision via standard harmonic number expansions.

---

## 6. Concrete Finite Numerical Test for Muse

To enable immediate independent verification by Muse or another reviewer, the table below provides the exact values of the components across eleven test values of $N \in [16, 1000]$.

In all cases:
- $K = \lfloor\sqrt{N}\rfloor$
- $M = \lfloor N/2 \rfloor$
- $U = \lfloor\sqrt{M}\rfloor$
- Defect is $|D_N - (\mathcal{S}_{\mathrm{smooth}} + \Sigma_1 + \Sigma_2)|$.
Table values reproduced by the independent `factorization_diagnostic.py` (fresh sieve, exact integer $\mu$, float64 logs) to better than $5 \times 10^{-5}$; record: `results_factorization_diagnostic.json`. Defects are float64-level. Finite agreement is diagnostic, not a bound proof. (Caption corrected 2026-09-20: no generating script or precision record existed for this table.)

| N | K | M | U | S_smooth | Sigma_1 | Sigma_2 | D_N | Defect |
|---:|--:|--:|--:|---------:|--------:|--------:|----:|--------:|
| 16 | 4 | 8 | 2 | 14.2786 | -18.2432 | 0.6931 | -3.2715 | 5.08e-16 |
| 25 | 5 | 12 | 3 | 32.8889 | -34.8791 | 0.0000 | -1.9902 | 1.64e-15 |
| 36 | 6 | 18 | 4 | 59.9236 | -64.1311 | 0.6931 | -3.5144 | 3.60e-15 |
| 49 | 7 | 24 | 4 | 96.1160 | -100.8375 | 3.5835 | -1.1379 | 2.26e-15 |
| 64 | 8 | 32 | 5 | 142.0853 | -139.9752 | -4.7875 | -2.6774 | 5.07e-15 |
| 81 | 9 | 40 | 6 | 198.3672 | -207.9158 | 8.3710 | -1.1776 | 5.09e-15 |
| 100 | 10 | 50 | 7 | 265.4338 | -266.9905 | -4.0943 | -5.6511 | 9.49e-15 |
| 144 | 12 | 72 | 8 | 433.5698 | -431.5832 | -4.4308 | -2.4441 | 6.81e-15 |
| 200 | 14 | 100 | 10 | 666.7213 | -690.2463 | 29.6492 | 6.1242 | 2.14e-14 |
| 400 | 20 | 200 | 14 | 1606.5025 | -1591.4802 | -16.8221 | -1.7997 | 1.29e-14 |
| 1000 | 31 | 500 | 22 | 4923.7976 | -5057.3877 | 126.4718 | -7.1182 | 1.39e-13 |

### Key Observations from the Numerical Evidence:
1. **Defect:** The algebraic defect is identically at the machine epsilon level ($< 2 \times 10^{-13}$ across the entire range), verifying that the two-piece Dirichlet hyperbola decomposition is exact.
2. **Main Cancellation:** At $N = 400$, $\mathcal{S}_{\mathrm{smooth}} = +1606.5025$ and $\Sigma_1 = -1591.4802$. Their sum is $+15.0223$. When added to $\Sigma_2 = -16.8221$, the result is $D_N = -1.7997$. This demonstrates how $\Sigma_1$ absorbs over 99% of the smooth scale growth.
3. **Type II Behavior:** $|\Sigma_2|$ remains small relative to $N$ across all tested cases ($|\Sigma_2| \le 127$ at $N = 1000$), but oscillates in sign, reflecting the underlying Mertens oscillations.
