# Arithmetic cancellation candidate: the Dirichlet hyperbola bilinear decomposition of D_N

Date: 2026-09-20 (revised following independent review). Base commit: `271fc26`.
Prior work: `FRONTIER_2026_09_12.md`, `SIGNED_MEAN_RENEWAL.md`, `FRONTIER_INDEPENDENT_REVIEW.md`,
`RANK3_CONDUCTOR_SUM.md`, `FAREY_BASELINE_REPAIR.md`, `ARITHMETIC_CANCELLATION_REVIEW.md`.
Verification scripts: `hunts/prime_pair_error/arithmetic_cancellation_candidate_check.py`,
`hunts/prime_pair_error/independent_arithmetic_cancellation_check.py`.
Diagnostic records: `hunts/prime_pair_error/results_arithmetic_cancellation_candidate.json`,
`hunts/prime_pair_error/independent_arithmetic_cancellation_evidence.json`.

---

## 1. Exact candidate and parameter ranges

Let $N \ge 4$ be an integer. Define
\[
K = \lfloor\sqrt{N}\rfloor, \qquad Y = \frac{N}{K}.
\]
Then $K \le \sqrt{N} < K + 1$ and $\sqrt{N} \le Y < \sqrt{N} + 1$.
The von Mangoldt function $\Lambda(n)$ is supported on all prime powers $n = p^m$ ($m \ge 1$),
with $\psi(x) = \sum_{n \le x} \Lambda(n)$ and $R(x) = \psi(x) - x$.
The target quantity isolated in `SIGNED_MEAN_RENEWAL.md` equation (17) is
\[
D_N = N \int_{N/K}^\infty \frac{R(u)}{u^2}\,du - \sum_{k=2}^K R(N/k).
\tag{1}
\]
The existing unconditional scale reduction proves $R(N) = D_N + O(\sqrt{N})$.
The RH target is $|D_N| \ll_\epsilon N^{1/2+\epsilon}$ for every $\epsilon > 0$.

The candidate decomposition developed here is the exact algebraic partition
\[
\boxed{\quad D_N = \mathcal{T}_{\mathrm{bilinear}}(N, K) + \mathcal{T}_{\mathrm{sawtooth}}(N, K) + \mathcal{R}_{\mathrm{boundary}}(N, K), \quad}
\tag{2}
\]
where the constituent terms are defined explicitly as follows:

1. **The centered bilinear hyperbolic sum:**
\[
\mathcal{T}_{\mathrm{bilinear}}(N, K) := -\sum_{k=2}^K \sum_{Y < d \le N/k} \big(\Lambda(d) - 1\big).
\tag{3}
\]
Because $\sum_{Y < d \le N/k} 1 = \lfloor N/k \rfloor - \lfloor Y \rfloor$ uses discrete integer floors
while $R(N/k) - R(Y) = (\psi(N/k) - \psi(Y)) - (N/k - Y)$ uses continuous linear slopes,
the relation to the prime-counting error $R$ is
\[
\mathcal{T}_{\mathrm{bilinear}}(N, K) = -\sum_{k=2}^K \big( R(N/k) - R(Y) \big) + \mathcal{E}_{\mathrm{frac}}(N, K),
\tag{3'}
\]
where the exact rational discrepancy is
\[
\mathcal{E}_{\mathrm{frac}}(N, K) = \sum_{k=2}^K \left( \left\{ \frac{N}{k} \right\} - \{ Y \} \right).
\]
Since $0 \le \{x\} < 1$, $|\mathcal{E}_{\mathrm{frac}}(N, K)| < K \le \sqrt{N}$ is unconditionally bounded.
2. **The signed sawtooth correlation:**
\[
\mathcal{T}_{\mathrm{sawtooth}}(N, K) := -\sum_{d \le Y} \Lambda(d) \left( \left\{ \frac{N}{d} \right\} - \frac{1}{2} \right),
\tag{4}
\]
where $\{x\} = x - \lfloor x \rfloor$ denotes the fractional part.
3. **The explicit boundary remainder:**
\[
\mathcal{R}_{\mathrm{boundary}}(N, K) := \frac{1}{2}\psi(Y) - \mathcal{B}_{\mathrm{main}}(N, K) - \sum_{d \le Y} \Lambda(d) \left\lfloor \frac{N}{d} \right\rfloor + \mathcal{S}_{\mathrm{smooth}}(N, K),
\tag{5}
\]
in which
\[
\mathcal{B}_{\mathrm{main}}(N, K) = \sum_{k=2}^K \left( \left\lfloor \frac{N}{k} \right\rfloor - \lfloor Y \rfloor \right),
\tag{6}
\]
and the smooth baseline is
\[
\mathcal{S}_{\mathrm{smooth}}(N, K) = N \big( \log Y + H_K - 2 - \gamma \big), \qquad H_K = \sum_{k=1}^K \frac{1}{k}.
\tag{7}
\]

---

## 2. Complete derivation achieved

### 2.1. Exact reduction of the improper integral
The integral in (1) extends to infinity. In previous analyses, this feature appeared to prevent
a discrete arithmetic attack. However, the unconditional PNT ensures absolute convergence of
$\int_1^\infty R(u) u^{-2} du = -(1+\gamma)$. Therefore, the tail decomposes exactly as
\[
\int_{N/K}^\infty \frac{R(u)}{u^2}\,du = -(1+\gamma) - \int_1^{N/K} \frac{R(u)}{u^2}\,du.
\tag{8}
\]
On the finite interval $[1, Y]$ where $Y = N/K$, $\psi(u)$ is piecewise constant with jump discontinuities
of magnitude $\Lambda(n)$ at prime powers $n \le Y$, so $R(u) = \psi(u) - u$ is piecewise linear with slope $-1$.
Integrating by parts or summing over intervals between prime powers yields the identity:
\[
\int_1^Y \frac{\psi(u)}{u^2}\,du = \sum_{d \le Y} \Lambda(d) \int_d^Y \frac{du}{u^2}
= \sum_{d \le Y} \frac{\Lambda(d)}{d} - \frac{\psi(Y)}{Y}.
\tag{9}
\]
Since $\int_1^Y u^{-1} du = \log Y$, we have the exact closed formula
\[
\int_1^Y \frac{R(u)}{u^2}\,du = \sum_{d \le Y} \frac{\Lambda(d)}{d} - \frac{\psi(Y)}{Y} - \log Y.
\tag{10}
\]
Multiplying by $N$ (and noting that $N/Y = K$):
\[
N \int_{N/K}^\infty \frac{R(u)}{u^2}\,du = K \psi(Y) - N \sum_{d \le Y} \frac{\Lambda(d)}{d} + N \log Y - (1+\gamma)N.
\tag{11}
\]
This removes the improper integral completely. Every term is now evaluated at scales $u \le Y \approx \sqrt{N}$.

### 2.2. Subtraction of the discrete sum
The discrete sum in (1) is
\[
\sum_{k=2}^K R(N/k) = \sum_{k=2}^K \psi(N/k) - N \sum_{k=2}^K \frac{1}{k}
= \sum_{k=2}^K \psi(N/k) - N (H_K - 1).
\tag{12}
\]
Subtracting (12) from (11) gives the exact finite representation:
\[
D_N = \left[ K \psi(Y) - \sum_{k=2}^K \psi(N/k) - N \sum_{d \le Y} \frac{\Lambda(d)}{d} \right] + \mathcal{S}_{\mathrm{smooth}}(N, K),
\tag{13}
\]
where $\mathcal{S}_{\mathrm{smooth}}(N, K) = N (\log Y + H_K - 2 - \gamma)$ is given in (7).

### 2.3. Hyperbola decomposition of the arithmetic bracket
We partition the term $K \psi(Y) - \sum_{k=2}^K \psi(N/k)$:
\[
K \psi(Y) - \sum_{k=2}^K \psi(N/k) = \psi(Y) + \sum_{k=2}^K \big( \psi(Y) - \psi(N/k) \big)
= \psi(Y) - \sum_{k=2}^K \sum_{Y < d \le N/k} \Lambda(d).
\tag{14}
\]
Next, write $\Lambda(d) = 1 + (\Lambda(d) - 1)$. The double sum becomes
\[
\sum_{k=2}^K \sum_{Y < d \le N/k} \Lambda(d) = \mathcal{B}_{\mathrm{main}}(N, K) - \mathcal{T}_{\mathrm{bilinear}}(N, K),
\tag{15}
\]
with $\mathcal{B}_{\mathrm{main}}(N, K)$ and $\mathcal{T}_{\mathrm{bilinear}}(N, K)$ defined in (6) and (3).
Similarly, decomposing $N/d = \lfloor N/d \rfloor + 1/2 + (\{N/d\} - 1/2)$, the divisor sum evaluates to
\[
N \sum_{d \le Y} \frac{\Lambda(d)}{d} = \sum_{d \le Y} \Lambda(d) \left\lfloor \frac{N}{d} \right\rfloor + \frac{1}{2}\psi(Y) - \mathcal{T}_{\mathrm{sawtooth}}(N, K),
\tag{16}
\]
with $\mathcal{T}_{\mathrm{sawtooth}}(N, K)$ defined in (4).
Substituting (14), (15), and (16) into (13) proves the candidate identity (2) with zero defect:
\[
D_N = \mathcal{T}_{\mathrm{bilinear}}(N, K) + \mathcal{T}_{\mathrm{sawtooth}}(N, K) + \mathcal{R}_{\mathrm{boundary}}(N, K).
\]
This algebraic match has been verified independently to $10^{-12}$ at $N=100000$ and $10^{-38}$ on small $N$.

---

## 3. Decisive arithmetic property

The candidate replaces the scalar definition of $D_N$ with three structured components:

1. **Bilinear structure of $\mathcal{T}_{\mathrm{bilinear}}$:**
   The sum $\mathcal{T}_{\mathrm{bilinear}}(N, K) = -\sum_{k=2}^K \sum_{Y < d \le N/k} (\Lambda(d) - 1)$
   is an arithmetic bilinear form over the hyperbolic region $\{ (k, d) : 2 \le k \le K, Y < d \le N/k \}$.
   By Dirichlet convolution, $\Lambda(d) = \sum_{a b = d} \mu(a) \log b$.
   Therefore, $\mathcal{T}_{\mathrm{bilinear}}$ expands into a ternary sum:
   \[
   -\sum_{k=2}^K \sum_{\substack{a b \le N/k \\ a b > Y}} \mu(a) \log b + \sum_{k=2}^K \left( \left\lfloor \frac{N}{k} \right\rfloor - \lfloor Y \rfloor \right).
   \]
   The decisive arithmetic property is the sign oscillation of the Möbius function $\mu(a)$ across
   coprime factors, paired with bilinear decoupling between the scale variable $k$ and the modulus $d$.
2. **Equidistribution of fractional parts in $\mathcal{T}_{\mathrm{sawtooth}}$:**
   $\mathcal{T}_{\mathrm{sawtooth}}(N, K) = -\sum_{d \le Y} \Lambda(d) \psi_0(N/d)$, where $\psi_0(x) = \{x\} - 1/2$.
   The decisive arithmetic property is the non-resonance of the prime-power sequence $d = p^m$ with
   the modular inverses or fractional parts $N/d$.
3. **Exact boundary relation and algebraic coupling:**
   Let $A(N) = \sum_{d \le Y} \Lambda(d) \lfloor N/d \rfloor + \mathcal{B}_{\mathrm{main}}(N, K)$.
   Partitioning $\sum_{d k \le N} \Lambda(d) = \log(N!)$ reveals the exact algebraic identity
   \[
   A(N) - \log(N!) = \mathcal{T}_{\mathrm{bilinear}}(N, K) - \big(\psi(N) - \psi(Y)\big).
   \]
   Because $\psi(N) - \psi(Y) = N - Y + R(N) - R(Y) = N + o(N)$, this discrepancy is order $N$, not $O(\sqrt{N})$.
   The complementary region $\{k=1, d > Y\}$ carrying the main term $N - Y$ accounts for this difference.
   Consequently, the boundary term satisfies the exact identity
   \[
   \mathcal{R}_{\mathrm{boundary}}(N, K) = R(N) - \mathcal{T}_{\mathrm{bilinear}}(N, K) + E_{\mathrm{det}}(N),
   \]
   where $E_{\mathrm{det}}(N) = \mathcal{S}_{\mathrm{smooth}}(N, K) - \log(N!) + N - \frac{1}{2}\psi(Y) = -\frac{1}{2}R(Y) + O(\log N) = O(\sqrt{N})$.
   Hence bounding $\mathcal{R}_{\mathrm{boundary}}$ is algebraically coupled to bounding $R(N) - \mathcal{T}_{\mathrm{bilinear}}$.

---

## 4. Strongest justified bound per term

| Component | Baseline bound (justified) | Conjectured bound (target) | Status / Proof mechanism |
|---|---|---|---|
| $\mathcal{T}_{\mathrm{sawtooth}}(N, K)$ | $O(\sqrt{N})$ | $O(N^{1/4+\epsilon})$ | **Established unconditionally at $O(\sqrt{N})$.** Trivial absolute bound: $|\psi_0(x)| \le 1/2 \implies |\mathcal{T}_{\mathrm{sawtooth}}| \le \frac{1}{2}\psi(Y) \ll \sqrt{N}$. Improvement requires Vinogradov-type exponential sums. |
| $\mathcal{R}_{\mathrm{boundary}}(N, K)$ | $O(N \exp(-c\sqrt{\log N}))$ | $O(\sqrt{N})$ | **Unresolved (algebraically coupled).** Satisfies $\mathcal{R}_{\mathrm{boundary}} = R(N) - \mathcal{T}_{\mathrm{bilinear}} + E_{\mathrm{det}}(N)$ with $E_{\mathrm{det}} = O(\sqrt{N})$. It is bounded by $O(\sqrt{N})$ if and only if $R(N) - \mathcal{T}_{\mathrm{bilinear}} = O(\sqrt{N})$. |
| $\mathcal{T}_{\mathrm{bilinear}}(N, K)$ | $O(N \exp(-c\sqrt{\log N}))$ | $O_\epsilon(N^{1/2+\epsilon})$ | **Unresolved.** Upper bound under RH: $\sum_{k=2}^K |R(N/k)| \ll N^{3/4}\log^2 N$. Retaining signed cancellation across $k$ is mandatory. |

### Baseline bounds details:
- **$\mathcal{T}_{\mathrm{sawtooth}}$:**
  Because $|\{N/d\} - 1/2| \le 1/2$ for all real arguments,
  \[
  |\mathcal{T}_{\mathrm{sawtooth}}(N, K)| \le \frac{1}{2} \sum_{d \le Y} \Lambda(d) = \frac{1}{2} \psi(Y).
  \]
  Since $Y = N/K \le \sqrt{N} + 1$, Chebyshev's bound $\psi(Y) \le 1.04 Y$ gives
  $|\mathcal{T}_{\mathrm{sawtooth}}| \le 0.52 \sqrt{N} + O(1)$. This is already within the target unconditionally.
- **$\mathcal{R}_{\mathrm{boundary}}$:**
  Because $\mathcal{R}_{\mathrm{boundary}} = R(N) - \mathcal{T}_{\mathrm{bilinear}} + E_{\mathrm{det}}(N)$
  with $E_{\mathrm{det}}(N) = -\frac{1}{2}R(Y) + O(\log N) \ll \sqrt{N}$,
  unconditional bounds on $R(N)$ and $\mathcal{T}_{\mathrm{bilinear}}$ transfer directly to $\mathcal{R}_{\mathrm{boundary}}$.
  An elementary $O(\sqrt{N})$ bound for $\mathcal{R}_{\mathrm{boundary}}$ is not established independently of $R(N) - \mathcal{T}_{\mathrm{bilinear}}$.

---

## 5. Exact remaining obstacle

The exact remaining obstacle to proving $|D_N| \ll_\epsilon N^{1/2+\epsilon}$ is:
\[
\boxed{\quad \left| \mathcal{T}_{\mathrm{bilinear}}(N, K) \right| \ll_\epsilon N^{1/2+\epsilon} \quad \text{and} \quad \left| R(N) - \mathcal{T}_{\mathrm{bilinear}}(N, K) \right| \ll_\epsilon N^{1/2+\epsilon}. \quad}
\tag{17}
\]
Notice the crucial analytical features:
1. **Absolute value norm loses the target:**
   If one takes absolute values inside the sum, then even assuming the Riemann Hypothesis
   $|R(x)| \le C x^{1/2} \log^2 x$, partial summation gives the upper bound
   \[
   \sum_{k=2}^K |R(N/k)| \ll N^{1/2} \log^2 N \sum_{k=2}^{\sqrt{N}} k^{-1/2} \ll N^{3/4} \log^2 N.
   \]
   This upper bound leaves an $N^{1/4}$ gap above $N^{1/2}$. Retaining signed cancellation across scales $k$ is mandatory.
2. **Spectral representation:**
   Under the formal explicit formula $R(x) \approx -\sum_\rho \frac{x^\rho}{\rho}$, the mode sum is
   \[
   \sum_{k=2}^K R(N/k) \approx -\sum_\rho \frac{N^\rho}{\rho} \sum_{k=2}^K k^{-\rho}.
   \]
   By Euler summation, $\sum_{k=1}^K k^{-\rho} = \frac{K^{1-\rho}}{1-\rho} + \zeta(\rho) + \text{tail}_K$,
   where $\text{tail}_K = O(K^{-\beta})$.
   Crucially, $\sum_{k=2}^K k^{-\rho} = \sum_{k=1}^K k^{-\rho} - 1$.
   When testing the pure power mode $g(u) = u^\rho$ in the functional $D_N$, we find
   \[
   D_N[u^\rho] = N \int_{N/K}^\infty u^{\rho-2}\,du - \sum_{k=2}^K (N/k)^\rho = N^\rho B(\rho),
   \]
   where
   \[
   B(\rho) = \frac{K^{1-\rho}}{1-\rho} - \sum_{k=2}^K k^{-\rho} = 1 - \zeta(\rho) - \text{tail}_K.
   \]
   At any zeta zero, $\zeta(\rho) = 0$, so $B(\rho) = 1 - \text{tail}_K \to 1$ as $K \to \infty$.
   Therefore, for a zero mode:
   \[
   D_N[u^\rho] \sim N^\rho.
   \]
   On the critical line ($\Re\rho = 1/2$), this remainder has magnitude $N^{1/2}/|\rho|$, which is borderline
   at the target scale, not $N^{1/4}$.
   Off-critical with $\Re\rho = \beta > 1/2$, the mode produces $|D_N[u^\rho]| \sim N^\beta \gg \sqrt{N}$.
   For non-real zeros $\rho = \beta + i\gamma$, the mode $N^\rho = N^\beta e^{i\gamma\log N}$ oscillates;
   the bound is an envelope, not monotonic growth at every integer.
   This reconciles Section 5 with Section 7.

---

## 6. Quantitative implication for $D_N$ if resolved

Adding the exact boundary identity $\mathcal{R}_{\mathrm{boundary}} = R(N) - \mathcal{T}_{\mathrm{bilinear}} + E_{\mathrm{det}}(N)$
to the decomposition (2) yields the exact relation
\[
D_N = R(N) + \mathcal{T}_{\mathrm{sawtooth}}(N, K) + E_{\mathrm{det}}(N).
\tag{18}
\]
Since $|\mathcal{T}_{\mathrm{sawtooth}}| \le 0.52\sqrt{N} + O(1)$ and $|E_{\mathrm{det}}| = |-\frac{1}{2}R(Y) + O(\log N)| \ll \sqrt{N}$
are unconditionally bounded by $O(\sqrt{N})$, we recover $D_N = R(N) + O(\sqrt{N})$.
Therefore:
1. Bounding $|D_N| \ll_\epsilon N^{1/2+\epsilon}$ is equivalent to bounding $|R(N)| \ll_\epsilon N^{1/2+\epsilon}$.
2. In decomposition (2), establishing $|\mathcal{T}_{\mathrm{bilinear}}| \ll_\epsilon N^{1/2+\epsilon}$
   and $|\mathcal{R}_{\mathrm{boundary}}| \ll_\epsilon N^{1/2+\epsilon}$ jointly proves $|D_N| \ll_\epsilon N^{1/2+\epsilon}$,
   which by the two-way mean criterion (`SIGNED_MEAN_RENEWAL.md` equation (5)) is equivalent to RH.

---

## 7. Analysis of the smooth zero-mode diagnostic

In `SIGNED_MEAN_RENEWAL.md` section 8, a smooth perturbation $R_\eta(u)$ was constructed with
$R_\eta(u) = -a + \eta \Re u^\rho$ for $u \ge 4$, where $\zeta(\rho) = 0$ with $\beta = \Re\rho > 1/2$.
That diagnostic satisfies:
- Nonnegativity $\Psi_\eta \ge 0$ and monotonicity $\Psi_\eta' \ge 1/2$;
- The integral normalization $\int_1^\infty R_\eta(u) u^{-2} du = -(1+\gamma)$;
- The Chebyshev total variation bound $\operatorname{Var}_{[1, y]} R_\eta \ll y$;
- The scale relation $(L_K R_\eta)(N) = O(N/K) = O(\sqrt{N})$.

### Why $R_\eta$ fails to bound $D_N$:
1. **$D_N[R_\eta]$ is large:**
   By definition, $D_N[f] = f(N) - (L_K f)(N)$.
   For the smooth model $R_\eta$, $(L_K R_\eta)(N) = O(\sqrt{N})$, but $R_\eta(N) \asymp \eta N^\beta$.
   Therefore,
   \[
   D_N[R_\eta] \asymp \eta N^\beta \gg \sqrt{N}.
   \]
   Thus, $R_\eta$ does **not** satisfy $|D_N| \ll \sqrt{N}$. It honestly demonstrates that $L_K f(N) = O(\sqrt{N})$
   does not by itself force $f(N) = O(\sqrt{N})$ for general smooth functions.
2. **$R_\eta$ lacks the decisive arithmetic hypotheses:**
   - **No prime-power support:** $R_\eta$ is $C^1$ smooth; its derivative has no delta masses.
   - **Violates exact divisor recurrence:** For the true von Mangoldt function, $\sum_{k \le N} R(N/k) = G(N) = \log(N!) - N H_N$.
     For $R_\eta$, $\sum_{k \le N} R_\eta(N/k) = -(1+\gamma)N + O(1)$, which misses the exact arithmetic forcing by $\frac{1}{2}\log N + O(1)$.
   - **No Dirichlet convolution structure:** $R_\eta$ cannot be decomposed into a bilinear form with Möbius signs.
   The smooth model is a valid diagnostic for the transfer operator $L_K$, not a counterexample to RH.

---

## 8. Falsifiable small-case diagnostic for Muse

Verified independent values reproducing the author's JSON records (`results_arithmetic_cancellation_candidate.json`):

| $N$ | $K$ | $R(N)$ | $D_N$ | $R(N) - D_N$ | $\mathcal{T}_{\mathrm{bilinear}}$ | $\mathcal{T}_{\mathrm{sawtooth}}$ | $\mathcal{R}_{\mathrm{boundary}}$ | Algebraic defect |
|---|---|---|---|---|---|---|---|---|
| **16** | 4 | -2.5120 | -3.2715 | +0.7595 | -0.8579 | +0.8762 | -3.2898 | $< 10^{-35}$ |
| **25** | 5 | -0.9894 | -1.9902 | +1.0008 | +2.2254 | +1.1611 | -5.3767 | $< 10^{-35}$ |
| **36** | 6 | -3.3964 | -3.5144 | +0.1180 | -2.0460 | +1.7253 | -3.1936 | $< 10^{-35}$ |
| **49** | 7 | +0.4854 | -1.1379 | +1.6233 | +3.5168 | +0.8465 | -5.5013 | $< 10^{-35}$ |
| **64** | 8 | -1.6628 | -2.6774 | +1.0146 | +1.1492 | +1.4350 | -5.2615 | $< 10^{-35}$ |
| **81** | 9 | -0.4369 | -1.1776 | +0.7407 | +3.8899 | +1.8757 | -6.9432 | $< 10^{-35}$ |
| **100** | 10 | -5.9547 | -5.6511 | -0.3036 | -8.4518 | +2.5252 | +0.2755 | $< 10^{-35}$ |
| **144** | 12 | -2.3390 | -2.4441 | +0.1051 | -1.8236 | +2.4975 | -3.1180 | $< 10^{-35}$ |
| **200** | 14 | +6.1459 | +6.1242 | +0.0217 | +13.5970 | +2.8864 | -10.3592 | $< 10^{-35}$ |
| **400** | 20 | -2.1692 | -1.7997 | -0.3695 | +16.3908 | +4.0005 | -22.1910 | $< 10^{-35}$ |

---

## 9. Distinction from equivalent rewritings of R

A trivial manipulation would express $D_N = R(N) - (R(N) - D_N) = R(N) + O(\sqrt{N})$.
Candidate decomposition (2):
1. **Syntactic elimination:** The terms $\mathcal{T}_{\mathrm{bilinear}}$, $\mathcal{T}_{\mathrm{sawtooth}}$, and
   $\mathcal{R}_{\mathrm{boundary}}$ are defined without invoking $R(N)$ or $\psi(N)$; the largest argument is $N/2$.
2. **Algebraic coupling:** As revealed by the exact identity $\mathcal{R}_{\mathrm{boundary}} = R(N) - \mathcal{T}_{\mathrm{bilinear}} + E_{\mathrm{det}}(N)$,
   the decomposition does not eliminate $R(N)$ semantically. Rather, it partitions $D_N$ into a short-range
   sawtooth term $\mathcal{T}_{\mathrm{sawtooth}}$ and the coupled difference $R(N) - \mathcal{T}_{\mathrm{bilinear}}$.
3. **Identification of structure:** It separates the short-range fractional correlation $\mathcal{T}_{\mathrm{sawtooth}}$
   (bounded by $0.52\sqrt{N}$) from the multi-scale hyperbolic remainder $\mathcal{T}_{\mathrm{bilinear}}$.

---

## 10. Conclusion and disposition

Under `ALIGNMENT.md` Section 5:
- **Disposition:** *Attempt unresolved.*
- The arithmetic bilinear decomposition (2) is exact and verified independently.
- The sawtooth term $\mathcal{T}_{\mathrm{sawtooth}}$ is unconditionally bounded by $O(\sqrt{N})$.
- The boundary term $\mathcal{R}_{\mathrm{boundary}}$ and bilinear term $\mathcal{T}_{\mathrm{bilinear}}$ remain unresolved and algebraically coupled.
- The spectral remainder at a zero mode is of order $N^\beta$ (borderline $N^{1/2}$ on the critical line), not $N^{1/4}$.
- No claim of having proved RH is made.
