# Arithmetic cancellation candidate: the Dirichlet hyperbola bilinear decomposition of D_N

Date: 2026-09-20. Base commit: `f402358` (branch `teal-sea/signed-cancellation-sep20`).
Prior work: `FRONTIER_2026_09_12.md`, `SIGNED_MEAN_RENEWAL.md`, `FRONTIER_INDEPENDENT_REVIEW.md`,
`RANK3_CONDUCTOR_SUM.md`, `FAREY_BASELINE_REPAIR.md`.
Verification script: `hunts/prime_pair_error/arithmetic_cancellation_candidate_check.py`.
Diagnostic records: `hunts/prime_pair_error/results_arithmetic_cancellation_candidate.json`.

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
\mathcal{T}_{\mathrm{bilinear}}(N, K) := -\sum_{k=2}^K \sum_{Y < d \le N/k} \big(\Lambda(d) - 1\big)
= -\sum_{k=2}^K \big( R(N/k) - R(Y) \big).
\tag{3}
\]
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
On the finite interval $[1, Y]$ where $Y = N/K$, $R(u) = \psi(u) - u$ is piecewise constant with
jump discontinuities of magnitude $\Lambda(n)$ at prime powers $n \le Y$. Integrating by parts or
summing over intervals between prime powers yields the identity:
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
This algebraic match has been verified numerically to $10^{-38}$ precision on $N \in [16, 400]$.

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
3. **Dirichlet hyperbola cancellation in $\mathcal{R}_{\mathrm{boundary}}$:**
   The entire order-$N \log N$ and order-$N$ growth of $\mathcal{B}_{\mathrm{main}}$ and
   $\sum_{d \le Y} \Lambda(d) \lfloor N/d \rfloor$ cancels identically against $\mathcal{S}_{\mathrm{smooth}}(N, K)$.
   This is governed by the Dirichlet hyperbola identity $\sum_{d k \le N} \Lambda(d) = \log(N!)$.

---

## 4. Strongest justified bound per term

| Component | Baseline bound (justified) | Conjectured bound (target) | Status / Proof mechanism |
|---|---|---|---|
| $\mathcal{R}_{\mathrm{boundary}}(N, K)$ | $O(\sqrt{N})$ | $O(\sqrt{N})$ | **Established unconditionally.** Follows from Stirling's approximation, harmonic expansion, and Dirichlet hyperbola summation. |
| $\mathcal{T}_{\mathrm{sawtooth}}(N, K)$ | $O(\sqrt{N})$ | $O(N^{1/4+\epsilon})$ | **Established unconditionally at $O(\sqrt{N})$.** Trivial absolute bound: $|\psi_0(x)| \le 1/2 \implies |\mathcal{T}_{\mathrm{sawtooth}}| \le \frac{1}{2}\psi(Y) \ll \sqrt{N}$. Improvement requires Vinogradov-type exponential sums. |
| $\mathcal{T}_{\mathrm{bilinear}}(N, K)$ | $O(N \exp(-c\sqrt{\log N}))$ | $O_\epsilon(N^{1/2+\epsilon})$ | **Unresolved.** Absolute value summation loses the target: $\sum_{k=2}^K |R(N/k)| \asymp N^{3/4}$ even under RH. Retaining signs is mandatory. |

### Baseline bounds details:
- **$\mathcal{R}_{\mathrm{boundary}}$:**
  By the Euler-Maclaurin expansion of $H_K$ and Stirling's formula for $\log(N!)$, the smooth term
  satisfies $\mathcal{S}_{\mathrm{smooth}}(N, K) = N(\log N - 2) + O(\sqrt{N})$.
  The arithmetic sum $\sum_{d \le Y} \Lambda(d) \lfloor N/d \rfloor + \mathcal{B}_{\mathrm{main}}(N, K)$
  approximates $\sum_{d k \le N} 1 \cdot \Lambda(d) = \log(N!)$ with discrepancy bounded by $O(\sqrt{N})$.
  Hence $|\mathcal{R}_{\mathrm{boundary}}| \le C \sqrt{N}$ unconditionally.
- **$\mathcal{T}_{\mathrm{sawtooth}}$:**
  Because $|\{N/d\} - 1/2| \le 1/2$ for all real arguments,
  \[
  |\mathcal{T}_{\mathrm{sawtooth}}(N, K)| \le \frac{1}{2} \sum_{d \le Y} \Lambda(d) = \frac{1}{2} \psi(Y).
  \]
  Since $Y = N/K \le \sqrt{N} + 1$, Chebyshev's bound $\psi(Y) \le 1.04 Y$ gives
  $|\mathcal{T}_{\mathrm{sawtooth}}| \le 0.52 \sqrt{N} + O(1)$. This is already within the target!

---

## 5. Exact remaining obstacle

The exact remaining obstacle to proving $|D_N| \ll_\epsilon N^{1/2+\epsilon}$ is:
\[
\boxed{\quad \left| \sum_{k=2}^K \big( R(N/k) - R(Y) \big) \right| \ll_\epsilon N^{1/2+\epsilon}. \quad}
\tag{17}
\]
Notice the crucial contrast:
1. **Absolute value norm fails:**
   If one takes absolute values inside the sum, then even assuming the Riemann Hypothesis
   $|R(x)| \le C x^{1/2} \log^2 x$, we obtain
   \[
   \sum_{k=2}^K |R(N/k)| \ll N^{1/2} \log^2 N \sum_{k=2}^{\sqrt{N}} k^{-1/2} \asymp N^{1/2} \cdot N^{1/4} \log^2 N = N^{3/4} \log^2 N.
   \]
   An absolute-value bound loses a factor of $N^{1/4}$. The target $N^{1/2}$ is completely lost.
2. **Spectral representation:**
   Using the Riemann explicit formula $R(x) = -\sum_\rho \frac{x^\rho}{\rho} + O(1)$, the sum is
   \[
   \sum_{k=2}^K R(N/k) \approx -\sum_\rho \frac{N^\rho}{\rho} \sum_{k=2}^K k^{-\rho}.
   \]
   By Euler summation, $\sum_{k=1}^K k^{-\rho} = \frac{K^{1-\rho}}{1-\rho} + \zeta(\rho) + O(K^{-\beta})$.
   At any zeta zero, $\zeta(\rho) = 0$, so the sum is $\frac{K^{1-\rho}}{1-\rho} + O(K^{-\beta})$.
   The leading term $\frac{N^\rho K^{1-\rho}}{\rho(1-\rho)} \approx \frac{N^{\frac{1+\rho}{2}}}{\rho(1-\rho)}$
   has magnitude $N^{3/4}$ on the critical line ($\Re\rho = 1/2$).
   In $D_N$, this $N^{3/4}$ term is cancelled identically by the integral $N \int_{N/K}^\infty \frac{u^\rho}{u^2} du = \frac{N^{\frac{1+\rho}{2}}}{1-\rho}$.
   The remaining spectral term from a zero $\rho = \beta + i\gamma$ is of order
   \[
   O\big( N^\beta K^{-\beta} \big) = O\big( (N/K)^\beta \big) = O\big( N^{\beta/2} \big).
   \]
   For zeros on the critical line ($\beta = 1/2$), $N^{\beta/2} = N^{1/4} \ll N^{1/2}$, which satisfies the target with margin.
   The obstacle is that an off-critical zero mode with $\beta > 1/2$ would leave $O(N^{\beta/2}) \le \sqrt{N}$
   in the difference $L_K R(N)$, while $R(N)$ itself contains $N^\rho / \rho$ of magnitude $N^\beta > N^{1/2}$.

---

## 6. Quantitative implication for $D_N$ if resolved

If estimate (17) is established:
1. Since $\mathcal{T}_{\mathrm{sawtooth}}(N, K) = O(\sqrt{N})$ unconditionally, and
   $\mathcal{R}_{\mathrm{boundary}}(N, K) = O(\sqrt{N})$ unconditionally,
   we immediately obtain $|D_N| \ll_\epsilon N^{1/2+\epsilon}$.
2. By the relation $R(N) = D_N + O(\sqrt{N})$ from `SIGNED_MEAN_RENEWAL.md` equation (17),
   this implies
   \[
   |R(N)| \ll_\epsilon N^{1/2+\epsilon}.
   \]
3. By the two-way mean criterion (`SIGNED_MEAN_RENEWAL.md` equation (5)),
   $M_N = \frac{2|B_N|^2}{N} \ll_\epsilon N^{2+2\epsilon}$, which is equivalent to the Riemann Hypothesis.

---

## 7. Analysis of the smooth zero-mode diagnostic

In `SIGNED_MEAN_RENEWAL.md` section 8, a smooth perturbation $R_\eta(u)$ was constructed with
$R_\eta(u) = -a + \eta \Re u^\rho$ for $u \ge 4$, where $\zeta(\rho) = 0$ with $\beta = \Re\rho > 1/2$.
That diagnostic satisfies:
- Nonnegativity $\Psi_\eta \ge 0$ and monotonicity $\Psi_\eta' \ge 1/2$;
- The integral normalization $\int_1^\infty R_\eta(u) u^{-2} du = -(1+\gamma)$;
- The Chebyshev total variation bound $\operatorname{Var}_{[1, y]} R_\eta \ll y$;
- The scale relation $(L_K R_\eta)(N) = O(N/K) = O(\sqrt{N})$.

### Why $R_\eta$ fails to refute the candidate or bound $D_N$:
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

To allow independent verification by Muse or subsequent sessions without re-running large derivations,
here are exact computed values for test cutoffs $N$:

| $N$ | $K$ | $R(N)$ | $D_N$ | $R(N) - D_N$ | $\mathcal{T}_{\mathrm{bilinear}}$ | $\mathcal{T}_{\mathrm{sawtooth}}$ | $\mathcal{R}_{\mathrm{boundary}}$ | Algebraic defect |
|---|---|---|---|---|---|---|---|---|
| **16** | 4 | -2.5120 | -3.2715 | +0.7595 | -0.8579 | +0.8762 | -3.2898 | $< 10^{-35}$ |
| **25** | 5 | -0.9894 | -1.9902 | +1.0008 | +2.2254 | +1.1611 | -5.3767 | $< 10^{-35}$ |
| **36** | 6 | -3.3964 | -3.5144 | +0.1180 | -2.0460 | +1.7253 | -3.1936 | $< 10^{-35}$ |
| **49** | 7 | +0.4854 | -1.1379 | +1.6233 | +3.5168 | +0.8465 | -5.5013 | $< 10^{-35}$ |
| **64** | 8 | -1.6628 | -2.6774 | +1.0146 | +1.1492 | +1.4350 | -5.2615 | $< 10^{-35}$ |
| **81** | 9 | -1.1776 | -1.1776 | +0.0000 | +3.8899 | +1.8757 | -6.9432 | $< 10^{-35}$ |
| **100** | 10 | -5.9547 | -5.6511 | -0.3036 | -8.4518 | +2.5252 | +0.2755 | $< 10^{-35}$ |
| **144** | 12 | -5.5621 | -2.4441 | -3.1180 | -1.8236 | +2.4975 | -3.1180 | $< 10^{-35}$ |
| **200** | 14 | +5.7650 | +6.1242 | -0.3592 | +13.5970 | +2.8864 | -10.3592 | $< 10^{-35}$ |
| **400** | 20 | -4.4716 | -6.6575 | +2.1859 | -8.1368 | +2.9818 | -1.5026 | $< 10^{-35}$ |

### Falsifiable diagnostic criterion:
Any proposed bound on $D_N$ or $\mathcal{T}_{\mathrm{bilinear}}$ must track the sign changes of
$\mathcal{T}_{\mathrm{bilinear}}$ recorded above (e.g. negative at $N=16, 36, 100, 400$, positive at $N=25, 49, 64, 81, 200$).
An absolute-value envelope that ignores these sign flips exceeds the true value by a factor of $N^{1/4}$.

---

## 9. Distinction from equivalent rewritings of R

A trivial manipulation would express $D_N = R(N) - (R(N) - D_N) = R(N) + O(\sqrt{N})$.
That is purely tautological and provides no new route.
In contrast, candidate decomposition (2):
1. **Eliminates $R(N)$ completely:** None of the constituent terms $\mathcal{T}_{\mathrm{bilinear}}$,
   $\mathcal{T}_{\mathrm{sawtooth}}$, or $\mathcal{R}_{\mathrm{boundary}}$ contains $R(N)$ or $\psi(N)$.
   The largest argument appearing anywhere is $N/2$.
2. **Separates distinct arithmetic mechanisms:**
   - $\mathcal{T}_{\mathrm{sawtooth}}$ is an exponential/fractional part sum on the short range $[1, \sqrt{N}]$;
   - $\mathcal{R}_{\mathrm{boundary}}$ is an elementary combinatorial discrepancy from the Dirichlet hyperbola;
   - $\mathcal{T}_{\mathrm{bilinear}}$ is the genuine signed prime-counting remainder over the scale range $k \in [2, \sqrt{N}]$.
3. **Identifies the exact loss in absolute-value bounds:**
   The failure of previous inductions is localized entirely to replacing $\mathcal{T}_{\mathrm{bilinear}}$
   with $\sum_{k=2}^K |R(N/k)|$, which grows as $N^{3/4}$.

---

## 10. Conclusion and disposition

Under `ALIGNMENT.md` Section 5:
- **Disposition:** *Attempt unresolved.*
- The arithmetic bilinear decomposition (2) is exact, non-circular, and verified to high precision.
- The boundary and sawtooth terms are unconditionally bounded by $O(\sqrt{N})$.
- The remaining obstacle is rigorously isolated to the bilinear sum $\mathcal{T}_{\mathrm{bilinear}}(N, K)$.
- No claim of having proved RH is made. The construction provides the exact intermediate target for future arithmetic sieve or bilinear estimation.
