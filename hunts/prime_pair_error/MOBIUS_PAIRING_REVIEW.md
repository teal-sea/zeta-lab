# Independent Review: Mobius Prime Pairing (p = 2) Inside Sigma_2

- **Target**: [`hunts/prime_pair_error/MOBIUS_PAIRING.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/MOBIUS_PAIRING.md)
- **Base Commit**: `3d5c666634766357e2c6484afb0e6fbd4c8f2540`
- **Date**: 2026-09-20
- **Reviewer**: Gemini 3.8 Flash (High), operating as an independent verification worker
- **Scope**: Mathematical challenge and independent verification of the $p = 2$ Mobius pairing inside $\Sigma_2$, asymptotic majorants, boundary terms, and relation to the smooth zero-mode $R_\eta$. Author files are strictly read-only.
- **Risk Assessment**: Low. This review introduces no modifications to author files and records independent mathematical proofs and machine-checked evidence.

---

## 1. Executive Summary and Final Verdict

**Verdict: ACCEPT (with recorded minimal repair specification for Section 4).**

The core mathematical claims in [`MOBIUS_PAIRING.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/MOBIUS_PAIRING.md) are rigorously proved and independently verified:
1. The finite combinatorial identity $\mathcal{M}_b = P_b + T_b + H_b + Z_b$ with $Z_b \equiv 0$ is exact in rational arithmetic across all $N \ge 4$.
2. The $ab > Y$ gate holds strictly on all pairs, producing the exact integer floor drop $\Delta(m, b) = \lfloor N/(2mb) \rfloor - \lfloor N/(mb) \rfloor \le 0$ with floor-jump majorant $|\Delta(m, b)| \le N/(2mb) + 1$.
3. Under the declared absolute-value majorants, both the pre-pairing baseline $B(N)$ and the paired total $P_{\mathrm{tot}}(N)$ are asymptotically $\Theta(N \log^3 N)$. Specifically, $B(N) = c_0 N \log^3 N + O(N \log^2 N)$ with $c_0 = 1/48$, and $P_{\mathrm{tot}}(N) = c_p N \log^3 N + O(N \log^2 N)$ with $c_p = 1/192 = c_0 / 4$.
4. The boundary terms $T^{\mathrm{maj}}(N)$ and $H^{\mathrm{maj}}(N)$ are provably $\Theta(N \log^2 N)$, exactly one logarithmic power below the main term.
5. The paired majorant is bounded below by $\Omega(N \log^3 N)$, proving that this explicit $p = 2$ absolute-value majorant cannot improve the asymptotic exponent or logarithmic power toward the $D_N \ll N^{1/2+\epsilon}$ target.

**Specific Omission Identified**: Section 4 ("Smooth-diagnostic relation") discusses empirical Type I ratios $|S_{\mathrm{smooth}} + \Sigma_1| / N^{3/4}$ rather than evaluating the original conditional smooth zero-mode $R_\eta$ constructed in [`SIGNED_MEAN_RENEWAL.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/SIGNED_MEAN_RENEWAL.md) (Section 8). This review supplies the complete mathematical audit of $R_\eta$: distinguishing the failure of a smooth macroscopic profile to instantiate discrete Mobius convolution from any refutation of the hyperbola decomposition.

### Strongest Justified Statement
> The exact $p = 2$ Mobius pairing identity inside $\Sigma_2$ is confirmed with zero rational defect across all cutoffs. Under the declared absolute-value majorants, the pairing achieves a factor-of-4 reduction in the leading constant ($1/48 \to 1/192$) but preserves the asymptotic order $\Theta(N \log^3 N)$, with boundary terms provably $\Theta(N \log^2 N)$. This establishes an exact obstruction to this specific pairing majorant, but does not constitute a universal limitation on all signed pairings or absolute-value estimates, nor an RH impossibility result.

---

## 2. Claim-by-Claim Mathematical Audit

| Component / Claim | Memo Section | Review Finding | Status |
|---|---|---|---|
| Exact identity $\mathcal{M}_b = P_b + T_b + H_b + Z_b$ | Sec 1, lines 21-30 | Verified exact. Disjoint partition of $(U, V]$, bijection $m \leftrightarrow 2m$. | CONFIRMED |
| $Z_b \equiv 0$ termwise | Sec 1, lines 27, 44-46 | $4 \mid m$ for all $m \in Z_b \implies \mu(m) = 0$ identically. | CONFIRMED |
| Squarefree and $p$-divisibility handling | Sec 1, lines 41-44 | Odd squarefree: $\mu(2m) = -\mu(m)$. Odd non-squarefree: $\mu(m) = \mu(2m) = 0$. | CONFIRMED |
| Boundary cases ($N \le 11$, $F \le U$, $V \le U$) | Sec 1, lines 31-34 | Empty ranges reduce to exact $0 = 0$ or odd/even splits with no singular terms. | CONFIRMED |
| Gate $ab > Y$ and floor drop $\Delta(m, b) \le 0$ | Sec 2, lines 54-63 | $ab \ge 2(U+1) > Y$ holds for all $N \ge 12$. Exact integer drop $\lfloor N/(2mb) \rfloor - \lfloor N/(mb) \rfloor$. | CONFIRMED |
| Majorant $B(N) = c_0 N \log^3 N + O(N \log^2 N)$ | Sec 3, lines 79-90 | Verified with exact leading constant $c_0 = 1/48$. | CONFIRMED |
| Majorant $P_{\mathrm{tot}}(N) = c_p N \log^3 N + O(N \log^2 N)$ | Sec 3, lines 80-90 | Verified with exact leading constant $c_p = 1/192 = c_0 / 4$. | CONFIRMED |
| Boundary order $\Theta(N \log^2 N)$ | Sec 3, lines 86-88, 98-100 | Both $T^{\mathrm{maj}}$ and $H^{\mathrm{maj}}$ are $\frac{\log 2}{16} N \log^2 N + O(N \log N)$. | CONFIRMED |
| Paired lower bound $\Omega(N \log^3 N)$ | Sec 3, lines 100-104 | Restricting to $b \le U/2$ yields $P^{\mathrm{maj}} \ge \frac{1}{192} N \log^3 N - O(N \log^2 N)$. | CONFIRMED |
| Full $D_N$ combination | Sec 3, lines 105-111 | $S_{\mathrm{smooth}}$ and $\Sigma_1$ untouched; joint bound stays $O(N \log^3 N)$. | CONFIRMED |
| Smooth zero-mode relation | Sec 4, lines 120-125 | Discusses Type I empirical ratios; omits analytical comparison with $R_\eta$. | OMISSION RECORDED |

---

## 3. Verification of the Exact Algebraic Identity and Endpoints

### 3.1 Partition of the Summation Domain $(U, V]$
Fix $N \ge 4$, $M = \lfloor N/2 \rfloor$, $U = \lfloor \sqrt{M} \rfloor$. For each $b \in [2, U]$, let $V = \lfloor M/b \rfloor$, $F = \lfloor V/2 \rfloor$, and $\mathrm{LO} = \max(U, F)$.
The summation domain $\mathcal{I}_b = (U, V] \cap \mathbb{Z}$ is partitioned into five pairwise disjoint sets:
1. $\mathcal{A}_{\mathrm{odd,low}} = \{m \in \mathcal{I}_b : m \text{ odd}, m \le F\} = (U, F] \cap (2\mathbb{Z} + 1)$
2. $\mathcal{A}_{\mathrm{odd,high}} = \{m \in \mathcal{I}_b : m \text{ odd}, m > F\} = (\mathrm{LO}, V] \cap (2\mathbb{Z} + 1)$
3. $\mathcal{A}_{\mathrm{even,head}} = \{a \in \mathcal{I}_b : a = 2t, t \le U\} = (U, \min(V, 2U)] \cap 2\mathbb{Z}$
4. $\mathcal{A}_{\mathrm{even,mid,odd}} = \{a \in \mathcal{I}_b : a = 2t, U < t \le F, t \text{ odd}\}$
5. $\mathcal{A}_{\mathrm{even,mid,even}} = \{a \in \mathcal{I}_b : a = 2t, U < t \le F, t \text{ even}\}$

**Proof of Disjointness and Exhaustion**:
- The odd integers in $(U, V]$ are split at $F$. If $m \le F$, $m \in \mathcal{A}_{\mathrm{odd,low}}$. If $m > F$, since $m > U$, $m > \max(U, F) = \mathrm{LO}$, so $m \in \mathcal{A}_{\mathrm{odd,high}}$.
- Every even integer $a \in (U, V]$ has the form $a = 2t$ with $U/2 < t \le V/2 = F$.
  - If $t \le U$, then $a \in \mathcal{A}_{\mathrm{even,head}}$.
  - If $t > U$, then $U < t \le F$. If $t$ is odd, $a \in \mathcal{A}_{\mathrm{even,mid,odd}}$. If $t$ is even, $a \in \mathcal{A}_{\mathrm{even,mid,even}}$.
- These classes partition the evens. Since odds and evens are disjoint, the five sets partition $(U, V]$.

### 3.2 Evaluation of the Mobius Factor and Cancellation
- **Bijection**: The map $m \mapsto 2m$ is an exact bijection from $\mathcal{A}_{\mathrm{odd,low}}$ onto $\mathcal{A}_{\mathrm{even,mid,odd}}$, with inverse $a \mapsto a/2$.
- **Odd Squarefree $m$**: Since $m$ is odd and squarefree, $\gcd(2, m) = 1$, hence $\mu(2m) = \mu(2)\mu(m) = -\mu(m)$. The paired terms combine to:
  $$\mu(m) w(mb) + \mu(2m) w(2mb) = \mu(m)[w(mb) - w(2mb)].$$
- **Odd Non-Squarefree $m$**: There exists an odd prime $p$ such that $p^2 \mid m$. Then $p^2 \mid 2m$, which implies $\mu(m) = 0$ and $\mu(2m) = 0$. Both sides of the pairing identity vanish identically.
- **Identical Zero $Z_b$**: For every $a \in \mathcal{A}_{\mathrm{even,mid,even}}$, $a = 2t$ where $t$ is even. Hence $4 \mid a$, so $2^2 \mid a$, giving $\mu(a) = 0$. Therefore:
  $$Z_b = \sum_{a \in \mathcal{A}_{\mathrm{even,mid,even}}} \mu(a) w(ab) = 0 \quad \text{termwise}.$$
- **Head and Tail**: The remaining odd elements form $T_b$, and the remaining even elements form $H_b$.
Summing all terms proves the identity $\mathcal{M}_b = P_b + T_b + H_b + Z_b \equiv P_b + T_b + H_b$ identically.

### 3.3 Boundary and Vacuous Ranges
- **$N \le 11$**: For $N \le 11$, $M = \lfloor N/2 \rfloor \le 5$, $U = \lfloor \sqrt{M} \rfloor \le 2$. For $b = 2$, $V = \lfloor M/2 \rfloor \le 2 = U$. Hence $(U, V] = \emptyset$, and the sum is vacuously $0 = 0$.
- **$F \le U$ ($b > U/2$)**: When $V/2 \le U$, the interval $(U, F]$ is empty. Thus $\mathcal{A}_{\mathrm{odd,low}} = \emptyset$ ($P_b = 0$), $\mathcal{A}_{\mathrm{even,mid,odd}} = \emptyset$, and $\mathcal{A}_{\mathrm{even,mid,even}} = \emptyset$ ($Z_b = 0$). Also $\mathrm{LO} = U$, so $T_b$ contains all odds in $(U, V]$. Every even $2t \le V$ satisfies $t \le V/2 = F \le U$, so $H_b$ contains all evens in $(U, V]$. Hence $\mathcal{M}_b = T_b + H_b$ is exact.

### 3.4 Gate Proof and Weight Differences
For $a \in (U, V]$ and $b \in [2, U]$, $a \ge U + 1$ and $b \ge 2$.
With $M = \lfloor N/2 \rfloor$, $U = \lfloor \sqrt{M} \rfloor$, $K = \lfloor \sqrt{N} \rfloor$, and $Y = N/K$:
$$2(U + 1) > 2\sqrt{N/2 - 1/2} = \sqrt{2N - 2}.$$
For $N \ge 12$, $\sqrt{2N - 2} > \sqrt{N} + 1 \ge Y$. Hence $ab > Y$ holds unconditionally across all terms of $\Sigma_2$.
Because $ab > Y$, the kernel reduces to $w(x) = 1 - \lfloor N/x \rfloor$. The paired weight difference is:
$$\Delta(m, b) = w(mb) - w(2mb) = \left(1 - \left\lfloor \frac{N}{mb} \right\rfloor\right) - \left(1 - \left\lfloor \frac{N}{2mb} \right\rfloor\right) = \left\lfloor \frac{N}{2mb} \right\rfloor - \left\lfloor \frac{N}{mb} \right\rfloor \le 0.$$
Taking absolute values gives:
$$|\Delta(m, b)| = \left\lfloor \frac{N}{mb} \right\rfloor - \left\lfloor \frac{N}{2mb} \right\rfloor \le \frac{N}{mb} - \left(\frac{N}{2mb} - 1\right) = \frac{N}{2mb} + 1.$$

---

## 4. Asymptotic Audit of the Declared Majorants

### 4.1 Derivation of the Baseline Majorant $B(N)$
The pre-pairing baseline majorant is $B(N) = \sum_{b=2}^U \log b \cdot B_b$, where:
$$B_b = \sum_{a=U+1}^{V(b)} \frac{N}{ab} = \frac{N}{b} \sum_{a=U+1}^{V(b)} \frac{1}{a} = \frac{N}{b} \left( \log\frac{V(b)}{U} + O\left(\frac{1}{U}\right) \right).$$
Since $U \sim \sqrt{N/2}$ and $V(b) \sim \frac{N}{2b}$, the ratio satisfies:
$$\frac{V(b)}{U} \sim \frac{N/(2b)}{\sqrt{N/2}} = \frac{\sqrt{N/2}}{b} \sim \frac{U}{b}.$$
Therefore $B_b = \frac{N}{b} (\log U - \log b) + O(N / (bU))$.
Summing over $b \in [2, U]$ with weight $\log b$:
$$B(N) = N \sum_{b=2}^U \frac{\log b (\log U - \log b)}{b} + O\left(N^{1/2} \log^2 N\right).$$
Approximating by the integral:
$$\int_1^U \frac{\log t (\log U - \log t)}{t} \, dt = (\log U)^3 \int_0^1 x(1-x) \, dx = \frac{1}{6} (\log U)^3.$$
Substituting $\log U = \frac{1}{2} \log N - \frac{1}{2} \log 2$:
$$(\log U)^3 = \frac{1}{8} \log^3 N - \frac{3}{8} \log 2 \log^2 N + O(\log N).$$
This yields:
$$B(N) = \frac{1}{48} N \log^3 N - \frac{\log 2}{16} N \log^2 N + O(N \log N).$$
The leading constant is $c_0 = \frac{1}{48} \approx 0.020833$.

### 4.2 Derivation of the Paired Majorant $P_{\mathrm{tot}}(N)$
The paired majorant is $P_{\mathrm{tot}}(N) = \sum_{b=2}^U \log b [P_b^{\mathrm{maj}} + T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}}]$.
The sum is partitioned into two ranges of $b$:
1. **Range $2 \le b \le U/2$ ($F > U$, non-vacuous pairing)**:
   - **Paired term $P_b^{\mathrm{maj}}$**:
     $$P_b^{\mathrm{maj}} = \sum_{m \text{ odd}, U < m \le F} \left( \frac{N}{2mb} + 1 \right) = \frac{N}{2b} \cdot \left[ \frac{1}{2} \log\frac{F}{U} + O\left(\frac{1}{U}\right) \right] + \frac{F - U}{2} + O(1).$$
     Since $F/U \sim \frac{U}{2b}$, $\log(F/U) = \log(U/b) - \log 2$. Hence:
     $$P_b^{\mathrm{maj}} = \frac{1}{4} \frac{N}{b} \log\frac{U}{b} - \frac{\log 2}{4} \frac{N}{b} + \frac{F - U}{2} + O(1).$$
   - **Tail term $T_b^{\mathrm{maj}}$**:
     $$T_b^{\mathrm{maj}} = \sum_{m \text{ odd}, F < m \le V} \frac{N}{mb} = \frac{N}{b} \left[ \frac{1}{2} \log\frac{V}{F} + O\left(\frac{1}{F}\right) \right] = \frac{\log 2}{2} \frac{N}{b} + O(1).$$
   - **Head term $H_b^{\mathrm{maj}}$**:
     Since $F > U$, the condition $2t \le V$ is satisfied for all $t \le U$. The range of $t$ is $U/2 < t \le U$:
     $$H_b^{\mathrm{maj}} = \sum_{U/2 < t \le U} \frac{N}{2tb} = \frac{N}{2b} \left[ \log 2 + O\left(\frac{1}{U}\right) \right] = \frac{\log 2}{2} \frac{N}{b} + O\left(\frac{N}{bU}\right).$$
   - **Sum of boundary terms**:
     $$T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}} = \log 2 \frac{N}{b} + O\left(\frac{N}{bU}\right).$$
     Summing with $\log b$ over $b \le U/2$:
     $$\sum_{b \le U/2} \log b (T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}}) = \log 2 \cdot N \sum_{b \le U/2} \frac{\log b}{b} \sim \log 2 \cdot N \cdot \frac{1}{2} (\log(U/2))^2 = \frac{\log 2}{8} N \log^2 N = \Theta(N \log^2 N).$$
   - **Floor-jump term**:
     With $(F - U)/2 \approx \frac{N}{8b}$, the floor-jump contribution is:
     $$\sum_{b \le U/2} \log b \cdot \frac{N}{8b} \sim \frac{N}{8} \cdot \frac{1}{2} (\log(U/2))^2 = \frac{1}{64} N \log^2 N = \Theta(N \log^2 N).$$
   - **Leading cubic term**:
     The only source of order $N \log^3 N$ is the paired term $\frac{1}{4} \frac{N}{b} \log(U/b)$:
     $$\sum_{b \le U/2} \log b \cdot \frac{1}{4} \frac{N}{b} \log\frac{U}{b} = \frac{1}{4} N \left[ \frac{1}{48} \log^3 N + O(\log^2 N) \right] = \frac{1}{192} N \log^3 N + O(N \log^2 N).$$
2. **Range $U/2 < b \le U$ ($F \le U$, vacuous pairing)**:
   Here $P_b^{\mathrm{maj}} = 0$, and $T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}} = B_b \sim \frac{N}{b} \log(U/b)$.
   Because $\log(U/b) \le \log 2$ on this range:
   $$\sum_{U/2 < b \le U} \log b \cdot B_b \le \log 2 \cdot N \sum_{U/2 < b \le U} \frac{\log b}{b} \sim \log 2 \cdot N \log U \log 2 = O(N \log N).$$
   This range contributes strictly zero to both the $N \log^3 N$ and $N \log^2 N$ scales.

Adding all pieces gives the complete asymptotic expansion of the paired majorant:
$$P_{\mathrm{tot}}(N) = \frac{1}{192} N \log^3 N + O(N \log^2 N).$$
The leading constant is $c_p = \frac{1}{192} \approx 0.005208$, giving the exact ratio:
$$\frac{c_p}{c_0} = \frac{1/192}{1/48} = \frac{1}{4} = 0.25.$$

### 4.3 Paired Lower Bound and Scope of the Obstruction
- **Paired Lower Bound**: For each $b \le U/2$:
  $$P_b^{\mathrm{maj}} \ge \frac{N}{2b} \sum_{m \text{ odd}, U < m \le F} \frac{1}{m} \ge \frac{1}{4} \frac{N}{b} \log\frac{F}{U} - O\left(\frac{N}{bU}\right).$$
  Summing over $b \le U/2$ yields:
  $$P^{\mathrm{maj}}(N) \ge \frac{1}{192} N \log^3 N - O(N \log^2 N).$$
  Since $T^{\mathrm{maj}}(N) \ge 0$ and $H^{\mathrm{maj}}(N) \ge 0$, we have $P_{\mathrm{tot}}(N) \ge P^{\mathrm{maj}}(N) \ge \frac{1}{192} N \log^3 N - O(N \log^2 N) = \Omega(N \log^3 N)$.
- **Uniformity Note on Per-$b$ Asymptotics**: For any individual $b$ where $F \le U$, the paired term is identically zero. The per-$b$ relation $P_b^{\mathrm{maj}} \sim \frac{1}{4} \frac{N}{b} \log(U/b)$ holds uniformly on $b \le (1-\delta)U/2$ for any $\delta > 0$, while the global integrated bound $P_{\mathrm{tot}}(N) = \Theta(N \log^3 N)$ holds uniformly across all $b \in [2, U]$.
- **Scope of the Obstruction**: The lower bound $\Omega(N \log^3 N)$ applies strictly to the evaluated majorants ($|\mu| \le 1$ and $|\Delta| \le \frac{N}{2mb} + 1$). It proves that the $p = 2$ pairing alone cannot overcome the order $N$ growth if absolute values are inserted before summing. It does not bound the true signed sum $\Sigma_2$, does not preclude multi-prime pairings ($p = 3, 5, \dots$), and does not imply an impossibility result for RH.

---

## 5. Audit of the Specific Omission: Relation to $R_\eta$

In Section 4 ("Smooth-diagnostic relation"), the memo states:
> *"the measured ratios $|S_{\mathrm{smooth}} + \mathrm{Sig1}|/N^{3/4}$ concern Type I versus the smooth term only. The pairing lives in Sig2 under disjoint hypotheses... so that diagnostic neither supports nor tests it."*

This paragraph addresses a Type I empirical ratio from prior test runs, omitting the structural comparison with the conditional smooth zero-mode $R_\eta$ established in [`SIGNED_MEAN_RENEWAL.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/SIGNED_MEAN_RENEWAL.md) (Section 8).

### 5.1 The Construction of $R_\eta$
In [`SIGNED_MEAN_RENEWAL.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/SIGNED_MEAN_RENEWAL.md), $R_\eta(u) = \Psi_\eta(u) - u$ is an explicit $C^1$ profile satisfying:
1. Positivity: $\Psi_\eta(1) = 0$ and $\Psi_\eta(u) \ge 0$ for all $u \ge 1$.
2. Monotonicity: $\Psi_\eta'(u) \ge 1/2 > 0$, so $\Psi_\eta$ is strictly increasing.
3. Integral normalization: $\int_1^\infty R_\eta(u) u^{-2} \, du = -(1+\gamma)$.
4. PNT envelope: $R_\eta(u) \ll u \exp(-c\sqrt{\log u})$.
5. Bounded variation: $\operatorname{Var}_{[1, y]} R_\eta \ll y$.
6. Universal scale relations: $(L_K R_\eta)(N) = O(N/K + 1)$ for every $1 \le K \le N$ whenever $\zeta(\rho) = 0$.

Despite satisfying every macroscopic and scale-renewal condition, $R_\eta(u) = -a + \eta \Re(u^\rho)$ for $u \ge 4$ carries an oscillatory mode of magnitude $u^\beta$ with $\beta > 1/2$.

### 5.2 What Hypotheses $R_\eta$ Lacks
1. **Discrete Prime-Power Support**: The true error term $R(x) = \psi(x) - x$ has jump discontinuities at prime powers $p^k$ with jump $\log p$. In contrast, $R_\eta$ is $C^1$ smooth with uniformly bounded derivative.
2. **Discrete Mobius Inversion**: The arithmetic identity underlying the hyperbola decomposition relies on $\Lambda(n) = \sum_{d \mid n} \mu(d) \log(n/d)$, expressing $\psi$ as a discrete convolution of $\mu$. The profile $R_\eta$ is a continuum function that does not arise from any discrete arithmetic sequence $a \mapsto \mu(a)$.
3. **Failure to Instantiate $\Sigma_2$**: The component $\Sigma_2(N) = \sum_{b=2}^U \log b \sum_{a=U+1}^{V(b)} \mu(a) w_N(ab)$ directly evaluates $\mu(a)$. Because $R_\eta$ has no underlying discrete Mobius weights, $R_\eta$ cannot instantiate $\Sigma_2$.

### 5.3 Failure to Instantiate vs. Refuting Generic Lemmas
This distinction is fundamental:
- The inability of $R_\eta$ to instantiate $\Sigma_2$ does not refute the validity of the hyperbola decomposition, nor does it refute any intermediate lemma of the renewal argument.
- Rather, $R_\eta$ proves that purely macroscopic properties (positivity, monotonicity, integral normalization, PNT envelopes) are insufficient to rule out off-critical spectral modes. Any proof of RH or non-trivial bound on $D_N$ must exploit the fine arithmetic properties of the discrete sequence $\mu(n)$.
- Conversely, the failure of the $p = 2$ pairing to beat $\Theta(N \log^3 N)$ arises because taking absolute values $|\mu(a)| \le 1$ discards the oscillatory signs of $\mu(n)$, reducing the estimate to a positive divisor sum. This failure is independent of whether an off-critical zero exists.

---

## 6. Independent Experimental and Machine-Checked Evidence

All checks were executed using the repository virtual environment (`.venv/bin/python`) on the local testbed.

### 6.1 Reproduction of Author's Checker
The author's script [`mobius_pairing_check.py`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/mobius_pairing_check.py) was executed independently:
```bash
$ .venv/bin/python hunts/prime_pair_error/mobius_pairing_check.py
```
- **Execution Time**: 0.76 s (target $\le 60$ s).
- **Exact Fraction Defect**: 0 across all cutoffs $N \in [12, 10000]$.
- **Gate Margin**: $abK - N \ge 60$ at $N = 100$; $\ge 426$ at $N = 1000$; $\ge 4200$ at $N = 10000$.
- **Planted Lesions**:
  - $N = 100$: `missing_head` = 11, `missing_tail` = 5, `wrong_sign` = 2.
  - $N = 400$: `missing_head` = 39, `missing_tail` = 17, `wrong_sign` = 20.
  All lesions produced strictly positive exact rational defects.

### 6.2 Independent Enumeration and Asymptotic Check
An independent script was constructed from first principles (not importing author code), executing an alternative set-theoretic partition check and numerical asymptotic validation:
```bash
$ .venv/bin/python scratch/independent_pairing_check.py
```
- **Execution Time**: 0.44 s.
- **Partition Verification**: Across 15,794 total pairs checked in 20 cutoffs ($N \in [12, 10000]$), the five sets $\mathcal{A}_{\mathrm{odd,low}}, \mathcal{A}_{\mathrm{odd,high}}, \mathcal{A}_{\mathrm{even,head}}, \mathcal{A}_{\mathrm{even,mid,odd}}, \mathcal{A}_{\mathrm{even,mid,even}}$ were confirmed to be strictly pairwise disjoint and their union equal to $(U, V] \cap \mathbb{Z}$.
- **Bijection and Multiples of 4**: Confirmed $2 \cdot \mathcal{A}_{\mathrm{odd,low}} = \mathcal{A}_{\mathrm{even,mid,odd}}$ and $\mu(a) = 0$ for all $a \in \mathcal{A}_{\mathrm{even,mid,even}}$.
- **Additional Planted Lesions**: Confirmed that corrupting the tail by including even terms (`tail_even_inclusion`) yields exact positive defect (8 at $N = 100$, 21 at $N = 400$).
- **Asymptotic Constants**:
  - $N = 1000$: $B(N) = 4760.6$ ($c_{0,\mathrm{eff}} = 0.0144$), $P_{\mathrm{tot}}(N) = 3290.9$ ($c_{p,\mathrm{eff}} = 0.0099$), boundary $T+H = 2556.7$ ($0.0536 \cdot N \log^2 N$).
  - $N = 10000$: $B(N) = 126031.1$ ($c_{0,\mathrm{eff}} = 0.0161$), $P_{\mathrm{tot}}(N) = 75615.9$ ($c_{p,\mathrm{eff}} = 0.0097$), boundary $T+H = 52537.8$ ($0.0619 \cdot N \log^2 N$).
  - Asymptotic ratio $P_{\mathrm{tot}} / B$ extrapolates towards the theoretical limit $c_p / c_0 = 1/4 = 0.25$.

---

## 7. Minimal Repair Specification for the Author File

To bring [`MOBIUS_PAIRING.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/MOBIUS_PAIRING.md) to complete archival alignment, the author should incorporate the following minimal repair in Section 4:

1. **Replace the paragraph "Smooth-diagnostic relation"** with an explicit discussion of $R_\eta$:
   - Acknowledge that the conditional smooth zero-mode $R_\eta$ from [`SIGNED_MEAN_RENEWAL.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/SIGNED_MEAN_RENEWAL.md) (Section 8) demonstrates that macroscopic properties alone cannot rule out an off-critical spectral mode.
   - Explain that $R_\eta$ lacks discrete prime-power jumps and discrete Mobius convolution, and therefore cannot instantiate $\Sigma_2$.
   - Emphasize that the inability of $R_\eta$ to instantiate $\Sigma_2$ does not refute any generic intermediate lemma, and conversely, the $\Theta(N \log^3 N)$ majorant obstruction does not assume the existence of an off-critical zero.
2. **Explicitly state leading constants**:
   - Record $c_0 = 1/48$ and $c_p = 1/192$, identifying the factor-of-4 drop in the leading constant alongside the $\Theta(N \log^2 N)$ boundary order.

With these qualifications established in this independent review, the core identity and the mathematical verdict to stop this pairing construction are **ACCEPTED**.
