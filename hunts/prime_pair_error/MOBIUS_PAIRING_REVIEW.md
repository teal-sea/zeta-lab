# Independent Review: Mobius Prime Pairing (p = 2) Inside Sigma_2

- **Target**: [`hunts/prime_pair_error/MOBIUS_PAIRING.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/MOBIUS_PAIRING.md)
- **Base Commit**: `425e4f46355c1f68bce3ed064b818de7f265feb3` (repair of prior review dispatch; author files remain strictly read-only at `3d5c666634766357e2c6484afb0e6fbd4c8f2540`)
- **Date**: 2026-09-20
- **Reviewer**: Gemini 3.8 Flash (High), operating as an independent verification worker
- **Scope**: Mathematical challenge, rigorous asymptotic audit of declared majorants, and independent reproducible verification of the $p = 2$ Mobius pairing inside $\Sigma_2$.
- **Risk Assessment**: Low. All author files are untouched. Independent check script, generated evidence, and review are strictly self-contained.

---

## 1. Executive Summary and Final Verdict

**Verdict: ACCEPT (with recorded minimal repair specification for Section 4).**

The core mathematical claims in [`MOBIUS_PAIRING.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/MOBIUS_PAIRING.md) are confirmed:
1. The finite combinatorial identity $\mathcal{M}_b = P_b + T_b + H_b + Z_b$ with $Z_b \equiv 0$ is proved for all $N \ge 4$ by the five-way partition of $(U, V]$. It is machine-checked with zero rational defect across all 20 tested cutoffs $N \in [12, 10000]$.
2. The gate $ab > Y$ holds for all $N \ge 12$ by the integer inequality $2(U+1)K - N \ge 3 > 0$, producing the exact floor drop $\Delta(m, b) = \lfloor N/(2mb) \rfloor - \lfloor N/(mb) \rfloor \le 0$ with floor-jump majorant $|\Delta(m, b)| \le N/(2mb) + 1$.
3. Under the declared absolute-value majorants, both the baseline $B(N)$ and the paired total $P_{\mathrm{tot}}(N)$ are asymptotically $\Theta(N \log^3 N)$. Specifically, $B(N) = c_0 N \log^3 N + O(N \log^2 N)$ with $c_0 = 1/48$, and $P_{\mathrm{tot}}(N) = c_p N \log^3 N + O(N \log^2 N)$ with $c_p = 1/192 = c_0 / 4$.
4. The boundary terms $T^{\mathrm{maj}}(N)$ and $H^{\mathrm{maj}}(N)$ and the floor-jump costs are provably $\Theta(N \log^2 N)$, exactly one logarithmic power below the main term.
5. The paired majorant is bounded below by $\Omega(N \log^3 N)$, establishing that this explicit $p = 2$ absolute-value majorant cannot produce an asymptotic saving toward the $D_N \ll N^{1/2+\epsilon}$ target.

**Historical Correction and Provenance Retraction**:
The initial review draft cited an ephemeral path (`scratch/independent_pairing_check.py`) that was not part of the committed repository tree, and cited an invalid upper bound $Y \le \sqrt{N} + 1$. That provenance statement is hereby explicitly retracted. The independent verification is now fully reproducible via the committed script [`hunts/prime_pair_error/mobius_pairing_independent_check.py`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/mobius_pairing_independent_check.py) and its durable evidence file [`hunts/prime_pair_error/results_mobius_pairing_independent.json`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/results_mobius_pairing_independent.json).

### Strongest Justified Statement
> The exact $p = 2$ Mobius pairing identity inside $\Sigma_2$ is established by combinatorial partition for all $N \ge 4$, with zero rational defect verified across 20 cutoffs up to $N = 10000$. Under the declared absolute-value majorants, the pairing achieves an exact factor-of-4 drop in the leading constant ($1/48 \to 1/192$) while preserving the asymptotic order $\Theta(N \log^3 N)$, with boundary terms provably $\Theta(N \log^2 N)$. This establishes an exact obstruction to this specific pairing majorant. It does not bound the true signed sum $\Sigma_2$, does not limit general signed pairings or multi-prime mechanisms, and does not imply an RH impossibility result.

---

## 2. Claim-by-Claim Mathematical Audit

| Component / Claim | Memo Section | Review Finding | Status |
|---|---|---|---|
| Exact identity $\mathcal{M}_b = P_b + T_b + H_b + Z_b$ | Sec 1, lines 21-30 | Proved for all $N \ge 4$ by 5-way partition; machine-checked with zero defect at 20 cutoffs. | CONFIRMED |
| $Z_b \equiv 0$ termwise | Sec 1, lines 27, 44-46 | $4 \mid m$ for all $m \in Z_b \implies \mu(m) = 0$ identically. | CONFIRMED |
| Squarefree and $p$-divisibility handling | Sec 1, lines 41-44 | Odd squarefree: $\mu(2m) = -\mu(m)$. Odd non-squarefree: $\mu(m) = \mu(2m) = 0$. | CONFIRMED |
| Boundary cases ($N \le 11$, $F \le U$, $V \le U$) | Sec 1, lines 31-34 | Empty ranges reduce to exact $0 = 0$ or odd/even splits with zero defect. | CONFIRMED |
| Gate $ab > Y$ and floor drop $\Delta(m, b) \le 0$ | Sec 2, lines 54-63 | Proved by integer inequality $2(U+1)K - N \ge 3 > 0$ for all $N \ge 12$. | CONFIRMED |
| Majorant $B(N) = c_0 N \log^3 N + O(N \log^2 N)$ | Sec 3, lines 79-90 | Verified with exact leading constant $c_0 = 1/48$. | CONFIRMED |
| Majorant $P_{\mathrm{tot}}(N) = c_p N \log^3 N + O(N \log^2 N)$ | Sec 3, lines 80-90 | Verified with exact leading constant $c_p = 1/192 = c_0 / 4$. | CONFIRMED |
| Boundary order $\Theta(N \log^2 N)$ | Sec 3, lines 86-88, 98-100 | Both $T^{\mathrm{maj}}$ and $H^{\mathrm{maj}}$ are $\frac{\log 2}{16} N \log^2 N + O(N \log N)$. | CONFIRMED |
| Paired lower bound $\Omega(N \log^3 N)$ | Sec 3, lines 100-104 | Summed over $b \le b^*$ yields $P^{\mathrm{maj}} \ge \frac{1}{192} N \log^3 N - O(N \log^2 N)$. | CONFIRMED |
| Full $D_N$ combination | Sec 3, lines 105-111 | $S_{\mathrm{smooth}}$ and $\Sigma_1$ remain unpriced; joint bound $|D_N|$ is not bounded. | CONFIRMED |
| Smooth zero-mode relation | Sec 4, lines 120-125 | Discusses Type I empirical ratios; omits analytical comparison with $R_\eta$. | OMISSION RECORDED |

---

## 3. Proof of the Combinatorial Identity and Integer Gate

### 3.1 Partition of the Summation Domain $(U, V]$
Fix $N \ge 4$, $M = \lfloor N/2 \rfloor$, $U = \lfloor \sqrt{M} \rfloor$. For each $b \in [2, U]$, let $V = \lfloor M/b \rfloor$, $F = \lfloor V/2 \rfloor$, and $\mathrm{LO} = \max(U, F)$.
The integer summation interval $\mathcal{I}_b = (U, V] \cap \mathbb{Z}$ is partitioned into five pairwise disjoint sets:
1. $\mathcal{A}_{\mathrm{odd,low}} = \{m \in \mathcal{I}_b : m \text{ odd}, m \le F\} = (U, F] \cap (2\mathbb{Z} + 1)$
2. $\mathcal{A}_{\mathrm{odd,high}} = \{m \in \mathcal{I}_b : m \text{ odd}, m > F\} = (\mathrm{LO}, V] \cap (2\mathbb{Z} + 1)$
3. $\mathcal{A}_{\mathrm{even,head}} = \{a \in \mathcal{I}_b : a = 2t, t \le U\} = (U, \min(V, 2U)] \cap 2\mathbb{Z}$
4. $\mathcal{A}_{\mathrm{even,mid,odd}} = \{a \in \mathcal{I}_b : a = 2t, U < t \le F, t \text{ odd}\}$
5. $\mathcal{A}_{\mathrm{even,mid,even}} = \{a \in \mathcal{I}_b : a = 2t, U < t \le F, t \text{ even}\}$

**Proof of Disjointness and Exhaustion**:
- The odd integers in $(U, V]$ split at $F$. If $m \le F$, $m \in \mathcal{A}_{\mathrm{odd,low}}$. If $m > F$, since $m > U$, $m > \max(U, F) = \mathrm{LO}$, so $m \in \mathcal{A}_{\mathrm{odd,high}}$.
- Every even integer $a \in (U, V]$ has the form $a = 2t$ with $U/2 < t \le \lfloor V/2 \rfloor = F$ (since $a \le V \implies t \le V/2$, and $t$ integer gives $t \le \lfloor V/2 \rfloor = F$; corrected 2026-09-20: $V/2 = F$ is false for odd $V$).
  - If $t \le U$, then $a \in \mathcal{A}_{\mathrm{even,head}}$.
  - If $t > U$, then $U < t \le F$. If $t$ is odd, $a \in \mathcal{A}_{\mathrm{even,mid,odd}}$. If $t$ is even, $a \in \mathcal{A}_{\mathrm{even,mid,even}}$.
- These classes partition the evens. Since odds and evens are disjoint, the five sets partition $(U, V] \cap \mathbb{Z}$.

### 3.2 Evaluation of the Mobius Factor and Cancellation
- **Bijection**: The map $m \mapsto 2m$ is an exact bijection from $\mathcal{A}_{\mathrm{odd,low}}$ onto $\mathcal{A}_{\mathrm{even,mid,odd}}$, with inverse $a \mapsto a/2$.
- **Odd Squarefree $m$**: Since $m$ is odd and squarefree, $\gcd(2, m) = 1$, hence $\mu(2m) = \mu(2)\mu(m) = -\mu(m)$. The paired terms combine to:
  $$\mu(m) w(mb) + \mu(2m) w(2mb) = \mu(m)[w(mb) - w(2mb)].$$
- **Odd Non-Squarefree $m$**: There exists an odd prime $p$ such that $p^2 \mid m$. Then $p^2 \mid 2m$, which implies $\mu(m) = 0$ and $\mu(2m) = 0$. Both sides of the pairing identity vanish identically.
- **Identical Zero $Z_b$**: For every $a \in \mathcal{A}_{\mathrm{even,mid,even}}$, $a = 2t$ where $t$ is even. Hence $4 \mid a$, so $2^2 \mid a$, giving $\mu(a) = 0$. Therefore:
  $$Z_b = \sum_{a \in \mathcal{A}_{\mathrm{even,mid,even}}} \mu(a) w(ab) = 0 \quad \text{termwise}.$$
- **Head and Tail**: The remaining odd elements form $T_b$, and the remaining even elements form $H_b$.
Summing all terms proves the identity $\mathcal{M}_b = P_b + T_b + H_b + Z_b \equiv P_b + T_b + H_b$ for all $N \ge 4$.

### 3.3 Boundary and Vacuous Ranges
- **$N \le 11$**: For $N \le 11$, $M = \lfloor N/2 \rfloor \le 5$, $U = \lfloor \sqrt{M} \rfloor \le 2$. For $b = 2$, $V = \lfloor M/2 \rfloor \le 2 = U$. Hence $(U, V] = \emptyset$, and the sum is vacuously $0 = 0$.
- **$F \le U$**: When $F \le U$, the interval $(U, F]$ is empty. Thus $\mathcal{A}_{\mathrm{odd,low}} = \emptyset$ ($P_b = 0$), $\mathcal{A}_{\mathrm{even,mid,odd}} = \emptyset$, and $\mathcal{A}_{\mathrm{even,mid,even}} = \emptyset$ ($Z_b = 0$). Also $\mathrm{LO} = U$, so $T_b$ contains all odds in $(U, V]$. Every even $2t \le V$ satisfies $t \le \lfloor V/2 \rfloor = F \le U$ (corrected 2026-09-20: $V/2 = F$ is false for odd $V$), so $H_b$ contains all evens in $(U, V]$. Hence $\mathcal{M}_b = T_b + H_b$ holds with zero defect.

### 3.4 Rigorous Proof of the Gate $ab > Y$ via Integer Inequalities
The claim $Y \le \sqrt{N} + 1$ is known to fail at integers $N = K^2 + 2K$ (where $Y = K + 2 > \sqrt{N} + 1$). The gate $ab > Y = N/K$ does not depend on that false upper bound.

Recall $a \in (U, V]$ and $b \in [2, U]$, where $U = \lfloor \sqrt{M} \rfloor$, $M = \lfloor N/2 \rfloor$, and $K = \lfloor \sqrt{N} \rfloor$.
Since $a \ge U + 1$ and $b \ge 2$, we have $ab \ge 2(U + 1)$. To prove $ab > N/K$, it suffices to establish the integer inequality:
$$2(U + 1) K - N \ge 1 \quad \text{for all } N \ge 12.$$

**Analytical Proof for $N \ge 36$**:
By definition of the floor function:
- $K = \lfloor \sqrt{N} \rfloor > \sqrt{N} - 1$.
- $M = \lfloor N/2 \rfloor \ge (N-1)/2$.
- $U = \lfloor \sqrt{M} \rfloor > \sqrt{M} - 1 \ge \sqrt{(N-1)/2} - 1$, which implies $U + 1 > \sqrt{(N-1)/2}$.

Therefore:
$$2(U + 1) K > 2 \sqrt{\frac{N-1}{2}} (\sqrt{N} - 1) = \sqrt{2(N-1)} (\sqrt{N} - 1) = \sqrt{2} N \sqrt{1 - \frac{1}{N}} \left(1 - \frac{1}{\sqrt{N}}\right).$$
For $N \ge 36$:
$$\sqrt{1 - \frac{1}{N}} \ge \sqrt{\frac{35}{36}}, \qquad 1 - \frac{1}{\sqrt{N}} \ge \frac{5}{6}.$$
Hence $2(U+1)K/N > \sqrt{2}\cdot\sqrt{35/36}\cdot(5/6)$. Both sides are positive, so
squaring is exact (no lower bound is read off rounded decimals; corrected 2026-09-20):
$$\left(\sqrt{2}\cdot\sqrt{\frac{35}{36}}\cdot\frac{5}{6}\right)^2 = 2\cdot\frac{35}{36}\cdot\frac{25}{36} = \frac{875}{648} > 1,$$
verified in exact `Fraction` arithmetic. Therefore
$\sqrt{2}\cdot\sqrt{35/36}\cdot(5/6) > 1$ and $2(U + 1) K > N$ for all $N \ge 36$.

**Finite Integer Check for $12 \le N \le 35$**:
For $12 \le N \le 35$, $K \in \{3, 4, 5\}$:
- $K = 3$ ($N \in [12, 15]$): $M \ge 6, U = 2 \implies 2(U+1)K = 2(3)(3) = 18$. The margin $18 - N$ ranges from $6$ (at $N=12$) down to $3$ (at $N=15$).
- $K = 4$ ($N \in [16, 24]$):
  - $N \in [16, 17] \implies M = 8, U = 2 \implies 2(U+1)K = 2(3)(4) = 24 > N$ (margin $\ge 7$).
  - $N \in [18, 24] \implies M \ge 9, U \ge 3 \implies 2(U+1)K \ge 2(4)(4) = 32 > N$ (margin $\ge 8$).
- $K = 5$ ($N \in [25, 35]$):
  - $N \in [25, 31] \implies M \ge 12, U \ge 3 \implies 2(U+1)K \ge 2(4)(5) = 40 > N$ (margin $\ge 9$).
  - $N \in [32, 35] \implies M \ge 16, U = 4 \implies 2(U+1)K \ge 2(5)(5) = 50 > N$ (margin $\ge 15$).

The minimum margin across all $N \ge 12$ is exactly $3$ (at $N = 15$). Furthermore, all 387 near-square cases ($N = K^2 - 1, K^2, K^2 + 1, K^2 + 2K$ for $3 \le K \le 100$) were verified with strictly positive margin in [`mobius_pairing_independent_check.py`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/mobius_pairing_independent_check.py).
Hence $ab \ge 2(U + 1) > Y$ holds unconditionally for all $N \ge 12$.

Because $ab > Y$, the kernel reduces to $w(x) = 1 - \lfloor N/x \rfloor$. The paired weight difference is:
$$\Delta(m, b) = w(mb) - w(2mb) = \left(1 - \left\lfloor \frac{N}{mb} \right\rfloor\right) - \left(1 - \left\lfloor \frac{N}{2mb} \right\rfloor\right) = \left\lfloor \frac{N}{2mb} \right\rfloor - \left\lfloor \frac{N}{mb} \right\rfloor \le 0.$$
Taking absolute values gives:
$$|\Delta(m, b)| = \left\lfloor \frac{N}{mb} \right\rfloor - \left\lfloor \frac{N}{2mb} \right\rfloor \le \frac{N}{mb} - \left(\frac{N}{2mb} - 1\right) = \frac{N}{2mb} + 1.$$

---

## 4. Asymptotic Audit of the Declared Majorants

### 4.1 Exact Cutoff for Non-Vacuous Pairing and Endpoint-Strip Bounds
The condition $F > U$ is not identical to $b \le U/2$.
Because $F = \lfloor V/2 \rfloor = \lfloor \lfloor M/b \rfloor / 2 \rfloor = \lfloor M/(2b) \rfloor$:
$$F > U \iff F \ge U + 1 \iff \left\lfloor \frac{M}{2b} \right\rfloor \ge U + 1 \iff \frac{M}{2b} \ge U + 1 \iff b \le b^* := \left\lfloor \frac{M}{2(U+1)} \right\rfloor.$$

**Asymptotics of $b^*$ and the Vacuous Strip**:
Since $M = N/2 + O(1)$ and $U = \sqrt{N/2} + O(1)$:
$$b^* = \frac{M}{2(U+1)} + O(1) = \frac{U}{2} + O(1).$$
For $b \in [b^* + 1, U]$, $F \le U$, so the paired sum $P_b^{\mathrm{maj}}$ is identically zero.
On this strip, $T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}} = B_b = \sum_{a=U+1}^V \frac{N}{ab}$.
Since $V = \lfloor M/b \rfloor \le 2(U+1)$, the ratio $V/U \le 2 + O(1/U)$, so $\sum_{a=U+1}^V \frac{1}{a} \le \log 2 + O(1/U)$.
Summing with $\log b$ over the strip $b \in [b^* + 1, U]$:
$$\sum_{b=b^*+1}^U \log b \cdot B_b \le N \log U \sum_{b=b^*+1}^U \frac{\log 2 + O(1/U)}{b} \le (\log 2) N \log U \log\frac{U}{b^*} + O(N) = O(N \log N).$$
This entire strip contributes at most $O(N \log N)$, which is strictly lower-order than both $N \log^3 N$ and $N \log^2 N$.

### 4.2 Derivation of the Baseline Majorant $B(N)$
The baseline majorant is $B(N) = \sum_{b=2}^U \log b \cdot B_b$.
For each $b \in [2, U]$, $V(b) = \lfloor M/b \rfloor = \frac{N}{2b} + O(1)$ and $U = \sqrt{N/2} + O(1)$.
Thus $V(b)/U = \frac{U}{b} (1 + O(b/N + 1/U))$, which gives:
$$\log\frac{V(b)}{U} = \log\frac{U}{b} + O\left(\frac{1}{U}\right).$$
The inner harmonic sum evaluates to:
$$B_b = \frac{N}{b} \sum_{a=U+1}^{V(b)} \frac{1}{a} = \frac{N}{b} \left( \log\frac{U}{b} + O\left(\frac{1}{U}\right) \right) = \frac{N}{b} \log\frac{U}{b} + O\left(\frac{N}{bU}\right).$$
Summing over $b \in [2, U]$ with weight $\log b$:
$$B(N) = N \sum_{b=2}^U \frac{\log b (\log U - \log b)}{b} + O\left(\frac{N}{U} \sum_{b=2}^U \frac{\log b}{b}\right).$$
The error term is $O\left(\frac{N}{U} \log^2 U\right) = O(N^{1/2} \log^2 N)$.
By Euler-Maclaurin summation:
$$\sum_{b=2}^U \frac{\log b (\log U - \log b)}{b} = \int_1^U \frac{\log t (\log U - \log t)}{t} \, dt + O(\log U) = \frac{1}{6} (\log U)^3 + O(\log U).$$
Because $U = \sqrt{N/2} + O(1)$:
$$\log U = \frac{1}{2} \log N - \frac{1}{2} \log 2 + O(N^{-1/2}).$$
Cubing this expansion gives:
$$(\log U)^3 = \frac{1}{8} \log^3 N - \frac{3}{8} \log 2 \log^2 N + O(\log N).$$
Multiplying by $N/6$:
$$B(N) = \frac{1}{48} N \log^3 N - \frac{\log 2}{16} N \log^2 N + O(N \log N).$$
The leading constant is $c_0 = \frac{1}{48} \approx 0.020833$.

### 4.3 Derivation of the Paired Majorant $P_{\mathrm{tot}}(N)$
The paired majorant is $P_{\mathrm{tot}}(N) = \sum_{b=2}^U \log b [P_b^{\mathrm{maj}} + T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}}]$.
We evaluate the components over the non-vacuous range $b \le b^*$:
1. **Paired term $P_b^{\mathrm{maj}}$**:
   $$\sum_{m \text{ odd}, U < m \le F} \frac{1}{m} = \frac{1}{2} \log\frac{F}{U} + O\left(\frac{1}{U}\right).$$
   Multiplying by $\frac{N}{2b}$ requires carrying the error term as $O(N / (bU))$ (which is $\Theta(\sqrt{N})$ for small $b$):
   $$\frac{N}{2b} \sum_{m \text{ odd}, U < m \le F} \frac{1}{m} = \frac{N}{4b} \log\frac{F}{U} + O\left(\frac{N}{bU}\right).$$
   Since $F = \lfloor M/(2b) \rfloor = \frac{N}{4b} + O(1)$ and $U = \sqrt{N/2} + O(1)$, we have $F/U = \frac{U}{2b} (1 + O(1/U))$, so $\log(F/U) = \log(U/b) - \log 2 + O(1/U)$.
   The floor-jump term contributes $\sum_{m \text{ odd}, U < m \le F} 1 = \frac{F - U}{2} + O(1) = \frac{N}{8b} - \frac{U}{2} + O(1)$.
   Thus:
   $$P_b^{\mathrm{maj}} = \frac{1}{4} \frac{N}{b} \log\frac{U}{b} - \frac{\log 2}{4} \frac{N}{b} + \frac{N}{8b} + O\left(\frac{N}{bU} + U\right).$$
2. **Tail term $T_b^{\mathrm{maj}}$**:
   For odd $V$, $F = \lfloor V/2 \rfloor = (V-1)/2$, so $V/F = 2 + O(1/F) = 2 + O(b/N)$.
   Hence $\log(V/F) = \log 2 + O(b/N)$.
   The odd harmonic sum gives $\sum_{m \text{ odd}, F < m \le V} \frac{1}{m} = \frac{1}{2} \log 2 + O(b/N + 1/F) = \frac{1}{2} \log 2 + O(b/N)$.
   Multiplying by $N/b$, the error is $(N/b) \cdot O(b/N) = O(1)$:
   $$T_b^{\mathrm{maj}} = \frac{\log 2}{2} \frac{N}{b} + O(1).$$
3. **Head term $H_b^{\mathrm{maj}}$**:
   For $b \le b^*$, the condition $2t \le V$ holds for all $t \le U$, so $t$ runs over $U/2 < t \le U$:
   $$H_b^{\mathrm{maj}} = \frac{N}{2b} \sum_{U/2 < t \le U} \frac{1}{t} = \frac{N}{2b} \left( \log 2 + O\left(\frac{1}{U}\right) \right) = \frac{\log 2}{2} \frac{N}{b} + O\left(\frac{N}{bU}\right).$$
4. **Boundary and Floor-Jump Totals**:
   Adding $T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}}$:
   $$T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}} = \log 2 \frac{N}{b} + O\left(\frac{N}{bU} + 1\right).$$
   Summing over $b \le b^*$ with weight $\log b$:
   $$\sum_{b \le b^*} \log b (T_b^{\mathrm{maj}} + H_b^{\mathrm{maj}}) = (\log 2) N \sum_{b \le b^*} \frac{\log b}{b} + O(N^{1/2} \log^2 N) = \frac{\log 2}{8} N \log^2 N + O(N \log N).$$
   Summing the floor-jump term $\frac{N}{8b}$:
   $$\sum_{b \le b^*} \log b \cdot \frac{N}{8b} = \frac{N}{8} \cdot \frac{1}{8} \log^2 N + O(N \log N) = \frac{1}{64} N \log^2 N + O(N \log N).$$
5. **Main Cubic Term**:
   The only term generating order $N \log^3 N$ is $\frac{1}{4} \frac{N}{b} \log(U/b)$:
   $$\sum_{b \le b^*} \log b \cdot \frac{1}{4} \frac{N}{b} \log\frac{U}{b} = \frac{1}{4} N \cdot \left[ \frac{1}{48} \log^3 N + O(\log^2 N) \right] = \frac{1}{192} N \log^3 N + O(N \log^2 N).$$

Summing all pieces (and adding the $O(N \log N)$ contribution from $b > b^*$) gives:
$$P_{\mathrm{tot}}(N) = \frac{1}{192} N \log^3 N + O(N \log^2 N).$$
The leading constant is $c_p = \frac{1}{192} \approx 0.005208$, yielding the exact ratio:
$$\frac{c_p}{c_0} = \frac{1/192}{1/48} = \frac{1}{4} = 0.25.$$

### 4.4 Absence of Uniform Per-$b$ Asymptotics and Paired Lower Bound
- **Per-$b$ Behavior**: A uniform per-$b$ asymptotic of the form $P_b^{\mathrm{maj}} \sim \frac{1}{4} \frac{N}{b} \log(U/b)$ cannot hold uniformly as $b \to b^*$. When $b = \alpha U$ for any constant $\alpha \in (0, 1/2)$, $\log(U/b) = \log(1/\alpha) = O(1)$, so the term does not grow with $\log N$. As $b \to b^*$, $F - U \to 0$ and the relative error diverges. The asymptotic $c_p N \log^3 N$ is a property of the integrated sum over all $b$, not a uniform pointwise statement for every individual $b$.
- **Paired Lower Bound**: For each $b \le b^*$, $P_b^{\mathrm{maj}} \ge \frac{N}{4b} \log(F/U) - O(N/(bU))$. Summing over $b \le b^*$ yields $P^{\mathrm{maj}}(N) \ge \frac{1}{192} N \log^3 N - O(N \log^2 N)$. Since $T^{\mathrm{maj}} \ge 0$ and $H^{\mathrm{maj}} \ge 0$, we have $P_{\mathrm{tot}}(N) \ge \Omega(N \log^3 N)$.
- **Scope of the Obstruction**: This lower bound pins the specific majorants $B(N)$ and $P_{\mathrm{tot}}(N)$. It demonstrates that taking absolute values $|\mu(a)| \le 1$ and bounding floor differences by $|\Delta| \le N/(2mb) + 1$ cannot beat $\Theta(N \log^3 N)$. It does not constrain the true signed sum $\Sigma_2$, where signs of $\mu(a)$ can produce cancellations, nor does it constrain multi-prime pairings or imply an RH ceiling.
- **Complete $D_N$ Principal Expression**: In the exact partition $D_N = S_{\mathrm{smooth}} + \Sigma_1 + \Sigma_2$, $S_{\mathrm{smooth}}$ is explicit and $\Sigma_1$ remains unpriced. Because $\Sigma_1$ has no accepted bound, $|D_N|$ cannot be asserted to be $O(N \log^3 N)$ without an established estimate for $\Sigma_1$. The joint target $|D_N| \ll N^{1/2+\epsilon}$ remains unmoved.

---

## 5. Audit of the Specific Omission: Relation to $R_\eta$

In Section 4 ("Smooth-diagnostic relation"), the memo referenced an empirical Type I numerical ratio ($|S_{\mathrm{smooth}} + \Sigma_1| / N^{3/4}$) rather than evaluating the conditional smooth zero-mode $R_\eta$ from [`SIGNED_MEAN_RENEWAL.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/SIGNED_MEAN_RENEWAL.md) (Section 8).

### 5.1 The Construction of $R_\eta$
In [`SIGNED_MEAN_RENEWAL.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/SIGNED_MEAN_RENEWAL.md), $R_\eta(u) = \Psi_\eta(u) - u$ is constructed conditionally under the hypothesis that there exists an off-critical zero $\rho = \beta + i\gamma$ with $\zeta(\rho) = 0$ and $\beta > 1/2$.
It satisfies:
1. Positivity: $\Psi_\eta(1) = 0$ and $\Psi_\eta(u) \ge 0$ for all $u \ge 1$.
2. Monotonicity: $\Psi_\eta'(u) \ge 1/2 > 0$, so $\Psi_\eta$ is strictly increasing.
3. Integral normalization: $\int_1^\infty R_\eta(u) u^{-2} \, du = -(1+\gamma)$.
4. PNT envelope: $R_\eta(u) \ll u \exp(-c\sqrt{\log u})$.
5. Bounded variation: $\operatorname{Var}_{[1, y]} R_\eta \ll y$.
6. Universal scale relations: $(L_K R_\eta)(N) = O(N/K + 1)$ for every $1 \le K \le N$.

Despite satisfying every macroscopic and scale-renewal condition, $R_\eta(u) = -a + \eta \Re(u^\rho)$ for $u \ge 4$ carries an oscillatory mode of magnitude $u^\beta$ with $\beta > 1/2$.

### 5.2 What Hypotheses $R_\eta$ Lacks
1. **Discrete Prime-Power Support**: The true error term $R(x) = \psi(x) - x$ has jump discontinuities at prime powers $p^k$ with jump $\log p$. In contrast, $R_\eta$ is $C^1$ smooth with uniformly bounded derivative.
2. **Discrete Mobius Inversion**: The arithmetic identity underlying the hyperbola decomposition relies on $\Lambda(n) = \sum_{d \mid n} \mu(d) \log(n/d)$, expressing $\psi$ as a discrete convolution of $\mu$. The profile $R_\eta$ is a continuum function that does not arise from any discrete arithmetic sequence $a \mapsto \mu(a)$.
3. **Failure to Instantiate $\Sigma_2$**: The component $\Sigma_2(N) = \sum_{b=2}^U \log b \sum_{a=U+1}^{V(b)} \mu(a) w_N(ab)$ directly evaluates $\mu(a)$. Because $R_\eta$ has no underlying discrete Mobius weights, $R_\eta$ cannot instantiate $\Sigma_2$.

### 5.3 Failure to Instantiate vs. Refuting Generic Lemmas
- The inability of $R_\eta$ to instantiate $\Sigma_2$ does not refute the validity of the hyperbola decomposition, nor does it refute any intermediate lemma of the renewal argument.
- Rather, $R_\eta$ is a conditional diagnostic demonstrating that macroscopic properties alone cannot rule out an off-critical spectral mode.
- Conversely, the failure of the $p = 2$ pairing to beat $\Theta(N \log^3 N)$ arises because taking absolute values $|\mu(a)| \le 1$ discards the arithmetic oscillations of $\mu(n)$, reducing the estimate to a positive divisor sum. This majorant obstruction is unconditional and does not assume the existence of an off-critical zero.

---

## 6. Independent Experimental and Machine-Checked Evidence

All checks were executed independently using the repository environment (`.venv/bin/python`) on the local testbed.

### 6.1 Reproduction of Author's Checker
The author's script [`mobius_pairing_check.py`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/mobius_pairing_check.py) was executed independently:
```bash
$ .venv/bin/python hunts/prime_pair_error/mobius_pairing_check.py
```
- **Execution Time**: 0.76 s.
- **Exact Fraction Defect**: 0 across all tested cutoffs $N \in [12, 10000]$.
- **Planted Lesions**: All three planted lesions detected with positive defects (`missing_head` = 11, `missing_tail` = 5, `wrong_sign` = 2 at $N = 100$; 39, 17, 20 at $N = 400$).

### 6.2 Independent Check Script and Durable Evidence
An independent clean-room script was written and committed to [`hunts/prime_pair_error/mobius_pairing_independent_check.py`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/mobius_pairing_independent_check.py). It does not import author code or data.
```bash
$ .venv/bin/python hunts/prime_pair_error/mobius_pairing_independent_check.py
```
- **Execution Time**: 0.54 s (well within the $\le 60$ s budget).
- **Total Pairs Checked**: 15,794 pairs across 20 cutoffs ($N \in [12, 10000]$).
- **Global Minimum Gate Margin**: $\min (abK - N) = 3$ (at $N = 15$).
- **Near-Square Stress Checks**: 387 cases ($N = K^2 - 1, K^2, K^2 + 1, K^2 + 2K$ for $K \in [3, 100]$) all verified with $2(U+1)K - N \ge 3 > 0$.
- **Exact Cutoff Equivalence**: Verified $F > U \iff b \le b^* = \lfloor M / [2(U+1)] \rfloor$ across all cutoffs.
- **5-Part Partition**: Disjointness and exhaustion verified on all 15,794 pairs; $m \mapsto 2m$ bijection verified; $\mu(a) = 0$ for all $a \in \mathcal{A}_{\mathrm{even,mid,even}}$ verified.
- **Planted Lesions**: Verified four lesions with strictly positive rational defects:
  - $N = 100$: `missing_head` = 11, `missing_tail` = 5, `wrong_sign` = 2, `tail_even_inclusion` = 8.
  - $N = 400$: `missing_head` = 39, `missing_tail` = 17, `wrong_sign` = 20, `tail_even_inclusion` = 21.
- **Durable Evidence Saved**: Written to [`hunts/prime_pair_error/results_mobius_pairing_independent.json`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/results_mobius_pairing_independent.json).

---

## 7. Minimal Repair Specification for the Author File

To bring [`MOBIUS_PAIRING.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/MOBIUS_PAIRING.md) to complete archival alignment, the author should incorporate the following minimal repairs in Section 4:

1. **Replace the paragraph "Smooth-diagnostic relation"** with an explicit discussion of $R_\eta$:
   - Acknowledge that the conditional smooth zero-mode $R_\eta$ from [`SIGNED_MEAN_RENEWAL.md`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error/SIGNED_MEAN_RENEWAL.md) (Section 8) demonstrates that macroscopic properties alone cannot rule out an off-critical spectral mode.
   - Clarify that $R_\eta$ lacks discrete prime-power jumps and discrete Mobius convolution, and therefore cannot instantiate $\Sigma_2$.
   - Note that the inability of $R_\eta$ to instantiate $\Sigma_2$ does not refute the hyperbola decomposition, and the majorant obstruction does not assume an off-critical zero exists.
2. **Explicitly state the leading constants and cutoff**:
   - Record $c_0 = 1/48$ and $c_p = 1/192$, identifying the factor-of-4 drop in the leading constant alongside the $\Theta(N \log^2 N)$ boundary order.
   - Replace $b \le U/2$ with the exact integer cutoff $b \le b^* = \lfloor M / [2(U+1)] \rfloor$.

With these repairs documented, the core combinatorial identity and the mathematical verdict to halt this specific pairing construction are **ACCEPTED**.

**Author integration note (2026-09-20):** the §7 repair spec is incorporated in the
author file (R_eta discussion, constants 1/48 and 1/192, exact cutoff b*, restricted
per-b theta, proper-prime-power wording, proof/check scope distinction). Review-side
typos corrected in place above (two $V/2 = F$ occurrences, exact radical inequality);
all prior review corrections and the provenance retraction are otherwise preserved
verbatim.
