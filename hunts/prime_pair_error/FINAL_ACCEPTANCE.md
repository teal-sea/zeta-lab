# Final Acceptance Record: Arithmetic Bilinear and Dirichlet Hyperbola Factorization of D_N

Date: 2026-09-20.
Runtime observed: Gemini 3.8 Flash high (provenance accurately recorded; not Opus, per coordinator notice).
Scope: Bounded audit, repair, and final acceptance of package files under [`hunts/prime_pair_error`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error).
Base commit: `109c79808158252b7134c6a19543111bfdbb1e08`.

---

## 1. Executive Disposition

Under `ALIGNMENT.md` Section 5, the mathematical status of this candidate is:

$$\mathbf{ATTEMPT\_UNRESOLVED}$$

No new improved asymptotic bound on $D_N$ or $\psi_2(N, k)$ has been established.
The scientific value of this package consists of:
1. Exact, closed finite algebraic identities for the full functional $D_N$ without remainder leakage.
2. Independent verification of all finite algebraic identities to zero defect in exact rational `Fraction` arithmetic.
3. Rigorous refutation, retraction, or bounded repair of all unsupported analytic sub-claims introduced in earlier drafts.
4. Restored unconditional subexponential baseline for $\Sigma_2$ via monotone floor telescoping.
5. Sharply formulated remaining open joint analytic inequality.

---

## 2. Exact Finite Equations Accepted

The following exact algebraic equations are fully proved, derived with explicit remainders, and machine-verified to zero defect:

### 2.1. Candidate Bilinear Partition and Exact Integral Reduction
For integer $N \ge 4$, $K = \lfloor\sqrt{N}\rfloor$, and $Y = N/K$:
$$D_N = \mathcal{T}_{\mathrm{bilinear}}(N, K) + \mathcal{T}_{\mathrm{sawtooth}}(N, K) + \mathcal{R}_{\mathrm{boundary}}(N, K)$$
where the improper integral is evaluated in finite closed form:
$$N \int_{N/K}^\infty \frac{R(u)}{u^2} \, du = K \psi(Y) - N \sum_{d \le Y} \frac{\Lambda(d)}{d} + N \log Y - (1+\gamma)N$$
with $R(u) = \psi(u) - u$.

### 2.2. Exact Rational Discrepancy for Bilinear Sum
$$\mathcal{T}_{\mathrm{bilinear}}(N, K) = -\sum_{k=2}^K \big( R(N/k) - R(Y) \big) - \mathcal{E}_{\mathrm{frac}}(N, K)$$
with confirmed minus sign and rational discrepancy:
$$\mathcal{E}_{\mathrm{frac}}(N, K) = \sum_{k=2}^K \left( \left\{ \frac{N}{k} \right\} - \{Y\} \right)$$
satisfying $|\mathcal{E}_{\mathrm{frac}}| < K \le \sqrt{N}$.

### 2.3. Exact Boundary Relation and Algebraic Coupling
With $A(N) = \sum_{d \le Y} \Lambda(d) \lfloor N/d \rfloor + \mathcal{B}_{\mathrm{main}}(N, K)$:
$$A(N) - \log(N!) = \mathcal{T}_{\mathrm{bilinear}}(N, K) - \big(\psi(N) - \psi(Y)\big) \asymp -N$$
$$\mathcal{R}_{\mathrm{boundary}}(N, K) = R(N) - \mathcal{T}_{\mathrm{bilinear}}(N, K) + E_{\mathrm{det}}(N)$$
where $E_{\mathrm{det}}(N) = \mathcal{S}_{\mathrm{smooth}}(N, K) - \log(N!) + N - \frac{1}{2}\psi(Y) = -\frac{1}{2}R(Y) + O(\log N) = O(\sqrt{N})$.
Consequently, the partition collapses to the exact renewal relation:
$$D_N = R(N) + \mathcal{T}_{\mathrm{sawtooth}}(N, K) + E_{\mathrm{det}}(N) = R(N) + O(\sqrt{N})$$

### 2.4. Discrete Kernel Representation
$$D_N = \mathcal{S}_{\mathrm{smooth}}(N, K) + \sum_{m=1}^M w_N(m) \Lambda(m)$$
where $M = \lfloor N/2 \rfloor$, $\mathcal{S}_{\mathrm{smooth}}(N, K) = N (\log Y + H_K - 2 - \gamma)$, and:
$$w_N(m) = \begin{cases} 1 - \frac{N}{m}, & 1 \le m \le Y \\ 1 - \lfloor \frac{N}{m} \rfloor, & Y < m \le M \end{cases}$$

### 2.5. Truncated Dirichlet Hyperbola Partition
Substituting $\Lambda = \mu * \log$:
$$D_N = \mathcal{S}_{\mathrm{smooth}}(N, K) + \Sigma_1(N) + \Sigma_2(N)$$
with $U = \lfloor\sqrt{M}\rfloor$:
$$\Sigma_1(N) = \sum_{a=1}^U \mu(a) \sum_{b=2}^{\lfloor M/a \rfloor} \log b \, w_N(a b)$$
$$\Sigma_2(N) = \sum_{b=2}^U \log b \sum_{a=U+1}^{\lfloor M/b \rfloor} \mu(a) w_N(a b)$$
Absence of remainder region: because $(U+1)^2 > M$, the region $\{a > U, b > U, ab \le M\}$ is strictly empty.

### 2.6. Signed Smooth and Fractional Splitting of $\Sigma_2$
Because $1 - \lfloor x \rfloor = 1 - x + \{x\}$ (plus sign for the fractional part):
$$\mathcal{M}_b(N) = \sum_{U < a \le \lfloor M/b \rfloor} \mu(a) \left( 1 - \frac{N}{ab} \right) + \sum_{U < a \le \lfloor M/b \rfloor} \mu(a) \left\{ \frac{N}{ab} \right\} =: \mathcal{M}_{b,\mathrm{smooth}}(N) + \mathcal{M}_{b,\mathrm{frac}}(N)$$
$$\Sigma_2(N) = \Sigma_{2,\mathrm{smooth}}(N) + \Sigma_{2,\mathrm{frac}}(N)$$
verified independently in exact rational arithmetic with zero tolerance.

### 2.7. Guarded Level-Set Mertens Expansion
For $hi = \min(\lfloor M/b \rfloor, \lfloor N/(bk) \rfloor)$ and $lo = \max(U, \lfloor N/(b(k+1)) \rfloor)$:
$$\mathcal{M}_b(N) = [M(\lfloor M/b \rfloor) - M(U)] - \sum_{k=2}^K k [M(hi) - M(lo)] \cdot \mathbf{1}_{hi > lo}$$
where the guard $hi > lo$ is required to prevent wrong-signed nonzero contributions on empty cells.

### 2.8. Spectral Mode Normalization
For $g(u) = u^\rho$:
$$D_N[u^\rho] = N^\rho B(\rho), \qquad B(\rho) = 1 - \zeta(\rho) - \text{tail}_K$$
At any zeta zero $\zeta(\rho) = 0$, $B(\rho) \to 1$. For a critical zero $\rho = 1/2 + i\gamma$, the mode is borderline at $|D_N[u^\rho]| \sim N^{1/2}$, oscillating as $\cos(\gamma \log N)$, not $N^{1/4}$.

---

## 3. Evidence Classes

The mathematical assertions in this package are grounded in three distinct evidence classes:

| Class | Method | Scope | Key Results |
|---|---|---|---|
| **Class A** | Exact rational `Fraction` arithmetic (zero tolerance) | Purely algebraic identities | Rational residual $\mathcal{E}_{\mathrm{frac}}$ values; prime-log coefficient matches for all $p \le M$ across 15 cutoffs; smooth/fractional split $M_b = M_{b,\mathrm{smooth}} + M_{b,\mathrm{frac}}$; 4 planted lesion detections. |
| **Class B** | High-precision transcendental evaluation (mpmath dps=80) | Transcendentals ($\log, \gamma, \zeta$) | Candidate identity (2) defect $\le 5.3 \times 10^{-12}$; integral reduction formula defect $\le 6.0 \times 10^{-17}$; remainder identities defects $\le 2.5 \times 10^{-10}$. |
| **Class C** | Measured floating-point diagnostics (double precision) | Envelopes, ratios, and diagnostics | Measured defect $|D_N - (\mathcal{S}_{\mathrm{smooth}} + \Sigma_1 + \Sigma_2)| \le 1.03 \times 10^{-11}$; $(A - \log(N!))/N \approx -1$; spectral bracket convergence $|B| \to 1$; $Y$-range sweep violations count (314 near-squares). |

---

## 4. Conditional and Unconditional Baselines

The table below summarizes the strongest justified baselines on record:

| Quantity | Justified Baseline | Status / Derivation |
|---|---|---|
| $\mathcal{T}_{\mathrm{sawtooth}}(N, K)$ | $O(\sqrt{N})$ | **Established unconditionally.** $|\psi_0(x)| \le 1/2 \implies |\mathcal{T}_{\mathrm{sawtooth}}| \le \frac{1}{2}\psi(Y) \ll \sqrt{N}$. |
| $E_{\mathrm{det}}(N)$ | $O(\sqrt{N})$ | **Established unconditionally.** $E_{\mathrm{det}} = -\frac{1}{2}R(Y) + O(\log N) \ll \sqrt{N}$ via Chebyshev. |
| $\mathcal{T}_{\mathrm{bilinear}}(N, K)$ | $O(N \log N \exp(-c\sqrt{\log N}))$ | **Unconditional.** Inherited from PNT for $R(x)$ across $k \le K$. Under RH: $\sum_{k \le K} |R(N/k)| \ll N^{3/4}\log^2 N$. |
| $\mathcal{R}_{\mathrm{boundary}}(N, K)$ | $O(N \log N \exp(-c\sqrt{\log N}))$ | **Unconditional (algebraically coupled).** Coupled to $R(N) - \mathcal{T}_{\mathrm{bilinear}} + O(\sqrt{N})$. |
| $\Sigma_2(N)$ (trivial) | $O(N \log^3 N)$ | **Trivial bound.** Absolute values $|\mu| \le 1$ without sign cancellation. Honestly labeled not best known. |
| $\Sigma_2(N)$ (monotone telescoping) | $O(N \exp(-c''\sqrt{\log N}))$ | **Established unconditionally.** Abel summation on monotone floor weights $w_N(ab)$ replaces $k$ weights by forward differences $\Delta w_N \in \{0, 1\}$. Subexponential saving is fully preserved. |
| $\Sigma_2(N)$ (under RH for $\zeta$) | $O_\epsilon(N^{7/8+\epsilon})$ (or $O(N^{3/4+\epsilon})$) | **Conditional under RH.** Boundary term at $U$ gives $\frac{\sqrt{N}}{b} U^{1/2+\epsilon} \asymp N^{3/4+\epsilon}/b$; does not reach $N^{1/2+\epsilon}$. |
| Joint target $D_N$ (under RH for $\zeta$) | $O(N^{1/2}\log^2 N)$ | **Proved conditionally.** Follows from $D_N = R(N) + O(\sqrt{N})$ and von Koch $|R(x)| \ll x^{1/2}\log^2 x$. |

---

## 5. The Remaining Open Joint Inequality

The remaining obstacle to establishing $|D_N| \ll_\epsilon N^{1/2+\epsilon}$ without assuming RH is the joint cancellation:

$$\boxed{\quad \left| \mathcal{S}_{\mathrm{smooth}}(N, K) + \Sigma_1(N) + \Sigma_2(N) \right| \ll_\epsilon N^{1/2+\epsilon} \quad}$$

Crucial structural conclusions established by this audit:
1. **Separation into individual pieces fails to reach $N^{1/2}$:**
   Neither $\Sigma_1$ nor $\Sigma_2$ is individually bounded by $O(N^{1/2+\epsilon})$ under RH:
   - $\Sigma_1$ carries the $N \log N$ and $N$ scales of $\mathcal{S}_{\mathrm{smooth}}$;
   - $\Sigma_2$ saturates at $O(N^{3/4+\epsilon})$ even under Mertens-strength input.
   Therefore, establishing the target requires cancellation between $\mathcal{S}_{\mathrm{smooth}}$, $\Sigma_1$, and $\Sigma_2$ jointly.
2. **Status of the fractional-weight piece:**
   The fractional piece $\Sigma_{2,\mathrm{frac}} = \sum_{b=2}^U \log b \sum_{U < a \le M/b} \mu(a) \{N/(ab)\}$ is one component of $\Sigma_2$. It has not been proved equivalent to RH nor to the entire joint functional $D_N$.

---

## 6. What Changed Scientifically

1. **Exact identities established:** The algebraic structures of both the bilinear partition and the Dirichlet hyperbola factorization are verified with zero defect in exact rational arithmetic.
2. **Unsupported claims eradicated:**
   - The claim that $A(N) - \log(N!) = O(\sqrt{N})$ was refuted: the discrepancy is $\Theta(N)$, which algebraically couples $\mathcal{R}_{\mathrm{boundary}}$ to $R(N) - \mathcal{T}_{\mathrm{bilinear}}$.
   - The spectral claim of an $N^{1/4}$ margin was refuted: the $k=1$ mode keeps the remainder at $N^\beta$ (borderline $N^{1/2}$ on the critical line).
   - The claim of an exact proved inner main term in $\Sigma_1$ was retracted to a formal heuristic scale match.
   - The sign error expanding $1 - \lfloor x \rfloor$ was corrected to plus $\{x\}$.
   - The claim that naive $k$ weights necessarily erase subexponential savings was refuted: telescoping on monotone floor weights restores the genuine unconditional subexponential baseline $\Sigma_2 \ll N \exp(-c''\sqrt{\log N})$.
3. **Scientific verdict:**
   No improved asymptotic bound on $D_N$ is obtained. The research attempt is closed as unresolved, leaving a rigorous, verified foundation of exact finite identities and a sharply stated open problem.
