# Final Acceptance Record: Arithmetic Bilinear and Dirichlet Hyperbola Factorization of D_N

Date: 2026-09-20.
Runtime observed: Gemini 3.8 Flash high (provenance accurately recorded; not Opus, per coordinator notice).
Scope: Bounded audit, repair, and final acceptance of package files under [`hunts/prime_pair_error`](file:///Users/thomas/orca/workspaces/zeta-lab/signed-cancellation-sep20/hunts/prime_pair_error).
Base commit: `109c79808158252b7134c6a19543111bfdbb1e08`.

---

## 1. Executive Disposition

Under `ALIGNMENT.md` Section 5, the mathematical status of this candidate is:

$$\mathbf{ATTEMPT\_UNRESOLVED}$$

**ACCEPTED ONLY AS A PRESERVED UNRESOLVED ATTEMPT.** No new cancellation estimate for $D_N$ has been obtained. Proposed finer analytic baselines (in particular the monotone-telescoping subexponential estimate for $\Sigma_2$) are not accepted; see section 4. No originality or novelty is claimed for standard identities ($\Lambda = \mu * \log$, Dirichlet hyperbola partition, Stirling/harmonic expansions); the package's contribution, if any, is only in their assembly and checking.

No new improved asymptotic bound on $D_N$ or $\psi_2(N, k)$ has been established.
The scientific value of this package consists of:
1. Exact, closed finite algebraic identities for the full functional $D_N$ without remainder leakage (proved by the written derivations plus inherited integral/PNT facts; finite-case machine checks per section 3 support, not replace, the proofs).
2. Exact rational checks of stated finite cases: $\mathcal{E}_{\mathrm{frac}}$ values, prime-log coefficient matches at 15 cutoffs, the smooth/fractional split, and 4 planted lesion detections (section 3).
3. Retraction of unsupported analytic sub-claims introduced in earlier drafts, as itemized in section 6.
4. Elementary unconditional bound $\Sigma_2 \ll N \log^3 N$ retained as justified; the proposed subexponential baseline needs review.
5. Sharply formulated remaining open joint analytic inequality.

Provenance honesty: the exact tests are worker-written code from this same campaign (a same-model worker, per the runtime record below), independent of the author checker but not a third-model review. Pending-review items are not complete.

---

## 2. Exact Finite Equations Accepted

The following exact algebraic equations are proved by the written derivations in the candidate and factorization notes together with the inherited integral/PNT facts; finite-case machine checks (section 3) support but do not replace those proofs, and no numerical oracle is invoked for the general case:

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
For fixed $\rho$ with $0 < \Re\rho < 1$ and $g(u) = u^\rho$:
$$D_N[u^\rho] = N^\rho B(\rho), \qquad B(\rho) = 1 - \zeta(\rho) - \text{tail}_K$$
At any zeta zero $\zeta(\rho) = 0$, $B(\rho) \to 1$. For a critical zero $\rho = 1/2 + i\gamma$, $|D_N[u^\rho]| = N^{1/2}|B(\rho)| \sim N^{1/2}$, not $N^{1/4}$. (The $1/|\rho|$ factor belongs to the explicit-formula coefficient $N^\rho/\rho$ of $R$ itself, not to the pure mode tested here.) Since $|u^\rho| = u^\beta$ with $\beta = \Re\rho$: the cosine $\cos(\gamma \log N)$ describes only the real part $\Re(N^\rho)$, whose oscillation is not monotonic growth at every integer.

---

## 3. Evidence Classes

The mathematical assertions in this package are grounded in three distinct evidence classes:

| Class | Method | Scope | Key Results |
|---|---|---|---|
| **Class A** | Exact rational `Fraction` arithmetic (zero tolerance) | Stated finite cases only | Rational residual $\mathcal{E}_{\mathrm{frac}}$ values at 13 cutoffs including N = 49 (both signs discriminated); prime-log coefficient matches at 15 finite cutoffs (N = 12..400 per `results_factorization_diagnostic.json`); smooth/fractional split $M_b = M_{b,\mathrm{smooth}} + M_{b,\mathrm{frac}}$ at checked cells; 4 planted lesion detections. These prove the stated finite cases only. |
| **Class B** | High-precision transcendental evaluation (mpmath dps=80) | Transcendentals ($\log, \gamma, \zeta$) at checked cutoffs | Candidate identity (2) defect $\le 5.3 \times 10^{-12}$; integral reduction formula defect $\le 6.0 \times 10^{-17}$; remainder identities defects $\le 2.5 \times 10^{-10}$. Finite-cutoff agreement only. |
| **Class C** | Measured floating-point diagnostics (double precision) | Envelopes, ratios, and diagnostics | Measured defect $|D_N - (\mathcal{S}_{\mathrm{smooth}} + \Sigma_1 + \Sigma_2)|$ at float64 level; $(A - \log(N!))/N \approx -1$; spectral bracket values tracking $|1 - \zeta(\rho)|$; $Y$-range sweep violations count (314). Diagnostic only. |

General algebraic identities rest on the written derivations plus the inherited integral/PNT facts, not on any numerical oracle. Kernel and partition identities were checked in floats (Class C), not in exact arithmetic: there is no exact kernel verification. All test code is campaign-worker code (same-model family), independent of the author checker but not a third-model review.

---

## 4. Conditional and Unconditional Baselines

The table below summarizes the strongest justified baselines on record:

| Quantity | Justified Baseline | Status / Derivation |
|---|---|---|
| $\mathcal{T}_{\mathrm{sawtooth}}(N, K)$ | $O(\sqrt{N})$ | **Established unconditionally.** $|\psi_0(x)| \le 1/2 \implies |\mathcal{T}_{\mathrm{sawtooth}}| \le \frac{1}{2}\psi(Y) \ll \sqrt{N}$. |
| $E_{\mathrm{det}}(N)$ | $O(\sqrt{N})$ | **Established unconditionally.** $E_{\mathrm{det}} = -\frac{1}{2}R(Y) + O(\log N) \ll \sqrt{N}$ via Chebyshev. |
| $\mathcal{T}_{\mathrm{bilinear}}(N, K)$ | $O(N \log N \exp(-c\sqrt{\log N}))$ | **Unconditional.** Inherited from PNT for $R(x)$ across $k \le K$. Under RH: $\sum_{k \le K} |R(N/k)| \ll N^{3/4}\log^2 N$. |
| $\mathcal{R}_{\mathrm{boundary}}(N, K)$ | $O(N \log N \exp(-c\sqrt{\log N}))$ | **Unconditional (algebraically coupled).** Coupled to $R(N) - \mathcal{T}_{\mathrm{bilinear}} + O(\sqrt{N})$. |
| $\Sigma_2(N)$ (trivial) | $O(N \log^3 N)$ | **Justified.** Absolute values $|\mu| \le 1$ without sign cancellation. Honestly labeled not best known. |
| $\Sigma_2(N)$ (monotone telescoping) | $O(N \exp(-c''\sqrt{\log N}))$ | **Proposed baseline, needs review — not accepted.** The written derivation does not rigorously handle active jump ranges, changing exponential constants, $V$ endpoints, and small $N$. |
| Joint target $D_N$ (under RH for $\zeta$) | $O(N^{1/2}\log^2 N)$ | **Proved conditionally.** Follows from $D_N = R(N) + O(\sqrt{N})$ and von Koch $|R(x)| \ll x^{1/2}\log^2 x$. |

---

## 5. The Remaining Open Joint Inequality

The remaining obstacle to establishing $|D_N| \ll_\epsilon N^{1/2+\epsilon}$ without assuming RH is the joint cancellation:

$$\boxed{\quad \left| \mathcal{S}_{\mathrm{smooth}}(N, K) + \Sigma_1(N) + \Sigma_2(N) \right| \ll_\epsilon N^{1/2+\epsilon} \quad}$$

What this audit does and does not say:
1. The estimates attempted here do not establish the required joint bound. No lower bound for $\Sigma_2$ was proved, and nothing here shows that separate bounds saturate, that $N^{1/2+\epsilon}$ cannot be achieved piece by piece, or that joint cancellation is required as a proved impossibility: sharper estimates or different decompositions are not ruled out.
2. **Status of the fractional-weight piece:**
   The fractional piece $\Sigma_{2,\mathrm{frac}} = \sum_{b=2}^U \log b \sum_{U < a \le M/b} \mu(a) \{N/(ab)\}$ is one component of $\Sigma_2$. It has not been proved equivalent to RH nor to the entire joint functional $D_N$.

---

## 6. What Changed Scientifically

1. **Exact identities proved by derivation, checked on finite cases:** The algebraic structures of both the bilinear partition and the Dirichlet hyperbola factorization are proved in the notes; finite-case checks (Classes A-C) support them within the stated scopes.
2. **Unsupported claims retracted:**
   - The claim that $A(N) - \log(N!) = O(\sqrt{N})$ was refuted: the discrepancy is $\Theta(N)$, which algebraically couples $\mathcal{R}_{\mathrm{boundary}}$ to $R(N) - \mathcal{T}_{\mathrm{bilinear}}$.
   - The spectral claim of an $N^{1/4}$ margin was refuted: the $k=1$ mode keeps the remainder at $N^\beta$ (borderline $N^{1/2}$ on the critical line).
   - The claim of an exact proved inner main term in $\Sigma_1$ was retracted to a formal heuristic scale match.
   - The sign error expanding $1 - \lfloor x \rfloor$ was corrected to plus $\{x\}$.
   - The monotone-telescoping subexponential baseline for $\Sigma_2$ is downgraded to a proposal needing review (jump-range uniformity, exponential constants, $V$ endpoints, small $N$ unhandled); the justified bound stays $\Sigma_2 \ll N \log^3 N$.
3. **Scientific verdict:**
   No improved asymptotic bound on $D_N$ is obtained. The research attempt is preserved as unresolved: derivation-proved exact finite identities with stated finite-case checks, and a sharply stated open joint inequality. No saturation, impossibility, or individual non-boundedness result is claimed.
