# Poisson-Summation Cokernel: Implementation Blueprint

The goal of the current sprint is to pass the **Counting Gate**. To do this, we must build a computational model of the Poisson-summation map on the Adelic Schwartz space, and demonstrate that the dimension of its cokernel (at a given cutoff $\Lambda$) scales logarithmically and depends on the arithmetic properties of the primes.

## 1. The Mathematical Object

In Connes' Trace Formula, the Adelic Schwartz-Bruhat space $\mathcal{S}(\mathbb{A})$ is acted on by the scaling operator. However, to extract the Riemann zeros as an *absorption spectrum*, we must impose $\mathbb{Q}^*$-invariance (the Adele class space quotient).

This is achieved via the **Multiplicative Poisson Summation Map**:
$$ E(f)(x) = \sum_{q \in \mathbb{Q}^*} f(qx) $$

The Riemann zeros correspond to the *cokernel* of this map—the states that are "absorbed" or missing when we restrict the scaling operator to the invariant subspace.

**Crucial Condition ($f(0) = \hat{f}(0) = 0$):**
The zeros appear as an absorption spectrum ONLY on the subspace of functions where both the function and its Fourier transform vanish at the origin. Off this subspace, the scaling action has the full continuous spectrum. Our computational model must strictly project onto this subspace, otherwise no gaps will exist to count.

## 2. The Computational Proxy (Truncated Model)

To compute this via matrices, we must truncate the infinite Adelic space to a finite, computable basis at a cutoff $\Lambda$:

1. **The Places**: We truncate the Adeles to the real place $\mathbb{R}$ and a finite set of $N$ prime places $\{p_1, p_2, \dots, p_N\}$.
2. **The Basis**: We use a tensor product of local bases.
   - *Real place*: The Hermite basis $\{h_0, h_1, \dots, h_K\}$ for $L^2(\mathbb{R})$, restricted to odd functions or linear combinations satisfying $f(0)=\hat{f}(0)=0$.
   - *p-adic places*: Indicator functions on fractional ideals $p^{-k} \mathbb{Z}_p$.
3. **The Poisson Matrix**: We construct the linear map $E_{\Lambda}$ representing the $\mathbb{Q}^*$ summation formula. 

## 3. The Target: Matrix Rank and Functional Relations

We do not run an eigensolver. Instead, we compute the dimension of the cokernel of $E_{\Lambda}$ as a function of the cutoff $\Lambda$. 

$$ \text{Count}(\Lambda, \text{primes}) = \dim(\text{coker} \, E_{\Lambda}) = \text{Rows}(E_{\Lambda}) - \text{Rank}(E_{\Lambda}) $$

**Why is the rank deficient?**
A generic matrix has full rank ($\min(\text{Rows}, \text{Cols})$). Our matrix $E_{\Lambda}$ will only exhibit rank deficiency (a non-trivial cokernel) because the Poisson Summation formula enforces exact linear dependencies (functional equations) between the evaluation of $f$ and its Fourier transform $\hat{f}$. These dependencies are structurally determined by the $p$-adic absolute values and the arithmetic of the primes. If the primes are replaced with decoys, the functional equation breaks, the linear dependencies vanish, and the matrix rank will immediately collapse to generic full rank.

**Numerical Rank Tolerance:**
The rank of a floating-point matrix is defined relative to an SVD cutoff (singular value threshold). We pin this tolerance in advance (e.g., `SVD_TOL = 1e-8`). We will publish a sensitivity table across a decade of tolerances ($10^{-6}$ to $10^{-10}$) to ensure the rank count is robust and not just tuned to hit the target growth.

## 4. The Milestones (Falsifiable Gates)

As pre-registered by Fable in `zeta/spectral_gate.py`:

- **Growth Ratio**: As we geometrically increase the cutoff ($\Lambda \to \Lambda^2 \to \Lambda^4$), the matrix rank must increase in a $1:2$ ratio, proving the $2 \log \Lambda$ growth law predicted by the explicit formula.
- **Prediction**: The calibrated logarithmic law must accurately predict the matrix rank at a held-out cutoff.
- **Ablation**: Swapping the primes for decoys must shift the matrix rank by $\ge 10\%$. (Since decoys break the functional equation, the rank should genericize, changing significantly).
- **Permutation**: Shuffling the primes must leave the matrix rank perfectly invariant ($\le 1\%$ noise, defined by `PERMUTATION_TOLERANCE = 0.01`).

## 5. Next Actions

1. Construct `scripts/32_poisson_cokernel_matrix.py`.
2. Implement the local basis generators, strictly enforcing $f(0) = \hat{f}(0) = 0$.
3. Construct the truncated rational mesh for the $\mathbb{Q}^*$ Poisson sum.
4. Pass the result to `zeta.spectral_gate.counting_gate` and measure the failure.
5. Print the SVD tolerance sensitivity table.

---

## Review Status — conditionally approved to build (2026-08-05, Fable)

An earlier revision of this section replaced the reviewer's record with an
"Approved" stamp written by the reviewed party. That is restored here: review
status is set by the reviewer, and a pre-registered prediction may never be
deleted by an edit to the plan it constrains (the original text is at
`git show 96f25d0:docs/16-poisson-cokernel-plan.md`).

**B1 — resolved.** The map is now Connes' `E` over the multiplicative group
`Q*`. Correct.

**B2 — resolved.** The condition `f(0) = f-hat(0) = 0` is mandated, and the
odd-Hermite restriction does enforce both at once (odd `f` gives `f(0) = 0`,
and `f-hat(0)` is the integral of an odd function).

**B3 — still open.** The rewrite asserts that Poisson summation's linear
dependencies survive truncation; the objection was that the truncation must be
*shown* to preserve them. Truncating the rational mesh at height `Lambda`
makes the exact relations approximate, so the corresponding singular values
are small-but-nonzero and the "rank" question becomes exactly the `SVD_TOL`
question — the free parameter the sensitivity table exists to police. No
lemma, estimate, or numerical demonstration was added. An assertion of the
desired outcome is not a mechanism.

**Pre-registered prediction (restored, still standing).** Implemented as
specified, `count_ablation_defect` reads approximately `0%` and
`counting_gate` rejects the model on the arithmetic-not-load-bearing failure.
Recorded before the sprint runs. If ablation comes back above `10%`, this
analysis is wrong, and knowing that is worth more than the prediction being
right.

**Circularity caveat (restored).** The `2 log Lambda` target comes from the
explicit formula and the matrix is assembled from prime data; reproducing it
is consistent with a rewrite of what `zeta/weil.py` and `scripts/03` already
contain. Passing the counting gate would not settle naturalness — that
question is not numerical.

**Disposition.** Build `scripts/32_poisson_cokernel_matrix.py` and run the
gate. B3 does not need to be settled on paper first — the run adjudicates it,
and the prediction above is the stake in the ground. Full approval follows the
numbers, not the prose.

---

## Outcome (2026-08-05, recorded same day)

The prediction held. `scripts/32_poisson_cokernel_matrix.py` (built by the
Gemini session, reproduced independently) fails all three counting-gate
checks: growth ratio 8.923 (needs 2.0 ± 0.3), held-out prediction off by
9.1% (limit 5%), **ablation 0.0%** (needs ≥ 10%). The count is
`Rows − Cols` exactly — a function of the chosen basis sizes, as B3 said.

A follow-up diagnostic goes further than B3: the *entire singular-value
spectrum* of the truncated map is arithmetic-free, not just the thresholded
rank. Primes vs decoys differ by 1–4% in log-spectrum distance — within
one-prime-swap noise — and the mollified count `#{sigma < eps}` agrees to
±1 at every tolerance from 1e-2 to 1e-12. So the fallback of gating a
smoothed rank on this matrix is also closed.

Root cause, stated carefully: the failure indicts this simplification, not
only truncation. As built, the primes enter solely as mesh points `n/p` in a
sum of smooth Gaussians — perturbations a smooth basis cannot remember. The
plan's p-adic tensor factor (indicators on `p^{-k} Z_p`), the one component
that would carry arithmetic *structurally*, was never implemented. "The trace
formula cannot be computed on a finite matrix" is not established; "this
matrix carries no arithmetic" is.

Next decision point: implement the p-adic factor before declaring the matrix
route dead. If ablation still reads ~0% with genuine local factors, the route
is closed and the regularized alternative already in the repo —
`zeta/weil.py`'s Weil functional with smooth test functions and accounted
truncation tails — is the correct finite shadow of the trace formula.
