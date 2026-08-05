# Poisson-Summation Cokernel: Implementation Blueprint

The goal of the current sprint is to pass the **Counting Gate**. To do this, we must build a computational model of the Poisson-summation map on the Adelic Schwartz space, and demonstrate that the dimension of its cokernel (at a given cutoff $\Lambda$) scales logarithmically and depends on the arithmetic properties of the primes.

## 1. The Mathematical Object

In Connes' Trace Formula, the Adelic Schwartz-Bruhat space $\mathcal{S}(\mathbb{A})$ is acted on by the scaling operator. However, to extract the Riemann zeros as an *absorption spectrum*, we must impose $\mathbb{Q}^*$-invariance (the Adele class space quotient).

This is achieved via the **Poisson Summation Map**:
$$ P(f)(x) = \sum_{q \in \mathbb{Q}} f(qx) $$

The Riemann zeros correspond to the *cokernel* of this map—the states that are "absorbed" or missing when we restrict the scaling operator to the invariant subspace.

## 2. The Computational Proxy (Truncated Model)

To compute this via matrices, we must truncate the infinite Adelic space to a finite, computable basis at a cutoff $\Lambda$:

1. **The Places**: We truncate the Adeles to the real place $\mathbb{R}$ and a finite set of $N$ prime places $\{p_1, p_2, \dots, p_N\}$.
2. **The Basis**: We use a tensor product of local bases.
   - *Real place*: The Hermite basis $\{h_0, h_1, \dots, h_K\}$ for $L^2(\mathbb{R})$.
   - *p-adic places*: Indicator functions on fractional ideals $p^{-k} \mathbb{Z}_p$.
3. **The Poisson Matrix**: We construct the linear map $P_{\Lambda}$ representing the Poisson summation formula acting on this finite basis. The sum over $\mathbb{Q}$ is truncated to a finite mesh of rationals whose height is bounded by the cutoff $\Lambda$.

## 3. The Target: Matrix Rank (Dimension)

We do not run an eigensolver. Instead, we compute the dimension of the cokernel of $P_{\Lambda}$ as a function of the cutoff $\Lambda$. 

$$ \text{Count}(\Lambda, \text{primes}) = \dim(\text{coker} \, P_{\Lambda}) = \text{Rows}(P_{\Lambda}) - \text{Rank}(P_{\Lambda}) $$

## 4. The Milestones (Falsifiable Gates)

As pre-registered by Fable in `zeta/spectral_gate.py`:

- **Growth Ratio**: As we geometrically increase the cutoff ($\Lambda \to \Lambda^2 \to \Lambda^4$), the matrix rank must increase in a $1:2$ ratio, proving the $2 \log \Lambda$ growth law predicted by the explicit formula.
- **Prediction**: The calibrated logarithmic law must accurately predict the matrix rank at a held-out cutoff.
- **Ablation**: Swapping the primes for decoys must shift the matrix rank by $\ge 10\%$.
- **Permutation**: Shuffling the primes must leave the matrix rank perfectly invariant ($\le 5\%$ noise).

## 5. Next Actions

1. Construct `scripts/32_poisson_cokernel_matrix.py`.
2. Implement the local basis generators.
3. Construct the truncated rational mesh for the Poisson sum.
4. Pass the result to `zeta.spectral_gate.counting_gate` and measure the failure.
