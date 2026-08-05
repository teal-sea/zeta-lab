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

---

## Review — not approved as written (2026-08-05)

Three blocking issues; the third means the sprint fails before it starts. Fix
these and the approach is sound.

### B1. The map is stated two different ways

Section 1 writes `P(f)(x) = sum_{q in Q} f(qx)` but the surrounding prose
requires `Q*`-invariance. These are different objects: the additive sum
includes `q = 0` and does not converge. Connes' map `E` sums over the
multiplicative group `Q*`. Settle this before any code is written, because the
whole construction hangs off which group acts.

### B2. The condition `f(0) = f-hat(0) = 0` is absent

This is not a refinement, it is the mechanism. The zeros appear as an
*absorption* spectrum only on the subspace where a function and its Fourier
transform both vanish at the origin; off that subspace the scaling action has
the full continuous spectrum and nothing is missing from it. A model that omits
the condition has no gaps to count, whatever its rank does. The plan does not
mention it.

### B3. A generic finite matrix has generic rank

`dim coker = Rows - Rank`, and a matrix with no special structure has rank
`min(Rows, Cols)` almost surely. The count then collapses to
`max(0, Rows - Cols)` — a function of the basis sizes chosen in section 2, not
of arithmetic. Swapping the primes for decoys does not change the shape of the
matrix, so the rank does not move.

**Pre-registered prediction.** Implemented as specified, `count_ablation_defect`
reads approximately `0%` and `counting_gate` rejects the model on the
arithmetic-not-load-bearing failure. This is recorded before the sprint runs.
If ablation comes back above `10%`, this analysis is wrong, and knowing that
is worth more than the prediction being right.

The plan must therefore state, in advance, **why the rank should be deficient
at all**. Poisson summation does supply linear relations among the images — the
functional equation is one — but only if the truncation preserves them. If no
such argument exists, there is no cokernel to compute and no sprint.

### Two smaller items

* **Numerical rank needs a declared tolerance.** Rank of a floating-point matrix
  is defined only relative to an SVD cutoff, and the count jumps as that cutoff
  moves. That is a free parameter capable of tuning the growth ratio onto
  `2.000`. Declare it before the first run and publish a sensitivity table
  across at least a decade of tolerances, in the same spirit as the pinned
  thresholds in `zeta/spectral_gate.py`.
* Section 4 states the permutation tolerance as `5%`; the constant is
  `PERMUTATION_TOLERANCE = 0.01`, one percent.

### One thing the plan is right to say out loud

Section 4 describes the target as "the `2 log Lambda` growth law predicted by
the explicit formula". That is the circularity risk stated plainly: if the law
comes from the explicit formula and the matrix is assembled from prime data,
reproducing it is consistent with a rewrite of something this repository
already contains twice (`zeta/weil.py`, `scripts/03`). Passing the counting
gate would not settle naturalness, and the gates cannot — that question is not
numerical.
