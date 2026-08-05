# Session handoff — The Adelic Pivot, Spectral Realization, and the 3-Gate Harness

**Snapshot:** 2026-08-05 (Post-Adelic Sprint)
**Branch:** `main`
**Detailed sources of truth:** `state_of_the_lab.md`, `docs/07-equivalences-and-criteria.md`, `docs/06-hilbert-polya-and-gue.md`

**Status in one line:** Classical analytic criteria (Li, Weil) have been mathematically quantified as computationally blind to off-line zeros; the lab has relocated entirely onto the Adele class space (Connes, 1999), and a 4-Gate falsification harness has been built to ruthlessly reject forged spectral matrices.

## Where the work landed

### 1. Detector Sensitivity & Falsification
- **The Imposter Gauntlet (`zeta/epstein.py`, `scripts/23_`):** The Epstein Zeta function (Discriminant -23) has been implemented and verified. Both the Davenport-Heilbronn function and the Epstein Zeta pass the functional equation but fail the Euler product. Any proposed criterion that relies only on geometric symmetry without the arithmetic (primes) will incorrectly pass these imposters.
- **Detector Power (`zeta/detectors.py`, `scripts/24_`):** The classical criteria are mapped. The Gaussian-family Weil Positivity is exponentially blind to off-line zeros (maximum negative dip of $10^{-964}$ for $\delta=0.01$). It cannot be used as a computational falsifier. The Fejér-family is exponentially sensitive but requires phase alignment ($b$-scans).

### 2. The Adelic Foundation (`zeta/adele.py`)
To move from analytic float-estimation into Non-Commutative Geometry, we constructed the exact Adelic primitives:
- **p-adic valuations and the Adele Ring:** Embedding $\mathbb{Q} \to \mathbb{A}_\mathbb{Q}$.
- **Artin's Product Formula (`scripts/25_`):** Computationally verified $\prod_v |q|_v = 1$.
- **Tate's Thesis (`scripts/26_`, `scripts/28_`):** Local zeta integrals over the Ideles reproduce the global Riemann Zeta function. The completed Adelic Zeta Integral $\Lambda(s) = \Lambda(1-s)$ was verified natively.
- **Adelic Additive Character (`scripts/27_`):** Verified the discrete embedding of $\mathbb{Q}$ in $\mathbb{A}_\mathbb{Q}$ ($\psi(q) = 1$). (Fixed a major anti-pattern here: truncation of the product is now explicitly measured as a phase defect, rather than patched with hardcoded primes).

### 3. Connes' Trace Formula & The Spectral Harness
- **The Trace (`scripts/29_`):** Relocated the classical Weil Explicit Formula onto the trace of a scaling operator on the space $\mathbb{A}_\mathbb{Q} / \mathbb{Q}^*$.
- **The 4-Gate Harness (`zeta/spectral_gate.py`):** A strict falsifier for any matrix projection claiming to extract the Riemann zeros from this operator. It demands:
  1. **Stability:** $\le 5\%$ drift when the basis doubles (kills continuous spectrum artifacts).
  2. **Target:** $\le 1\%$ error against the exact ordinates `14.1347, 21.0220` (not just "on the line").
  3. **Ablation:** $\ge 10\%$ spectral shift when primes are swapped for decoys (kills structural tautologies).
  4. **Permutation:** Must react to the *set* of primes, not their list order.
- **The Negative Control (`scripts/30_connes_spectral_matrix.py`):** We wired a structurally antisymmetric matrix that perfectly forged the Riemann zeros to machine precision. The `spectral_gate` instantly rejected it because it failed the Ablation gate (the arithmetic wasn't load-bearing). Later, our genuine Hermite-Adelic projection passed Ablation but was destroyed by the Permutation gate.

## What not to infer

- **None of this is evidence for or against RH.**
- **The Adelic computations don't prove Connes' theorem;** they simply map his analytical structure into computational objects. 
- **Passing the 3-Gate Harness is not a discovery.** A matrix projection built from the primes that survives ablation and hits the target might simply be a re-encoding of the explicit formula (which already reconstructs zeros from primes, see `scripts/03`). It guarantees the math is load-bearing, but it does *not* prove naturalness.

## What is open now

**The Cokernel of the Poisson-Summation Map (The True Adelic Pivot)**

The previous stated next step — "find the subspace projection that locks the spectrum of the scaling operator into stability" — was mathematically wrong. The Archimedean generator $xp + px$ on $L^2(\mathbb{R})$ has a continuous spectrum (all of $\mathbb{R}$) and carries no arithmetic. Refining a finite basis of it will only produce cutoff artifacts forever.

In Connes' framework, the Riemann zeros are an **absorption spectrum**. They are what is *missing* from the continuous spectrum after quotienting the Adeles by $\mathbb{Q}^*$. They are visible as gaps in a cokernel, not as eigenvalues you converge onto.

The next physical sprint is not diagonalizing an eigensolver. It is computing the cokernel of the Poisson-summation map on the Adelic Schwartz space. That is a radically different, much harder computation, but it is the exact place where the primes are mathematically load-bearing. 

Any computational proxy constructed must survive the **4-Gate Harness** (now including the Permutation Gate, verifying that the spectrum depends on the *set* of places, not the *list order*).
