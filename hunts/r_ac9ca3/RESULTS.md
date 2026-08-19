# Hunt R-AC9CA3 Results: Truncated Weil Form Positivity Failure on Davenport-Heilbronn

## Executive Summary

The question investigated is whether the first positivity failure of the Connes–van Suijlekom / Connes–Consani–Moscovici (CvS/CCM) Galerkin truncation of the Weil quadratic form on the Davenport–Heilbronn (DH) function occurs at $(c, N) = (31, 60)$ on the integer lattice, and whether this failure tracks the off-line zero pair.

**Verdict: Settled.**
On the integer lattice $c \in \{6, \dots, 60\}$ and Fourier band limit $N \le 128$:
1. For all integer $c \le 30$, the truncated Weil form is strictly positive definite across all tested $N \le 128$ (and up to $N = 256$ at $c = 29, 30$).
2. At $c = 31$, the even sector develops its first negative eigenvalue at precisely $N = 60$, with rigorous Arb ball enclosure $\lambda_{\min} = -1.87393568857 \times 10^{-31} < 0$, while one step earlier at $N = 59$ the form is strictly positive with $\lambda_{\min} = +8.36504566170 \times 10^{-31} > 0$.
3. The odd sector at $(31, 60)$ remains strictly positive definite (inertia $60$ positive, $0$ negative).
4. The Riemann zeta control at the identical cell $(31, 60)$ is strictly positive definite by a factor of 100 orders of magnitude: inertia $(61, 0)$ in the even sector, $(60, 0)$ in the odd sector, with $\lambda_{\min}(\zeta, 31, 60) = +4.82160175 \times 10^{-100} > 0$.
5. Mechanism attribution: At $(31, 60)$, the zero-side dictionary decomposition proves that the off-line quadruple term $4 \text{Re} g_v(\gamma_{\text{off}} - i\delta) = -6.734989 \times 10^{-29}$ is the sole negative contributor. Removing this quadruple flips the value positive to $+6.716250 \times 10^{-29} > 0$.

---

## 1. Positivity Horizon and the Crossing Curve

For each integer cutoff $c \in [6, 60]$, a Ball $\text{LDL}^T$ factorization of the $N_{\max} = 128$ Galerkin matrix at precision 600 bits determines the inertia of every leading principal submatrix simultaneously.

| $c$ | Bandwidth $L = \log c$ | First Negative $N$ (Even) | First Negative $N$ (Odd) | Band Edge $\omega = \frac{2\pi N}{L}$ | Notes |
|:---:|:----------------------:|:-------------------------:|:------------------------:|:-------------------------------------:|:------|
| 6..30 | 1.792 .. 3.401 | None (to $N=128$) | None (to $N=128$) | N/A | Conclusive positive |
| 29 | 3.367 | None (to $N=256$) | None (to $N=256$) | N/A | Deep probe; band edge ~477.5 |
| 30 | 3.401 | None (to $N=256$) | None (to $N=256$) | N/A | Deep probe; band edge ~472.8 |
| **31** | **3.434** | **60** | **None (to $N=192$)** | **109.78** | **First positivity failure** |
| 32 | 3.466 | 49 | 50 | 88.83 | Band edge enters zero region |
| 33 | 3.497 | 48 | 48 | 86.25 | Near $\gamma_{\text{off}} = 85.699$ |
| 35 | 3.555 | 49 | 49 | 86.60 | Closely tracking off-line ordinate |
| 40 | 3.689 | 50 | 50 | 85.16 | Closely tracking off-line ordinate |
| 44 | 3.784 | 51 (2nd neg at 128) | 51 | 84.69 | Second off-line pair enters |
| 47 | 3.850 | 52 (2nd neg at 128) | 52 | 84.92 | Deep cell ($\lambda_{\min} \approx -0.3163$) |
| 50 | 3.912 | 53 (2nd neg at 128) | 53 | 85.14 | Second pair active |
| 60 | 4.094 | 51 | 51 | 78.30 | High bandwidth |

Across $c \in [32, 60]$, the mean band edge frequency at the crossing is $\bar{\omega} = 83.64 \pm 2.44$, which directly matches the target off-line zero ordinate $\gamma_{\text{off}} \approx 85.6993$. At $c = 31$, the margin is larger ($N^* = 60$, $\omega = 109.78$) due to weaker analytic continuation amplification $c^\delta = 31^{0.3085} \approx 2.89$.

---

## 2. Marginal Cell $(c, N) = (31, 60)$ Multi-Route Verification

| Method / Oracle | Quantity | Measured Value | Sign |
|:----------------|:---------|:---------------|:----:|
| Arb `BallTruncation` ($N=58$) | $\lambda_{\min}(31, 58)$ enclosure (prec 700) | $+1.326102956 \times 10^{-30} \pm 2.88 \times 10^{-192}$ | $> 0$ |
| Arb `BallTruncation` ($N=59$) | $\lambda_{\min}(31, 59)$ enclosure (prec 700) | $+8.365045662 \times 10^{-31} \pm 1.71 \times 10^{-192}$ | $> 0$ |
| Arb `BallTruncation` ($N=60$) | $\lambda_{\min}(31, 60)$ enclosure (prec 700) | $-1.873935689 \times 10^{-31} \pm 3.12 \times 10^{-192}$ | $< 0$ |
| Arb `BallTruncation` ($N=61$) | $\lambda_{\min}(31, 61)$ enclosure (prec 700) | $-8.273174079 \times 10^{-31} \pm 2.39 \times 10^{-192}$ | $< 0$ |
| Arb `BallTruncation` ($N=64$) | $\lambda_{\min}(31, 64)$ enclosure (prec 700) | $-3.809628551 \times 10^{-30} \pm 2.93 \times 10^{-191}$ | $< 0$ |
| Exact Dyadic Rayleigh Upper Bound | $\frac{v^T M v}{v^T v}$ upper endpoint (prec 700) | $-1.873935689 \times 10^{-31}$ | $< 0$ |
| High-Precision Float Scout | mpmath `eigsy` (dps 60) | $-1.8739356885701883865 \times 10^{-31}$ | $< 0$ |
| Odd Sector at $(31, 60)$ | Ball $\text{LDL}^T$ inertia (prec 700) | $(60, 0)$, conclusive | $> 0$ |
| **Riemann Zeta Control $(31, 60)$** | Ball $\text{LDL}^T$ + enclosure (prec 2400) | Even $(61, 0)$, Odd $(60, 0)$; $\lambda_{\min} = +4.8216 \times 10^{-100}$ | $> 0$ |

The Riemann zeta control confirms sharp discrimination: the identical Galerkin truncation cell is strictly positive for $\zeta$ by 100 orders of magnitude, but strictly negative for the Davenport–Heilbronn imposter.

---

## 3. Mechanism and Localization

### 3.1 Deep Cell $(c, N) = (47, 64)$ Beam Profile
At $c = 47, N = 64$ ($\lambda_{\min} \approx -0.316303$):
- Peak mode index: $k_{\text{peak}} = 52$, corresponding to frequency $\omega_{\text{peak}} = \frac{2\pi \cdot 52}{\log 47} \approx 84.86$.
- Theoretical target mode: $k_{\text{target}} = \frac{85.6993 \cdot \log 47}{2\pi} \approx 52.51$ ($\omega = 85.70$).
- Mass concentration: $95.63\%$ of the eigenvector coefficient mass is concentrated within $\pm 6.0$ of the off-line ordinate $\gamma_{\text{off}} = 85.6993$.

### 3.2 Dictionary Decomposition at $(31, 60)$
Using the zero-side identity $\lambda = \langle v, Q v \rangle = \sum_{\gamma > 0} 2 g_v(r_\gamma)$:
- Lowest eigenvalue: $\lambda_{\min} = -1.8739 \times 10^{-31}$
- Off-line zero quadruple ($4 \text{Re} g_v(\gamma_{\text{off}} - i\delta)$): $-6.7350 \times 10^{-29}$
- On-line zeros partial sum ($T \le 120$, 64 zeros, all terms $\ge 0$): $+5.9537 \times 10^{-29}$
- Eigenvalue without off-line quadruple ($\lambda_{\min} - \text{quad}$): $+6.7162 \times 10^{-29} > 0$
- Tail model ($T > 120$ via mean density): $+2.956 \times 10^{-30}$
- Second off-line pair contribution: $+7.57 \times 10^{-32}$
- Bookkeeping residual: $4.67 \times 10^{-30}$ (~7% of the quadruple magnitude).

Because all on-line terms are non-negative, the off-line quadruple is the sole negative component in the explicit formula, and its subtraction flips the sign decisively positive.

---

## 4. Second Off-Line Pair Detection

At $c \ge 44$, a second negative eigenvalue appears in the even sector by $N = 128$.
This matches the second off-line zero of Davenport–Heilbronn at:
$$\rho_2 \approx 0.6508300806 + 114.1633427308 i \quad (\delta_2 = 0.15083, \gamma_2 = 114.1633)$$
Because $\delta_2 < \delta_1$, the amplification $c^{\delta_2}$ is weaker, requiring a larger cutoff $c \ge 44$ before the second pair produces a negative direction.

---

## ## Loose threads

1. **Exact continuous threshold $c^*$ in $(30, 31)$**:
   - What it was: The scan established that on the integer lattice, $c = 30$ is positive to $N = 256$ while $c = 31$ fails at $N = 60$. The continuous critical cutoff $c^* \in (30.0, 31.0)$ where the infinite-dimensional form first fails positivity was not bisected.
   - Why it might matter: Pinning $c^*$ to several decimal digits would test the precise analytic barrier where beam shaping matches the decay rate of the off-line pair.
   - First step: Run bisection on $c \in [30.0, 31.0]$ at $N = 128$ and $N = 256$ using `BallTruncation`.
