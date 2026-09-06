# prime_pair_error: results

All numbers below are in `results.json`, written by `probe.py` on 2026-09-06 (run cost in
`RUNS.md`). Notation as in Chou, Haag, Huryn, Ledoan (arXiv:2308.14888): psi_2(N, k) is
the von Mangoldt pair count with both members at most N, S(k) the singular series with
S(odd) = 0, e(N, k) = psi_2(N, k) - S(k)(N - k) for 1 <= k <= N, and
E(N) = 2 sum_{k=1}^{N} e(N, k)^2. R(x) = psi(x) - x throughout. Everything is measured;
nothing is a theorem.

## 1. What replicated

**Table 1, all eleven rows.** E(N)/(N^2 log^2 N), computed, then truncated to five
decimals as the paper does:

| N | computed | truncated | paper |
|---|---|---|---|
| 10^3 | 0.0946445 | 0.09464 | 0.09464 |
| 10^4 | 0.1232782 | 0.12327 | 0.12327 |
| 2 x 10^4 | 0.1306120 | 0.13061 | 0.13061 |
| 3 x 10^4 | 0.1450729 | 0.14507 | 0.14507 |
| 4 x 10^4 | 0.1508151 | 0.15081 | 0.15081 |
| 5 x 10^4 | 0.1548087 | 0.15480 | 0.15480 |
| 6 x 10^4 | 0.1612496 | 0.16124 | 0.16124 |
| 7 x 10^4 | 0.1774517 | 0.17745 | 0.17745 |
| 8 x 10^4 | 0.1595350 | 0.15953 | 0.15953 |
| 9 x 10^4 | 0.1619235 | 0.16192 | 0.16192 |
| 10^5 | 0.1685736 | 0.16857 | 0.16857 |

The 10^4 row is the one that tells truncation from rounding: 0.1232782 rounds to 0.12328
and truncates to the paper's 0.12327. The Figure 3 curve for N <= 1000 peaks at 0.6158
at N = 16 and ends at 0.09464, as drawn. C_2 from the Euler product to 4 x 10^6 is
0.6601618261 against the pinned 0.6601618158, inside the tail bound.

**The implementation against itself.** psi_2 by FFT autocorrelation agrees with a
pure-Python pair count (no numpy) at N = 2000 to 7 x 10^-12, with a direct numpy pair
count at N = 10^5 to 2 x 10^-10, and with direct sums at seven values of k at N = 10^7
to 1.5 x 10^-8. The singular-series sieve agrees with trial-division factorization at
every k <= 3 x 10^4 to 9 x 10^-16. The identity
sum_{|k| <= N} psi_2(N, k) = psi(N)^2 - sum Lambda(n)^2, which is the paper's Section 3,
holds at every N to floating precision, and gives the mean of e over k as
psi(N) - N + c(N) with c(N) between 1.21 and 1.32 at all six N.

**Beyond the paper's range.** The ratio keeps rising:

| N | 10^6 | 3 x 10^6 | 10^7 |
|---|---|---|---|
| E(N)/(N^2 log^2 N) | 0.21811 | 0.22096 | 0.24449 |

After the signed part of Section 4 is removed the ratio is 0.1667, 0.2124, 0.2201, 0.2399
at 10^5, 10^6, 3 x 10^6, 10^7. The data through 10^7 do not separate convergence from
slow growth; the paper's Corollary 3 allows either up to a power of log N.

## 2. Where the error sits

**Odd separations carry nothing.** Their share of E(N) is 4.5 x 10^-2 at N = 10^3,
3 x 10^-4 at 10^5 and 2 x 10^-6 at 10^7; the only pairs at odd k involve a power of 2.

**By size of separation**, the share of E(N) in each decile of k/N at N = 10^7:

    0.172  0.160  0.146  0.132  0.113  0.097  0.077  0.057  0.034  0.012

stable from 10^5 on. A squared error proportional to the prediction S(k)(N - k) would give
0.19, 0.17, 0.15, ..., 0.01; the measured profile is flatter at small k. Small
separations dominate, but less than the count of pairs would say.

**By prime factors of k**, at N = 10^7 (k-share is the fraction of separations in the
class, E-share its fraction of E(N), the ratio column is the class mean of
e^2 / (S(k)(N - k))):

| class | k-share | E-share | e^2/pred | mean e |
|---|---|---|---|---|
| 2 divides k exactly once | 0.250 | 0.500 | 68.5 | -2951 |
| 4 exactly | 0.125 | 0.250 | 68.4 | -2950 |
| 8 or more | 0.125 | 0.250 | 68.6 | -2948 |
| 3 divides k | 0.167 | 0.479 | 65.9 | -4470 |
| even, 3 does not | 0.333 | 0.521 | 69.8 | -2191 |
| 5 divides k | 0.100 | 0.237 | 65.2 | -3725 |
| 15 divides k | 0.033 | 0.114 | 63.2 | -5641 |
| 105 divides k | 0.005 | 0.018 | 60.4 | -6632 |

Two things read off this table. The power of 2 in k is invisible, exactly as it is
invisible to S(k): the three 2-adic classes have E-share equal to k-share to three
decimals and the same mean. And the odd small primes matter through S(k) but less than
proportionally: k divisible by 3 is one sixth of the separations and just under half of
E(N), and the ratio e^2/pred falls as the class gets richer in small primes.

**The variance is not proportional to the prediction.** Binning even k by quintile of
S(k) and fifth of k/N, the cell mean of e^2 / (S(k)(N - k)) at N = 10^7 runs from 64.7
(smallest S, smallest k) down to 52.9 across S and up to 79.6 across k. A power fit at
small k gives e^2 proportional to S(k)^gamma with gamma = 0.71, 0.75, 0.79, 0.83 at
N = 10^5, 10^6, 3 x 10^6, 10^7, drifting toward 1 but not there. A linear fit
e^2 = A + B S(k)(N - k) per k-fifth gives an S-independent part A that shrinks with k
roughly like N log N (1 - k/N), not a constant floor. Recorded, not explained.

## 3. The mean of the error is S(k) times the prime number theorem remainder

The paper's identity fixes the k-average of e at psi(N) - N + O(1) and uses it for
Theorem 2. The class means above show how that average is distributed: the 3-divides-k
class has mean -4470 against -2191 for the rest of the even k, ratio 2.04, and the factor
S(k) carries for 3 | k is exactly 2. At N = 10^6, where psi(N) - N = -413 is an unusually
large excursion, every class mean is its class mean of S(k) times about -430, within the
noise. The offset is not a constant across k; it is S(k) times one number.

## 4. The one compact relationship, and its test

Write theta_2(N, k) for the pair count over primes only (proper prime powers removed),
P(N, k) = psi_2 - theta_2 for the pairs with at least one proper prime power, and

    B(N, k) = (psi - theta)(N) + (psi - theta)(N - k) - (psi - theta)(k),

which is about sqrt(N) + sqrt(N - k) - sqrt(k). On even k < N, fit each of e, the
prime-only error e_theta = theta_2 - S(k)(N - k), and P by least squares on the three
profiles

    S(k),     S(k) (B(N, k) - mean B),     S(k) (R(N - k) - R(k)),

with coefficients alpha, beta, gamma. The first-order heuristic (each factor of the pair
carries the one-point fluctuation, and the arcs that build S(k) carry it multiplied by
S(k)) predicts alpha = R(N), beta = 0, gamma = 1 for e; alpha = theta(N) - N,
beta = -1, gamma = 1 for e_theta; and beta = 1, gamma = 0 for P. Measured:

| N | alpha_e | psi(N)-N | beta_e | gamma_e | alpha_theta | theta(N)-N | beta_theta | gamma_theta | beta_P |
|---|---|---|---|---|---|---|---|---|---|
| 10^3 | -10.4 | -3.3 | -0.053 | 0.639 | -42.2 | -43.8 | -0.937 | 0.506 | 0.884 |
| 10^4 | 2.6 | 13.4 | -0.010 | 0.806 | -102.8 | -104.0 | -0.951 | 0.755 | 0.941 |
| 10^5 | 37.6 | 51.6 | -0.005 | 0.987 | -313.1 | -314.6 | -0.985 | 0.971 | 0.980 |
| 10^6 | -430.3 | -413.4 | -0.001 | 0.994 | -1513.6 | -1515.8 | -0.995 | 0.986 | 0.994 |
| **3 x 10^6** | -19.7 | 0.0 | -0.001 | 1.000 | -1891.3 | -1892.5 | -0.998 | 0.993 | 0.996 |
| **10^7** | -1481.5 | -1460.6 | -0.000 | 0.994 | -4818.3 | -4820.7 | -0.998 | 0.991 | 0.998 |

The relationship was found on N <= 10^6; the two bold rows are the held-out test. At
10^7 the independence-approximation standard errors are 5 on alpha, 0.003 on beta and
0.008 on gamma, so every coefficient is within a few percent of its predicted value and
the two that should vanish do. Compactly, for F either psi or theta and
R_F(x) = F(x) - x,

    F_2(N, k) - S(k)(N - k)  =  S(k) [ R_F(N) + R_F(N - k) - R_F(k) ]  +  noise.

The offset alpha_e - (psi(N) - N) is -7, -11, -14, -17, -20, -21 across the six N,
about -1.5 log N + 3; it mirrors the positive mean of e on odd k (12 to 32, the pairs
with a power of 2), which the exact identity forces the even k to compensate.

**How much it explains.** For the von Mangoldt count the fitted part carries 1.1, 2.6,
0.4 and 1.9 percent of sum e^2 at 10^5, 10^6, 3 x 10^6, 10^7, tracking |psi(N) - N| /
sqrt(N) (0.16, 0.41, 0.00, 0.46). For the prime-only count it carries 20, 22, 12 and
16 percent, because theta(N) - N has the extra -(psi - theta)(N) of size sqrt(N) at every
N. After removal the residual ratio is the same for both counts (0.2399 against 0.2455 at
10^7): the noise is shared, and prime powers only move the signed part.

**What the beta column says.** P(N, k) is S(k) B(N, k) to within 0.2 percent in slope
(correlation 0.90; the remaining 12 percent of its variance is the Legendre-symbol
modulation of pairs (p^2, p^2 +- k), for instance p^2 + 2 is always divisible by 3). The
prime-only count sits below the Hardy-Littlewood count by exactly that amount, and the
von Mangoldt count does not see it at all. This is the pair analogue of
theta(x) = psi(x) - (psi - theta)(x). It is invisible in a per-k table: at k = 2 and
N = 10^7 the deficit S(2) B is about 9 x 10^3 against a per-k noise of about 3 x 10^4,
and only pooling over k shows it: the beta_theta entry is hundreds of standard errors from zero under the independence approximation, which overstates the significance since neighbouring k are correlated, but not by a factor that matters.

## 5. The literature

- **Chou, Haag, Huryn, Ledoan**, Section 3: the k-sum identity and the mean R(N). Our
  Section 3 is the k-resolved form of that mean.
- **Korevaar and te Riele**, Average prime-pair counting formula, Math. Comp. 79 (2010),
  arXiv:0902.4352, Approximation 2.1: for N large and x much larger than N,
  (1/N) sum_{r <= N} {psi_{2r}(x) - 2 C_{2r} x} = -4 sum_rho x^rho / rho + ... , supported
  by prime-pair counts to x = 10^12. That is the small-k, k-averaged limit of the
  relationship above: S(k) averages to 2 over even k, and R(N - k) - R(k) tends to R(N)
  for k much smaller than N, so the profile averages to 4 R(N), which is their -4 times
  the zero sum. Their (2.5) splits psi_{2r} - theta_{2r} through the prime-square pair
  count, the same split as the beta column. So the relationship is a refinement of a
  published heuristic: the S(k) weighting at each k, the R(N - k) - R(k) term, and the
  range up to k = N are what is measured here and not stated there, as far as pages
  1 to 8 of that paper go. **Not claimed new.** Keating and Smith (arXiv:1903.07057)
  derive S(k) from the pair correlation of zeros and do not carry this term.
- **Funkhouser, Goldston, Sengupta, Sengupta**, Prime difference champions (2020,
  arXiv:1612.02938), Figure 11: the unweighted analogue, the variance of the
  prime-difference count over d divided by pi(x)^2, sits near 0.16 for x from 10^4 to
  10^7, flat. Our log-weighted ratio rises from 0.12 to 0.24 over the same range. The
  two normalizations are not the same object and were not reconciled here.
- **Friedlander and Goldston** (1995), as cited by Korevaar and te Riele: the sum of the
  singular series to h is h - (1/2) log h + O(log^{2/3} h). Measured
  sum_{k <= N} S(k) - N + (1/2) log N stays within +-0.55 across 10^3 to 10^7, so the
  coefficient of log is -1/2 to within 0.1. Korevaar and te Riele's displayed (3.4)
  reads (1/2) log m for the sum of C_{2r} to m, which would be a full log h here and is
  inconsistent with this measurement; read it as a normalization slip in the display.

## 6. What failed, and what was not pursued

- The Poisson-type law e^2 proportional to S(k)(N - k) does not hold (Section 2). No
  compact variance law was found.
- Whether E(N)/(N^2 log^2 N) converges, and to what, is open at 10^7. A crude model in
  which the minor-arc part of |S(alpha)|^2 is exponentially distributed about half of
  N log N gives 1/4; the data are at 0.244 and still rising. That model is a heuristic
  aside, not a claim.
- The class means at N = 10^5 miss the S(k) R(N) prediction by three to four sigma in the
  richer classes (3 | k: 94 against 155, sigma 15). The non-principal characters
  contribute L-function zero sums of the same sqrt(N) order with signs that depend on k
  modulo small q; those were not modelled. At 10^6 and 10^7 the principal term dominates
  because |psi(N) - N| is large there.
- A finer profile for P(N, k) with the Legendre-symbol singular series of p^2 +- k would
  close the last 12 percent of its variance. Not built.
