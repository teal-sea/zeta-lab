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

---

# Second pass, 2026-09-06: a fixed-coefficient residue-class correction

All numbers in this part are in `results_residue.json`, written by `residue.py` (cost in
`RUNS.md`); `tests/test_prime_pair_residue.py` pins the identities, the closed form, the
frozen coefficients and the recorded numbers. Notation as above. Everything is measured;
the identities in Section 8 are exact and are checked as such; nothing is a theorem
about the asymptotics.

## 7. What was checked before anything new was built

**The modulo-3 formula.** The brief asked for an independent check of a supplied
modulo-3 formula. No such formula was found in this repository, in PR #181, in the
Fulcrum record, in the private ledger or in any checkout, so the formula checked here is
the one the decomposition of Section 8 produces at modulus 3, written in closed form
with the character mod 3 (Section 9). It is checked two ways: the closed form, which
never forms residue-class sums of the centered function, agrees with the general
modulus-q code to rounding (`check_chi3_closed_form_vs_general_maxabs`, below
2 x 10^-6 at every cutoff, on terms of size 10^3 to 10^4), and the general code is checked against the exact
identity with an independent pair count.

**The first-pass results.** `probe.py` was re-run to N = 10^6: Table 1 matches at all
eleven rows, and the ratio, the three-profile coefficients and the class means at
10^3, 10^4, 10^5, 10^6 are identical to `results.json` to every printed digit. The
three-profile fit was also re-implemented from scratch in `residue.py`
(`first_pass_fit_at_fresh_N`) and gives alpha = 37.6, gamma = 0.987 at 10^5 and
alpha = -430.3, gamma = 0.994 at 10^6, the first pass's numbers.

## 8. The decomposition at a modulus q

Fix q with phi = phi(q), w = q / phi, and write M_q(n) = w for (n, q) = 1, n >= 1, and 0
otherwise: the periodic model of Lambda with the right mean on the reduced classes.
Split Lambda on the reduced classes as Lambda' = M_q + delta', and leave the
non-reduced classes, which carry only the powers of the primes dividing q, alone. Then
for 1 <= k <= N,

    psi_2(N, k) = A_q(N, k) + L_q(N, k) + X_q(N, k) + D_q(N, k),                (I1)

    A_q = sum_{n <= N-k} M(n) M(n+k)                                periodic baseline
    L_q = sum_{n <= N-k} [M(n) delta'(n+k) + delta'(n) M(n+k)]      linear endpoint terms
    X_q = sum over pairs with a member a power of a prime dividing q    exceptional
    D_q = sum_{n <= N-k} delta'(n) delta'(n+k)                      remaining correlation

(I1) is an exact identity: it is the expansion of (M + delta' + Lambda^x)(n) times the
same at n + k, with the three products involving Lambda^x collected into X_q. The
pieces have the following exact properties.

**(I2) The baseline is the local singular series times the length, plus a bounded
periodic term.** With nu_q(k) = #{a mod q : (a, q) = 1 = (a + k, q)},

    A_q(N, k) = S_q(k) (N - k) + rho_q(N, k),    S_q(k) = q nu_q(k) / phi^2,    |rho_q| <= w^2 nu_q(k),

and by the Chinese remainder theorem S_q(k) = prod_{p | q} sigma_p(k) with
sigma_p(k) = p/(p-1) for p | k and p(p-2)/(p-1)^2 otherwise. For p = 2 this is 2 or 0,
for p = 3 it is 3/2 or 3/4, for p = 5 it is 5/4 or 15/16.

**(I3) The singular series factors over the modulus.** S(k) = S_q(k) S^(q)(k), where
S^(q) is the same product over the primes not dividing q, i.e.
S^(q)(k) = C_2^(q) prod_{p | k, p > 2, p not | q} (p-1)/(p-2) times sigma_2(k) when q is
odd, with C_2^(q) = C_2 / prod_{p | q, p > 2} (1 - 1/(p-1)^2). This holds at every k,
odd k included, and the test checks it at every k <= 5000 for q = 1, 2, 3, 5, 30, 210.

**(I4) The endpoint terms are linear in the prime counts of residue classes.** Writing
Psi'_b(x) = sum_{n <= x, n = b (q)} delta'(n) = psi(x; q, b) - w #{n <= x : n = b (q)}
for reduced b,

    L_q(N, k) = w sum_{b : (b - k, q) = 1} [Psi'_b(N) - Psi'_b(k)] + w sum_{a : (a + k, q) = 1} Psi'_a(N - k),

both sums over reduced residues. So L_q reads psi(x; q, b) at x = N, k and N - k only,
plus an exactly known sawtooth. In characters, psi(x; q, b) = (1/phi) sum_chi
chi-bar(b) psi(x, chi), so L_q carries the principal-character remainder with weight
S_q(k) and each non-principal psi(x, chi) with a weight that is a twisted Ramanujan-type
sum over the reduced pairs (a, a + k); for q = 30 that is eight characters, of
conductors 1, 3, 5 and 15.

**(I5) The exceptional term is small and exact.** X_q(N, k) is a sum over the
O(log N) powers of 2, 3, 5 up to N, each paired with Lambda at distance k; it is
O(log^2 N) at every k and is computed by enumeration. For q = 1 it is empty. Its
k-mean on even k is what the first pass saw as the offset alpha_e - (psi(N) - N) of
about -1.5 log N: the pairs (2^j, 2^j +- k) that the exact identity forces the even k to
compensate for.

**(I6) The q = 1 member.** For q = 1, M = 1, rho = 0, X = 0 and
L_1 = R(N) + R(N - k) - R(k), so the first pass's profile is the endpoint term of the
trivial modulus.

## 9. The one heuristic, and the three corrections

Everything above is an identity. The heuristic is one sentence, applied once:

> **(H_q)** the primes not dividing q act on the reduced classes mod q as all primes act
> on the integers,

i.e. the centered correlation carries the factor (S^(q)(k) - 1) on everything the model
already carries: D_q(N, k) = (S^(q)(k) - 1) [A_q(N, k) + L_q(N, k)] + noise with mean
zero. Under (H_q) the predicted signed part of e(N, k) = psi_2 - S(k)(N - k) is, using
(I2) and (I3),

    c_q(N, k) = S^(q)(k) [ rho_q(N, k) + L_q(N, k) ] + X_q(N, k),

and the residual Z_q = e - c_q = D_q - (S^(q) - 1)(A_q + L_q) is what (H_q) says is
centered. **Every coefficient is fixed at 1 by the derivation**; the `FROZEN` table in
`residue.py` records the six numbers a fit could have moved, all at their derived
values, and the test refuses any other value. (H_q) is the same first-order heuristic
the first pass used, restricted to a residue class pair; the un-linearised form,
S^(q)(k) (q/(N-k)) sum_a psi(N-k; q, a) [psi(N; q, a+k) - psi(k; q, a+k)], differs from
c_q by at most 73 at any k < N at every cutoff, against endpoint terms of size 10^3 to
10^4, and changes no reduction by more than 0.002 points.

The three corrections compared, and the one diagnostic:

- **Original (q = 1)**: c_1 = S(k) [R(N) + R(N - k) - R(k)], the first pass's profile with
  its predicted coefficients (R(N), 0, 1), not the fitted ones.
- **Modulo 3 (q = 3)**: with chi the character mod 3, R'(x) = psi(x) - x - (log 3) floor(log_3 x),

      c_3 = S(k) [R'(N) + R'(N-k) - R'(k)]
            + S(k) chi(k) [psi(N-k, chi) - psi(N, chi) + psi(k, chi)]
            + S^(3)(k) [rho_3(N, k) + sawtooth] + X_3(N, k).

  The character term has opposite signs on k = 1 and k = 2 mod 3 and vanishes on 3 | k;
  the sign comes from the twisted sums sum_{a : (a, 3) = 1 = (a + k, 3)} chi(a) = chi(k)
  and sum chi(a + k) = -chi(k), which for prime q are the values of a Ramanujan sum
  twisted by chi.
- **Period 30 (q = 30)**: c_30 from (I2) to (I5) with the eight reduced residues mod 30 and
  the eight characters; not the sum of the q = 2, 3, 5 corrections, because the
  residue constraint (a, 30) = 1 = (a + k, 30) couples the three primes and the
  baseline factor S_30 = sigma_2 sigma_3 sigma_5 is a product, not a sum.
- **Diagnostic (q = 210)**: c_210 is computed only to ask whether what c_30 leaves behind
  is what the next prime predicts. It is not one of the three candidates.

## 10. The comparison at fresh cutoffs

The first pass evaluated at 10^3, 10^4, 10^5, 10^6, 3 x 10^6 and 10^7. The five cutoffs
below were never used before; the coefficients were frozen (Section 9) before the run;
nothing was looked at in between. The reduction is 1 - sum_k (e - c_q)^2 / sum_k e^2
over all 1 <= k <= N, in percent (restricting to even k changes the third decimal);
the slope is the post-hoc least-squares coefficient of e on c_q over even k, a
diagnostic whose derived value is 1.

| N | E/(N^2 log^2 N) | q = 1 | q = 3 | q = 30 | (q = 210) | slope q = 1 | q = 3 | q = 30 |
|---|---|---|---|---|---|---|---|---|
| 2 x 10^5 | 0.18974 | 0.62 | 7.64 | 10.04 | 13.12 | 0.946 | 1.001 | 1.001 |
| 5 x 10^5 | 0.19863 | 0.90 | 1.27 | 3.24 | 6.99 | 0.933 | 0.966 | 0.998 |
| 2 x 10^6 | 0.21833 | 0.52 | 0.95 | 2.71 | 4.67 | 0.990 | 1.000 | 1.002 |
| 5 x 10^6 | 0.23438 | 1.89 | 2.41 | 3.60 | 5.26 | 0.983 | 0.990 | 1.000 |
| 7 x 10^6 | 0.23720 | 0.80 | 1.32 | 2.20 | 4.06 | 0.987 | 0.994 | 1.002 |

Three things to read off it.

**The order is the same at every cutoff**: each refinement removes more than the last,
and the modulus-30 correction removes between 1.2 and 16 times what the original does.
The size of the reduction at a given N is set by how large the one-point excursions
happen to be there: at 2 x 10^5, psi(N) - N is 27 and the original carries 0.6 percent,
while the character mod 3 has a large excursion and carries 7 percent on its own. That
is the first pass's observation (the q = 1 share tracks |psi(N) - N| / sqrt N) with
more characters to track.

**The coefficient is 1.** The slope of e on c_30 is within 0.2 percent of 1 at all five
cutoffs, on c_3 within 3.5 percent, on c_1 within 7 percent; the modulus-1 slope is the
noisiest because c_1 is the smallest of the three. The share sum c_q^2 / sum e^2 equals
the reduction to two decimals at every row, which is the same statement.

**What each piece weighs**, at 7 x 10^6 on even k: the endpoint term S^(q) L_q has rms
1838, 2334 and 2984 for q = 1, 3, 30; the exceptional term X_q has rms 43 and 70 for
q = 3, 30 (maximum 102 at q = 210); the bounded term rho_q is at most 0.8 and 16.9. The
per-k noise has rms 1.4 x 10^4, which is why a correction that is right to one percent
in slope removes only a few percent of the squared error: E(N) is noise, and the signed
part is a tenth of it in amplitude. The residual ratio (sum (e - c_30)^2 in units of
N^2 log^2 N, doubled for +-k) is 0.1707, 0.1922, 0.2124, 0.2260, 0.2320, still rising.

**The offset the first pass could not place.** The mean of e - c_1 on even k is -22 to
-28 at the five cutoffs, the first pass's alpha_e - (psi(N) - N) of about -1.5 log N.
The mean of e - c_3 is the same; the mean of e - c_30 is 2.3 to 2.5 at all five. The
offset is the exceptional term of the prime 2, the pairs (2^j, 2^j +- k), which the
modulus-30 decomposition carries exactly and the modulus-3 one does not (X_3 holds only
the powers of 3). What is left, +2.4, is constant across N and is not explained.

## 11. Where the remaining discrepancy sits

For the residual Z_30 = e - c_30 on even k < N, and for e, Z_1, Z_3 as contrast; z is
the class mean divided by its standard error under independence, which overstates
significance for neighbouring k but not by a factor that matters here.

**Nothing is left at the modulus.** Over the fifteen even classes k mod 30, the largest
|z| is 53, 29, 67, 104, 79 for e; 25, 25, 56, 70, 52 for Z_3; and 0.6, 0.4, 0.3, 0.2, 0.3
for Z_30. By k mod 3 at 7 x 10^6: e has class means 1639, 1704, 24 (se 22, 17, 17);
Z_1 has -83, +840, -839, the antisymmetric pair the character term predicts and the
original correction cannot see; Z_3 has -35, -23, -17, the offset of Section 10; Z_30
has 6, -1, 2. The class k = 0 mod 3 of Z_30 sits at +6 with se 15 to 22 at every cutoff,
consistent with zero and consistently positive; recorded.

**Everything is left at the next primes.** The largest |z| of Z_30 by k mod 7, 11, 13 is
15, 15, 10 at 2 x 10^5 and 97, 66, 36 at 7 x 10^6. The modulus-210 member of the same
family, with the same frozen coefficients, predicts the mod-7 class means of Z_30 to
within one standard error at every cutoff; at 7 x 10^6 the seven class means of Z_30
are -34, +688, +1566, -2733, +913, +912, -1295 and the increment c_210 - c_30 averages
-42, +687, +1564, -2737, +912, +912, -1296 on the same classes, with standard errors
of 17 to 30. After c_210 the largest |z| by k mod 7 is 0.35 at every cutoff. The
correlation of Z_30 with the increment is 0.13 to 0.20 and the slope 0.99 to 1.00. The
mod-11 and mod-13 structure remains and would be the next two rungs; the cost of a rung
is linear in phi(q).

**Not in the size of k, not in S(k).** The share of sum Z_30^2 by decile of k/N at
7 x 10^6 is 0.174, 0.162, 0.148, 0.133, 0.115, 0.096, 0.076, 0.054, 0.032, 0.010, the
first pass's profile for e itself to the third decimal; the correction does not move
where the squared error lives. The mean of Z_30 by quintile of S(k) is within one
standard error of zero in every cell at every cutoff (at 7 x 10^6: +20, -8, -7, +13, -7
with se 20 to 29).

## 12. One statement to prove

Let chi be the non-principal character mod 3 and

    T(N) = sum_{1 <= k <= N} chi(k) [psi_2(N, k) - S(k)(N - k)] = sum_{n < n' <= N} Lambda(n) Lambda(n') chi(n' - n) - sum_k chi(k) S(k)(N - k).

Under (H_3), with S(k) replaced by its class mean 3/2 on even k not divisible by 3 and
the class sum by a third of the full sum, T(N) is I(N) = sum_{x < N} psi(x, chi)
- ((N - 1)/2) psi(N, chi). Measured, against the original correction's version:

| N | T(N) measured | from c_1 | I(N) | T/I | (T - I)/(N log N) | N^{3/2} |
|---|---|---|---|---|---|---|
| 2 x 10^5 | -4.683 x 10^7 | 4.8 x 10^4 | -4.679 x 10^7 | 1.0009 | -0.017 | 8.9 x 10^7 |
| 5 x 10^5 | 1.936 x 10^7 | 1.3 x 10^5 | 1.926 x 10^7 | 1.0053 | 0.015 | 3.5 x 10^8 |
| 2 x 10^6 | -1.1554 x 10^8 | 4.9 x 10^5 | -1.1551 x 10^8 | 1.0002 | -0.001 | 2.8 x 10^9 |
| 5 x 10^6 | -1.5723 x 10^9 | 1.3 x 10^6 | -1.5714 x 10^9 | 1.0006 | -0.012 | 1.1 x 10^10 |
| 7 x 10^6 | 1.9587 x 10^9 | 1.9 x 10^6 | 1.9625 x 10^9 | 0.9981 | -0.035 | 1.9 x 10^10 |

The statement, in the form the data support:

> **(T)** For the non-principal character chi mod 3, as N -> infinity,
>
>     sum_{1 <= k <= N} chi(k) [psi_2(N, k) - S(k)(N - k)] = integral_0^N psi(x, chi) dx - (N/2) psi(N, chi) + O(N^{1 + epsilon}),
>
> equivalently, by the explicit formula for psi(x, chi) with rho over the non-trivial
> zeros of L(s, chi),  = sum_rho N^{rho + 1} (rho - 1) / (2 rho (rho + 1)) + O(N^{1 + epsilon}).

Why this one. First, it is the exact character analogue of the mechanism behind the
paper's Theorem 2, which lower-bounds E(N) by Omega(N^{1 + 2 Theta - epsilon}) from the
variability of psi(N) - N through the k-mean of e: by Cauchy-Schwarz,
E(N) >= T(N)^2 / N, so (T) with Landau's theorem would give
E(N) = Omega(N^{1 + 2 Theta_chi - epsilon}) with Theta_chi the supremum of the real parts
of the zeros of L(s, chi_3); the pair error would then be bounded below by the zeros of
L(s, chi_3) as well as by those of zeta, and by the same route by every L(s, chi).
Second, unlike the k-mean the paper uses, T(N) does not reduce to one-point counts: the
sum over ordered pairs n != n' of Lambda(n) Lambda(n') chi(n' - n) is sum_{a, b}
psi(N; 3, a) psi(N; 3, b) chi(b - a), which vanishes identically because chi is odd, so
T(N) is the antisymmetric half n < n' and carries genuine pair information. It is the
character-weighted analogue of Korevaar and te Riele's Approximation 2.1 at the level
of the secondary term. Third, it is sharp enough to be wrong: the main term is of order
N^{3/2} and the measured discrepancy is at most 0.035 N log N in absolute value at the
five cutoffs, so an error term of order N^{3/2 - delta} for any delta > 0 is what the
data can distinguish; they cannot tell O(N log N) from O(N^{1 + epsilon}) and they say
nothing about the constant. The zero-sum form is derived from the integral form and
was not measured: no zero of L(s, chi_3) was computed here; psi(x, chi) was summed
directly from Lambda.

## 13. The literature, and what was not done

- **Chou, Haag, Huryn, Ledoan**, Theorem 2: E(N) = Omega(N^2 (log log log N)^2) and
  Omega(N^{1 + 2 Theta - epsilon}), proved, in their words, from "the variability in the
  number of primes up to N", i.e. through the k-mean of e, which is the q = 1 endpoint
  term of Section 8. Sections 9 to 12 are that mechanism run through the characters.
- **Korevaar and te Riele** (Math. Comp. 2010): the k-averaged small-k form with zeta
  zeros only; no characters, no residue classes of k.
- **Bhowmik, Halupczok, Matsumoto, Suzuki**, Goldbach representations in arithmetic
  progressions and zeros of Dirichlet L-functions, Mathematika 65 (2019) 57-97,
  arXiv:1704.06103: the average number of representations of an integer as a sum of
  two primes in arithmetic progressions, with the secondary term as a sum over zeros
  of Dirichlet L-functions, conditionally. That is the sum side (n + n' = m, averaged
  over m) of what Section 8 does on the difference side, unaveraged in k, with the sign
  rule chi(k). The difference-side statement in this form was not found; the search
  covered abstract pages and search listings, not paper bodies. **Not claimed new.**
- **Fujii** (Acta Arith. 1991) and **Languasco and Zaccagnini** (2012): the average
  Goldbach count sum_{n <= N} G(n) = N^2/2 - 2 sum_rho N^{rho+1}/(rho(rho+1)) + error,
  proved under RH. The zero-sum form of (T) has the same shape with L(s, chi_3) in place
  of zeta and (rho - 1)/(2 rho (rho + 1)) in place of -2/(rho(rho+1)); whether their
  method reaches the difference side is exactly what proving (T) would settle.
- **Bogomolny and Keating** (arXiv:1307.6010): the Hardy-Littlewood conjecture for
  primes in arithmetic progressions used in the other direction, from prime pairs to the
  pair correlation of zeros of L(s, chi); their finite products over the primes dividing
  the modulus are the factorisation (I3).

Not done: the modulus-210 member is a diagnostic here, not a candidate, and the mod-11
and mod-13 structure it leaves is unmeasured against the modulus-2310 member; the
second-order (product-form) term was bounded, not modelled; the prime-only count
theta_2 was not redone at modulus q (the first pass's prime-power profile is orthogonal
to everything here); no zeros of any L-function were computed; and the question of
whether E(N)/(N^2 log^2 N) converges is unchanged, 0.2372 at 7 x 10^6 and rising. The
constant +2.4 in the residual mean is recorded and not explained.
