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

    F_2(N, k) - S(k)(N - k)  =  S(k) [ R_F(N) + R_F(N - k) - R_F(k) ]  +  a residual not modelled here.

The offset alpha_e - (psi(N) - N) is -7, -11, -14, -17, -20, -21 across the six N,
about -1.5 log N + 3; it mirrors the positive mean of e on odd k (12 to 32, the pairs
with a power of 2), which the exact identity forces the even k to compensate.

**How much it explains.** For the von Mangoldt count the fitted part carries 1.1, 2.6,
0.4 and 1.9 percent of sum e^2 at 10^5, 10^6, 3 x 10^6, 10^7, tracking |psi(N) - N| /
sqrt(N) (0.16, 0.41, 0.00, 0.46). For the prime-only count it carries 20, 22, 12 and
16 percent, because theta(N) - N has the extra -(psi - theta)(N) of size sqrt(N) at every
N. After removal the residual ratio is the same for both counts (0.2399 against 0.2455 at
10^7): the residual is shared, and prime powers only move the signed part.

**What the beta column says.** P(N, k) is S(k) B(N, k) to within 0.2 percent in slope
(correlation 0.90; the remaining 12 percent of its variance is the Legendre-symbol
modulation of pairs (p^2, p^2 +- k), for instance p^2 + 2 is always divisible by 3). The
prime-only count sits below the Hardy-Littlewood count by exactly that amount, and the
von Mangoldt count does not see it at all. This is the pair analogue of
theta(x) = psi(x) - (psi - theta)(x). It is invisible in a per-k table: at k = 2 and
N = 10^7 the deficit S(2) B is about 9 x 10^3 against a per-k residual of about 3 x 10^4,
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
already carries: D_q(N, k) = (S^(q)(k) - 1) [A_q(N, k) + L_q(N, k)] + a remainder that
(H_q) takes to have mean zero. Under (H_q) the predicted signed part of e(N, k) = psi_2 - S(k)(N - k) is, using
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
per-k residual has rms 1.4 x 10^4, which is why a correction that is right to one percent
in slope removes only a few percent of the squared error: most of E(N) remains
unexplained by the tested corrections, and the signed part they capture is a tenth of the
residual in amplitude. The residual ratio (sum (e - c_30)^2 in units of
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
directly from Lambda. Part 3 below (Sections 14 to 19) takes (T) apart: it holds under RH
for zeta and for L(s, chi) with O(N log^4 N) in place of O(N^{1+eps}), and the lower bound
on E(N) it was named for holds unconditionally.

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

---

# Third pass, 2026-09-06: Section 12's sum is a Wronskian, and what is proved about it

All numbers in this part are in `results_wronskian.json`, written by `wronskian.py`
(cost in `RUNS.md`); section 5 of `tests/test_prime_pair_residue.py` pins the identities
on arbitrary weights as well as on Lambda, and the recorded numbers. Notation as above,
and in addition P(x) = psi(x, chi) = sum_{n <= x} Lambda(n) chi(n) with chi the
non-principal character mod 3, R(x) = psi(x) - x, and

    T(N) = sum_{k=1}^{N} chi(k) [psi_2(N, k) - S(k)(N - k)],
    I(N) = integral_0^N P(x) dx - (N/2) P(N) = sum_{j=0}^{N-1} P(j) - (N/2) P(N),

so that (T) of Section 12 reads T(N) = I(N) + O(N^{1+eps}). Section 12 measured T/I
within 0.5 percent at five cutoffs and stated (T) as a conjecture. This part asks what is
true of T(N) - I(N). In one line: it is a Wronskian of the two prime-counting remainders
R and P plus an explicit term of order N; the Wronskian is bounded by
N^{Theta + Theta_chi} (log N)^4 unconditionally, Theta and Theta_chi the suprema of the
real parts of the zeros of zeta(s) and of L(s, chi); so (T) holds under RH for zeta and
for L(s, chi) with O(N log^4 N) in place of O(N^{1+eps}), and, unconditionally,
E(N) = Omega(N^{1 + 2 Theta_chi - eps}), the lower bound by the zeros of L(s, chi) that
Section 12 named. Not proved: (T) without the two hypotheses, and anything sharper than
log^4 N.

The sections separate four questions: what is an identity (14, 16), what is elementary
(15), what is a theorem and under which hypothesis (17, 18), what is known elsewhere (19).

## 14. The reduction, verified

Write A(n), B(n) for the sums of Lambda over m <= n in the classes 1 and 2 mod 3, so
P = A - B and, with r(n) = A(n) + B(n) - n, A = (n + r + P)/2 and B = (n + r - P)/2.
Lambda' = Lambda on 3 not | n is the reduced part; the rest is the powers of 3.

**(E0) The character is antisymmetric and linear on reduced pairs.** For 3 dividing
neither n nor m,

    chi(m - n) = (chi(n) - chi(m)) / 2.

Four cases: (n, m) = (1, 2) mod 3 gives chi(1) = 1 = (1 - (-1))/2; (2, 1) gives
chi(2) = -1 = (-1 - 1)/2; (1, 1) and (2, 2) give chi(0) = 0. Everything below rests on
this line, and it is special to the modulus 3, the one modulus whose two reduced classes
are exchanged by negation with a non-zero character (mod 4 and mod 6 have chi(m - n) = 0
on every reduced pair).

**(E1) The reduced pairs.** By (E0) and the definition of the prefix sums, for any weight
f supported on 3 not | n,

    sum_{n < m <= N} f(n) f(m) chi(m - n) = sum_{n=1}^{N} [A(n-1) dB(n) - B(n-1) dA(n)]
                                          = sum_{j=0}^{N-1} P(j) - ((N-1)/2) P(N) + W(N),

    W(N) = (1/2) sum_{n=1}^{N} [P(n-1) dr(n) - r(n-1) dP(n)],    df(n) = f(n) - f(n-1),

all cumulative functions vanishing at 0. The second line is the expansion of A and B in
n + r and P: A(n-1) dB(n) - B(n-1) dA(n) = (1/2)[P(n-1)(1 + dr(n)) - (n - 1 + r(n-1)) dP(n)],
and sum_n (n-1) dP(n) = (N-1) P(N) - sum_{j=0}^{N-1} P(j) by partial summation. So the
coefficient of P(N) is (N-1)/2 and not N/2; the two differ by P(N)/2, and the test
checks that the N/2 form misses by exactly that.

**(E2) The pairs with a power of 3.** chi(3^j + k) = chi(k) and chi(3^j - k) = -chi(k), so

    X_chi(N) = sum_{n < m <= N, 3 | nm} Lambda(n) Lambda(m) chi(m - n)
             = (log 3) sum_{3^j <= N} [P(N) - 2 P(3^j)],

and for a general weight f the same with f(3^j) for log 3 and the sum over all 3 | n.

**(E3) The identity.** With H_chi(N) = sum_{k <= N} chi(k) S(k) (N - k), (E1) and (E2)
applied to Lambda give

    T(N) - I(N) = W(N) + P(N)/2 + X_chi(N) - H_chi(N).                                   (E3)

This is the identity the brief proposed, confirmed, including its (N-1)/2; the P(N)/2 is
what separates that from the N/2 of (T).

**Checks.** (E1) and (E2) are checked against an O(N^2) pair enumeration on Gaussian
random weights at N = 7, 50, 301, 1000 (agreement to 5 x 10^-12 absolute) and on Lambda at
N = 3000 against the pure-Python pair count (3 x 10^-11). (E3) is checked at the five
fresh cutoffs against T(N) from the FFT pair count: the residual is at most 1.2 x 10^-3 on
T of size 10^8 to 2 x 10^9, rounding. The T(N) used is the one `residue.py` recorded, to
10^-9 relative.

## 15. The auxiliary term is of order N exactly

The brief proposed P(N)/2 + X_chi(N) - H_chi(N) = O(N log^2 N) without proof. It holds,
it is elementary, and it is not sharp: the term is 0.3131 N + o(N).

- **P(N)/2** is O(N exp(-c sqrt(log N))) by the prime number theorem for the character;
  |P(N)| <= psi(N) < 2N by Chebyshev in any case.
- **X_chi(N)** is exact by (E2): log_3 N terms, each at most 2 max_{x <= N} |P(x)|, so
  O(N log N) by Chebyshev and O(N log N exp(-c sqrt(log N))) = o(N) by the same theorem.
- **H_chi(N)** = sum_k chi(k) S(k) (N - k) = integral_0^N M(x) dx, M(x) = sum_{k <= x} chi(k) S(k).
  With S(k) = 2 C_2 sum_{d | k, d odd squarefree} g(d), g(p) = 1/(p - 2), and
  chi(2dj) = -chi(d) chi(j), sum_{j <= y} chi(j) in {0, 1}:

      M(x) = -2 C_2 sum_{d odd squarefree, 3 not | d, d <= x/2} g(d) chi(d) 1[floor(x/2d) = 1 mod 3],

  so |M(x)| <= 2 C_2 sum_{d <= x/2} g(d) << log x by Mertens, and H_chi(N) << N log N with
  nothing beyond Chebyshev. Sharper: the Dirichlet series of chi(k) S(k) is
  D(s) = -2^{1-s} C_2 L(s, chi) F(s), F(s) = sum_d g(d) chi(d) d^{-s} = L(1 + s, chi) K(s)
  with K(s) an Euler product absolutely convergent for Re s > -1/2; D is analytic there,
  L(s, chi) is O(|t|^{3/4}) on Re s = -1/4 by the functional equation and convexity, and
  the Riesz-mean form H_chi(N) = (1/2 pi i) integral D(s) N^{s+1} / (s (s+1)) ds, shifted to
  Re s = -1/4, leaves the residue at s = 0 alone:

      H_chi(N) = c_H N + O(N^{3/4}),    c_H = D(0) = -(2 C_2 / 3) prod_{p > 3} (1 + chi(p)/(p - 2)) = -0.31306,

  using L(0, chi) = 1/3 and F(0) = prod_{p > 3} (1 + chi(p)/(p-2)) = 0.71133, the product
  taken in the order of the primes (it is L(1, chi) K(0), and both converge). Measured
  H_chi(N)/N is -0.3131, -0.3131, -0.3130, -0.3130, -0.3130 at the five cutoffs.
  `H_chi_by_divisor_expansion` evaluates the divisor form with no code in common with the
  singular-series sieve; the two agree to 10^-10 relative.

So P(N)/2 + X_chi(N) - H_chi(N) = -c_H N + O(N log N exp(-c sqrt(log N))): established,
unconditionally, as O(N), and it is Theta(N). Consequence for (T): its error cannot be
o(N) unless W(N) is c_H N + o(N), which the five cutoffs (W/N = -0.56, -0.11, -0.32,
-0.50, -0.86) do not show; the O(N^{1+eps}) in (T) is the right shape and O(N) would be
best possible.

## 16. What W is: the Wronskian of the two remainders

**(E4)** Partial summation of sum_n P(n-1) dR(n) against sum_n R(n) dP(n), with
dR(n) = Lambda(n) - 1 and dP(n) = Lambda(n) chi(n), gives the exact split

    W(N) = R(N) P(N) / 2 - J(N) + Q(N),    J(N) = sum_{m <= N} Lambda(m) chi(m) R(m),

    Q(N) = (1/2) [ sum_{m <= N} Lambda(m)^2 chi(m) - P(N) - (log 3) sum_{3^j <= N} P(3^j - 1)
                   + sum_{m <= N} Lambda(m) chi(m) psi_0(m - 1) ],

psi_0(x) the sum of Lambda over the powers of 3 up to x, so |Q(N)| <= 2 psi(N) log_3 N + 2N
= O(N log N) by Chebyshev. `split_W` evaluates the three pieces; the test checks
W - (RP/2 - J + Q) = 0 to rounding at N = 3000 and at the five cutoffs.

So W is, up to O(N log N), (1/2) integral (P dR - R dP): the Wronskian of R = psi - x and
P = psi(., chi). The symmetric combination integral P dR + integral R dP = R(N) P(N) -
sum Lambda^2 chi is a one-point quantity; the antisymmetric one is the pair content of
T(N), and it does not reduce to one-point counts. In (E4) it is J(N), the zeta remainder
sampled at the prime powers and weighted by the character:

    J(N) = sum_{p^a <= N} (log p) chi(p^a) [psi(p^a) - p^a].

**The reduction, in one line.** By (E3), (E4) and Section 15,

    T(N) - I(N) = R(N) P(N) / 2 - J(N) + O(N log N),                                      (E5)

so (T) is equivalent to J(N) - R(N) P(N) / 2 = O(N^{1+eps}) for every eps > 0. Under RH
for zeta and for L(s, chi) the product term is O(N log^4 N) on its own and (T) is the one
statement J(N) = O(N^{1+eps}): the values psi(p) - p at the primes p = 1 mod 3 and at the
primes p = 2 mod 3 agree, in the log-weighted mean, to relative accuracy N^{-1/2+eps}.

**Why a pointwise bound does not do it.** |J(N)| <= sum_m Lambda(m) |R(m)| <= psi(N)
max_{x <= N} |R(x)|, which is N^{3/2} log^2 N under RH: N^{1/2} short of the target. The
target needs the sign of chi(m) to cancel R(m) across the two classes, and nothing about
the size of R alone says that it does. Section 17 gets the cancellation from the zeros:
J is a double sum over pairs (rho, rho') of a zero of zeta and a zero of L(s, chi), each
term of modulus N^{Re rho + Re rho'}, and the count of pairs, weighted by the
coefficients, is a power of log N.

**Measured.** At the five cutoffs J/N = 0.61, 0.10, 0.33, 0.55, 0.83 and
J/(N log N) = 0.050, 0.007, 0.022, 0.036, 0.053; R(N) P(N)/(2N) = 0.03, -0.01, 0.00, 0.06,
-0.02; |Q|/N is at most 0.022. J is positive at all five cutoffs, recorded and not
explained. The data are consistent with W = O(N) and cannot distinguish that from
O(N log N); the bound of Section 17 is a power of log N above either.

## 17. Theorem A: the Wronskian is bounded by the zeros

Let Theta = sup Re rho over the non-trivial zeros of zeta(s) and Theta_chi = sup Re rho'
over those of L(s, chi), so 1/2 <= Theta, Theta_chi <= 1, equality to 1/2 being the two
Riemann hypotheses.

> **Theorem A.** W(N) << N^{Theta + Theta_chi} (log N)^4. Hence
> T(N) = I(N) + O(N^{Theta + Theta_chi} log^4 N), and under RH for zeta(s) and for
> L(s, chi), T(N) = I(N) + O(N log^4 N).

The unconditional form is empty when Theta + Theta_chi = 2 and is (T) with log^4 N for
N^eps when both suprema are 1/2. It is the difference-side analogue of Bhowmik,
Halupczok, Matsumoto and Suzuki's Theorem 1(1) (Section 19), whose error term is
x^{1 + B_q} for the same reason.

**Standard facts used** (Davenport, Multiplicative Number Theory, chapters 15 to 19;
Montgomery and Vaughan, Multiplicative Number Theory I, chapters 5, 10 and 12), all
unconditional:

- (F1) For x >= 2 and T >= 2, psi(x) = x - sum_{|gamma| <= T} x^rho / rho
  + O(x T^{-1} log^2(xT) + log x); and for 2 <= T <= x,
  psi(x, chi) = -sum_{|gamma'| <= T} x^{rho'} / rho' + O(x T^{-1} log^2 x + x^{1/4} log x)
  (Davenport ch. 17 and ch. 19; L(s, chi_3) has no real zero in (0, 1), and an exceptional
  zero would in any case join the sum with the same bounds).
- (F2) The number of zeros of zeta, or of L(s, chi), with ordinate in [t, t + 1] is
  O(log(|t| + 2)); hence sum_{0 < |gamma| <= T} 1/|gamma| << log^2 T for either function.
- (F3) For -1 <= sigma <= 2, L'/L(s, chi) = sum_{|t - gamma'| <= 1} 1/(s - rho')
  + O(log(|t| + 2)); for sigma <= -1/4 at distance >= 1/40 from the trivial zeros,
  L'/L(s, chi) << log(|s| + 2) by the functional equation. The same for zeta'/zeta.
- (F4) Perron's formula with remainder (Montgomery and Vaughan, Corollary 5.3).
- (F5) The classical zero-free region: no zero of zeta with Re rho > 1 - c/log(|gamma| + 2),
  hence, by rho -> 1 - conj(rho), none with Re rho < c/log(|gamma| + 2).

**Proof.** By (E4) and Section 15 it is enough to bound J(N) and R(N) P(N).

*Step 0, the product.* By (F1) with T = N and (F2), R(N) << N^Theta log^2 N and
P(N) << N^{Theta_chi} log^2 N, so R(N) P(N) << N^{Theta + Theta_chi} log^4 N.

*Step 1, R inside J through its zeros.* Insert (F1) with T = N into
J(N) = sum_m Lambda(m) chi(m) R(m); at a prime power m the formula is off by at most
Lambda(m), absorbed in the O(log m). Then

    J(N) = - sum_{|gamma| <= N} (1/rho) A_rho(N) + O(N log^2 N),
    A_rho(N) = sum_{m <= N} Lambda(m) chi(m) m^rho,

the error being sum_m Lambda(m) [(m/N) log^2 N + log m] << N log^2 N.

*Step 2, the twisted prime sum through the zeros of L.* Fix rho = beta + i gamma with
|gamma| <= N. The Dirichlet series of a_m = Lambda(m) chi(m) m^rho is -L'/L(w - rho, chi),
absolutely convergent for Re w > 1 + beta. Apply (F4) with c = 1 + beta + 1/log N and a
height T_rho in [2N, 2N + 1] chosen so that the two lines Im(w - rho) = +-T_rho - gamma
are at distance >= 1/(C log N) from every ordinate gamma' of L(s, chi); by (F2) the
excluded set has measure below 1/2 for C large, so such T_rho exists. Since
|a_m| <= Lambda(m) N^beta for m <= N and sum_m Lambda(m) m^{-1 - 1/log N} << log N, the
remainder in (F4) is << N^beta log^2 N. Move the contour to Re w = -delta, delta in
{1/8, 3/16} chosen so that |beta - 1 + delta| >= 1/40, which keeps the vertical line
1/40 away from the trivial zero of L(w - rho, chi) at w = rho - 1. The poles crossed are
w = rho + rho' for every zero rho' of L(s, chi) with |gamma + gamma'| < T_rho, with
residue -N^{rho + rho'} / (rho + rho') counted with multiplicity; w = 0, with residue
-L'/L(-rho, chi); and, when beta > 1 - delta, the trivial zero at w = rho - 1, with
residue -N^{rho - 1} / (rho - 1) = O(N^{beta - 1} / |gamma|). On the horizontal
segments Im(w - rho) is at least N in absolute value, so where -1 <= Re(w - rho) <= 2
(F3) gives O(log N) terms each << C log N by the choice of T_rho, and where
Re(w - rho) < -1 the point is at height >= N and so at distance >= 1/40 from every trivial
zero, where the functional-equation bound gives << log N; either way << log^2 N, and the
two segments contribute << log^2 N integral_{-delta}^{c} N^sigma d sigma / T_rho
<< N^beta log N. On the vertical segment Re(w - rho) = -delta - beta < 0 while every
non-trivial zero has Re rho' > 0, so |w - rho - rho'| >= delta for all of them and (F3)
gives << log N where it applies, the functional-equation bound << log N where
Re(w - rho) < -1; so it contributes << N^{-delta} log^2 N. The residue at 0 is
<< log^2 N by (F3) and (F5), since its terms 1/(-rho - rho') have
|rho + rho'| >= beta + beta' >= beta >> 1/log N.
Altogether

    A_rho(N) = - sum_{rho' : |gamma + gamma'| < T_rho} N^{rho + rho'} / (rho + rho') + O(N^beta log^2 N).

*Step 3, the double sum.* For fixed rho split the zeros rho' by j = floor(|gamma + gamma'|).
For j >= 1, |rho + rho'| >= j and there are O(log N) zeros in the interval (all have
|gamma'| <= 3N + 1), so these contribute << sum_{j <= 2N + 1} log N / j << log^2 N to
sum_{rho'} 1/|rho + rho'|. For j = 0, |rho + rho'| >= beta + beta' >= beta >> 1/log N by
(F5) and there are O(log N) such rho': again << log^2 N. With
|N^{rho + rho'}| <= N^{Theta + Theta_chi} and (F2),

    sum_{|gamma| <= N} (1/|rho|) |sum_{rho'} N^{rho + rho'} / (rho + rho')|
        << N^{Theta + Theta_chi} log^2 N sum_{|gamma| <= N} 1/|gamma| << N^{Theta + Theta_chi} log^4 N.

The remainders of Step 2 add sum_rho N^beta log^2 N / |rho| << N^Theta log^4 N. With
Step 1, J(N) << N^{Theta + Theta_chi} log^4 N + N log^2 N, and Theta + Theta_chi >= 1
absorbs the second term. With Step 0 and (E4), W(N) << N^{Theta + Theta_chi} log^4 N;
with (E3) and Section 15, so is T(N) - I(N). QED.

**Where each hypothesis enters, and where the cancellation comes from.** No Riemann
hypothesis is used in the argument; the two suprema enter only through
|N^{rho + rho'}| = N^{beta + beta'} in Step 3, and the zero-free region (F5) only to keep
the near-diagonal denominators |rho + rho'| away from 0 (under RH they are at least 1).
The cancellation that a pointwise bound on R cannot see is Step 2: the character-twisted
prime sum A_rho(N), which is N^{1 + beta} pointwise, is N^{beta + beta'} per zero of
L(s, chi) once its own explicit formula is used, and Step 3 counts the pairs. The N^{1/2}
that Section 16 said was missing is N^{Theta_chi} with Theta_chi = 1/2. Nothing is
imported: under the two hypotheses every term has modulus N and their weighted number
is log^4 N.

**What the bound is not.** It is a bound and not an asymptotic. The double sum has no
non-oscillating term: one would need a zero of zeta and a zero of L(s, chi) with opposite
ordinates, which is not known to occur and is expected never to. The exponent 4 is what
counting gives. On the sum side the analogous exponent went from Fujii's (x log x)^{4/3}
to x log^5 x (Bhowmik and Schlage-Puchta, Gallagher's lemma with Cramer's and
Saffari-Vaughan's mean squares under RH) and to x log^3 x (Languasco and Zaccagnini,
the exponential sum with weight e^{-n/N} and their Lemma 1), and that route should
transfer: the pair part of T(N) is integral_0^1 |S(alpha)|^2 conj(X(alpha)) d alpha with
X(alpha) = sum_{k <= N} chi(k) e(k alpha), peaked at alpha = 1/3 and 2/3 rather than at
0, and the cross term Im(S' conj(S_chi)) there is the Wronskian in Fourier form. Not
carried out; the exponent is not what (T) is about.

## 18. Theorem B: the lower bound by the zeros of L(s, chi)

This is the payoff Section 12 named: a lower bound on E(N), not the upper bound the
original RH strategy would need.

> **Theorem B.** For every eps > 0, E(N) = Omega(N^{1 + 2 Theta_chi - eps}). With Chou,
> Haag, Huryn and Ledoan's Theorem 2, E(N) = Omega(N^{1 + 2 max(Theta, Theta_chi) - eps}).

**Proof.** E(N) = 2 sum_{k <= N} e(N, k)^2 >= 2 T(N)^2 / N by Cauchy-Schwarz, since
sum_{k <= N} chi(k)^2 <= N. If Theta_chi <= Theta the claim is their Theorem 2,
E(N) = Omega(N^{1 + 2 Theta - eps}), cited and not re-derived here; it is the same
Cauchy-Schwarz step applied to the unweighted k-sum, whose main term is
N (psi(N) - N) by their Section 3. Otherwise Theta < Theta_chi <= 1. The Mellin
transform of I(x) = sum_{m <= x} Lambda(m) chi(m) (x/2 - m) is, for Re s > 1,

    integral_1^infinity I(x) x^{-s-2} dx = -(L'/L)(s, chi) (1 - s) / (2 s (s + 1)),

which has a pole at every zero rho' of L(s, chi), the factor (1 - rho')/(2 rho' (rho' + 1))
being non-zero. If I(x) were O(x^{1 + Theta_chi - eps'}) the left side would converge
absolutely and be analytic in Re s > Theta_chi - eps', where the right side has a pole;
so I(x) = Omega(x^{1 + Theta_chi - eps'}) for every eps' > 0. Only absolute convergence
implies analyticity is used, so no sign condition on the coefficients is needed; this is
the direction of Landau's oscillation theorem that does not require one (Ingham, ch. V;
Montgomery-Vaughan, section 15.1). Put eps' = min(eps, 1 - Theta)/2. Along integers
N with |I(N)| >= N^{1 + Theta_chi - eps'} (I(x) - I(floor x) = O(P(x)) is negligible),
(E3), Section 15 and Theorem A give
|T(N)| >= N^{1 + Theta_chi - eps'} - O(N^{Theta + Theta_chi} log^4 N + N log N)
>= (1/2) N^{1 + Theta_chi - eps'}, because Theta + Theta_chi < 1 + Theta_chi - eps'.
Hence E(N) >= (1/2) N^{1 + 2 Theta_chi - 2 eps'} >= (1/2) N^{1 + 2 Theta_chi - eps}. QED.

**What it says and does not say.** Theorem B is unconditional, and it is informative only
if RH fails for L(s, chi): with Theta_chi = 1/2 it gives Omega(N^{2 - eps}), below the
Omega(N^2 (log log log N)^2) their Theorem 2 gets unconditionally from Littlewood's
oscillation, and below the N^2 log^2 N their conjecture predicts. That is the shape of
their Theorem 2, informative only if RH fails for zeta. The statement is: the pair error
is bounded below by the zeros of L(s, chi_3) as it is by those of zeta, through the same
mechanism, the k-mean of e weighted by a character in place of 1. It is not evidence about
RH (docs/08) and it says nothing about the upper bound E(N) = O(N^2 log^2 N), which is the
direction the original objective needed. Whether the same holds for the characters of
every modulus is a thread, not pursued: (E0) is special to modulus 3; for a general q the
pair part of sum_k chi(k) e(N, k) is a bilinear antisymmetric form in the psi(x, psi_j)
over the characters psi_j mod q, to which Step 2 applies pairwise, but its main term
would have to be derived afresh.

## 19. Placement: known, consequence, or additional

- **Is (T) a known estimate?** Not in what was read. The sum-side average
  sum_{n <= N} r_2(n), r_2(n) = sum_{a + b = n} Lambda(a) Lambda(b), has this structure:
  main term N^2/2, zero sum -2 sum_rho N^{rho + 1} / (rho (rho + 1)), and an error term
  O((N log N)^{4/3}) under RH (Fujii, Acta Arith. 58 (1991) 173-179; Proc. Japan Acad. 67
  (1991) 248-252 and 278-283), O(N log^5 N) under RH with Omega(N log log N)
  unconditionally (Bhowmik and Schlage-Puchta, Nagoya Math. J. 200 (2010) 27-33),
  O(N log^3 N) under RH (Languasco and Zaccagnini, Proc. AMS 140 (2012) 795-804,
  Theorem 1, from Theorem 2 there, the e^{-n/N}-weighted sum, and Languasco-Perelli's
  integral_{-xi}^{xi} |S(alpha) - 1/z|^2 << N xi log^2 N under RH; reproved by Goldston
  and Yang, arXiv:1601.06902, Theorem 1, by Bhowmik and Schlage-Puchta's method with an
  average over the length), and O(N) for the Cesaro average of order 1 under RH (Goldston
  and Yang, Theorem 2). Granville (Funct. Approx. 37 (2007) 159-173; corrigendum 38 (2008)
  235-237) showed that sum_{n <= x} (G(n) - J(n)) << x^{3/2 + o(1)} is equivalent to RH. All
  of these are the sum side a + b = n averaged over n; none is the difference side, and none
  carries a character on the difference. The sum-side quadratic term
  sum_{rho, rho'} N^{rho + rho'} Gamma(rho) Gamma(rho') / Gamma(rho + rho' + 1)
  (Languasco and Zaccagnini, Forum Math. 27 (2015) 1945-1960, unconditional with a Cesaro
  weight of order k > 1/2) carries Gamma factors; the difference-side term of Step 3
  carries 1/(rho (rho + rho')) and no Gamma factor, which is why the near-coincidences
  gamma' = -gamma are the terms to control and why (F5) is needed unconditionally.
- **Primes in progressions.** Bhowmik, Halupczok, Matsumoto and Suzuki (Mathematika 65
  (2019) 57-97, arXiv:1704.06103) treat S(x; q, a, b) = sum_{n <= x} sum_{l + m = n,
  l = a, m = b (q)} Lambda(l) Lambda(m): Theorem 1(1), S = x^2 / (2 phi(q)^2) + O(x^{1 + B_q})
  unconditionally with B_q the supremum of Re over the zeros of every L(s, chi) mod q;
  Theorem 2, the explicit formula with those zeros and error O(x^{2 B_q^*} (log qx)^5);
  Theorem 1(2) and Theorem 3, the converses under their Distinct Zero Conjecture. Their
  double sums pair zeros of two different L-functions and carry Gamma factors. Theorem A
  is the difference-side counterpart for the pair (zeta, L(s, chi_3)), its exponent
  Theta + Theta_chi playing the part of 1 + B_q; Theorem B runs their Theorem 3 direction
  the other way (there an error term bounds the zeros, here the zeros bound the error from
  below). Suzuki (Int. J. Number Theory 13 (2017), arXiv:1504.01967) is the earlier mean
  value in progressions. Read: statements, introductions, and the Section 2 lemmas of
  BHMS; the whole of Goldston and Yang; Sections 1 and 2 of Languasco and Zaccagnini.
- **Is (T) a consequence of known estimates?** Under RH for zeta and for L(s, chi_3), yes,
  by Theorem A, and the proof uses nothing beyond (F1) to (F5): no cancellation is
  assumed beyond |N^{rho + rho'}| = N. Unconditionally, no: what is known about Theta and
  Theta_chi (zero-density estimates and the zero-free region) does not give
  Theta + Theta_chi < 2, and Theorem A is then empty. On this route (T) is exactly as
  hard as RH for the two functions. Whether (T) implies anything back about the zeros
  was not investigated; Granville's converse on the sum side rests on the main term N^2/2
  being smooth, and the difference-side main term I(N) is itself a zero sum.
- **What is additional.** Nothing, conditionally. The one estimate the whole of (T)
  rests on is J(N) = sum_{m <= N} Lambda(m) chi(m) (psi(m) - m) = O(N^{1+eps}) of
  Section 16, a double sum over the zeros of zeta and of L(s, chi_3) with coefficient
  1/(rho (rho + rho')).

**Provenance and status, kept apart.** (E0) to (E5) are identities, checked as such.
Section 15 is elementary and unconditional. Theorem A is proved under no hypothesis and
its interesting case is conditional on two Riemann hypotheses; Theorem B is
unconditional. All are original to this hunt in the sense of CLAUDE.md, produced here
from the record; none is claimed novel: the search covered the papers named above, read
in the parts stated, and a web search of 2026-09-06 for a character-weighted
difference-side pair sum, which returned nothing relevant. The proofs are written out
above with the standard lemmas cited and are not kernel-checked, so on the certainty
ladder they stand as written proofs on cited lemmas, below anything `rigor.py` or the
Lean arm can say; a reader walking (F1) to (F5) against Davenport and Montgomery-Vaughan
is the next step. Relevance to the original objective: none for the upper bound.
Section 12's route was to a lower bound, and Theorem B is that lower bound.
