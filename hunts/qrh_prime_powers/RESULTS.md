# Primes between consecutive ninth powers, given the 7/8 half-plane

**Status: candidate, pending external review.** Every statement below is
conditional on OpenAI's zero-free half-plane and is "proved, given OpenAI's
Theorem 1.1" in the following sense: the analytic steps are ordinary written
proofs that nobody outside this hunt has reviewed; every numerical inequality
they need is decided by Arb ball arithmetic (python-flint 0.9.0, 256 bits,
certain comparisons only), so the numerics are enclosure-carrying (hardened);
the small cases are explicit primes with Pratt certificates checked by
integer arithmetic. The composite grade is that of the weakest step: the
unreviewed written argument here, on top of OpenAI's argument, which no human
has reviewed. Nothing here is kernel-checked.

## 0. Statements

Write QRH(theta) for: zeta(s) is not zero for Re s > theta.

**Theorem 1 (given QRH(7/8)).** For every integer n >= 1 there is a prime p
with n^9 < p < (n+1)^9.

Quantitatively, for n >= 10, with x = n^9 and h = (n+1)^9 - n^9,

    sum_{x < p < x+h} log p  >=  (4h/9) (1 - E_n) - P_n,
    E_n + (9/4) P_n / h  <=  0.17473,

and the proof also closes with no verified height of RH at all (every zero
treated as possibly at real part 7/8), where E_n + (9/4) P_n/h <= 0.69730.

**Theorem 1' (given QRH(11/12) only).** For every integer n >= 1 there is a
prime between n^13 and (n+1)^13.

**Theorem 2 (given QRH(7/8)).** For every real x >= e^8 there is a prime in
(x, x + (1/2) x^(7/8) log x].

**Theorem 3 (given QRH(7/8)).** For every real x >= e^10,

    |psi(x) - x|  <  x^(7/8) (log x)^2 / (128 pi).

The constant 1/(128 pi) = (1/8)^2/(2 pi) is the asymptotic constant of the
method, approached from below.

**Proposition T (threshold control).** The same chain, run with abscissa
theta, closes at k = floor(1/(1-theta)) + 1 and fails at k - 1:

| theta | closes at | margin (with H0) | k - 1 fails from | E at log n = 1000, k - 1 |
| --- | --- | --- | --- | --- |
| 7/8 | k = 9 | 0.8253 | log n = 28.425 | 344.9 |
| 11/12 | k = 13 | 0.5662 | log n = 29.033 | 229.9 |
| 15/16 (weakened control) | k = 17 | 0.3609 | log n = 29.465 | 172.3 |

"Fails" means the enclosed upper bound for E plus the prime-power share is
certainly at least 1 at every sampled log n from that point to 1000 (step
0.5: 1944 of 1944 samples for k = 8, 1941 of 1941 for k = 16), and it grows
linearly in log n with slope J1/(k pi) (J1 = 8.69185..., section 5): a failure
of this chain, not a statement about primes.

**What this improves.** The unconditional record for "a prime between n^k and
(n+1)^k for every n >= 1" is k = 86 (E. S. Lee, arXiv:2602.14340v2, 3 Mar 2026,
Theorem 1.2), after k = 90 (M. Cully-Hugill and D. R. Johnston, Funct. Approx.
Comment. Math. 73 (2025) 223-242, arXiv:2402.04272v3, Theorem 1.4), k = 140
(Cully-Hugill and Johnston, Int. J. Number Theory 19 (2023) 1205-1228,
Theorem 1.3, as reported in arXiv:2508.18786) and k = 155 (Cully-Hugill,
J. Number Theory 247 (2023) 100-117). Given QRH(7/8) the exponent drops from
86 to 9; given only the October 5 theorem QRH(11/12), to 13. Under the full
RH much more is known: Chamberland and Straub (arXiv:2602.22502, Theorem 1.2)
observe that Carneiro, Milinovich and Soundararajan's gap bound gives primes
in [x^(2+delta), (x+1)^(2+delta)] for all real x >= 1 when delta >= 1/4.

## 1. Inputs, cited from located sources

- **(I1) The half-plane.** OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free
  Half-Plane Re s > 7/8*, OpenAI Math Release preprint dated 30 September
  2026, Theorem 1.1 (every finite-order Hecke L-function over Q(sqrt(-3)),
  hence zeta, has no zero in Re s > 7/8). The lab's Lean statement is
  `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`. **Citation note for the
  lead:** the brief attributes the 7/8 statement to "The Quasi-Riemann
  Hypothesis (October 5, 2026), Theorem 1.1". In the October 5 text in hand,
  Theorem 1.1 is the weaker half-plane Re s > 11/12, and that paper cites the
  7/8 result as its reference [36], the 30 September preprint above. Theorem 1
  uses the 7/8 statement; Theorem 1' uses only the October 5 statement.
  Use made of (I1): every nontrivial zero rho = beta + i gamma has
  beta <= 7/8 (0 < beta < 1 is classical). Nothing else.
- **(I2) Verified height (optional).** D. Platt and T. Trudgian, *The Riemann
  hypothesis is true up to 3 * 10^12*, Bull. London Math. Soc. 53 (2021)
  792-797, arXiv:2004.09765, Theorem 1: every zero with 0 < gamma <= H0 =
  3 000 175 332 800 has beta = 1/2. Theorems 1 and 1' also hold with H0
  replaced by 0 (sections 6.6 and 7), so for them (I2) only improves the
  margins. The covers for Theorems 2 and 3 as recorded use H0 (the tail of
  Theorem 3 does not).
- **(I3) Zero counting.** For T >= e,
  |N(T) - (T/2pi) log(T/(2 pi e))| <= C1 log T + C2 log log T + C3, with
  (C1, C2, C3) = (0.11200, 0.12567, 3.77417) by C. Bellotti and P.-J. Wong,
  arXiv:2412.15470v2 (7 Jul 2025), Theorem 1.1 (second estimate), and with
  (0.137, 0.443, 2.463) by Rosser (1941) as tabulated in the same paper's
  Table 1. We use the coefficientwise maximum (0.137, 0.443, 3.77417), which
  is valid as soon as either source is. N(T) counts zeros with 0 < gamma <= T
  with multiplicity.
- **(I4) Explicit formula, qualitative.** H. L. Montgomery and R. C. Vaughan,
  *Multiplicative Number Theory I*, Cambridge 2007, Theorem 12.5: for fixed
  c > 1, x >= c, T >= 2, psi_0(x) = x - sum_{|gamma| <= T} x^rho/rho - log 2 pi
  - (1/2) log(1 - x^-2) + R(x, T) with R(x, T) << (log x) min(1, x/(T <x>)) +
  (x/T)(log xT)^2, where <x> is the distance from x to the nearest prime
  power other than x. Only used for a dominated-convergence limit; no
  constant from it enters any bound.
- **(I5) For Theorem 3 only:** no zero has 0 < gamma <= 14. Checked by Arb's
  zero count, `arb(14).zeta_nzeros() == 0` (and `== 1` at 15), matching the
  first tabulated ordinate 14.1347.
- Classical facts used: zeros come in conjugate pairs; zeta(sigma) is not
  zero for real 0 < sigma < 1 (the alternating eta series is positive there),
  so no nontrivial zero has gamma = 0; the trivial zeros are -2, -4, ...

Not used: any prime-gap table, any explicit short-interval theorem, any
zero-free region of de la Vallee Poussin type, any zero-density estimate.

## 2. The weight and its Mellin transform

Let phi be the quadratic B-spline on [0, 1]:

    phi(u) = (27/2) u^2               on [0, 1/3],
             -27 u^2 + 27 u - 9/2     on [1/3, 2/3],
             (27/2) (1 - u)^2         on [2/3, 1],      and 0 elsewhere.

Exact facts (checked symbolically in `test_weight_constants_are_exact`):
integral of phi = 1; phi is C^1 on R; max phi = phi(1/2) = 9/4;
||phi'||_1 = 9/2; phi'' = 27, -54, 27 on the three thirds, so phi'' jumps by
27, -81, 81, -27 at 0, 1/3, 2/3, 1 (total variation 216).

For x > 1 and h > 0 put w(t) = phi((t - x)/h), eta = h/x, a = 1 + 1/eta, and
W(s) = integral w(t) t^(s-1) dt (entire). Three integrations by parts give

    W(s) = - (1/(h^2 s (s+1)(s+2))) sum_{i=0..3} J_i (x + i h/3)^(s+2),
    (J_0, J_1, J_2, J_3) = (27, -81, 81, -27),                          (2.1)

and W(1) = h.

**Lemma 2.1 (envelope).** For rho = beta + i gamma with 0 < beta <= 1 and
gamma != 0, |W(rho)| <= h x^(beta-1) g(|gamma|/a), where

    g(u) = min(1, (9/2)/u, 216/u^3).

*Proof.* (m = 0) |W| <= integral w t^(beta-1) <= x^(beta-1) integral w =
h x^(beta-1), since t >= x on the support and beta - 1 <= 0.
(m = 1) W(rho) = -(1/rho) integral w'(t) t^rho dt, so
|W| <= (x+h)^beta ||w'||_1/|gamma| = (x+h)^beta (9/2)/|gamma|. As
(x+h)^beta <= x^beta (1+eta) and x^beta = h x^(beta-1)/eta, this is
h x^(beta-1) (9/2) a/|gamma|.
(m = 3) By (2.1), |W| <= 216 (x+h)^(beta+2)/(h^2 |rho(rho+1)(rho+2)|) <=
216 x^(beta+2)(1+eta)^3/(h^2 |gamma|^3) = h x^(beta-1) 216 a^3/|gamma|^3.
The minimum of the three is the claim. (The m = 2 bound 36 a^2/gamma^2 is
never below g; checked on a grid in the same test.) QED

## 3. The explicit formula for the weight

**Lemma 3.1.** For x >= 2 and h > 0,

    sum_n Lambda(n) w(n) = h - sum_rho W(rho) - tau,
    tau = integral w(t) dt/(t (t^2 - 1)),   0 <= tau <= h/(x (x^2 - 1)),

the sum running over nontrivial zeros with multiplicity and converging
absolutely.

*Proof.* Since w is C^1 with compact support in (x, x+h),
sum_n Lambda(n) w(n) = integral w dpsi = -integral psi(t) w'(t) dt, and psi
may be replaced by psi_0 (they differ on a null set). Insert (I4) for t in
[x, x+h]: -integral t w'(t) dt = integral w = h; for each zero,
integral (t^rho/rho) w'(t) dt = -W(rho), contributing -W(rho); the constant
log 2 pi integrates against w' to 0; and
(1/2) integral log(1 - t^-2) w'(t) dt = -integral w(t)/(t(t^2-1)) dt = -tau.
The remainder: |R(t, T)| is bounded uniformly for t in [x, x+h] and T >= 2
(by O(log(x+h)) plus O((x+h) log^2((x+h)T)/T)) and tends to 0 for every t as
T -> infinity, because <t> > 0; w' is bounded, so the integral of R w' tends
to 0 by dominated convergence. Hence the limit over T of the truncated zero
sum exists and the identity holds with it; by Lemma 2.1 (m = 3),
|W(rho)| << |gamma|^-3, so the zero sum converges absolutely and equals the
limit. Finally 0 <= tau <= (integral w)/(x(x^2-1)). QED

*Independent check of the normalisation* (`test_explicit_formula_normalization_against_tabulated_zeros`):
x = h = 1000. Direct prime-power sum 1014.638796; h - (sum over the 1000
tabulated zeros of 2 Re W(1/2 + i gamma)) - tau = 1014.638956; difference
-1.6e-4 (the omitted zeros above gamma_1000 contribute at most about 0.02).
The zero sum itself is -14.639, so a flipped sign misses by 29.

## 4. From the formula to primes

**Proposition 4.1.** Assume every zero has 0 < beta <= theta, theta in
[1/2, 1), and let H >= 0 be such that every zero with 0 < gamma <= H has
beta = 1/2 (H = 0 is allowed and assumes nothing). For x >= 2, h > 0,

    sum_{x < p < x+h} log p >= (4h/9)(1 - E) - P,
    E = 2 x^(-1/2) S_H^low(a) + 2 x^(theta-1) S_H^high(a) + 1/(x(x^2-1)),
    S_H^low(a) = sum_{0<gamma<=H} g(gamma/a),  S_H^high(a) = sum_{gamma>H} g(gamma/a),
    P <= (pi^2/6 - 1) h x^(-1/2) l + l log(l/log 2),   l = log(x+h).

In particular there is a prime in (x, x+h) whenever the **margin**
1 - E - (9/4) P/h is positive.

*Proof.* By Lemma 3.1 and Lemma 2.1, using conjugate symmetry and
x^(beta-1) <= x^(-1/2) below H, x^(beta-1) <= x^(theta-1) above:
sum_n Lambda(n) w(n) >= h - sum_rho |W(rho)| - tau >= h(1 - E). Since
0 <= w <= 9/4 and w vanishes outside (x, x+h),
sum_{x<n<x+h} Lambda(n) >= (4/9) h (1 - E). The proper prime powers p^j
(j >= 2) in (x, x+h) contribute log p <= l/j each; there are at most
(x+h)^(1/j) - x^(1/j) + 1 <= h/(j x^(1-1/j)) + 1 integers m with m^j in
(x, x+h), and only j <= J = floor(log_2(x+h)) occur. So
P <= h l x^(-1/2) sum_{j>=2} 1/j^2 + l sum_{j=2..J} 1/j <=
(pi^2/6 - 1) h x^(-1/2) l + l log J, and log J <= log(l/log 2). QED

## 5. Sums over zeros in closed form

For a >= 1 put G(t) = g(t/a), t1 = (9/2) a, t2 = sqrt(48) a. Then G = 1 on
(0, t1], G = (9/2) a/t on [t1, t2], G = 216 a^3/t^3 on [t2, infinity); G is
continuous and nonincreasing, with -G' = (9/2) a t^-2 on (t1, t2) and
648 a^3 t^-4 beyond. Let N_+(t), N_-(t) = (t/2pi) log(t/(2 pi e)) +- R(t),
R(t) = C1 log t + C2 log log t + C3 (I3).

**Lemma 5.1.** For H >= e,

    S_H^low(a)  <= G(H) N_+(H) + integral_{t1}^{H} N_+(t) (-G'(t)) dt    (H > t1; else <= N_+(H)),
    S_H^high(a) <= -G(H) N_-(H) + integral_{max(H, t1)}^{infinity} N_+(t) (-G'(t)) dt,
    S_0^high(a) <= integral_{t1}^{infinity} N_+(t) (-G'(t)) dt.

*Proof.* Riemann-Stieltjes: sum_{0<gamma<=H} G(gamma) = G(H) N(H) +
integral_0^H N(t)(-dG(t)), and -dG >= 0 is supported on [t1, infinity) with
t1 >= 9/2 > e, where N <= N_+. Similarly
sum_{H<gamma<=T} G = G(T)N(T) - G(H)N(H) + integral_H^T N (-dG), with
G(T)N(T) -> 0 (G is O(T^-3)) and N(H) >= N_-(H). For H = 0, N(0) = 0. QED

The integrals are elementary once log log t is replaced, on each piece
[A, B], by its tangent line at A, log log A + (log t - log A)/log A, which
lies above it (concavity of log): every piece reduces to
integral t^-p (log t)^j dt with j in {0, 1}, evaluated exactly in Arb
(`bound.int_N_plus`). Checked against 30-digit mpmath quadrature of the same
integrand to relative 1e-15, and shown to dominate the quadrature with the
true log log t (`test_closed_form_integrals_against_quadrature`). As a sanity
check, the bound for S^low and for S_0^high both exceed the actual partial
sum over the first 1000 zeros for a in {1, 3, 10, 40}.

Constants of g used below (exact closed forms, Arb values):

    J1  = integral u (-g'(u)) du = integral_0^infty g = (9/2) log(sqrt(48)/(9/2)) + 324/48 = 8.6918539890...
    J1L = integral u log u (-g'(u)) du = 19.7799795395...
    JL  = integral log u (-g'(u)) du = 2.0710646948...

## 6. Proof of Theorem 1

Throughout, k = 9, theta = 7/8, x = n^9, h = (n+1)^9 - n^9,
eta = (1 + 1/n)^9 - 1, a = 1 + 1/eta.

### 6.1 Small n

For n = 1, ..., 9 the least prime above n^9 lies below (n+1)^9:

| n | prime | n | prime |
| --- | --- | --- | --- |
| 1 | 2 | 6 | 10077721 |
| 2 | 521 | 7 | 40353611 |
| 3 | 19687 | 8 | 134217757 |
| 4 | 262147 | 9 | 387420499 |
| 5 | 1953151 | | |

Each carries a Pratt certificate (`witnesses_k9.json`), verified by
`pratt.check` with integer arithmetic only (Lucas' theorem: a base of order
p - 1 with p - 1 fully factored, recursively). The checker rejects a planted
composite, a planted wrong factorisation and a prime outside the interval.

### 6.2 Monotonicity on an interval

**Lemma 6.2.** If n lies in [n_a, n_b], then E_n and (9/4)P_n/h_n are at
most the values of the expressions of Proposition 4.1 with x^(-1/2) and
x^(theta-1) evaluated at x_a = n_a^9, with a replaced by
a* = 1 + 1/eta(n_b), with l replaced by 9 log(n_b + 1), and with 1/h replaced
by 1/h(n_a).

*Proof.* x and h increase with n and eta decreases, so a <= a*; g is
nonincreasing, so g(gamma/a) <= g(gamma/a*) for every zero, and the
Lemma 5.1 bounds are then applied to the function g(t/a*). The other
replacements are monotone in the stated direction. QED

### 6.3 The cover

Parametrise by L = log n. Starting from L_s = 2414435/2^20 < log 10 (checked
in Arb) and ending at 100, the range is split into 1564 intervals of width
1/16; on each, the Lemma 6.2 margin is certainly positive in Arb
(`verify.cover`). The weakest interval is log n in
[32626531/2^20, 32692067/2^20] = [31.115, 31.178], where E <= 0.17473 and
the margin is >= 0.82527, so E_n + (9/4)P_n/h <= 0.17473 for every n >= 10.
Boundary margins (point enclosures):

| boundary | log n | E (upper) | prime-power share | margin |
| --- | --- | --- | --- | --- |
| witnesses to analytic | log 10 | 2.87e-4 | 9.90e-4 | 0.99872 |
| height transition, a* (9/2) = H0 | 29.4228 | 0.10303 | 1.2e-55 | 0.89697 |
| analytic to tail | 100 | 1.11e-4 | 4.8e-193 | 0.99989 |

The peak sits just above the height transition: below it every zero that
matters has beta = 1/2; above it the zeros between H0 and about a are
counted at real part 7/8 with the full N(T) density, and the factor
x^(-1/8) is not yet large enough to make that cheap.

### 6.4 The tail n >= e^100

**Lemma 6.4.** Let k > 1/(1 - theta), d = k(1-theta) - 1 > 0, and
L_inf = log N with log(N/k) > log(2 pi e) + 1. For every n >= N,
E_n + (9/4)P_n/h_n <= sum_i c_i n^(-e_i) (log n)^(j_i) (log log n)^(l_i)
with the twelve monomials of `bound.kth_power_tail`, namely

    (J1/pi) n^-d log n,  (B+/pi) n^-d,  2C1 n^-d' log n,  2C2 n^-d' log log n,  2K0 n^-d',
    2 N_+(H0) n^(-k/2),  2 n^(-3k),  (9/4)(pi^2/6-1) k n^(-k/2) (log n + 1),
    (9/4)(k/log 2) n^(-(k-1)) (log^2 n + 2 log n + 1),

where d' = k(1-theta), B+ = max(0, J1L - J1 log(2 pi e)),
K0 = C1 JL + C2 JL/log(N/k) + C3.

*Proof.* Bernoulli gives eta >= k/n, so a <= a* := 1 + n/k, and
S^high <= S_0^high(a*) <= V(a*) with, by Lemma 5.1 and the substitution
t = a* u,

    V(a) = integral_{9/2}^{infty} N_+(a u) (-g'(u)) du
         <= (a/2pi)((log a - log(2 pi e)) J1 + J1L) + C1 (log a + JL)
            + C2 (log log a + JL/log a) + C3,

using integral (-g') = g(9/2) = 1 and log log(au) <= log log a + log u/log a
for u >= 1. With a* <= n, log a* <= log n, 1/log a* <= 1/log(N/k), and
(log a* - log 2 pi e) J1 + J1L >= 0 (from the hypothesis on N), the term
2 x^(theta-1) V(a*) is bounded by the first five monomials. S^low <= N(H0) <=
N_+(H0); tau <= 2 x^-3; and in P/h, log(x+h) = k log(n+1) <= k(log n + 1),
log(log_2(x+h)) <= log(x+h)/log 2 and h >= k n^(k-1). QED

Each monomial c n^-d_i (log n)^j (log log n)^l decreases for log n >= L
when j/L + l/(L log L) < d_i, which
holds at L = 100 for every monomial (checked in Arb), so the sum is
nonincreasing on [e^100, infinity) and bounded by its value at n = e^100:
**0.0010311** (Arb upper bound) < 1.

### 6.5 Conclusion

Sections 6.1, 6.3 and 6.4 cover every n >= 1. For n >= 10 the margin is
positive, so by Proposition 4.1 the interval (n^9, (n+1)^9) contains a
prime. QED (given (I1), (I3), (I4); (I2) only through the margins.)

### 6.6 Without any verified height

With H = 0 in Proposition 4.1 (every zero treated as possibly at real part
7/8), the same 1564 intervals all close; the weakest is the first one,
log n in [L_s, L_s + 1/16], with E <= 0.69628 and margin >= 0.30270
(so E_n + (9/4)P_n/h <= 0.69730); the tail is unchanged. So Theorem 1 needs (I1), (I3), (I4) and
nine Pratt certificates, and not the Platt-Trudgian computation.

## 7. Theorem 1' and the threshold controls

The chain of section 6 is parametrised by (k, theta) and rerun unchanged
(`verify.chain`), with L_inf = 200 for the two weaker abscissae and Pratt
witnesses for n <= 9 (`witnesses_k13.json`, `witnesses_k17.json`).

- **theta = 11/12, k = 13 (Theorem 1').** 3164 intervals, weakest margin
  0.56624 (log n near 32.05); without verified height 0.22529; tail bound
  3.2e-5. k = 12 fails from log n = 29.033 on.
- **theta = 15/16, k = 17 (weakened control).** 3164 intervals, weakest margin
  0.36092 at log n near 32.80; boundary margins 0.99999979 at n = 10, 0.67031
  at the height transition (log n = 30.0588), 0.99988 at log n = 200; tail
  bound 0.0020621. k = 16 fails from log n = 29.465 on.
- **theta = 7/8, k = 8.** Fails from log n = 28.425 on (bisected to about
  1e-13 in log n between the samples 28.40 and 28.45).

Where k - 1 fails, and why: always in the analytic range near the height
transition (log(k H0/(9/2)) = 29.30 for k = 8), and always in the high-zero
term. When k(1 - theta) = 1
the factor x^(theta-1) exactly cancels the 1/eta growth of the zero count
up to height a, and what remains is
2 x^(theta-1) (a/2pi) J1 log a ~ (J1/(k pi)) log n, unbounded. The tail
lemma correspondingly refuses (its leading exponent d is 0). The measured
slopes of E at log n = 500 to 1000 agree with J1/(k pi) to 1e-3 (test).

The prediction "least k = floor(1/(1 - theta)) + 1" is 9, 13, 17 for the
three abscissae, and the chain realises exactly these values. The weakened
abscissa moved the threshold as predicted.

## 8. Proof of Theorem 2

Take theta = 7/8, c = 1/2, h = c x^(7/8) log x, parametrised by L = log x.
Then eta = c x^(-1/8) L decreases for L >= 8 and h increases, so Lemma 6.2
holds verbatim with L in place of log n (`bound.PowerLog`).

*Cover.* L in [8, 400], 6272 intervals of width 1/16, every margin certainly
positive; weakest margin 0.38461 on the last interval [6399/16, 400].
Boundary margins: 0.58867 at L = 8 (E <= 0.16300, share <= 0.24833), 0.38940
at L = 400.

**Lemma 8.2 (tail).** For L = log x >= 400,
E + (9/4)P/h <= J1 (1-theta)/(pi c) + max(0, Y(400))/(pi c 400) + (decreasing
monomials at L = 400) = 0.6916758 (Arb upper bound), where
Y(L) = J1 (log 2 - log(2 pi e) - log(cL)) + J1L.

*Proof.* Here a = 1 + x^(1/8)/(cL) and x^(-1/8) a = x^(-1/8) + 1/(cL). With
log a <= (1/8) L - log(cL) + log 2 (as x^(1/8)/(cL) >= 1), the main part of
2 x^(-1/8) V(a) is at most
(1/pi)(x^(-1/8) + 1/(cL)) (J1 L/8 + Y(L)) = J1/(8 pi c) + Y(L)/(pi c L) +
(x^(-1/8)/pi)(J1 L/8 + Y(L)); Y decreases in L, so Y(L) <= max(0, Y(400)).
The remaining pieces (the C1, C2, C3 parts of V, the low zeros 2 x^(-1/2) N_+(H0),
tau <= 2 x^-3, and the prime-power share with h <= x and
log(log_2(x+h)) <= log(x+h)/log 2) are monomials c L^j (log L)^l e^(-dL)
with d >= 1/8, each decreasing on [400, infinity) (checked). QED

The limit of the bound is J1/(8 pi c) = 0.6916758 for c = 1/2; a constant
c <= J1/(8 pi) = 0.3458379 cannot close the tail by this method (the test
confirms c = 1/3 fails).

## 9. Proof of Theorem 3

### 9.1 One-sided weights

Fix x >= e^10 and delta in (0, 1/2). Let Phi(u) = integral_0^u phi, and put
w_+(t) = 1 - Phi((t - x)/(delta x)) and
w_-(t) = 1 - Phi((t - x(1-delta))/(delta x)). Then w_- <= 1_(0,x] <= w_+
on the positive integers, so sum Lambda(n) w_-(n) <= psi(x) <=
sum Lambda(n) w_+(n). With kappa = -w', a probability density
(1/(delta x)) phi((t - x_0)/(delta x)) on [x_0, x_0 + delta x], x_0 in
{x(1-delta), x}, the argument of Lemma 3.1 gives

    sum Lambda(n) w(n) = integral psi_0 kappa = E_kappa[t] - sum_rho K(rho) - log 2 pi - E_kappa[(1/2) log(1 - t^-2)],
    K(rho) = integral (t^rho/rho) kappa(t) dt.

E_kappa[t] = x +- delta x/2 by symmetry of phi; the last term is at most 0,
and for w_+ (t >= x) at least -x^-2. Integrating by parts 0, 1 or 3 times as in Lemma 2.1,
|K(rho)| <= (x(1+delta))^beta g(|gamma|/a)/|gamma| with a = (1+delta)/delta.
Hence, with Sp^low and Sp^high the sums of g(gamma/a)/gamma below and above
H0,

    |psi(x) - x| / x^(7/8) <= delta x^(1/8)/2 + 2 (1+delta)^(1/2) x^(-3/8) Sp^low(a)
                              + 2 (1+delta)^(7/8) Sp^high(a) + (log 2 pi + x^-2) x^(-7/8).

The sums are bounded as in Lemma 5.1 with G(t) = g(t/a)/t, whose -G' is
t^-2, 9a t^-3, 864 a^3 t^-5 on the three pieces; the Stieltjes integral
for Sp^low starts at 14 by (I5).

### 9.2 Cover

L = log x in [10, 200]: 3042 intervals (width at most 1/16), each with a
fixed delta = f L_a e^(-L_a/8)/(4 pi), f the best of {1/2, 7/10, 1, 7/5, 2};
the bound evaluated with x^(1/8) at the right end and x^(-3/8), x^(-7/8) at
the left end is certainly below (L_a)^2/(128 pi). Weakest relative margin
0.0427 on the first interval [10, 10.016]. Below L about 9.9 the bound
exceeds the target (at L = 6 the margin is certainly negative), so x0 = e^10
is near the limit of this weight.

### 9.3 Tail

**Lemma 9.3.** For L = log x >= 200, with delta = L e^(-L/8)/(4 pi) and no
verified height, |psi(x) - x|/x^(7/8) <= L^2/(128 pi) - D(L) with D(200) >
8.743 and D increasing on [200, infinity).

*Proof sketch with all constants in `bound.psi_tail`.* The delta term is
L/(8 pi). With lambda = log a <= L/8 - mu(L),
mu(L) = log L - log 4 pi - delta(200), the sum over all zeros satisfies
Sp(a) <= Q(lambda) + E1/a, and (1 + delta)/a = delta, where
Q(lambda) = (lambda - k1)^2/(4 pi) + rho1 + (1/pi)(1 - (9/2)/sqrt 48)(lambda - k2)
+ (864/(2 pi 48^(3/2)))((lambda - k2)/3 + 1/9), k1 = log(2 pi e) - log(9/2),
k2 = log(2 pi e) - log sqrt 48, rho1 >= integral_14^infty R(t) t^-2 dt, and
E1 collects the R-parts of the last two pieces (O(L)). Expanding
(L/8 - mu - k1)^2 gives L^2/64 - (L/4)(mu + k1) + (mu + k1)^2, so
D(L) = (L/(8 pi))(mu + k1 - 1 - pi lin) - (mu+k1)^2/(2 pi) - 2 rho1 - const
- small(L), lin = (2/pi)(1 - 9/(2 sqrt 48)) + 864/(3 pi 48^(3/2)) =
0.4988...; small(L) is a sum of positive-coefficient polynomials of degree
<= 3 times e^(-L/8) or e^(-7L/8), decreasing for L > 24. The derivative of
the main part is at least 0.0943 at L = 200 and increases. QED

## 10. Measured: sensitivity to the verified height (not part of any proof)

Pointwise peak of the k = 9 bound E over log n in [2.4, 120], step 0.25:

| H0 | peak log n | peak E |
| --- | --- | --- |
| 0 | 10.65 | 0.6409 |
| 10^4 | 12.65 | 0.6121 |
| 10^6 | 16.65 | 0.5072 |
| 10^8 | 21.15 | 0.3789 |
| 10^10 | 25.65 | 0.2662 |
| 3 000 175 332 800 | 31.15 | 0.1628 |

The verified height buys margin, roughly 0.11 per factor 100, and never
decides k.

## 11. Review state, novelty search, what is not done

**Review state.** No independent review of sections 2 to 9 has happened.
The numerical side has two routes for its two load-bearing identities (the
explicit-formula normalisation against a direct prime sum, and the
closed-form integrals against quadrature); every inequality that the proofs
need is decided in Arb. A reviewer should check first: the use of (I4) in
Lemma 3.1 (qualitative only); Lemma 5.1's Stieltjes boundary terms; the
monotonicity Lemma 6.2; and the tail lemmas 6.4, 8.2, 9.3, whose constants
live in `bound.py`.

**Novelty.** Searched (web and arXiv, 2026-10-08): "prime between consecutive
powers n^k (n+1)^k all n", "consecutive perfect kth powers 2026", "quasi-Riemann
hypothesis zero-free half-plane consequence prime gaps short intervals
explicit". Found: Cully-Hugill (2023, k = 155), Cully-Hugill and Johnston
(2023, k = 140; 2025, k = 90), Lee (2026, k = 86; also zero-free regions of
Littlewood shape on thin rectangles sufficient for 65 <= k <= 85), Visser
(arXiv:2508.18786, intervals [x, x + x^(1-1/n)] for n >= 106 and all x),
Chamberland and Straub (2026, under RH). OpenAI's October 5 paper states
Corollary 1.2 (primes in progressions with error << x^(11/12) log x,
inexplicit constant) and no prime-gap or short-interval statement. No
explicit consequence of a zero-free half-plane for primes between powers or
in short intervals was found. The qualitative implication (a half-plane
Re s > theta gives primes in [x, x + x^(theta+eps)] for large x) is classical;
what is produced here is the explicit closure for every n at k = 9 and the
explicit constants. This is an original construction of the lab; whether it
is new to the world rests on the searches listed, and the input theorem is
eight days old. The method (smoothed explicit formula, sums over zeros
through N(T), split at a verified height) follows J. Buthe,
arXiv:1511.02032 (an analytic method for bounding psi(x)); the B-spline
weight and the closed-form tangent-line integrals are the choices made here.

**Not done.**
- No external or model review of the written proofs.
- No Lean formalisation; the composite grade stays below kernel-checked.
- Theorem 2 is stated for x >= e^8 only; smaller x is not addressed (it would
  need a gap table, which was deliberately not used).
- Theorem 3's starting point e^10 and constant 1/(128 pi) were not optimised
  beyond a five-point choice of delta per interval.
- Lemma 9.3 is written as a sketch whose every constant is in code; it
  deserves a line-by-line expansion before review.
- No attempt below k = 9 (see the doors).

## The doors

The chain for k = 9 closes with room to spare; the wall is k = 8, where the
chain fails for every n beyond e^28.4 (section 7). That is a measured wall of
this method, not a proved impossibility for the information class: the
heuristic reason is that with only "beta <= 7/8 above the height" and the
N(T) density, the triangle-inequality bound over zeros is of size
(c/(8 pi)) log n at k = 8 for this weight (c = J1 = 8.69), and a short
Fourier argument suggests every weight supported on [0, 1] gives a bound
growing like log n; that argument is not written out here, so the
disposition is "attempt unresolved at k = 8", not "obstructed".

**1. Active constraints at the optimum.** At the weakest interval of the
k = 9 cover (log n near 31.1) the only active term is the high-zero sum:
zeros above H0 counted at real part 7/8 with the full N(T) density
(E = 0.1747 there; the low-zero term is below 1e-45 and the prime-power share
below 1e-55). Ranked by effect on the k = 8 wall: (i) the abscissa 7/8, which
fixes the exponent balance k(1 - theta) = 1; (ii) the zero density, through
the main term of N(T); (iii) the weight, through J1 (slope J1/(8 pi) per unit
of log n). The verified height H0 and the N(T) remainder constants are not
active (section 6.6 and section 10).

**2. Frozen-constant inventory.**
- Weight: quadratic B-spline (order 3). J1 = 8.69 sets the k = 8 slope, the
  Theorem 2 constant (c > J1/(8 pi) = 0.346) and the Theorem 3 lower-order
  terms. Genuine trade shape: smoother weights shrink the tail of g but
  enlarge its flat part; an extremal (Logan or Selberg type) weight would
  lower J1, improving constants, never k.
- H0 = 3.0e12: no trade at k = 9 (closes with H0 = 0); trades only margin.
- N(T) constants (0.137, 0.443, 3.77417): lower order; no trade shape.
- Grid width 1/16, L_inf (100, 200, 400): computational, no trade shape.
- c = 1/2 in Theorem 2: trades against margin (limit J1/(8 pi c) = 0.69).
- x0 = e^10 and 1/(128 pi) in Theorem 3: the constant is the method's
  asymptotic one; x0 trades against a larger constant or a better weight.
- The witness range n <= 9: arbitrary; the analytic bound already closes at
  n = 3 for k = 9 (measured pointwise), so it has no trade shape.

**3. Information class of each door.**
- *Explicit zero-density estimates* N(sigma, T) (for example Kadiri, Lumley and
  Ng, J. Math. Anal. Appl. 465 (2018) 22-46, cited by Cully-Hugill and
  Johnston): requires reading more. Thinning the zeros near real part 7/8
  above H0 is the only door below k = 9 for this half-plane; how far it goes
  depends on the explicit density constants, not attempted here.
- *A further zero-free half-plane*: requires reading more (a stronger input
  theorem); the chain gives k = floor(1/(1-theta)) + 1 for any theta, for
  example k = 5 at theta = 3/4 and k = 3 for theta < 2/3, subject to the margins
  being rechecked.
- *A better weight*: stays inside the data the current family reads;
  improves Theorems 2 and 3, cannot move k.
- *A larger verified height*: stays inside; inactive for k.
