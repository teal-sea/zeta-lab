# An explicit class-number bound from the quasi-Riemann hypothesis

**Status: candidate, pending external review.** Every statement below is
*proved, given OpenAI's Theorem 1.1* (input theorem below, unreviewed). The
analytic chain is an ordinary written proof by this hunt, not independently
reviewed. Every numerical constant in it is evaluated with Arb ball arithmetic
(python-flint, 128 bits), so the numerical steps are enclosure-carrying; the
class-number lists are exact integer computations checked against brute force,
PARI and Watkins. A composite claim takes the grade of its weakest step: here
the unreviewed input theorem, then the unreviewed written proof.

## 0. The input theorem

OpenAI, *The Quasi-Riemann Hypothesis* (preprint dated 30 September 2026),
Theorem 1.1: every Dirichlet L-function, including zeta, has no zero with
Re s > 7/8 (the pole at s = 1 of a principal character excepted). Its Lean
statements (`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`,
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`) were
kernel-checked by this lab on two kernels on 2026-10-08 (section 7 of the input-theorem page numbered 38,
unmerged PR #271). No human has reviewed the 195-page argument. This hunt
uses the theorem and does not re-check it.

The October 5, 2026 OpenAI paper (also titled *The Quasi-Riemann
Hypothesis*) proves the weaker half-plane Re s > 11/12 as its own Theorem 1.1,
cites the 7/8 paper as [36], and remarks in its introduction that Littlewood's
short Euler product gives h(D) >> sqrt|D| / log log |D| "with an absolute
computable implied constant", which it does not compute. Everything below is
stated for a general abscissa sigma0; section 6 gives the constants for
sigma0 = 11/12 as well (c = 1/16 in Theorem A, D(1000) = 10 592 194 843), so
a reader who prefers the October 5 statement loses only constants, and the
lists below remain complete for h <= 1000 under 11/12 alone.

**Hypothesis H(sigma0).** For the character in question, every zero
rho = beta + i gamma of L(s, chi) with 0 < beta < 1 has beta <= sigma0.
OpenAI's Theorem 1.1 gives H(7/8) for every Dirichlet character.

## 1. Results

Throughout, D < 0 is a fundamental discriminant, q = |D|, chi = chi_D is the
Kronecker symbol (primitive, real, odd), h(D) the class number, and for
D < -4 Dirichlet's formula reads h(D) = sqrt(q) L(1, chi_D) / pi.

**Theorem A (clean form).** Given OpenAI's Theorem 1.1, for every negative
fundamental discriminant D other than -3,

    L(1, chi_D) >= 1 / (10 log log |D|),

and for every negative fundamental discriminant D,

    h(D) >= sqrt|D| / (10 pi log log |D|).

So c = 1/10 in L(1, chi_D) >= c / log log |D| with A = 0 and D0 = 4, and the
implied constant of OpenAI's h(D) >> sqrt|D| / log log |D| is 1/(10 pi) =
0.0318. (For D = -3, -4 the class-number statement is trivial: the right side
is below 1. Section 4 splits the proof into an exact range, a verified cover
and an analytic tail.)

**Theorem B (the explicit inequality).** Assume H(sigma0) for chi_D, with
eps0 = 1 - sigma0 > 0. Let 1 < y < x, a = log y, b = log x, and
delta_x, delta_y > 0. Then

    log L(1, chi) >= M(a, b) - ( R(x, delta_x) + R(y, delta_y) + T(x) + T(y) ) / (b - a)

where, with S(t) = sum_{p <= t} 1/p and G as in (2.3),

    M(a, b) = -(1/(b-a)) int_a^b S(e^u) du
              + sum_{p <= y^(1/2)} (1/(2p^2) - 1/(3p^3)) + sum_{p <= y^(1/4)} (1/(4p^4) - 1/(5p^5)),

    R(t, delta) = t^(-eps0) [ (delta + eps0) G(1 + delta) int_0^delta t^(-u) (u + eps0)^(-2) du
                              + int_delta^inf t^(-u) G(1 + u) (u + eps0)^(-1) du ],

    T(t) = (pi^2/24) t^(-2) / log t.

R is increasing in q, so a value computed at q_hi bounds every q <= q_hi.

**Theorem C (the table D(h)).** Given OpenAI's Theorem 1.1: if h(D) <= h
then |D| <= D(h), with D(h) from `dtable.json` (verified for every
h <= 2000). Selected values:

| h | D(h) | h | D(h) | h | D(h) |
| --- | --- | --- | --- | --- | --- |
| 1 | 3 237 | 50 | 11 600 074 | 500 | 1 322 624 535 |
| 2 | 14 140 | 100 | 48 611 613 | 700 | 2 627 915 360 |
| 3 | 33 334 | 150 | 111 023 348 | 1000 | 5 433 399 820 |
| 5 | 96 751 | 200 | 201 695 793 | 1500 | 12 409 254 457 |
| 10 | 413 761 | 300 | 460 649 837 | 2000 | 22 320 645 193 |

**Corollary D (the class-number lists).** Given OpenAI's Theorem 1.1, the
imaginary quadratic fields of class number h are exactly those found by the
search of section 5, for every h <= 1500. In particular:

- for h <= 100 the search reproduces Watkins (2004) exactly: all 100 counts
  (total 42 272) and all 100 largest discriminants agree with OEIS
  A046125 / A038552; under QRH this is an independent completion of
  Watkins' classification, by a two-second computation;
- for every h <= 1000 there are 4 115 897 fields in all; the largest
  discriminant is D = -227 932 027 (h = 996);
- for every h <= 1500 there are 9 245 562 fields; the largest discriminant is
  D = -562 394 347 (h = 1489); every h <= 1500 occurs;
- for the 750 odd h <= 1500 the counts (995 897 fields) agree exactly with
  the GRH-conditional table of Holmin and Kurlberg (section 6), computed by a
  different method.

The full lists are reproducible with `run_search.py 1000 5433399820 OUTDIR`
and `run_search.py 1500 12409254457 OUTDIR`; their sorted texts ("|D| h" per
line) have sha256
`075a201c8e7cce6c0b6013423a5d96c6308452afab2fa79882388fc46d8b0c45` (h <= 1000)
and `c373d7c67bbecb922878481c50e6273f03ed07b93fc968a458bb0bf5389ee101`
(h <= 1500), and the h <= 1000 part of the second run has the same sha256
as the first. The counts F(h) and the largest |D| for each h are in
`search_H1000.json` and `search_H1500.json`.

## 2. Proof of Theorem B

**(2.1) Explicit formula.** For x > 1 and real sigma >= 1 (Perron's formula
with kernel x^w / w^2, contour moved to the left; the zero sum converges
absolutely; see the proof of Lemma 2.5 in Lamzouri, Li and Soundararajan,
Math. Comp. 84 (2015) 2391-2412, which is unconditional up to this display,
and Davenport, *Multiplicative Number Theory*, chapters 12, 17 and 19):

    sum_{n <= x} Lambda(n) chi(n) n^(-sigma) log(x/n)
        = -(L'/L)(sigma) log x - (L'/L)'(sigma)
          - sum_rho x^(rho - sigma) / (rho - sigma)^2
          - sum_{k >= 0} x^(-2k-1-sigma) / (2k + 1 + sigma)^2,

rho over the nontrivial zeros; the last sum is over the trivial zeros
-1, -3, -5, ... of an odd character.

**(2.2) Two cutoffs.** Subtract the same identity at y < x. The term
(L'/L)'(sigma) cancels. Integrate over sigma in [1, inf). On the left,
int_1^inf n^(-sigma) dsigma = 1/(n log n) and log(x/n)^+ - log(y/n)^+ =
log(x/y) w(n) with

    w(n) = 1 (n <= y),  log(x/n)/log(x/y) (y < n <= x),  0 (n > x).

On the right, L(sigma, chi) > 0 for real sigma >= 1 and tends to 1, so
int_1^inf -(L'/L)(sigma) dsigma = log L(1, chi). The interchange of the zero
sum and the integral is justified by the absolute bounds of (2.4). Hence

    log L(1, chi) = sum_n Lambda(n) chi(n) w(n) / (n log n) + E,
    |E| <= ( Z(x) + Z(y) + T(x) + T(y) ) / (b - a),
    Z(t) = sum_rho int_1^inf t^(beta - sigma) |sigma - rho|^(-2) dsigma.

For the trivial zeros, int_1^inf t^(-2k-1-sigma) (2k+1+sigma)^(-2) dsigma <=
t^(-2k-2) / ((2k+2)^2 log t), and the sum over k is at most T(t).

**(2.3) Positivity.** Let xi(s, chi) = (q/pi)^((s+1)/2) Gamma((s+1)/2)
L(s, chi), entire of order one. Hadamard's product and Re B(chi) =
-sum_rho Re(1/rho) (Davenport, chapter 12) give, for real sigma > 1,

    sum_rho (sigma - beta) / |sigma - rho|^2 = Re xi'/xi(sigma, chi)
        = (1/2) log(q/pi) + (1/2) psi((sigma+1)/2) + (L'/L)(sigma, chi),

every term on the left positive. Since (L'/L)(sigma, chi) =
-sum_p log p * chi(p) p^(-sigma) / (1 - chi(p) p^(-sigma)) and the summand is
largest at chi(p) = -1, where it equals log p / (p^sigma + 1),

    sum_rho (sigma - beta) / |sigma - rho|^2 <= G(sigma)
        := (1/2) log(q/pi) + (1/2) psi((sigma+1)/2) - zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma).

**(2.4) The zero sum.** Fix t > 1 and sigma1 = 1 + delta. Assume H(sigma0).

- For sigma >= sigma1: t^(beta-sigma) |sigma-rho|^(-2) = [t^(beta-sigma) /
  (sigma-beta)] (sigma-beta) |sigma-rho|^(-2), and beta -> t^(beta-sigma) /
  (sigma - beta) is increasing on beta < sigma, so the bracket is at most
  t^(sigma0-sigma)/(sigma-sigma0).
- For 1 <= sigma <= sigma1: as a function of gamma^2, the ratio
  |sigma-rho|^(-2) / [(sigma1-beta) |sigma1-rho|^(-2)] is largest at gamma = 0,
  so |sigma-rho|^(-2) <= (sigma1-beta)(sigma-beta)^(-2) (sigma1-beta)
  |sigma1-rho|^(-2); the factor t^(beta-sigma)(sigma1-beta)/(sigma-beta)^2 is
  increasing in beta < sigma (logarithmic derivative log t + 2/(sigma-beta) -
  1/(sigma1-beta) > 0), so it is at most its value at beta = sigma0.

Summing over rho with (2.3) at sigma and at sigma1 and integrating, with
u = sigma - 1, gives Z(t) <= R(t, delta). The only property of the zeros used
is beta <= sigma0, which is H(sigma0).

**(2.5) The prime sum.** Write the n-sum as a sum over prime powers,
sum_p sum_k chi(p)^k w(p^k) / (k p^k). For each p the inner sum is smallest
at chi(p) = -1 (at chi(p) = 1 it is positive; at chi(p) = 0 it is zero; the
alternating series with nonincreasing terms a_k = w(p^k)/(k p^k) is
negative). With chi(p) = -1 it equals -w(p)/p + sum_{k>=2} (-1)^k a_k, and
the alternating tail is at least a_2 - a_3 (+ a_4 - a_5) when p^2 <= y
(p^4 <= y), where a_2 = 1/(2p^2) and a_4 = 1/(4p^4) exactly and
a_3 <= 1/(3p^3), a_5 <= 1/(5p^5); for p^2 > y it is nonnegative. Finally
w(p) = (1/(b-a)) int_a^b 1[log p <= u] du, so
sum_p w(p)/p = (1/(b-a)) int_a^b S(e^u) du. This is M(a, b). Combining with
(2.2) and (2.4) proves Theorem B.

**(2.6) Evaluation (`lbound.py`).** All in Arb:

- int S(e^u) du is exact below 10^7 (S is a step function:
  int_a^c S(e^u) du = c S(e^c) - a S(e^a) - sum_{e^a < p <= e^c} log p / p,
  prefix sums over the 664 579 primes up to 10^7) and above 10^7 uses
  Rosser and Schoenfeld (1962), Theorem 5 (3.20):
  S(t) < log log t + B + 1/(2 log^2 t) for t >= 286, with the
  Meissel-Mertens constant B = gamma + sum_{k>=2} mu(k) log zeta(k) / k
  enclosed with a rigorous tail (test: it overlaps the published 50 digits).
- zeta'/zeta through Arb power series of zeta; psi through Arb's digamma.
- Both integrals in R are upper Riemann sums on a fixed rational grid
  (step 1/2000 on [0, 1/2], 1/500 on [1/2, 2], 1/100 on [2, 6]): on each cell
  the factor (u + eps0)^(-1) or ^(-2) is taken at the left end, int t^(-u) du
  exactly, psi((sigma+1)/2) at the right end (psi increasing) and
  -zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma) at the left end (it is
  sum_p log p/(p^sigma+1), decreasing); a cell bound is clamped at >= 0.
  For u >= 6, G(1+u) <= (1/2) log(q/pi) + P(7) + u/4 and the integral is
  done in closed form.
- delta is restricted to grid points; a, b are exact rationals chosen by a
  float optimiser (`FloatModel`, which assigns no truth; every reported
  number is recomputed in Arb).

## 3. Proof of Theorem C

`dtable.json` covers [10^2, 10^11] by 2041 intervals with q_hi/q_lo <= 1.01.
On each, parameters (a, b, delta_x, delta_y) are chosen and Theorem B is
evaluated at q_hi, where it is weakest; then h(D) >= sqrt(q_lo) L_lower / pi
for every |D| in the interval. If h(D) <= h, |D| cannot lie in an interval
whose verified bound exceeds h; D(h) is the right end of the last interval
whose bound is <= h. Beyond 10^11, Theorem A gives
h(D) >= sqrt|D| / (10 pi log log |D|) >= 3117 > 2000, increasing in |D|.

Typical parameters (verified rows): at q = 1.7 * 10^8, y = e^7.23, x = e^22.09,
delta = 1/8, M = -2.724, E = 0.389, L(1, chi) >= 0.04449; at q = 9.1 * 10^9,
y = e^7.95, x = e^23.1, M = -2.784, E = 0.375, L >= 0.04247. The weight is
close to a pure Cesaro weight: y is small and x is a power of log q near 8.

## 4. Proof of Theorem A

Three ranges.

1. **|D| <= 3 * 10^6, exact.** h(D) is computed exactly for every one of the
   911 878 fundamental discriminants (section 5) and
   L(1, chi_D) = 2 pi h / (w sqrt|D|). Every D with 4 <= |D| <= 3 * 10^6
   satisfies L log log |D| >= 0.1 (the minimum over |D| > 4 is 0.4006);
   D = -3 fails (0.057), which is the stated exception
   (`controls_exact_l.json`).
2. **121 <= q <= 10^50, verified cover.** 163 intervals with
   log q_hi / log q_lo <= 1.02; on each, Theorem B at q_hi times log log q_lo
   is at least 0.10030 (`theorem_a.json`).
3. **q >= Q1 = 10^50, tail lemma.** Take lambda = 1, eta = 3/20,
   delta_x = delta_y = 1/25 and a(q) = 8 log log q, b = (1 + eta) a. Then
   - main term: by Rosser-Schoenfeld for all t >= 286,
     (1/(b-a)) int_a^b S(e^u) du <= B + log a + kappa(eta) + 1/(2ab) with
     kappa(eta) = (1+eta) log(1+eta)/eta - 1; the P-sums are nondecreasing in a;
   - zero sums: e^(-a/8) = 1/log q, and G(sigma) <= log q (1/2 + g+(sigma)/log q)
     with g+ = max(0, psi((sigma+1)/2)/2 - zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma)),
     so R(y) <= [(delta+1/8)(1/2 + g+(1+delta)/log q) I_1(a) + int e^(-ua)
     (1/2 + g+/log q)/(u + 1/8) du], each factor nonincreasing in q; R(x) has the
     extra factor (log q)^(-eta); T and 1/(b-a) decrease.

   Every piece is therefore bounded by its value at Q1, and log L(1, chi) >=
   K1 - log a(q) with K1 = -B - kappa - 1/(2 a1 b1) + P2(a1) - E~(Q1) =
   -0.189581..., where E~(Q1) = 0.036241 (Arb). So
   L(1, chi) >= e^K1 / (8 log log q) >= 0.10341 / log log q.

Together these give Theorem A.

*Remark (the limit of the method; ordinary argument, not run in Arb).* With
eta -> 0, Q1 -> infinity and all prime powers kept in (2.5), the tail argument
gives L(1, chi) >= (1 - eps)(1 - sigma0) zeta(2) e^(-gamma) / log log q for
q >= q(eps): 0.11545 / log log q at sigma0 = 7/8, against Littlewood's GRH
constant zeta(2) e^(-gamma) / 2 = 0.4618. The two differ exactly by the
factor (1 - sigma0) / (1/2) = 1/4: the cutoff x must be a power
1/(1 - sigma0) = 8 of log q instead of 2. The verified values of
L log log q at feasible q are larger than this limit (0.1266 at 10^6, 0.1348
at 10^12, 0.1411 at 10^100, `abscissae.json`), because there the optimal y
is far below (log q)^8 and the weight is nearly a pure Cesaro weight.

## 5. The class-number computation

`cn.c` (exact integer arithmetic, no GRH, no floating point in any decision).

- **Fundamental discriminants.** n = |D| with n = 3 mod 4 squarefree, or
  n = 4, 8 mod 16 with n/4 squarefree; a segmented sieve removes n divisible
  by p^2 for odd p.
- **Reduced forms.** For fundamental D every form is primitive, so h(D) is
  the number of reduced forms (a, b, c): |b| <= a <= c, b >= 0 if |b| = a or
  a = c. For 4a^2 < n every b in (-a, a] with b^2 = D mod 4a gives c > a, so
  the number of reduced forms with first coefficient a is
  r(a) = #{b mod 2a : b^2 = D mod 4a}, multiplicative with r(p^k) = 1 + chi(p)
  for p not dividing D, r(p) = 1 and r(p^k) = 0 (k >= 2) for p | D.
- **Sieve.** Hence h(D) >= sum over any set of a with 4a^2 < n of r(a). For
  every segment the counts sum_a r(a) are streamed over all n at once (r(a)
  is periodic in n), over all a below sqrt(n)/2 where the primes alone cannot
  finish, and otherwise over the first K = 1.3 H + 40 primes; survivors
  continue prime by prime, and the rest of the reduced forms are counted
  exactly: r(a) by a multiplicative sieve for 4a^2 < n, and for
  n <= 4a^2 <= 4n/3 the roots of b^2 = D mod 4a by Tonelli-Shanks, Hensel
  lifting and the Chinese remainder theorem, each root checked.
- **Checks.** Every fundamental |D| <= 4000 against brute-force reduced-form
  counting (`classno.reference_h`), samples against PARI `qfbclassno`, the
  exact stage against an independent brute-force-over-b implementation inside
  `cn.c` (`CN_CHECK=1`), the streamed filter counts against a recomputation
  of every count with Jacobi symbols and no periodic patterns
  (`CN_CHECK_STREAM=1`), and the filtered runs against unfiltered full counts.
  The filter can only lose a field by over-counting, so the stream check is
  the one that guards completeness.

**The runs.** H = 1000 (`run_search.py 1000 5433399820`, one core, 9 min 59 s):
1 651 555 483 fundamental discriminants with |D| <= D(1000) = 5 433 399 820;
5 518 464 survived the streamed filter, 5 336 508 reached the exact count,
4 115 897 have h <= 1000. Time by range: below 10^7, 52 s (the list is dense
there); 10^7 to 10^8, 136 s; 10^8 to 5 * 10^8, 90 s; above, 316 s (the prime
stage, about 1340 periodic additions per discriminant). A separate H = 100 run
to D(100) = 48 611 613 takes 1.8 s and finds the same 42 272 fields. H = 1500
(`run_search.py 1500 12409254457`, one core, 2327 s of chunk time over two
sessions, the first stopped by a wall-clock limit and resumed from its chunk
checkpoints): 3 771 960 997 fundamental discriminants, 14 817 639 filter
survivors, 14 379 846 exact counts, 9 245 562 fields with h <= 1500. Its
h <= 1000 and h <= 100 sub-lists have the same sha256 as the H = 1000 and
H = 100 runs: no field with h <= 1000 lies in (D(1000), D(1500)], checked by
computation rather than by the theorem.

| h range | fields | largest abs(D) | D(h_max) | D(h_max) / largest |
| --- | --- | --- | --- | --- |
| h <= 100 | 42 272 | 2 383 747 | 48 611 613 | 20.4 |
| h <= 200 | 167 157 | 8 377 363 | 201 695 793 | 24.1 |
| h <= 500 | 1 028 749 | 55 171 603 | 1 322 624 535 | 24.0 |
| h <= 1000 | 4 115 897 | 227 932 027 | 5 433 399 820 | 23.8 |
| h <= 1500 | 9 245 562 | 562 394 347 | 12 409 254 457 | 22.1 |

The last column is the price of the analytic bound: the search must go about
24 times further than the last field it finds.

## 6. Controls

**Bound against exact L(1, chi_D).** For every fundamental D with
100 <= |D| <= 3 * 10^6 (911 847 discriminants) the exact value
L(1, chi_D) = 2 pi h / (w sqrt|D|) was compared with the verified lower bound
of the `dtable.json` interval containing |D|. No violation; the smallest
ratio exact / bound is **3.888**, at D = -163 (L = 0.24607 against the bound
0.06329). The class-number formula values agree with PARI's
`lfun(lfuncreate(D), 1)` at 34 sampled D to relative 2.2e-16, an independent
route to L(1, chi_D). Mosunov and Jacobson report the smallest L(1, chi_D)
for |D| < 2^40 as 0.17070 at D = -107 415 709 003, where Theorem B gives
about 0.041: the bound is about four times below the truth throughout the
range anyone has computed. A planted inflation of the bound by the observed
worst ratio times 1.01 is caught (`test_a_planted_inflation_is_caught`).

**Weakened and strengthened abscissa** (`abscissae.json`, Arb, verified
lower bounds for L(1, chi) at a single q):

| q | sigma0 = 1/2 | 7/8 | 11/12 | 15/16 |
| --- | --- | --- | --- | --- |
| 10^6 | 0.13672 | 0.04820 | 0.03496 | 0.02775 |
| 10^9 | 0.12617 | 0.04353 | 0.03158 | 0.02509 |
| 10^12 | 0.11894 | 0.04062 | 0.02945 | 0.02342 |
| 10^20 | 0.10778 | 0.03611 | 0.02616 | 0.02081 |
| 10^100 | 0.08142 | 0.02594 | 0.01866 | 0.01479 |

Strictly ordered at every q, as it must be. The predicted mechanism is that
the cutoff x scales like (log q)^(1/(1 - sigma0)) and the constant like
(1 - sigma0): at q = 10^100 the optimal log x is 37.0, 51.6 and 65.3 for
7/8, 11/12 and 15/16 (predicted ratios 1.5 and 2, observed 1.39 and 1.76),
and the ratio of bounds 15/16 to 7/8 is 0.570 (limit 1/2). The 11/12 column
is what the October 5 paper's own theorem gives: about 28% weaker than 7/8.

**GRH calibration.** At sigma0 = 1/2 the same code gives L(1, chi) >= 0.11894
at q = 10^12 and 0.08142 at q = 10^100, and L log log q -> 0.4618 (Littlewood).
Lamzouri, Li and Soundararajan (Theorem 1.5, GRH, q >= 10^10) give 0.0904 at
10^12, 0.0912 at 10^20 and 0.0802 at 10^100. The two share the limit and are
within 2% at 10^100; at 10^12 this method is 32% stronger, from optimising the two
cutoffs rather than fixing x = (log q)^2 / 4 and from LLS's 14 log log q /
log q term. Not implausibly better, which is the purpose of the control.

**Class numbers.** Every fundamental |D| <= 4000 against brute-force
reduced-form counting; 60 sampled D near 10^6 and 1900 D from the H = 1500
output (the largest |D| for every h <= 1500 and 400 random entries, up to
|D| = 562 394 347) against PARI `qfbclassno`, no disagreement
(`controls_pari_H1500.json`); every streamed count in four windows
(10^5 to 3 * 10^5 at H = 100; 3 * 10^8, 10^9 and 2 * 10^9 at H = 1000 or 1500,
composite and prime-only modes) recomputed independently (`CN_CHECK_STREAM=1`);
the fast exact count against the slower brute-force-over-b count inside `cn.c`
(`CN_CHECK=1`) on every survivor in a window near 4 * 10^7; filtered runs
against unfiltered full counts (tests: H = 7 and 60 on |D| <= 3 * 10^5;
during development also H = 100 and 1000 on |D| <= 3 * 10^6). Watkins: all 100 counts and all 100 largest squarefree k for
h <= 100 agree with OEIS A046125 and A038552 (from Watkins 2004), in both
the H = 100, H = 1000 and H = 1500 runs. Holmin and Kurlberg: all 750 odd
h <= 1500 agree with their GRH-conditional F(h) table
(`holmin_kurlberg_odd.json`, fetched from the authors' page). After the
runs, `cn.c` gained only the environment-gated stream check; two chunks
recomputed with the new binary are byte-identical to the run files.

**The October 5 abscissa, 11/12** (`eleven_twelfths.json`, same code with
sigma0 = 11/12): the tail constant at 10^50 is 0.06959 and the cover keeps
L log log q >= 1/16 from q = 100, so L(1, chi_D) >= 1/(16 log log |D|) for
|D| >= 4 (the exact range is as for 7/8); D(1) = 6 390, D(100) = 95 092 214,
D(1000) = 10 592 194 843. The H = 1500 search reaches 1.24 * 10^10, so the
lists for h <= 1000 are complete under the 11/12 theorem as well.

## 7. What this improves, and the literature searched

Searched on 2026-10-08 (web search over arXiv, journal pages, zbMATH-indexed
titles and author pages; the queries and hits are summarised here, not
exhaustive): explicit lower bounds for L(1, chi) under a zero-free half-plane;
"quasi-Riemann hypothesis" with "class number"; extensions of Watkins' h <= 100;
unconditional class-group tabulations.

Found, and what this hunt adds to each:

- **Littlewood (1928)**, GRH: L(1, chi) >= (1 + o(1)) zeta(2) / (2 e^gamma
  log log q). **Lamzouri, Li, Soundararajan**, Math. Comp. 84 (2015), Theorem
  1.5: the explicit GRH form for q >= 10^10. This hunt's inequality is the
  same mechanism with the GRH line replaced by the half-plane, a second Cesaro
  cutoff that removes their (L'/L)(1, chi) term, and Hadamard positivity for
  every zero; its sigma0 = 1/2 specialisation is the calibration above.
- **Friedlander and Iwaniec**, arXiv:1701.03771, Theorem 3: Littlewood's
  argument under "beta > 3/4 is the only zero in Re s > 3/4", with
  x = (log D)^4 and unspecified constants. The half-plane version of the
  mechanism is therefore known; no explicit constant for it was found.
- **OpenAI, October 5, 2026**, introduction: h(D) >> sqrt|D| / log log |D|
  from its 11/12 theorem, constant "absolute computable" and not computed.
  **Theorem A supplies the constant: 1/(10 pi) with the 7/8 input**, and
  1/(16 pi) with the 11/12 input (section 6).
- **Watkins (2004)**: unconditional complete lists for h <= 100. Reproduced
  here exactly; under QRH this is a second, independent completion.
- **Holmin, Jones, Kurlberg, McLeman, Petersen** (arXiv:1510.04387): complete
  lists for odd h < 10^6 conditional on GRH (LLS bound, PARI under GRH, 4.5
  CPU years). Odd h <= 1500 agree; this hunt replaces GRH by the 7/8
  half-plane for those h and adds every even h <= 1500.
- **Mosunov and Jacobson**, Math. Comp. 85 (2016): unconditional class groups
  for all |Delta| < 2^40, organised by discriminant; no per-h lists are
  published. Since D(1500) < 2^40, their tabulation could in principle be
  re-read to the same lists (a door below).

Not found: an explicit constant for the half-plane form of Littlewood's
bound, or complete lists for even h with 100 < h <= 1500 under any
hypothesis. Absence in this search is a statement about the search, not a
novelty claim. Within the searched set, **Theorem A, the table D(h) and the
QRH-conditional completion of the class-number lists for every h <= 1500 are
original to this hunt (provenance)**, graded as stated at the top, and
pending external review.

Checked and not used: a Bach-type bound from the 7/8 half-plane for the norms
of primes generating the class group. The argument needs the main term x to
beat the zero contribution x^(7/8) log q, so x must exceed about
(log q)^8; that is below the trivial Minkowski range sqrt(q/3) only when
8 log log q < (1/2) log(q/3), that is q > about 1.7 * 10^30, even with
implied constant 1. In the computed range it is useless, and the method here
counts reduced forms directly, so it needs no generators at all.

## 8. Not done

- **External review.** Neither the input theorem nor this hunt's written
  proof has been read by a human mathematician. The chain in section 2 is the
  part to check: (2.1) is cited, (2.2) to (2.5) are written out here.
- **Formalisation.** Nothing here is in Lean; the Arb evaluation is the
  numerical layer, not a kernel check.
- **Zero pairing.** Real characters have zeros in pairs beta, 1 - beta at the
  same height; the positivity step charges every zero as if it sat at
  beta = 7/8. Using the pairing would shrink the zero term by up to about 12%
  at low height and more at large height; not derived.
- **H beyond 1500.** H = 2000 (D(2000) = 2.23 * 10^10) is estimated at
  about an hour of one core and was not run; the cost grows like H^3.
- **Orders and group structures.** Only fundamental discriminants (maximal
  orders) and only class numbers, not class-group structures, were tabulated.
- **The full lists are not committed** (49 MB and 118 MB); their
  sha256 and the commands that regenerate them are.

## The doors

The hunt stops at H = 1500 for budget, not for a mathematical wall. What binds, and what would move it:

1. **Active constraints at the optimum.** (a) The zero-free abscissa itself:
   the constant scales with 1 - sigma0 and the cutoff with
   (log q)^(1/(1 - sigma0)); it is the input theorem's, frozen here. Ranked by
   shadow price it is first: 7/8 to 1/2 would multiply L by about 2.9 at
   q = 10^9 and shrink D(h) by about 8. (b) The zero term E, about 0.38 of
   log L at q = 10^9 (a factor e^0.38 = 1.46 in L, so about 2.1 in D(h)):
   the positivity bound charges every zero at beta = 7/8 and needs G(sigma)
   with its 1/(sigma - 1) pole, so the split point delta trades the pole
   against the factor (delta + 1/8). (c) The main term's prime sum, where the
   weight is already nearly optimal (y small, x a power of log q). (d) On the
   computation side, cost grows like X * H, that is H^3 (log log)^2:
   10 minutes at H = 1000 became 39 minutes at H = 1500 (the survivor stage
   below 10^9 grew faster than estimated), and H = 2000 extrapolates to well
   over an hour on one core.
2. **Frozen-constant inventory.** sigma0 = 7/8 (input, not ours to move).
   The trapezoid weight (two cutoffs); a smoother weight with more cutoffs is
   a genuine trade (it spends main term to spread the y-term of E). The grid
   steps 1/2000, 1/500, 1/100 and the tail point u = 6 (cost: about 1% in R;
   no trade shape). The prime-power truncation at k = 5 (0.2% of L; none).
   T_EXACT = 10^7 and Rosser-Schoenfeld above it (Dusart's 0.2/log^3 t would
   gain under 0.002 in log L; small trade). The cover ratios 1.01 and the
   tail point Q1 = 10^50 with lambda = 1, eta = 3/20, delta = 1/25 (these set
   c = 1/10; c = 0.105 needs Q1 near 10^200; genuine trade between c and the
   size of the verified cover). The search's K = 1.3 H + 40 primes and the
   composite cap 4000 (speed only, never correctness).
3. **Information class of each door.** Zero pairing (beta and 1 - beta at
   one height) stays inside the data the method already reads: the functional
   equation of a real character. Using explicit zero counting near height 0
   (Bennett, Martin, O'Bryant, Rechnitzer) reads more: its error term is
   comparable to the main term at small height, so it pays only with a
   short-interval count that is not in the literature found. Re-reading the
   Mosunov-Jacobson tabulation (CLGRP, unconditional to 2^40) reads more data:
   the single-q bound at 10^12 gives h >= 12 930 there (indicative; the
   verified cover stops at 10^11), so their class numbers plus Theorem B on a
   cover to 2^40 would complete the lists to h of order 10^4, far beyond
   this hunt's search, at the cost of re-running or obtaining their
   per-discriminant output. A smaller sigma0 is outside both: it needs a new
   zero-free region.

A measured optimum is not a proved ceiling: the bound's constant here is the
best the float optimiser found within this family of weights and grids, at
the stated q, with no proof that the family is optimal.
