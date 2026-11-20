# The class-number lists for h <= 5000, given GRH for the quadratic characters

**Status: candidate, pending external review.** Every statement below is
*proved, given GRH for the real primitive characters chi_D* (hypothesis
H(1/2) below), and is never unconditional. The analytic chain is the sibling
hunt's written proof, audited here line by line at sigma0 = 1/2 (section 2):
an ordinary derivation, not independently reviewed. Every numerical constant
in it is evaluated with Arb ball arithmetic (python-flint, 128 bits), so the
numerical steps are enclosure-carrying; the class-number lists are exact
integer computations that agree with every independent table found. A
composite claim takes the grade of its weakest step: here the hypothesis,
which is not a theorem, then the unreviewed written proof.

## 0. The hypothesis

Throughout, D < 0 is a fundamental discriminant, q = |D|, chi = chi_D is the
Kronecker symbol (primitive, real, odd), h(D) the class number, and for
D < -4 Dirichlet's formula reads h(D) = sqrt(q) L(1, chi_D) / pi.

**Hypothesis H(1/2) for chi_D.** L(s, chi_D) has no zero with Re s > 1/2.

By the functional equation this says that every nontrivial zero of
L(s, chi_D) has real part exactly 1/2: it is GRH for the one character
chi_D. Nothing is assumed about any other L-function, and nothing about
zeta.

*Why now.* On 2026-11-20 Levent Alpoge posted a claimed Lean proof of RH and
of GRH for Dirichlet L-functions, with the formal statement: for every
Dirichlet character chi mod N and every s with Re s > 1/2, L(s, chi) != 0
unless chi = 1 and s = 1. That statement contains H(1/2) for every chi_D. As
of this writing the archive has been accepted by no kernel and reviewed by
no human, and this hunt neither reads nor checks it. The results below are
GRH-conditional theorems whatever happens to that claim. If the archive is
accepted by a kernel, the hypothesis is discharged at the grade of that
check, and the weakest step becomes this hunt's written proof.

What exactly is assumed, and for which D: Theorems A, B and C use H(1/2) for
the character of the discriminant they speak about. Corollary D uses it only
for |D| > 16 396 235 837, because below that the search is exact and
assumes nothing. In contrapositive form: *a fundamental D < 0 with
h(D) <= 5000 that is missing from the list of section 5 has
|D| > 16 396 235 837 and its L(s, chi_D) has a zero with Re s > 1/2.*

## 1. Results

**Theorem A (clean form).** Given H(1/2) for chi_D: for every negative
fundamental discriminant D other than -3 and -4,

    L(1, chi_D) >= 1 / (3 log log |D|),

and for every negative fundamental discriminant D other than -3,

    h(D) >= sqrt|D| / (3 pi log log |D|).

For |D| >= 10^50 the constant 1/3 can be replaced by 0.3857. Littlewood's
asymptotic GRH constant is zeta(2) / (2 e^gamma) = 0.4618; the sibling
hunt's constant under the 7/8 half-plane is 1/10.

**Theorem B (the explicit inequality at 1/2).** Assume H(1/2) for chi_D,
D < -4. Let 1 < y < x, a = log y, b = log x, and delta_x, delta_y > 0. Then

    log L(1, chi) >= M(a, b) - ( R(x, delta_x) + R(y, delta_y) + T(x) + T(y) ) / (b - a)

where, with S(t) = sum_{p <= t} 1/p,

    M(a, b) = -(1/(b-a)) int_a^b S(e^u) du
              + sum_{p <= y^(1/2)} (1/(2p^2) - 1/(3p^3)) + sum_{p <= y^(1/4)} (1/(4p^4) - 1/(5p^5)),

    R(t, delta) = t^(-1/2) [ (delta + 1/2) G(1 + delta) int_0^delta t^(-u) (u + 1/2)^(-2) du
                             + int_delta^inf t^(-u) G(1 + u) (u + 1/2)^(-1) du ],

    G(sigma) = (1/2) log(q/pi) + (1/2) psi((sigma+1)/2) - zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma),

    T(t) = (pi^2/24) t^(-2) / log t.

R is increasing in q, so a value computed at q_hi bounds every q <= q_hi.
This is the sibling hunt's Theorem B with eps0 = 1 - sigma0 = 1/2; section 2
is the audit that licenses the substitution.

**Theorem C (the table D_GRH(h)).** Given H(1/2) for chi_D: if h(D) <= h
then |D| <= D_GRH(h), with D_GRH(h) from `dtable_grh.json`, for every
h <= 10 000. Selected values, with the 7/8 table of the sibling hunt:

| h | D_GRH(h) | D_7/8(h) | ratio | h | D_GRH(h) |
| --- | --- | --- | --- | --- | --- |
| 1 | 399 | 3 237 | 8.1 | 2500 | 4 071 475 474 |
| 2 | 1 706 | 14 140 | 8.3 | 3000 | 5 767 663 399 |
| 3 | 3 962 | 33 334 | 8.4 | 3500 | 7 930 195 043 |
| 10 | 48 190 | 413 761 | 8.6 | 4000 | 10 374 351 574 |
| 100 | 5 554 909 | 48 611 613 | 8.8 | 4500 | 13 172 673 663 |
| 500 | 151 139 146 | 1 322 624 535 | 8.8 | 5000 | 16 396 235 837 |
| 1000 | 620 886 399 | 5 433 399 820 | 8.8 | 6000 | 23 693 814 649 |
| 1500 | 1 432 212 849 | 12 409 254 457 | 8.7 | 8000 | 42 618 291 966 |
| 2000 | 2 576 135 045 | 22 320 645 193 | 8.7 | 10000 | 67 356 456 941 |

The sibling hunt's door analysis predicted a factor "about 8".

**Corollary D (the class-number lists).** Given H(1/2) for every chi_D with
|D| > 16 396 235 837, the imaginary quadratic fields of class number h are
exactly those found by the search of section 5, for every h <= 5000:

@@COROLLARY@@

## 2. The proof audit at sigma0 = 1/2

The sibling's proof (its RESULTS.md, section 2) is written for a general
abscissa sigma0 with eps0 = 1 - sigma0, and its code takes sigma0 as a
parameter. A parameter that was only ever exercised at 7/8 is not a proof at
1/2, so every step is restated here for sigma0 = 1/2, with what it uses and
what was checked. Verdict first:

| step | uses | where sigma0 enters | at sigma0 = 1/2 |
| --- | --- | --- | --- |
| (2.1) explicit formula | nothing about zeros | nowhere | unchanged; measured against real zeros below |
| (2.2) two cutoffs | L(sigma, chi) > 0 for sigma >= 1 | nowhere | unchanged |
| (2.3) positivity, G | Hadamard product | nowhere | unchanged; the pole of G at sigma = 1 is in the majorant, not in xi'/xi |
| (2.4) zero sum, sigma >= sigma_1 | beta <= sigma0 < sigma | t^(sigma0-sigma) / (sigma-sigma0) | an equality in beta (every beta is 1/2); needs sigma0 < 1 only |
| (2.4) zero sum, sigma < sigma_1 | beta <= sigma0, worst case gamma = 0 | (sigma_1-sigma0) / (sigma-sigma0)^2 | holds for every beta < sigma <= sigma_1; nothing special at 7/8 |
| (2.5) prime sum | chi real | nowhere | unchanged |
| (2.6) evaluation | monotone integrands on a grid | weights (u+eps0)^(-1), (u+eps0)^(-2) | unchanged; two guards of the code now bind (below) |
| cover (section 3) | R increasing in q | nowhere | recomputed, adjacency asserted |
| tail (section 4) | a(q) = eps0^(-1) log log q | the family and one side condition | **rederived**: a(q) = 2 log log q, and Rosser-Schoenfeld needs log q >= 16.92 |
| zero pairing | not used | | vacuous at 1/2 |
| sigma0 > 1/2 strictly | never used | | |

No step fails. The proof needs sigma0 < 1 and nothing else about sigma0.

**(2.1) Explicit formula.** For t > 1 and real sigma >= 1 (Perron's formula
with kernel t^w / w^2, contour moved to the left; Davenport, chapters 12, 17
and 19; the proof of Lemma 2.5 of Lamzouri, Li and Soundararajan up to this
display):

    sum_{n <= t} Lambda(n) chi(n) n^(-sigma) log(t/n)
        = -(L'/L)(sigma) log t - (L'/L)'(sigma)
          - sum_rho t^(rho - sigma) / (rho - sigma)^2
          - sum_{k >= 0} t^(-2k-1-sigma) / (2k + 1 + sigma)^2.

*Derivation of the signs, not memory:* the integrand
-(L'/L)(sigma + w) t^w / w^2 has a double pole at w = 0 with residue
d/dw [ -(L'/L)(sigma + w) t^w ] at 0, a simple pole at w = rho - sigma with
residue -t^(rho - sigma) / (rho - sigma)^2, and the same at the trivial
zeros -1, -3, ... of an odd character. *Audit:* no hypothesis on the zeros,
no sigma0.

**(2.2) Two cutoffs.** Subtract the identity at y from the identity at x:
(L'/L)'(sigma) cancels. Integrate over sigma in [1, inf). With the trapezoid
weight w(n) = 1 (n <= y), log(x/n) / log(x/y) (y < n <= x), 0 (n > x), and
int_1^inf -(L'/L)(sigma) dsigma = log L(1, chi) (L(sigma, chi) > 0 on
sigma >= 1 and tends to 1):

    log L(1, chi) = sum_n Lambda(n) chi(n) w(n) / (n log n) + E,
    E = (1/(b-a)) [ sum_rho int_1^inf (x^(rho-sigma) - y^(rho-sigma)) / (rho-sigma)^2 dsigma
                    + sum_k int_1^inf (x^(-2k-1-sigma) - y^(-2k-1-sigma)) / (2k+1+sigma)^2 dsigma ],
    |E| <= ( Z(x) + Z(y) + T(x) + T(y) ) / (b - a),
    Z(t) = sum_rho int_1^inf t^(beta - sigma) |sigma - rho|^(-2) dsigma.

*Audit:* no sigma0. *Measured, as a defect function:* at seven characters
(D = -163, -427, -5923, -99991, -999983, -2383747, -562394347) the left
side minus the prime sum, computed from the exact class number, was compared
with the signed zero expression for E computed from the zeros of
L(s, chi_D) given by PARI `lfunzeros` up to height 100 to 400. The defect is
at most 7 * 10^-6, below the estimated truncation tail (2 * 10^-4 to
10^-3) and far below the trivial-zero term (about 10^-4 at y = 31), so both
signs and the trivial zeros are confirmed (`controls_zero_term.json`).

**(2.3) Positivity.** With xi(s, chi) = (q/pi)^((s+1)/2) Gamma((s+1)/2)
L(s, chi), Hadamard's product and Re B(chi) = -sum_rho Re(1/rho) give, for
real sigma > 1,

    sum_rho (sigma - beta) / |sigma - rho|^2 = (1/2) log(q/pi) + (1/2) psi((sigma+1)/2) + (L'/L)(sigma, chi)
                                             <= G(sigma),

because (L'/L)(sigma, chi) = -sum_p log p chi(p) / (p^sigma - chi(p)) is
largest when every chi(p) = -1, where it is sum_p log p / (p^sigma + 1) =
-zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma). *Audit:* no sigma0. The pole of
G at sigma = 1 belongs to the majorant (a character with chi(p) = -1 for
every p), not to xi'/xi(sigma, chi), which is finite at 1. That is why the
range 1 <= sigma <= 1 + delta is handled separately in (2.4), at every
sigma0.

**(2.4) The zero sum.** Fix t > 1, delta > 0, sigma_1 = 1 + delta. Under
H(1/2) every zero has beta <= 1/2 (in fact beta = 1/2).

- For sigma >= sigma_1: t^(beta-sigma) |sigma-rho|^(-2) =
  [t^(beta-sigma) / (sigma-beta)] (sigma-beta) |sigma-rho|^(-2), and
  beta -> t^(beta-sigma) / (sigma-beta) is increasing on beta < sigma, so the
  bracket is at most t^(1/2-sigma) / (sigma-1/2). *At 1/2 this is an
  equality:* every zero sits at beta = 1/2, so nothing is lost in beta, and
  the only loss in this range is xi'/xi <= G.
- For 1 <= sigma <= sigma_1: as a function of gamma^2 >= 0 the ratio
  |sigma-rho|^(-2) / [(sigma_1-beta) |sigma_1-rho|^(-2)] =
  ((sigma_1-beta)^2 + gamma^2) / ((sigma_1-beta)((sigma-beta)^2 + gamma^2))
  is decreasing, so it is at most its value (sigma_1-beta) / (sigma-beta)^2
  at gamma = 0. Then beta -> t^(beta-sigma) (sigma_1-beta) / (sigma-beta)^2
  has logarithmic derivative log t + 2/(sigma-beta) - 1/(sigma_1-beta) > 0
  for beta < sigma <= sigma_1, so it is at most its value at beta = 1/2,
  namely t^(1/2-sigma) (delta + 1/2) / (sigma - 1/2)^2.

Summing over rho with (2.3) at sigma and at sigma_1, and integrating with
u = sigma - 1, gives Z(t) <= R(t, delta). *Audit:* both monotonicity
statements hold for every beta < sigma, so the step is uniform in
sigma0 < 1; the factor that at 7/8 read delta + 1/8 reads delta + 1/2, and
the denominators u + 1/8 read u + 1/2. Nothing vanishes and nothing
changes sign. The trade between the pole of G(1 + delta) and the factor
delta + 1/2 now puts the optimal delta between 0.20 and 0.50, against about
1/8 at 7/8. *Measured:* at the seven characters above the true Z(t), summed
over the PARI zeros with an estimated tail, is between 0.40 and 0.80 of
R(t, delta) at both cutoffs; at the three extremal discriminants (-163,
-2383747, -562394347, each the largest of its class number) it is between
0.70 and 0.80. The majorant is valid there and not slack by more than a
third.

**(2.5) The prime sum.** For each prime the inner sum
sum_k chi(p)^k w(p^k) / (k p^k) is smallest at chi(p) = -1 (an alternating
series with nonincreasing terms), where it is at least
-w(p)/p + (a_2 - a_3) + (a_4 - a_5) with a_2 = 1/(2p^2) for p^2 <= y,
a_4 = 1/(4p^4) for p^4 <= y, a_3 <= 1/(3p^3), a_5 <= 1/(5p^5); and
sum_p w(p)/p = (1/(b-a)) int_a^b S(e^u) du. This is M(a, b). *Audit:* no
sigma0, no zeros. *Measured:* the true prime sum exceeds M at all seven
characters, by 0.23 at the extremal discriminants and by 2.4 to 3.0 at the
two with large class number.

**(2.6) Evaluation.** As in the sibling's (2.6), through its `lbound.py`
unchanged: prime sums exact below 10^7 and Rosser-Schoenfeld above; both
integrals in R as upper Riemann sums on a fixed rational grid, valid because
(u + 1/2)^(-1) and (u + 1/2)^(-2) are decreasing, psi is increasing and
sum_p log p / (p^sigma + 1) is decreasing; the tail u >= 6 in closed form.
*Audit:* the monotonicity of the weights holds for every eps0 > 0. Two
guards of the code, harmless at 7/8, now bind, and both cost sharpness and
never validity: the split point is restricted to delta <= 1/2 (binding on
the 8 cells with q <= 108), and the lower cutoff to y > 30 (binding on 1311
cells, up to q = 7.0 * 10^7, where the optimiser would take y smaller).
The float optimiser was started from five different points at nine values
of q between 10^3 and 10^12: the default start gave the best value every
time (two other starts stalled 0.002 and 0.006 lower in log L at 10^8 and
10^9). It assigns no truth: every reported number is recomputed in Arb.

Typical parameters at 1/2 (verified cells): at q = 10^9, y = e^3.54 = 34,
x = e^7.48 = 1770, delta = 0.2245, M = -1.8075, E = 0.2683,
L(1, chi) >= 0.12545; at q = 1.64 * 10^10, y = e^3.9, x = e^7.7,
M = -1.8505, E = 0.2448, L >= 0.12304. At 7/8 the same q needed
x = e^23. The cutoff is now a power of log q near 2.4, as Littlewood's
argument says it should be near 2.

## 3. Proof of Theorem C

`dtable_grh.json` covers [10^2, 10^11] by 2041 cells with
q_hi/q_lo <= 1.01. On each, parameters are chosen and Theorem B is evaluated
at q_hi, where it is weakest; then h(D) >= sqrt(q_lo) L_lower / pi for every
|D| in the cell. The code asserts that the first cell starts at 10^2, the
last ends at 10^11 and every cell starts where the previous one ended
(`bounds.assert_adjacent`; a test removes a cell and sees the assertion
fail). The verified h-bound is nondecreasing along the 2041 cells, so
D_GRH(h) is the right end of the last cell whose bound is <= h.

Beyond 10^11 the sibling used its Theorem A. Here the range is closed
explicitly: a log-scale bridge of 77 cells from 10^11 to 10^50
(log q_hi / log q_lo <= 1.02, adjacency asserted) on which the verified
h-bound is at least 12 145, and the tail lemma of section 4 from 10^50 on
(h >= 2.5 * 10^23 there, increasing). Both exceed 10 000.

## 4. Proof of Theorem A

1. **7 <= |D| <= 3 * 10^6, exact.** Every one of the 911 878 fundamental
   discriminants up to 3 * 10^6 is in the list of section 5 with its exact
   class number (the list there equals the sibling's full list, same
   sha256), and L(1, chi_D) log log |D| >= 1/3 for all of them except
   D = -3 and D = -4; the minimum from |D| = 7 on is 0.4006, at D = -163
   (`theorem_a_small.json`).
2. **22 786 <= q <= 10^50, verified cover.** 163 cells with
   log q_hi / log q_lo <= 1.02; from q = 22 786 on, Theorem B at q_hi times
   log log q_lo is at least 0.33350 (`theorem_a_grh.json`).
3. **q >= Q1 = 10^50, tail lemma, rederived at 1/2.** Take eta = 1/4,
   delta_x = delta_y = 1/10 and a(q) = 2 log log q, b = (1 + eta) a, so
   that e^(-a/2) = 1/log q exactly. Then
   - main term: Rosser and Schoenfeld's S(t) < log log t + B +
     1/(2 log^2 t) for t >= 286 applies on [a, b] as soon as
     a(q) >= log 286 = 5.656, that is log q >= 16.92. **This is the one
     side condition that the change of abscissa touches**: at 7/8,
     a = 8 log log q made it automatic; at 1/2 it holds from Q1 on because
     a(Q1) = 9.492 (asserted in code and in a test). Then
     (1/(b-a)) int_a^b S(e^u) du <= B + log a + kappa(eta) + 1/(2ab) with
     kappa(eta) = (1+eta) log(1+eta)/eta - 1 = 0.115718; the P-sums are
     nondecreasing in a;
   - zero sums: G(sigma) <= (1/2) log q + g+(sigma) with
     g+ = max(0, psi((sigma+1)/2)/2 - zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma)),
     so e^(-a/2) G(sigma) <= 1/2 + g+(sigma)/log q and
     R(y) <= (delta + 1/2)(1/2 + g+(1+delta)/log q) int_0^delta e^(-ua) (u + 1/2)^(-2) du
     + int_delta^inf e^(-ua) (1/2 + g+(1+u)/log q) (u + 1/2)^(-1) du,
     every factor nonincreasing in q; R(x) has the extra factor
     (log q)^(-eta); T and 1/(b-a) = 1/(eta a) decrease.

   Every piece is bounded by its value at Q1, so log L(1, chi) >=
   K1 - log a(q) with K1 = -B - kappa - 1/(2 a1 b1) + P2(a1) - E~(Q1) =
   -0.259504, where P2(a1) = 0.179250 and E~(Q1) = 0.057100 (Arb). Hence
   L(1, chi) >= e^K1 / (2 log log q) >= 0.38571 / log log q for q >= 10^50.

Together: 1/3 from |D| = 7 on, for L; the class-number form follows from
Dirichlet's formula for D < -4 and is checked directly at D = -4 (the right
side is 0.65).

*Remark.* The tail family is less efficient at 1/2 than at 7/8, as it must
be: the zero term is of order 1/(eta a^2) and a is 2 log log q instead of
8 log log q. At 10^50 it costs 0.057 in log L, and with kappa = 0.116 the
constant is 0.3857, which is 83.5% of Littlewood's limit 0.4618; at
Q1 = 10^200 the same family gives 0.3973 (measured in Arb, not used).

## 5. The class-number computation

Exact integer arithmetic, no GRH, no floating point in any decision.

**Why not the sibling's program as it stands.** `cn.c` was timed first at
H = 5000 (RUNS.md): 23.6 s per 10^6 of range at 5 * 10^8, more than 20
CPU-hours for the whole range. Its streamed filter was tuned for H <= 1500,
and every listed field pays a scalar exact count of 40 to 110 microseconds;
at H = 5000 the list has 10^8 fields. `cnx.c` keeps the arithmetic and
replaces the driver: it includes `cn.c` unchanged (its `build_pattern`,
`chi`, `r_of`, `exact_h` are the sibling's own code) and adds three things.

- **Blocks and saturating counters.** Blocks of 2^19 integers, so the uint16
  counters of the three progressions (n = 3 mod 4, n = 4 and 8 mod 16) stay
  in the L2 cache; one cached periodic pattern of r(a) per a and
  progression; saturating adds, so a counter holds min(count, 65 535) and
  never a wrapped value.
- **Mode 1, |D| <= 3 * 10^9: every class number at once.** For a block
  starting at s, r(a) is streamed for every a with 4a^2 < s; for those a the
  number of reduced forms with first coefficient a is exactly r(a), for
  every n in the block (the sibling's section 5). Every reduced form with a
  larger first coefficient is then enumerated directly: for a from the first
  a with 4a^2 >= s to sqrt(e/3), b from 0 to a, and c >= a, the form
  (a, b, c) has discriminant -n with n = 4ac - b^2, and it is added at n
  with weight 2 (for the pair +-b) unless b = 0, b = a or c = a, where the
  weight is 1 (the reduction conditions). For fixed (a, b) the n are an
  arithmetic progression in c, so this is a strided increment. After it the
  counter is h(D) for every fundamental D in the block, and no
  per-discriminant stage exists. Cost: about 0.5 sqrt(n / 10^9) seconds per
  10^6 of range, 70 times faster than `cn.c` at 5 * 10^8.
- **Mode 0, |D| > 3 * 10^9: filter, then the sibling's exact count.** r(a)
  is streamed for every a <= A0 and for the primes in (A0, sqrt(s)/2); a
  discriminant whose partial count is <= 5000 goes to `exact_h`. A0 falls
  from "all a" at 3 * 10^9 to "primes only" above 1.4 * 10^10. The partial
  count is a lower bound for h(D), so the filter can only lose a field by
  over-counting.

**Checks of the new driver.** Mode 1 against brute-force reduced-form
counting for every fundamental |D| <= 6000; mode 1 output byte-identical to
`cn.c` output on [3, 2 * 10^6], [10^7, 1.2 * 10^7], [10^8, 1.02 * 10^8] and
[5 * 10^8, 5.2 * 10^8] (2 877 575 fields); every mode 1 class number against
`exact_h` on four windows up to 2.9 * 10^9 (212 769 discriminants,
`CNX_CHECK_FULL=1`); mode 1 against mode 0 on [3 * 10^9, 3.002 * 10^9]
(byte-identical, 1019 fields); 28 496 sampled streamed counts in four
windows between 3.2 * 10^9 and 1.4 * 10^10 recomputed with Jacobi symbols
and no patterns (`CNX_CHECK_STREAM`). The completed run is then checked
against every outside table (section 6).

@@RUN@@

## 6. Controls

**(a) The bound against exact L(1, chi_D). Any violation kills the hunt.**
@@CONTROL_A@@

**The two halves separately, against real zeros** (`controls_zero_term.json`;
measured, not an enclosure). The composite control (a) cannot tell a bound
that is right from one whose two errors cancel, so the inequality
log L = (prime sum) + E, prime sum >= M, |E| <= E_bound was taken apart at
seven characters, with the zeros of L(s, chi_D) from PARI `lfunzeros` (all
on the critical line, up to height T):

| D | h | zeros | lowest gamma | identity defect | prime sum - M | E true / E bound | Z(x)/R(x) | Z(y)/R(y) | L exact / bound |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| -163 | 1 | 525 | 0.2029 | -3.2e-6 | 0.265 | -0.0214 / 0.1761 | 0.697 | 0.721 | 1.522 |
| -427 | 2 | 426 | 0.2499 | 4.3e-6 | 0.475 | -0.0028 / 0.1847 | 0.624 | 0.656 | 1.930 |
| -5923 | 7 | 552 | 0.1548 | -4.1e-6 | 0.488 | -0.0418 / 0.2064 | 0.645 | 0.684 | 1.921 |
| -99991 | 205 | 445 | 0.5388 | -3.3e-6 | 2.406 | 0.0314 / 0.2286 | 0.420 | 0.474 | 14.39 |
| -999983 | 1171 | 518 | 0.5646 | -2.0e-6 | 3.036 | 0.0146 / 0.2419 | 0.404 | 0.462 | 26.91 |
| -2383747 | 98 | 403 | 0.0891 | -2.5e-6 | 0.233 | -0.0908 / 0.2472 | 0.753 | 0.793 | 1.476 |
| -562394347 | 1489 | 349 | 0.0437 | -7.0e-6 | 0.230 | -0.0507 / 0.2673 | 0.757 | 0.803 | 1.563 |

Reading: the identity of (2.2) holds to the truncation of the zero sum (the
trivial-zero part of E is 1.3 to 2.5 * 10^-5, so at D = -163 the defect is
eight times below it and its sign is resolved); the true prime sum is above
M everywhere; the true absolute zero sum Z is below the bound R at both
cutoffs, by a factor 1.25 to 1.43 at the three extremal discriminants. The
extremal discriminants are exactly the ones with a very low zero (0.04 to
0.20), which is the worst case gamma = 0 that (2.4) charges.

**A second route for the evaluation** (`controls_independent.json`). At six
cells from q = 163 to 10^11, Theorem B's right side was recomputed with
mpmath (a direct prime sum, adaptive quadrature of both integrals, zeta
from mpmath) in place of the sibling's Arb tables and upper Riemann sums.
M agrees to 10^-15; the Arb values of R are 1.00080 to 1.00086 times the
quadrature values, the grid loss and nothing more; the Arb bound for log L
is 0.00015 to 0.00022 below the second route, on the safe side.

**(b) Against the published GRH bound** (`controls_lls.json`): Lamzouri, Li
and Soundararajan, Theorem 1.5, valid for every q >= 3 by Languasco and
Trudgian. This hunt's bound is the stronger one on every one of the 2118
cells from 10^2 to 10^50, and at 10^100; nowhere is the published bound
stronger.

| q | this hunt | LLS / L-T | ratio |
| --- | --- | --- | --- |
| 10^2 | 0.16399 | 0.06966 | 2.35 |
| 10^4 | 0.14732 | 0.07890 | 1.87 |
| 10^6 | 0.13672 | 0.08436 | 1.62 |
| 10^8 | 0.12877 | 0.08749 | 1.47 |
| 10^10 | 0.12357 | 0.08933 | 1.38 |
| 10^11 | 0.12117 | 0.08994 | 1.35 |
| 10^20 | 0.10786 | 0.09123 | 1.18 |
| 10^50 | 0.09138 | 0.08646 | 1.06 |
| 10^100 | 0.08142 | 0.08016 | 1.016 |

A margin of 35 to 47% over a published bound in the range that matters is
the kind of result this control exists to distrust. Three facts account for
it. First, the published bound is not monotone (it rises until 10^20 and
then falls): its term 14 log log q / log q is a uniform simplification, 40%
of the bracket at 10^9. Second, the two bounds converge, 1.016 at 10^100, as
two correct forms of Littlewood's inequality must. Third, and decisive, the
margin cannot come from an under-counted zero term: the zero term here is
within a factor 1.25 to 1.43 of the true absolute zero sum at the extremal
discriminants (table above), and the composite bound stays below every
exact value (control (a)). In units of log(1/L) at q = 5.6 * 10^8:
published 2.427, this hunt 2.070, the truth at the extremal discriminant
-562394347 is 1.623. Cutoffs: h <= 5000 forces |D| <= 16 396 235 837 here,
30 702 866 530 by inverting the published bound, 43 651 697 617 by Cremona
and Sutherland's Proposition 19.

**(c) Monotonicity in sigma0** (`controls_ladder.json`). The cover here and
the sibling's 7/8 cover have the same 2041 cells; on every cell the bound at
1/2 is the larger, by a factor between 2.52 (at q = 100) and 2.92. At
identical parameters (those optimal for 1/2 and those optimal for 7/8, 82
points) the three values at 1/2, 3/4 and 7/8 are strictly ordered, as
R(t, delta) decreasing in eps0 requires.

**(d) A planted fault** (`controls_fault.json`).
@@CONTROL_D@@

**Class numbers.**
@@CONTROL_CN@@

## 7. The delta against the literature

Provenance of this section. The papers marked (notes) were read from their
primary PDFs on 2026-11-20 by the literature step of the same workflow run,
and are quoted here from its notes; this hunt did not re-read them. Watkins
2004 and Littlewood 1928 were read by neither (secondary). The search behind
"not found" was one extended web search; no zbMATH or OEIS search was run.

- **Littlewood (1928)**, GRH: L(1, chi) >= (1 + o(1)) zeta(2) / (2 e^gamma
  log log q). **Lamzouri, Li, Soundararajan**, Math. Comp. 84 (2015)
  2391-2412, Theorem 1.5: the explicit form for q >= 10^10 (notes).
  **Languasco and Trudgian**, J. Number Theory 236 (2022), arXiv:2011.08348,
  Theorem 1 and Corollary 1: the same inequalities for every q >= 3, and the
  class-number bound for every q >= 5 (notes). *Delta:* the bound here is
  larger on every cell of the cover: by 47% at 10^8, 38% at 10^10, 35% at
  10^11, 18% at 10^20, 6% at 10^50 and 1.6% at 10^100, where the two share
  Littlewood's limit. Inverting their bound gives |D| <= 30 702 866 530 for
  h <= 5000, against 16 396 235 837 here. The difference sits in the zero
  term, and section 6 says why it is not a bug.
- **Garcia, Grenie, Lee, Molteni**, arXiv:2610.14257v1 (9 October 2026)
  (notes): h_K >= (pi / (12 e^gamma)) sqrt|Delta| e^(-3 / ln ln |Delta|) /
  ln ln |Delta| under GRH, with cutoffs (1, 1 592), (100, 19 124 734),
  (2000, 8 213 527 466), and the complete list of imaginary quadratic fields
  with class number <= 2000 under GRH, with data, computed with PARI/GP.
  **This is the published frontier found for complete lists over all h.**
  *Delta:* the cutoffs here are 399, 5 554 909 and 2 576 135 045 (4.0, 3.4
  and 3.2 times smaller); the lists here go on to h = 5000
  (@@N5000@@ fields against their 16 453 493, so @@NABOVE@@ fields with
  2000 < h <= 5000); the class numbers here come from exact reduced-form
  counting, which assumes nothing; and all 20 rows of their Table 1 (count
  and largest discriminant for h <= 100, 200, ..., 2000) are reproduced
  exactly.
- **Cremona and Sutherland**, arXiv:2301.11169v4 (notes): Proposition 19
  (the cutoff 1 629 085 093 for h <= 1000, from Languasco-Trudgian) and
  section 5: 4 115 897 fundamental discriminants with h <= 1000, the largest
  227 932 027 with h = 996. Reproduced. They remark that the same approach
  with the Mosunov-Jacobson table would reach h <= 24 416 "but we did not
  attempt this"; with the bound of this hunt that number is 39 504 (a door
  below, not done).
- **Mosunov and Jacobson**, Math. Comp. 85 (2016), arXiv:1502.07953 (notes,
  abstract): unconditional class groups for all |Delta| < 2^40. Whether the
  per-discriminant data can be downloaded is reported inconsistently by the
  two papers above; not checked here.
- **Holmin, Jones, Kurlberg, McLeman, Petersen**, arXiv:1510.04387 (notes):
  F(h) for every odd h < 10^6 under GRH, used twice (the cutoff, and PARI's
  `quadclassunit0`). *Delta:* all 2500 odd h < 5000 agree (9 681 947
  fields), 1750 of them beyond the sibling hunt's range, by a computation
  that uses GRH only for the cutoff; and this hunt adds every even h.
- **Watkins (2004)** (secondary): the unconditional lists for h <= 100.
  Reproduced (42 272 fields, all 100 counts and largest discriminants).
- **`hunts/qrh_class_number`** (this lab, 2026-10-08): the 7/8 half-plane,
  h <= 1500. *Delta:* a cutoff 8.1 to 8.8 times smaller, lists to h = 5000,
  and the h <= 1500 lists identical line for line (same sha256).

Not found: a complete list over all h above 2000 under any hypothesis, or an
explicit GRH lower bound for L(1, chi_D) at finite q stronger than
Languasco-Trudgian. Absence in this search is a statement about the search,
not a novelty claim. Within the searched set, **the table D_GRH(h), the
constant 1/3 of Theorem A and the GRH-conditional lists for
2000 < h <= 5000 are original to this hunt (provenance)**, at the grade
stated at the top, and pending external review.

## 8. Not done

- **The hypothesis.** GRH for chi_D is assumed, not proved. The archive of
  2026-11-20 was not read, replayed or checked, and no kernel has accepted
  it so far.
- **External review.** The written proof (the sibling's section 2 and
  section 2 here) has been read by no human mathematician. The audit here is
  by the same lab that wrote the proof; the zero-term control measures the
  inequality at seven characters, it does not prove it.
- **Formalisation.** Nothing here is in Lean; the Arb evaluation is the
  numerical layer, not a kernel check.
- **Even h above 2000 have no outside table.** For odd h every count is
  compared with Holmin-Kurlberg, and up to 2000 with Garcia-Grenie-Lee-
  Molteni. For even h in (2000, 5000] the evidence is internal: the same
  code path as the odd h, the windows against PARI and against the sibling's
  exact count, and the stream recomputation.
- **PARI is a cross-check, not an oracle.** `qfbclassno` is documented as
  not rigorous for every discriminant; `lfunzeros` finds zeros on the line
  and does not prove it has all of them.
- **Orders and group structures.** Only fundamental discriminants (maximal
  orders) and only class numbers, not class-group structures.
- **The full lists are not committed** (about 1.6 GB); their sha256 and the
  commands that regenerate them are.
- **The literature was not re-read here**, and the Mosunov-Jacobson data
  and the Molteni data file were not downloaded.

## The doors

The hunt stops at H = 5000 because the task capped it there and the budget
fits it, not at a mathematical wall. What binds, and what would move it:

1. **Active constraints at the optimum**, ranked by shadow price at the
   h = 5000 cutoff (q = 1.64 * 10^10, where log L >= M - E with
   M = -1.8505, E = 0.2448).
   (a) The abscissa is no longer a door: 1/2 is the end of that line, and
   moving from 7/8 to it paid a factor 2.5 to 2.9 in L and 8.1 to 8.8 in
   D(h), as the sibling predicted. (b) The zero term E: dropping it
   entirely would multiply L by e^0.245 = 1.28 and D_GRH(5000) by 0.61. It
   is bounded in absolute value through the majorant G; measured at the
   extremal discriminants, the true absolute sum Z is 0.70 to 0.80 of the
   bound R, and the true signed E is only 0.12 to 0.37 of the bound, so
   most of what is lost is lost by taking absolute values, not by the
   majorant. (c) The worst-case prime sum M, which lets chi(p) = -1 at every
   prime up to x = 2200: at the extremal discriminants the true prime sum is
   0.23 above M, a factor 1.26 in L and 0.63 in D. (b) and (c) together are
   the whole measured margin, L_exact / L_bound = @@WORST@@ at worst, and
   they are about equal. (d) On the computation side the cost grows like
   H^3: mode 1 like X^(3/2), the filter like X * H. H = 5000 cost
   @@CPU@@ CPU-hours; H = 10 000 (X = 6.7 * 10^10) extrapolates to about 8
   times that.
2. **Frozen-constant inventory.** sigma0 = 1/2 (the hypothesis; cannot
   move). The trapezoid weight with two cutoffs (a genuine trade: more
   cutoffs spread the y-term of E, which is 90% of E, at a cost in M). The
   guards y > 30 and delta <= 1/2 of the sibling's `lbound.py`, which now
   bind for q <= 7.0 * 10^7 and q <= 108 (genuine trade for small h only:
   they are why D_GRH(1) = 399 and not lower; not relaxed because the
   sibling is imported unchanged). The grid steps 1/2000, 1/500, 1/100 and
   the tail point u = 6 (0.09% in R, measured against adaptive quadrature;
   no trade shape). The prime-power
   truncation at k = 5 (none). T_EXACT = 10^7 (irrelevant at 1/2: x is below
   10^4). The cover ratio 1.01 (at most 1% in D_GRH; a trade against Arb
   time, 80 s now). The bridge ratio 1.02 and the tail point Q1 = 10^50 with
   eta = 1/4, delta = 1/10 (these set 0.3857; 0.3973 needs 10^200; a genuine
   trade between the constant and the size of the cover). The constant 1/3
   of Theorem A (binding at q = 22 786, where the cover gives 0.3335 and the
   exact range above it is not used; with exact values to 10^8 the cover
   would support 0.37). In the search: the block size 2^19, the mode switch
   at 3 * 10^9 and the composite caps A0 per zone (speed only, never
   correctness), and the uint16 counters that saturate at 65 535 (H at most
   20 000 without widening them).
3. **Information class of each door.**
   *Stays inside the data the method reads (GRH for chi_D and the primes):*
   a weight whose transform is nonnegative on the critical line. Under GRH
   every zero is at 1/2 + i gamma, so such a weight makes every zero
   contribute with one sign and the zero sum could be dropped instead of
   bounded: that is door (b) above, it exists only at abscissa 1/2 (off the
   line the sign is lost, which is why the sibling could not have it), and
   it has not been derived here. It trades against the prime side, because
   positivity constrains the weight. Also inside: more cutoffs, and relaxing
   the two guards.
   *Reads more:* the Mosunov-Jacobson unconditional table to 2^40. A
   log-scale cover from 2^40 and the tail give h(D) >= 39 504 for every
   |D| >= 2^40 under H(1/2) (`door_2_40.json`, Arb-enclosed), so their
   class numbers would complete the lists for every h <= 39 504, against
   the 24 416 that Cremona and Sutherland state for the Languasco-Trudgian
   bound. It needs their per-discriminant output, or an exact sieve to
   1.1 * 10^12, about 500 times this run. Also reading more: zero data for
   individual characters, which the method does not use at all.
   *Outside both:* a kernel check of the archive of 2026-11-20, which would
   discharge the hypothesis and change nothing in the mathematics here.

A measured optimum is not a proved ceiling: the constants here are the best
the float optimiser found within this family of weights and grids, at the
stated q, with no proof that the family is optimal. The top door above has
no automatic priority; allocation is the owner's decision.
