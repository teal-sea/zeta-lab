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

**Update (2026-11-21).** The hypothesis is no longer open. Levent Alpoge's
Lean archive was verified outside this laboratory on 2026-11-21 (the joint
statement of the Lean and Mathlib communities, and Andrew Sutherland's
verification page; ROADMAP.md, "Decision: build on the Alpoge theorem
(2026-11-21)"). H(1/2) for every chi_D is contained in the third of its five
verified statements, the one for every Dirichlet L-function at Re s > 1/2;
the bridge that chi_D is a Dirichlet character whose Mathlib L-function is
L(s, chi_D) remains routine and unwritten here. Every result below is
therefore now stated as *proved, given the Alpoge theorem*. Its weakest step
is the written proof (sections 2 and 4, audited at sigma0 = 1/2), which no
person has reviewed, so it stays a candidate pending external review. The
kernel grade of the theorem is the outside checkers'; this laboratory's own
replay had not produced its verdict when this update was written. The
published list to 2000 of Garcia, Grenie, Lee and Molteni loses its GRH
hypothesis in the same way, for the bounds it uses (GRH for zeta_K of an
imaginary quadratic K, which is zeta times L(s, chi_D)); whether its list
below the cutoff also rests on a GRH-conditional routine is open, as row D02
of `docs/reviews/2026-11-20-rh-claim-regrade-board.md` records. The text
below is kept as written on 2026-11-20: where it says the hypothesis "is not
a theorem" or that the replay is pending, read it as the state of that day.

**After review (2026-11-20).** Two independent reviewers attacked this hunt,
one on the proof and one on the computation; both returned "holds" and
neither found a wrong or missing field or a failed step. Their eleven
findings and what was done about each are in section 9. Nothing above was
downgraded. What changed: the reviewer's full-range independent sweep is now
a committed control (`sweep.py`, `lsieve.c`, `controls_sweep.json`), the
list for h <= 2000 is compared field by field with Molteni's data file, the
planted-fault controls state what they cannot see, section 2.6 now describes
the stalled cover cells correctly (the table D_GRH(h) is a valid cutoff
everywhere, and 1 to 2% weaker than Theorem B allows for about
400 < h <= 2760), and the first door is now a different classical route that
measures 7 to 16% stronger in L than Theorem B (float grade, not adopted).
Hand-back was blocked on one shared-file item outside this directory, the
case-log entry for this hunt in `hunts/README.md`. That entry was added the
same day when the hunt was landed, and the case-log test passes.

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
GRH-conditional theorems whatever happens to that claim. A replay of the
archive is in progress in another session (`hunts/alpoge_replay/`, on
another branch); it is pending and this hunt states no verdict on it. The
hypothesis would be discharged only by a kernel check of that statement with
zero sorrys and standard axioms only, together with the bridge that chi_D is
a Dirichlet character mod |D| whose Mathlib L-function is L(s, chi_D)
(routine, but not written here); the weakest step would then be this hunt's
written proof.

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
h <= 10 000. The table is a valid cutoff everywhere; it is not the smallest
cutoff Theorem B gives, because the cover stalled on some cells (section
2.6). Selected values, with the 7/8 table of the sibling hunt:

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

- there are 102 746 940 fields in all; the largest discriminant is
  D = -6 912 348 787 (h = 4967); every h <= 5000 occurs; 9 681 947 of the
  fields have odd class number and 93 064 993 even;
- 86 293 447 of them have 2000 < h <= 5000: the delta against the published
  frontier (Garcia, Grenie, Lee and Molteni, every h <= 2000 under GRH) is
  the range 2000 < h <= 5000 (section 7);
- for h <= 2000 the list has 16 453 493 fields, the largest
  D = -1 062 350 083, the same count and the same largest discriminant as
  the GRH list of Garcia, Grenie, Lee and Molteni, in each of the 20 rows of
  their table, and the same set of discriminants for every h <= 2000 as
  Molteni's per-field data file (16 453 493 fields, `controls_molteni.json`);
- for every odd h < 5000 the count equals the GRH-conditional count of
  Holmin and Kurlberg (2500 values of h, computed by a different method);
- for h <= 1500 the list is line for line the sibling hunt's list under the
  7/8 half-plane (same sha256), and for h <= 100 it is Watkins'.

The full list is reproducible with
`python -m hunts.grh_class_number.search run 5000 16396235837 OUTDIR` and
`... summarise 5000 16396235837 OUTDIR`; its sorted text ("|D| h" per line,
1.5 GB) has sha256
`7bc67e064addc52f724682806b42894e8267556a4a949b7918edfd106ae6b421`. The
sub-lists have sha256 `07100ea3589ab2b490122fa69b438cd5393bdcd2e547dfc29bb3b5c86f9f24c0`
(h <= 2000), `c373d7c67bbecb922878481c50e6273f03ed07b93fc968a458bb0bf5389ee101`
(h <= 1500) and `075a201c8e7cce6c0b6013423a5d96c6308452afab2fa79882388fc46d8b0c45`
(h <= 1000); the last two are the sibling hunt's hashes. The counts F(h), the
largest |D| and the largest squarefree k for each h are in
`search_H5000.json`.

## 2. The proof audit at sigma0 = 1/2

The sibling's proof (its RESULTS.md, section 2) is written for a general
abscissa sigma0 with eps0 = 1 - sigma0, and its code takes sigma0 as a
parameter. A parameter that was exercised at 1/2 only as one calibration row
is not a proof at 1/2, so every step is restated here for sigma0 = 1/2, with
what it uses and what was checked. Verdict first:

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
zeros -1, -3, ... of an odd character. *The contour shift, written out
(review finding P1):* for c > 1 - sigma,
(1/(2 pi i)) int_(c) -(L'/L)(sigma + w) t^w / w^2 dw equals the left side
(expand -(L'/L) as a Dirichlet series and use
(1/(2 pi i)) int_(c) (t/n)^w / w^2 dw = log(t/n) for n <= t and 0 for n > t).
Move the line to Re(sigma + w) = -2K with K -> infinity through the
integers (the trivial zeros of an odd character sit at -1, -3, ..., so
these lines stay half-way between two of them), closing with horizontal segments at
heights +-T_j chosen at distance >> 1/log(q T_j) from every ordinate.
On such segments and lines (L'/L)(s) = O(log^2(q |s|)) (Davenport, chapters
17 and 19; on the far line through the functional equation), so the
horizontal integrals are O(t^c log^2(q T) / T^2) -> 0 and the far vertical
line contributes O(t^(-K) K^(-1) log K) -> 0 for t > 1. Every residue above
is then collected exactly once, and the sum over rho converges absolutely
because |rho - sigma|^(-2) is summable against N(T) = O(T log qT). This is the
standard route (the same display is the start of the proof of Lemma 2.5 of
Lamzouri, Li and Soundararajan); it is written here, not reviewed by a human.
*Audit:* no hypothesis on the zeros, no sigma0. The proof reviewer re-derived
the four terms and their signs by the same residue computation and measured
the identity at three characters this hunt did not use (D = -7, -1000003,
-6623767483: defects -3.4e-6, -3.3e-6 and +7.9e-6, against |E| of 0.0020,
0.0264 and 0.0437); those three numbers are the reviewer's run, not
repeated here.

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
10^-3) and below the trivial-zero part of E (1.3 to 2.5 * 10^-5; at
D = -163 the defect is eight times smaller than it), so the signs of both
sums are confirmed (`controls_zero_term.json`, table in section 6).

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
characters, by 0.23 to 0.27 at the three extremal discriminants and by 2.4
to 3.0 at the two with large class number.

**(2.6) Evaluation.** As in the sibling's (2.6), through its `lbound.py`
unchanged: prime sums exact below 10^7 and Rosser-Schoenfeld above; both
integrals in R as upper Riemann sums on a fixed rational grid, valid because
(u + 1/2)^(-1) and (u + 1/2)^(-2) are decreasing, psi is increasing and
sum_p log p / (p^sigma + 1) is decreasing; the tail u >= 6 in closed form.
*Audit:* the monotonicity of the weights holds for every eps0 > 0. Two
guards of the code, harmless at 7/8, now bind, and both cost sharpness and
never validity: the split point is restricted to delta <= 1/2 (the
optimiser sits on that cap on the 8 cells with q <= 115), and the lower
cutoff to y > 30 (it sits on that floor on 1311 cells, up to
q = 7.0 * 10^7).
*The optimiser and the stalled cells (corrected after review).* The cover
does not restart the float optimiser on each cell: `explicit.cover` warm-starts
every cell from the previous cell's optimum. From q = 2.99 * 10^7 to
4 967 973 832 (514 cells) it stays in a local optimum with the lower cutoff
y below 49, so p = 7 never enters the prime-square sum; at 4 967 973 832 it
jumps to y = e^3.9 = 49.4 and the bound rises by 0.76% from one cell to the
next. A restart at a = 3.9 does better on these cells: on the cell
[991 098 295, 1 001 009 278] the committed parameters (a = 177/50,
b = 187/25) give log L >= -2.075849, and a = 39/10, b = 751/100 give
-2.070110 in Arb, that is L >= 0.12617 against 0.12545 (pinned by a test).
Because the bound at a larger q is valid at every smaller q, 76 committed
cells are also beaten by a later cell of the same table (pinned). Each cell's
value is still an Arb-enclosed lower bound, so the table D_GRH(h) is a valid
cutoff; it is weaker than Theorem B allows. The proof reviewer restarted
every cell in Arb and measured the cost (reviewer's run, not repeated here):
D_GRH(1000) 620 886 399 against 614 739 008, D_GRH(1500) 1 432 212 849
against 1 418 032 523, D_GRH(2000) 2 576 135 045 against 2 525 375 006,
D_GRH(2500) 4 071 475 474 against 3 991 251 321, that is 1 to 2% for about
400 < h <= 2760, and D_GRH(1), D_GRH(100), D_GRH(5000) and D_GRH(10 000)
unchanged. So the search range and Corollary D are untouched, and the
search below 3 * 10^9 already exceeds what the smaller cutoffs would demand.
The table was not regenerated in this pass. The earlier sentence here, that
the default start gave the best value at nine values of q and two other
starts stalled at 10^8 and 10^9, described a separate experiment with the
default start, not the cover, whose cells at 10^8 and 10^9 are exactly those
stalled values; it was wrong as a description of the table and is withdrawn.
The optimiser assigns no truth: every reported number is recomputed in Arb.

Typical parameters at 1/2 (verified cells): at q = 10^9 the committed cell
has y = e^3.54 = 34, x = e^7.48 = 1770, delta = 0.2245, M = -1.8075,
E = 0.2683, L(1, chi) >= 0.12545 (a stalled cell; a restart gives 0.12617,
above); at q = 1.64 * 10^10, y = e^3.9, x = e^7.7, M = -1.8505, E = 0.2448,
L >= 0.12304. At 7/8 the same q needed
x = e^23. The cutoff is now (log q)^2.45; Littlewood's argument puts it
near (log q)^2.

## 3. Proof of Theorem C

`dtable_grh.json` covers [10^2, 10^11] by 2041 cells with
q_hi = ceil(1.01 q_lo), so q_hi/q_lo <= 1.0198 (the largest is the cell
[101, 103]). On each, parameters are chosen and Theorem B is evaluated
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
2. **22 786 <= q <= 10^50, verified cover.** The cover in
   `theorem_a_grh.json` has 163 cells from q = 100 to 10^50 with
   log q_hi / log q_lo <= 1.0213. On the first 39 cells (q_hi <= 22 786)
   Theorem B at q_hi times log log q_lo falls below 1/3; that range is
   covered by item 1. On the other 124, from q = 22 786 on, it is at least
   0.33350, attained on the cell [22 786, 27 850], only 0.00017 above 1/3 and
   inside the exact range of item 1 anyway.
3. **q >= Q1 = 10^50, tail lemma, rederived at 1/2.** Take eta = 1/4,
   delta_x = delta_y = 1/10 and a(q) = 2 log log q, b = (1 + eta) a, so
   that e^(-a/2) = 1/log q exactly. Then
   - main term: Rosser and Schoenfeld's S(t) < log log t + B +
     1/(2 log^2 t) for t >= 286 (Rosser and Schoenfeld 1962, Theorem 5; the
     equation number was not confirmed against the paper in this pass; the
     inequality was measured at every prime from 286 to 3 * 10^6, smallest
     margin 0.00112 at 293, and it fails at 283, as the threshold predicts:
     float grade, a test) applies on [a, b] as soon as
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
Q1 = 10^200 the family with delta = 1/25 gives 0.3973 (computed in Arb
while choosing the parameters; not committed, not used).

## 5. The class-number computation

Exact integer arithmetic, no GRH, no floating point in any decision.

**Why not the sibling's program as it stands.** `cn.c` was timed first at
H = 5000 (RUNS.md): 23.6 s per 10^6 of range at 5 * 10^8 and 17.5 at
2 * 10^9, more than 20 CPU-hours for the whole range. Its streamed filter was tuned for H <= 1500,
and every listed field pays a scalar exact count of 10 to 110 microseconds;
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
counting for every fundamental |D| <= 6000; mode 1 output identical, as
sorted lists, to `cn.c` output (which is written per progression and ends
with a stats line, so it is sorted and that line dropped before comparing) on [3, 2 * 10^6], [10^7, 1.2 * 10^7], [10^8, 1.02 * 10^8],
[5 * 10^8, 5.2 * 10^8] and [2 * 10^9, 2.02 * 10^9] (2 946 395 fields); every
mode 1 class number against
`exact_h` on four windows up to 2.9 * 10^9 (212 769 discriminants,
`CNX_CHECK_FULL=1`); mode 1 against mode 0 on [3 * 10^9, 3.002 * 10^9]
(byte-identical, 1019 fields); 28 496 sampled streamed counts in four
windows between 3.2 * 10^9 and 1.4 * 10^10 recomputed with Jacobi symbols
and no patterns (`CNX_CHECK_STREAM`). The completed run is then checked
against every outside table (section 6).

**The run** (`search.py run 5000 16396235837`, three workers, 42.6 minutes
of wall clock, 1.69 CPU-hours against an estimate of 1.81 written before
launch): 194 chunks, every one a checkpoint. 4 983 858 175 fundamental
discriminants with |D| <= D_GRH(5000) = 16 396 235 837. Below 3 * 10^9
(60 chunks, mode 1) every class number was computed and 102 516 219 are at
most 5000. Above (134 chunks, mode 0) 881 843 discriminants survived the
filter and 230 721 of them have h <= 5000. The summary recounts everything
from the list files with numpy, independently of the C program's own
histogram, and the two agree.

| h range | fields | largest abs(D) | its h | D_GRH(h_max) | D_GRH(h_max) / largest |
| --- | --- | --- | --- | --- | --- |
| h <= 100 | 42 272 | 2 383 747 | 98 | 5 554 909 | 2.33 |
| h <= 200 | 167 157 | 8 377 363 | 198 | 23 048 174 | 2.75 |
| h <= 500 | 1 028 749 | 55 171 603 | 494 | 151 139 146 | 2.74 |
| h <= 1000 | 4 115 897 | 227 932 027 | 996 | 620 886 399 | 2.72 |
| h <= 1500 | 9 245 562 | 562 394 347 | 1489 | 1 432 212 849 | 2.55 |
| h <= 2000 | 16 453 493 | 1 062 350 083 | 1978 | 2 576 135 045 | 2.42 |
| h <= 2500 | 25 708 497 | 1 595 778 787 | 2496 | 4 071 475 474 | 2.55 |
| h <= 3000 | 36 993 853 | 2 562 211 723 | 2976 | 5 767 663 399 | 2.25 |
| h <= 3500 | 50 299 869 | 3 495 584 467 | 3477 | 7 930 195 043 | 2.27 |
| h <= 4000 | 65 772 833 | 4 522 161 403 | 3996 | 10 374 351 574 | 2.29 |
| h <= 4500 | 83 205 069 | 5 683 027 267 | 4465 | 13 172 673 663 | 2.32 |
| h <= 5000 | 102 746 940 | 6 912 348 787 | 4967 | 16 396 235 837 | 2.37 |

The last column is the price of the analytic bound: the search goes about
2.4 times further than the last field it finds. Under the 7/8 half-plane
that factor was 24.

## 6. Controls

**(a) The bound against exact L(1, chi_D). Any violation kills the hunt.**
For every listed field with |D| >= 100 (102 746 909 fields) the exact
L(1, chi_D) = pi h / sqrt|D| was compared with the Arb-enclosed lower bound
of the `dtable_grh.json` cell containing |D|. No violation. The smallest
ratio exact / bound is **1.449**, at D = -6 623 767 483 (h = 4656,
L = 0.17973 against the bound 0.12402); one field is below 1.45, 20 are
below 1.50 and 472 below 1.60 (`controls_exact_l.json`). And because every
unlisted fundamental discriminant below 16 233 896 868 has h > 5000 while
sqrt|D| * bound / pi is at most 5000 there, the bound holds at **every one
of the 4 934 512 971 fundamental discriminants with
100 <= |D| <= 16 233 896 868**, not only at the listed ones. Under the 7/8
half-plane the same control had a margin of 3.9; at 1/2 it has 1.45, so it
is a much sharper test of the proof than it was, and it passes. *Its
detection floor:* by the same token this control cannot see any error that
raises the bound by less than the factor 1.449 in L, about 2.1 in D. Planted
at the largest |D| of every h, dropping the zero term altogether (exp(M))
leaves the smallest ratio at 1.1206 and halving it at 1.2816: both stay
green (`controls_fault.json`, a test). The size of the zero term, which
fixes the search cutoff, is therefore checked only by the seven-character
zero-term control below and by the written proof.

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
-562394347 is 1.623. Fourth, and found only in review: Theorem 1.5 is a
closed-form simplification of a route that is itself stronger than this
hunt's bound when it is evaluated numerically instead of in closed form
(`lls_route.py`, float grade, the first door below). The margin over the
published bound is a margin over its closed form, not over its method. Cutoffs: h <= 5000 forces |D| <= 16 396 235 837 here,
30 702 866 530 by inverting the published bound, 43 651 697 617 by Cremona
and Sutherland's Proposition 19.

**(c) Monotonicity in sigma0** (`controls_ladder.json`). The cover here and
the sibling's 7/8 cover have the same 2041 cells; on every cell the bound at
1/2 is the larger, by a factor between 2.52 (at q = 100) and 2.92. At
identical parameters (those optimal for 1/2 and those optimal for 7/8, 82
points) the three values at 1/2, 3/4 and 7/8 are strictly ordered, as
R(t, delta) decreasing in eps0 requires.

**(d) A planted fault** (`controls_fault.json`).
The zero term was given the wrong sign, exp(M + E) in place of exp(M - E),
and the result compared with the exact L(1, chi_D) at the largest |D| of
every h <= 5000. With the fault 2724 of the 5000 values fall below the
"bound" (the clearest: D = -3 416 131 987, h = 3377, L = 0.18152 against
0.21185, recomputed in Arb); without it none does. The control goes red.
The plant is sized at twice the zero term; the control's floor (factor 1.449
in L) and the two plants it does not catch are stated under (a) above.

Plants on the search side, each named in its test for what it can and cannot
catch: removing one field with odd h = 4999 is caught by the Holmin-Kurlberg
comparison; removing one field with even h = 2002, 3000 or 4998 passes every
published-table comparison (no table exists for those h), and is caught only
by the independent sweep (below), which on a window at 1.5 * 10^9 reports the
dropped field as missing; and a listed class number moved by 2 inside that
window passes the sweep too, because it stays within the sweep's tolerance
(it is the field-level PARI checks that can see that, and only on samples).

**Class numbers.**
`crosschecks.json`, `controls_pari.json`, `theorem_a_small.json`.

| against | what | result |
| --- | --- | --- |
| sibling hunt, H = 1500 run to 1.24 * 10^10 | all 1500 counts and largest abs(D); sha256 of the h <= 1500, h <= 1000 and h <= 100 lists | identical |
| sibling hunt, every abs(D) <= 3 * 10^6 | the 911 878 class numbers, as one sha256 | identical |
| Watkins (OEIS A046125, A038552) | 100 counts and largest squarefree k | identical (42 272 fields) |
| Holmin and Kurlberg, GRH | F(h) for all 2500 odd h < 5000 | identical (9 681 947 fields, 8 686 050 of them with h > 1500) |
| Garcia, Grenie, Lee, Molteni, GRH | 20 cumulative counts and largest discriminants, h <= 100, ..., 2000 | identical (16 453 493 fields) |
| Cremona and Sutherland, GRH | 4 115 897 fields with h <= 1000, largest 227 932 027 (h = 996) | identical |
| PARI `qfbclassno` | the largest abs(D) of every h <= 5000 | 5000 of 5000 agree |
| PARI | 577 random list entries | all agree |
| PARI | every fundamental abs(D) in 13 windows of width 3000 from 2 * 10^6 to the end of the range, one across the mode switch at 3 * 10^9 (11 856 discriminants, 2051 of them listed) | the same fields with the same h |
| PARI | the 600 fundamental abs(D) just above D_GRH(h), h = 1, 2, 3, 10, 100, 500, 1000, 2000, 3000, 4000, 5000, 10 000 | no class number <= h (smallest above D_GRH(5000): 11 082) |
| Molteni's per-field file for Garcia, Grenie, Lee, Molteni (sha256 `2900aabe...`, fetched by the computation reviewer) | the set of discriminants for every h <= 2000 | identical (16 453 493 fields, 6 491 770 of them with even h in (1500, 2000]) |
| independent sweep, reviewer's run (`sweep.py`, `lsieve.c`) | every fundamental abs(D) <= 16 396 235 837: Euler-product estimate, PARI on every unlisted candidate and every listed entry outside tolerance | no missing field, no wrong class number; smallest unlisted candidate h = 5001 |
| independent sweep, rerun here | [3, 5 * 10^7] and [1.5 * 10^9, 16 396 235 837] with the committed code | the reviewer's rows reproduced exactly; no missing field, no wrong class number |

The sibling's lists were computed by a different program path (its scalar
exact count on every survivor), the Holmin-Kurlberg and Garcia-Grenie-Lee-
Molteni tables by PARI on other machines. The 20 rows of Garcia-Grenie-Lee-
Molteni Table 1 were checked against the PDF by the computation reviewer,
and the rows 500, 1000, 1500 and 2000 re-read from the PDF by the
orchestrator; the Cremona-Sutherland numbers remain transcriptions from the
literature notes. The computation reviewer also ran PARI on 1 000 000 random
listed entries (823 685 with h > 2000), on all 230 721 listed entries above
3 * 10^9 and on 12 windows of width 2 * 10^5, with no disagreement
(reviewer's run, recorded here, not repeated).

*The independent sweep* (`controls_sweep.json`) is the full-range control for
the even h above 2000, for which no outside table exists. `lsieve.c` sieves
the fundamental discriminants itself and estimates every class number by a
truncated Euler product (p <= 20 000 and tolerance 2.5% below 3 * 10^9,
p <= 3000 and 6% above); every discriminant whose estimate is at most
5000 e^tol must be listed with a class number within tolerance, or goes to
PARI. It shares no code with `cn.c` or `cnx.c`. The reviewer ran it over the
whole range: 4 983 858 175 fundamental discriminants, every listed entry
inside tolerance except |D| = 3 and 4 (their unit factor), 5 358 520
unlisted candidates sent to PARI, smallest class number among them 5001. The
repair rerun with the committed code (536 s recorded, `RUNS.md`)
reproduced the reviewer's rows exactly on [3, 5 * 10^7] and on
[1.5 * 10^9, 16 396 235 837], which holds the whole filter zone. It is a
detector and a cross-check, not a bound: the truncated product has no error
term, PARI is not an oracle of record, and a class number wrong by less than
the tolerance passes it.

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
  **This is the published frontier found for complete lists over all h:
  every h <= 2000 under GRH.** Their Table 1 rows for 500, 1000, 1500 and
  2000 were re-read from the PDF by the orchestrator on 2026-11-20, all 20
  rows were checked against it by the computation reviewer, and their
  per-field data file equals the list here for every h <= 2000.
  *Delta:* the range **2000 < h <= 5000** (86 293 447 fields), under the
  same kind of hypothesis. Below 2000 nothing is new in the lists; the
  cutoffs here are smaller (399, 5 554 909 and 2 576 135 045 against their
  1 592, 19 124 734 and 8 213 527 466), and the class numbers here come from
  exact reduced-form counting, which assumes nothing. Whether their list
  below their cutoff depends on a further GRH, through PARI's class-group
  routine (`quadclassunit`, whose output is GRH-conditional by default), is
  unresolved here: their notes were not re-read for it.
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
  fields; 1750 of those values of h are beyond the sibling hunt's range),
  by a computation that uses GRH only for the cutoff; and this hunt adds
  every even h.
- **Watkins (2004)** (secondary): the unconditional lists for h <= 100.
  Reproduced (42 272 fields, all 100 counts and largest discriminants).
- **`hunts/qrh_class_number`** (this lab, 2026-10-08): the 7/8 half-plane,
  h <= 1500. *Delta:* a cutoff 8.1 to 8.8 times smaller, lists to h = 5000,
  and the h <= 1500 lists identical line for line (same sha256).

Not found: a complete list over all h above 2000 under any hypothesis, or an
explicit GRH lower bound for L(1, chi_D) at finite q stronger than
Languasco-Trudgian in published form (the LLS route evaluated numerically,
door 1, is stronger than both, but was derived by this lab's reviewer, not
found in print). Absence in this search is a statement about the search,
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
  compared with Holmin-Kurlberg, and up to 2000 every field with Molteni's
  file. For even h in (2000, 5000] (78 323 558 fields, 76% of the list) the
  evidence is the same code path as the odd h, the windows against PARI and
  against the sibling's exact count, the stream recomputation and, since
  review, the full-range independent sweep with PARI on every candidate; a
  detector and a cross-check, not a table and not a proof.
- **PARI is a cross-check, not an oracle.** `qfbclassno` is documented as
  not rigorous for every discriminant; `lfunzeros` finds zeros on the line
  and does not prove it has all of them.
- **Orders and group structures.** Only fundamental discriminants (maximal
  orders) and only class numbers, not class-group structures.
- **The full lists are not committed** (1.5 GB); their sha256 and the
  commands that regenerate them are.
- **The literature was not re-read here** (beyond the four Table 1 rows
  re-read by the orchestrator), and the Mosunov-Jacobson data were not
  downloaded. Molteni's data file was fetched by the computation reviewer
  and is compared here, not committed (165 MB; its sha256 is).
- **The cover was not re-optimised.** The stalled cells of section 2.6 stay
  in `dtable_grh.json`; a multi-start cover would shrink D_GRH(h) by 1 to 2%
  for about 400 < h <= 2760 and change nothing in the search.
- **The LLS route (door 1) was not derived here**: it is the reviewer's
  derivation, evaluated in float, with no enclosure and no written proof in
  this hunt.
- **Hand-back was blocked on the case log** (closed the same day):
  `hunts/README.md` had no entry for this hunt while it was being built. The
  entry was added when the hunt was landed, and the standing discipline test
  for the case log passes.

## 9. Review findings and dispositions

Two independent attack passes on 2026-11-20, one on the proof (P) and one on
the computation (C). Both verdicts: holds. Every finding is kept here with
what was done; none was dismissed.

| # | severity | finding | disposition |
| --- | --- | --- | --- |
| C1 | major | The standing test `test_every_hunt_directory_is_covered_by_the_case_log` is red: `hunts/README.md` has no case-log entry for this hunt. | Real, reproduced. Not fixable inside this directory (shared file); the orchestrator adds the entry. Stated at the top and in section 8. |
| C2 | major | Evidence gap: the 78 323 558 fields with even h in (2000, 5000] are backed by no outside table, and the search-side plant (h = 4999) sits at the one parity a table can catch; h = 4998, 3000, 2002 pass every table comparison. | Real, reproduced: the even-h plants now have a test that pins their blindness to the tables. Fixed by committing the reviewer's full-range sweep (`sweep.py`, `lsieve.c`) with its recorded outcome (`controls_sweep.json`, labelled the reviewer's run), rerunning it with the committed code on [3, 5 * 10^7] and [1.5 * 10^9, X] (rows reproduced exactly), and a test in which the sweep catches an even-h drop on a window and misses a shift inside its tolerance. No missing field, no wrong class number. |
| C3 | minor | Molteni's per-field file was not used; it agrees completely. | Real. Compared here field by field for every h <= 2000 (`controls.molteni`, `controls_molteni.json`, sha256 recorded, a test): identical. Section 8 no longer says the file was not downloaded. |
| C4 | minor | The sign plant is sized at twice the zero term; control (a) is blind below a factor 1.449 in L, including dropping the zero term. | Real, reproduced exactly (1.1206 with the zero term dropped, 1.2816 halved). The floor and both uncaught plants are now in `controls_fault.json`, section 6 and a test. |
| C5 | minor | `RUNS.md`: the estimate heading's time was changed from 16:53Z to 16:52Z after the run without a note. | Real. Restored to the time first written, with a note, and the driver log's plan line (printed at launch, 16:52:53Z) cited with its sha256 as the launch-time record. |
| C6 | minor | "Byte-identical to cn.c" holds only after sorting cn.c's output and dropping its stats line. | Real. Now "identical as sorted lists", in section 5 and `RUNS.md`. |
| C7 | minor | Much of the run record lives only in the scratchpad; exit status is per worker. | Real. The per-chunk stats table, the driver log lines and the sha256 of the driver, CPU and worker logs and plans are committed in `search_chunks.json`; the lists stay out (1.5 GB). |
| P1 | minor | The explicit formula (2.1) is quoted, not derived; supported only by measurement. | Real. The contour shift is written out in (2.1) with its estimates and the Davenport chapters; the reviewer's independent measurement at three new characters is recorded as the reviewer's run. The grade is unchanged: a written derivation, unreviewed by a human. |
| P2 | minor | The cover is stalled on about 500 cells; D_GRH(h) is valid but 1 to 2% too large for about 400 < h <= 2760; section 2.6 misdescribed the optimiser. | Real, reproduced: warm start confirmed in `explicit.cover`; 514 cells with y < 49 between 2.99 * 10^7 and 4 967 973 832, the restart at 10^9 (0.12617 against 0.12545 in Arb), the single jump and the 76 cells beaten by later cells, all pinned by a test. Section 2.6 and the typical-parameters line corrected; the earlier sentence is withdrawn there. Not regenerated (the claim, a valid cutoff, stands; Corollary D is untouched); the reviewer's restarted table is recorded as the reviewer's run. |
| P3 | minor | The LLS route itself, evaluated numerically, beats Theorem B; the door list missed it. | Real, reproduced with the reviewer's script, now `lls_route.py` (float grade): at q = 10^4, 10^6, 10^8, 10^10, 10^11, 10^20, 10^50 it gives 0.17021, 0.15412, 0.14392, 0.13671, 0.13376, 0.11736, 0.09762 against 0.14729, 0.13672, 0.12875, 0.12356, 0.12117, 0.10744, 0.09138 here, factors 1.16, 1.13, 1.12, 1.11, 1.10, 1.09, 1.07 (pinned by tests: the value at 10^10, and every factor between 1.06 and 1.16). Recorded as the first door; control (b) now says the margin is over the closed form only. Not adopted: no theorem changes. |
| P4 | minor | Small inaccuracies: the cell ratio (1.0198, not 1.01), the Theorem A cover description (39 cells below 1/3 up to 22 786, 124 above), the Rosser-Schoenfeld equation label, and the discharge condition. | Real. (1) and (2) corrected and pinned by a test. (3) This RESULTS.md gave no equation number; it now cites Theorem 5 and says the label was not confirmed, and the inequality is measured at every prime from 286 to 3 * 10^6 (a test; it fails at 283). The sibling's text, which says (3.20), is not edited from here. (4) Section 0 now states the discharge condition in the ladder's terms. |

## The doors

The hunt stops at H = 5000 because the task capped it there and the budget
fits it, not at a mathematical wall. What binds, and what would move it:

1. **Active constraints at the optimum**, ranked by shadow price at the
   h = 5000 cutoff (q = 1.64 * 10^10, where log L >= M - E with
   M = -1.8505, E = 0.2448).
   **(0) First door, found in review: a different route.** The route of
   Lamzouri, Li and Soundararajan (a single Cesaro cutoff, the zeros entering
   only through F = sum_rho Re 1/rho, F bounded with the (1 - n/x) kernel, the
   worst character prime by prime), evaluated numerically and optimised over
   its two cutoffs instead of in closed form, gives a lower bound for L that
   is 7 to 16% larger than Theorem B between 10^4 and 10^50 (factor 1.11 at
   10^10; all pinned by tests; `lls_route.py`, float grade). It exists only at abscissa
   1/2. The proof reviewer estimates it would move D_GRH(5000) from
   1.64 * 10^10 to about 1.33 * 10^10, a factor about 0.81 in D, and found
   no violation against the exact L at the largest |D| of every h (smallest
   ratio 1.263; reviewer's run, not repeated). It is not adopted: it has no
   enclosure and no written proof here. A measured optimum is not a proved
   ceiling, and this door shows that Theorem B's family was not the best
   classical one at 1/2.
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
   the whole measured margin, L_exact / L_bound = 1.449 at worst, and
   they are about equal. (d) On the computation side the cost grows like
   H^3: mode 1 like X^(3/2), the filter like X * H. H = 5000 cost
   1.7 CPU-hours; H = 10 000 (X = 6.7 * 10^10) extrapolates to about 8
   times that.
2. **Frozen-constant inventory.** sigma0 = 1/2 (the hypothesis; cannot
   move). The trapezoid weight with two cutoffs (a genuine trade: more
   cutoffs spread the y-term of E, which is 81 to 92% of E at the sampled
   characters, at a cost in M). The guards y > 30 and delta <= 1/2 of the
   sibling's `lbound.py`, which now bind for q <= 7.0 * 10^7 and q <= 115
   (a possible gain for small h only, not measured; not relaxed because the
   sibling is imported unchanged). The grid steps 1/2000, 1/500, 1/100 and
   the tail point u = 6 (0.09% in R, measured against adaptive quadrature;
   no trade shape). The cover's warm start (a frozen procedure, not a
   number: a multi-start costs about one more Arb evaluation per cell and
   buys 1 to 2% in D_GRH(h) for about 400 < h <= 2760, the reviewer's
   measurement; no trade shape beyond Arb time). The prime-power truncation at k = 5 (none).
   T_EXACT = 10^7 (irrelevant at 1/2: x is below 10^4). The cover ratio 1.01
   (at most 1% in D_GRH; a trade against Arb time, 80 s now). The bridge
   ratio 1.02 and the tail point Q1 = 10^50 with eta = 1/4, delta = 1/10
   (these set 0.3857; 0.3973 needs 10^200; a genuine trade between the
   constant and the size of the cover). The constant 1/3 of Theorem A
   (binding at q = 22 786, where the cover gives 0.3335 and the exact values
   above 22 786 are not used; with exact values to 10^8 the fine cover reads
   about 0.37, not run as a statement). In the search: the block size 2^19,
   the mode switch
   at 3 * 10^9 and the composite caps A0 per zone (speed only, never
   correctness), and the uint16 counters that saturate at 65 535 (H at most
   20 000 without widening them).
3. **Information class of each door.**
   *Stays inside the data the method reads (GRH for chi_D and the primes):*
   door (0), the LLS route evaluated numerically, which reads exactly the
   same data; and a weight whose transform is nonnegative on the critical line. Under GRH
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
