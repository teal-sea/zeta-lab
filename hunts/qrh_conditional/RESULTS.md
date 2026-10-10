# Hunt #121: what moves under QRH(theta), with every exponent explicit

> 2026-10-08. Everything on this page is conditional on QRH(theta), the
> unreplayed claim defined in `MISSION.md`. If that claim is withdrawn or
> refuted by an independent replay, every statement below is void and this
> page says so now. Nothing here is a result, nothing here is evidence about
> RH, and the strip is not RH: 7/8 is not 1/2, and the preprints say so
> themselves.
>
> Update, later on 2026-10-08: the claim has since been replayed here, Lean's
> kernel and the independent NanoDa kernel accepting its statements
> (`docs/38` section 7). The argument has not been reviewed by any person, so
> every statement below keeps the hypothesis exactly as written.

Grades used: **derived** (an ordinary argument on the cited inputs, written
out below, reviewed by nobody), **measured** (one mpmath route, dps 30,
pinned by `test_qrh_conditional.py`), **cited** (somebody else's statement,
with its location). A composite statement takes the grade of its weakest
step; the weakest step everywhere on this page is the hypothesis.

## 0. The one step every consequence uses, and its dependencies

**Under QRH(theta):** uniformly in q >= 1, x >= 2 and (a, q) = 1,

    psi(x; q, a) = x / phi(q) + O(x^theta (log qx)^2),                 (R)

with an absolute implied constant. This is the standard explicit-formula
argument (Davenport, *Multiplicative Number Theory*, chapters 19 and 20),
and it is stated here with its dependencies rather than assumed:

1. **Zero counting** (Davenport ch. 16): N(T, chi) << T log(qT), and the
   number of zeros of L(s, chi) with ordinate in [t, t + 1] is
   << log(q(|t| + 2)).
2. **The truncated explicit formula** for primitive chi (Davenport ch. 19,
   and ch. 17 for zeta): for x >= 2, T >= 2,
   psi(x, chi) = -sum_{|gamma| < T} x^rho / rho + (remainders), where the
   remainders Davenport displays are all O(x T^{-1} log^2(qx) + x^{1/4} log x + log(qx)).
3. **Where the hypothesis enters.** The functional equation pairs each zero
   rho of L(s, chi) with 1 - conj(rho), also a zero of L(s, chi), so under
   QRH(theta) every nontrivial zero has 1 - theta <= Re rho <= theta.
   Hence |x^rho / rho| <= x^theta / |rho| with |rho| >= 1 - theta, and by
   (1), sum_{|gamma| < T} 1/|rho| << log^2(qT). Taking T = x,
   psi(x, chi) - delta_chi x << x^theta log^2(qx), where delta_chi is 1 for
   the principal character and 0 otherwise.
4. **Imprimitive characters and orthogonality** (Davenport ch. 19 end and
   ch. 20): psi(x, chi) differs from psi(x, chi*) by O(log q log x), and
   psi(x; q, a) = (1/phi(q)) sum_chi conj(chi(a)) psi(x, chi). The phi(q)
   terms each carry the bound of step 3, the 1/phi(q) cancels the count, and
   (R) follows.
5. **From psi to pi.** Partial summation and psi - theta << x^{1/2} give
   pi(x; q, a) = Li(x)/phi(q) + O(x^theta log x), one log fewer. At
   theta = 11/12 this is the shape of the preprint's Corollary 1.2
   (x^{11/12} log x, absolute effective constant). The preprint's "effective"
   is its word; the chain above yields an absolute constant that nobody here
   has computed.

Grade: derived, on cited chapters. Limitations: step 2's remainder list is
quoted as a shape, not transcribed; nothing above was checked against the
preprint's own proof of its corollary.

**What (R) is, measured against the hunt's existing inputs.**

- **Level.** (R) is nontrivial only where x^theta (log qx)^2 < x / phi(q),
  that is q <= x^{1 - theta} / log^2 x: **pointwise level 1/8 at theta = 7/8,
  1/12 at 11/12**, with a power saving.
- **Siegel-Walfisz (SW)** as UPPER_BOUND.md states it: q <= L^B, error
  O(N L^{-H}), ineffective. Under QRH(theta), (R) is stronger in the error (a
  power of N against a power of log N), in the range (a power of N against a
  power of log N) and in effectivity. Everywhere (SW) is used, (R) supersedes
  it.
- **Bombieri-Vinogradov** gives level 1/2 on average over q with a
  logarithmic saving; (R) gives level 1/8 pointwise with a power saving.
  Neither implies the other. Bombieri-Vinogradov is not an input anywhere in
  `UPPER_BOUND.md`, `RESULTS.md`, `RANK3_SCOPE.md`, `SW_EFFECTIVE.md`, the two
  `SW_*_SPLICE.md` files or `SIEGEL_UNIFORMITY.md` (grep, 2026-10-08).
- **Barban-Davenport-Halberstam**, the input of the `RANK3_BDH_*` documents
  (not read here beyond their names), bounds
  sum_{q <= Q} sum_a |psi(x; q, a) - x/phi(q)|^2 << xQ log x for x L^{-A} <= Q <= x.
  Squaring (R) and summing over the ~Q^2 pairs gives Q^2 x^{2 theta} L^4,
  which beats xQ only for Q < x^{1 - 2 theta}: never, for theta > 1/2. **In
  BDH's own range the hunt's existing input is strictly stronger than what
  QRH(theta) provides.** Below that range, (R) beats the unconditional
  x^2 L^{-A} variance only for Q <= x^{1 - theta} L^{-2 - A/2}, level 1/8
  again.

## 1. Under QRH(7/8): rank 1 moves a quarter power and stops three quarters short

UPPER_BOUND.md section 7 identifies the q = 1 mixed moment through the exact
identity (29),

    T_N = sum_{t <= N} Delta(t)^2 + sum_{t < N} (Delta(N) - Delta(t))^2,   Delta(t) = psi(t) - t,

and bounds it by (SW) at q = 1 as T_N <<_H N^3 L^{-2H}. `SW_EFFECTIVE.md`
sharpens the input to the classical N exp(-c_1 sqrt(log N)) and records the
component as "a full power of N short of (31)", the unproved target
T_N <<_eps N^{2 + eps}.

**Under QRH(7/8):** (R) at q = 1 gives max_{t <= N} |Delta(t)| << N^{7/8} L^2.
Each of the 2N - 1 terms of (29) is at most (2 max |Delta|)^2, so

    T_N << N * (N^{7/8} L^2)^2 = N^{1 + 7/4} L^4 = N^{11/4} (log N)^4.

With every exponent explicit: the power of N is 1 + 2 theta = 11/4, the saving
over the recorded N^3 is 2 - 2 theta = **1/4 of a power**, and the distance to
(31) is 1 + 2 theta - 2 = 2 theta - 1 = **3/4 of a power**. **The gap narrows
and does not close.** Under QRH(11/12): N^{17/6} L^4, saving 1/6, gap 5/6.
Under theta = 1/2, RH, the gap is 0 and the bound is the N^2 L^4 that section 7
already records under RH.

Two facts about the shape of this gap, both derived here:

- **The exponent is the exact content of the information class.** If the
  supremum Theta of the real parts of zeta's zeros equals theta, then by the
  classical oscillation theorem (Ingham, ch. V: psi(x) - x = O(x^a) forces
  Theta <= a) Delta(N) is not O(N^{theta - eps}), and (29)'s first completed
  square gives T_N >= ((N + 1)/2) Delta(N)^2 >= N^{1 + 2 theta - eps}
  infinitely often. So nothing that reads only "Theta <= theta" can beat
  N^{1 + 2 theta - eps} at rank 1; the quarter power above is all a 7/8 strip
  can be worth there.
- **No fixed strip closes rank 1.** Section 7 states that (31) implies
  Delta(N) = O(N^{1/2 + eps}), which by the same oscillation theorem forces
  Theta = 1/2, i.e. RH. A hypothesis consistent with Theta = theta > 1/2
  therefore cannot prove (31). The gap 2 theta - 1 vanishes only at
  theta = 1/2, and at theta = 1/2 the strip is RH.

Grade: derived (exact exponent arithmetic on a displayed identity, with the
mean-square route checked to give the same power: sum_{t <= N} t^{2 theta} L^4
is again N^{1 + 2 theta} L^4). Pinned: `test_exponents_under_the_seven_eighths_strip`.

## 2. Under QRH(7/8): the completed bound (1) moves from a logarithmic saving to N^{35/12}

UPPER_BOUND.md (1) is E(N) <<_C N^3 (log N)^{-C} for every fixed C, proved in
its section 5 with polylogarithmic arcs Q = floor(L^B). Its "The doors" entry
records that the term binding (1) is the minor-arc fourth moment (20),
I_Q << (N^3 / Q + N^{13/5}) L^6, which takes no prime-counting input at all:
it is Vaughan's bound (V) times the second moment. **So at polylog Q the strip
changes nothing in (1): the major-arc term (19) gets smaller and the minor
arcs still cost N^3 L^6 / Q.** What the strip changes is how large Q may be.

**Under QRH(theta), with Q = N^a:** every exponent is explicit.

*(17), strip version.* On the arc |beta| <= Q/(qN) around a/q, split F_N by
residue class, insert (R) through the Gauss sums (Davenport ch. 26 does this
for the major arcs of the three-primes problem; the Gauss sum of any
character mod q to a reduced residue has modulus at most q^{1/2}), and
partially sum against e(t beta) at the cost of a factor (1 + 2 pi N|beta|):

    R_{q,a}(beta) := F_N(a/q + beta) - mu(q) K_N(beta)/phi(q) << q^{1/2} (1 + N|beta|) N^theta L^2,

absolute constant. On the arc N|beta| <= Q/q, so sup over all arcs of |R| is
<< Q N^theta L^2 (the q = 1 arc).

*The cross term of (18).* With |K_N(beta)| <= min(N, 1/(2|beta|)),
int_{|beta| <= Q/(qN)} |K_N|^2 (1 + N|beta|)^2 dbeta << N + N Q/q << NQ/q.
Per arc, 8 int |P|^2 |R|^2 << (mu^2(q)/phi(q)^2) q N^{2 theta} L^4 * NQ/q;
summed over the phi(q) residues and over q <= Q, with sum mu^2(q)/phi(q) << log 2Q,

    sum_{q,a} 8 int_{I_{q,a}} |P|^2 |R|^2 << Q N^{1 + 2 theta} L^5.

*The fourth power of (18), two routes that agree at the balance point.*
Route 1, pointwise: int_{|beta| <= Q/(qN)} (1 + N|beta|)^4 dbeta << Q^5 / (q^5 N),
so per arc 2 int |R|^4 << q^2 N^{4 theta} L^8 * Q^5 q^{-5} N^{-1}; over residues
and q, sum q^{-2} converges, giving Q^5 N^{4 theta - 1} L^8. Route 2, through
the second moment: sum_{q,a} int |R|^4 <= (sup |R|)^2 sum_{q,a} int (2|F|^2 + 2|P|^2)
<< Q^2 N^{2 theta} L^4 * (d_N + N log 2Q) << Q^2 N^{1 + 2 theta} L^5.

*The rest of (12).* The minor arcs are (20) unchanged, << (N^3/Q + N^{13/5}) L^6,
valid for any Q with 2Q^2 < N since Dirichlet approximation then puts (V) in
its own range. The leakage (13) is << N^3 Q^{-2} L^3, the tail (6) is
<< N^3 / Q^2, both needing only 2Q^2 < N and Q <= sqrt N.

*Balance.* With Q = N^a the constraints that each major-arc term stay below
the minor-arc N^{3 - a} are: cross term, a + 1 + 2 theta <= 3 - a, i.e.
a <= 1 - theta; fourth power, route 1, 5a + 4 theta - 1 <= 3 - a, and route 2,
2a + 1 + 2 theta <= 3 - a, both i.e. **a <= (2 - 2 theta)/3**. The fourth-power
constraint binds for every theta < 1 (pinned for theta in [0.50, 0.99]). So

    a = (2 - 2 theta)/3,     E(N) << N^{3 - a} (log N)^6 = N^{(7 + 2 theta)/3} (log N)^6,

the logarithm not optimized. **Under QRH(7/8): a = 1/12 and E(N) << N^{35/12} (log N)^6**,
a saving of **1/12 of a power** over the unconditional (1), **11/12 of a
power short** of the N^{2 + eps} that would force RH, and 5/12 of a power
behind the N^{5/2} L^c that CHHL report under GRH for Dirichlet L-functions
(UPPER_BOUND.md section 1, item 1), on a weaker hypothesis. Under QRH(11/12):
a = 1/18, N^{53/18} L^6. At theta = 1/2 the same route gives N^{8/3}, which is
weaker than CHHL's conditional 5/2: the route is lossy, and the strip buys
exactly its own a and nothing more.

*Bootstrap, so nobody tries it.* UPPER_BOUND.md section 1 records that CHHL's
Theorem 2, E(N) = Omega(N^{1 + 2 Theta - delta}), turns any bound
E(N) << N^c into Theta <= (c - 1)/2. Feeding the conditional bound back:
Theta <= ((7 + 2 theta)/3 - 1)/2 = (2 + theta)/3, which exceeds theta by
2(1 - theta)/3 > 0 for every theta < 1. Under QRH(7/8) the bootstrap says
Theta <= 23/24, weaker than the hypothesis. The map drifts toward 1 and never
toward 1/2; pinned.

Grade: derived, by this hunt, on UPPER_BOUND.md's displayed inequalities
(12), (13), (6), (18), (20) and the Gauss-sum major-arc approximation;
reviewed by nobody. Limitations: UPPER_BOUND.md's own grade is a written
argument with one model review and no kernel check, and this inherits it;
the (1 + N|beta|) factor from partial summation is what makes the fourth-power
term bind, and a mean-value treatment of int |R|^4 on major arcs (not
attempted) is the one place a sharper conditional exponent might come from;
no numerical check of a conditional asymptotic exists or could.

## 3. Under QRH(7/8): rank 2 does not move

Rank 2 of the doors table is the minor fourth moment I_Q and the fourth
residual moment Z_{q > R_0}, both O(N^{13/5} L^6) by (22) and (28), both
resting on Vaughan's bound (V). (V) is an unconditional exponential-sum
estimate through Vaughan's identity and reads no zero-free region; the
N^{4/5} term the text traces to its Type I/II balance at U = V = N^{2/5} has
no theta in it. **Under QRH(7/8) nothing derived here changes (V), I_Q or
Z_{q > R_0}.** This is a statement about the inputs of this hunt, not a
theorem that a strip cannot reach a minor arc by some other route.

Grade: derived (a reading of which inputs carry theta). Pinned only in the
sense that `strip_exponents` carries no rank-2 field.

## 4. Under QRH(7/8): rank 3 does not move in the square-root-arc configuration

RANK3_SCOPE.md prices the moments at 2 <= q <= R_0 = Q/L, Q = floor(sqrt N / 3),
and names Route A, "(SW)-type uniformity to q up to a positive power of N",
as the missing input. (R) is exactly such an input, but only to level
1 - theta = 1/8, while R_0 is of order N^{1/2}/L: for N^{1/8} < q <= R_0 the
remainder N^{7/8} L^2 exceeds the main term N/phi(q) and (R) says nothing. And
for q <= N^{1/8} the configuration itself defeats it: section 6's arcs have
width Q/(qN) with Q of order sqrt N, so the partial-summation factor
(1 + N|beta|) <= Q/q costs sqrt N, and the cross-term computation of section
2 above gives sum_{2 <= q <= Q'} U_{(q)} << Q N^{1 + 2 theta} L^5 = N^{13/4} L^5
for any Q' <= Q: worse than the trivial N^3 log Q. **Under QRH(7/8), in the
arc configuration of UPPER_BOUND.md section 6, rank 3 does not move.** In the
polylog configuration of section 5 the range "2 <= q <= R_0" does not exist as
a separate bucket: the strip widens the major arcs to N^{1/12} and the price of
that is section 2.

Grade: derived. Limitation: the RANK3 route documents were not read, so
whether any of them already carries a partial-summation-free treatment that
(R) would feed is not known here.

## 5. Under QRH(7/8): Theorem A becomes N^{7/4} L^4 and (T) does not follow; Theorem B is capped, not improved

RESULTS.md section 17, Theorem A: W(N) << N^{Theta + Theta_chi} (log N)^4
unconditionally, with Theta, Theta_chi the suprema of the real parts of the
zeros of zeta(s) and L(s, chi_3); the text calls the unconditional form empty
when Theta + Theta_chi = 2.

**Under QRH(7/8), for zeta and for L(s, chi_3):** Theta <= 7/8 and
Theta_chi <= 7/8, so

    W(N) << N^{7/4} (log N)^4,     T(N) = I(N) + O(N^{7/4} log^4 N),

the first instance in which Theorem A's exponent is below 2 without assuming
a Riemann hypothesis. The statement (T) needs O(N^{1 + eps}); the distance is
2 theta - 1 = **3/4 of a power**, the same number as rank 1 and for the same
reason: the double sum over pairs (rho, rho') carries N^{beta + beta'}, and
nothing in "Theta <= theta" keeps beta + beta' below 2 theta. Under
QRH(11/12): N^{11/6} L^4, gap 5/6.

RESULTS.md section 18, Theorem B: E(N) = Omega(N^{1 + 2 Theta_chi - eps})
along an unexhibited sequence. **Under QRH(7/8):** Theta_chi lies in
[1/2, 7/8] instead of [1/2, 1], so the lower bound Theorem B can deliver is
capped at N^{11/4 - eps}. A cap on a lower bound makes it weaker, not
stronger; of the three gaps `tb_bind.py` records (no constant, no exhibited
sequence, Theta_chi unknown), the strip narrows the third and touches
neither of the others. CHHL's own Omega(N^{1 + 2 Theta - delta}) is capped
the same way.

`FRONTIER_2026_09_12.md`'s RH-bearing scalar: B_N = N R(N) + R(N)^2/2 + O(N log^2 N),
M_N = 2|B_N|^2/N, and RH iff M_N <<_eps N^{2 + eps}. **Under QRH(7/8):**
R(N) << N^{7/8} L^2 gives M_N << N^{11/4} L^4, **3/4 of a power short**: it is
the rank-1 quantity N R(N)^2 under another name and moves by the same quarter
power. The same page's D_N target, |D_N| <<_eps N^{1/2 + eps}, gets only the
envelope bound: with |R(u)| << u^theta L^2 and K = floor(sqrt N),
|D_N| << N^{(1 + theta)/2} L^2 = N^{15/16} L^2 under QRH(7/8), 7/16 short, and
that page records that the envelope is not what binds on that route (the
multiplier zeta(rho) is), which a strip does not touch.

Grade: derived (substitution into displayed theorems). Pinned:
`theorem_A_exponent`, `theorem_B_cap`, `frontier_M_N_exponent`, `frontier_D_N_exponent`.

## 6. Under QRH(theta): the "ineffective constants" caveat goes, the exponent does not

UPPER_BOUND.md (1) is stated "with ineffective constants", and
`SW_EFFECTIVE.md` shows the q = 1 line never needed Siegel-Walfisz. The
remaining ineffectivity sits in (SW) at 2 <= q <= L^B in section 5, where
Siegel's theorem is the only unconditional tool. **Under QRH(theta):** the
hypothesis excludes every zero with Re s > theta, hence every Landau-Siegel
zero (document 38 section 3 notes that the 7/8 statement implies the uniform
Siegel bound with c = (log 3)/8), and (R) replaces (SW) with an absolute
constant. So (1), and the conditional N^{35/12} L^6 of section 2, carry
constants that are effective in principle under the hypothesis. Nobody has
computed one. `SW_EFFECTIVE.md`'s own sentence stands: effectiveness and
sufficiency are different questions, and only the first moved.

`SIEGEL_UNIFORMITY.md`'s displayed bound (1) carries two terms "present only
if the exceptional character/zero (q, chi, beta)" with beta > 1 - c_0/log Z
exists, Z = exp(L^{1/10}). **Under QRH(theta):** beta <= theta, so once
1 - c_0/log Z > theta, that is for all sufficiently large N, no such zero
exists and the bound reduces to its no-exception form N^3 exp(-c_kappa (log N)^kappa),
which that document itself says "is not a fixed power saving". Section 2's
N^{35/12} is stronger than it under the same hypothesis.

Grade: derived from headers and displayed statements; `SIEGEL_UNIFORMITY.md`
was read only at its header.

## 7. The two crossover heights

Where does x^theta (log x)^2 become the smaller bound against an explicit,
published de la Vallee Poussin remainder? `SW_EFFECTIVE.md` names no explicit
constant ("cannot quote a citation-checked numeric digit"), so one is
imported: Johnston and Yang, arXiv 2204.01980, Theorem 1.1, for all x >= 2,

    |psi(x) - x| <= 9.39 x (log x)^{1.515} exp(-0.8274 sqrt(log x)),

read from the arXiv HTML rendering on 2026-10-08 and hedged to that reading
(journal version not checked). The strip side has an absolute constant that
nobody has computed; it is set to **1 by labelled convention**, the same
convention `SW_EFFECTIVE.md` uses for its K, and the table shows what the
convention costs. In u = log x the comparison is the sign of

    g(u) = log C + (theta - 1) u + (2 - 1.515) log u - log 9.39 + 0.8274 sqrt(u),

negative where the strip-shaped bound is smaller. Roots by grid scan (pitch
1/4) and bisection, dps 30; measured.

| theta | C | roots in u | crossover u | x |
| --- | --- | --- | --- | --- |
| 7/8 | 1 | 6.822, **35.113** | 35.113 | 10^{15.25}, about 1.8e15 |
| 7/8 | 10 | 74.255 | 74.255 | 10^{32.25} |
| 7/8 | 100 | 104.700 | 104.700 | 10^{45.47} |
| 7/8 | 10^4 | 158.857 | 158.857 | 10^{68.99} |
| 11/12 | 1 | 5.131, **98.225** | 98.225 | 10^{42.66} |
| 11/12 | 10 | 152.723 | 152.723 | 10^{66.33} |
| 11/12 | 100 | 199.414 | 199.414 | 10^{86.60} |
| 11/12 | 10^4 | 283.779 | 283.779 | 10^{123.24} |

**(a) At theta = 7/8 the crossover is log x = 35.11, x about 1.8 x 10^15.
(b) At theta = 11/12 it is log x = 98.22, x about 4.6 x 10^42.** Both with
C = 1. The lower root at C = 1 (u = 6.8, x about 900) is where both bounds
exceed x itself and say nothing; between the two roots the explicit
unconditional bound is the smaller one, and that interval contains the whole
of `SW_EFFECTIVE.md`'s measured ladder 10^5 <= N <= 10^7 (pinned): **on every
height the hunt has measured, the strip-shaped bound is not the binding
one.** Each factor of e in C moves the 7/8 crossover by about 24 in u near
C = 1; the number is a convention-dependent order of magnitude, not a
constant of nature. Against the bare shape x exp(-0.8274 sqrt(log x)) with
K = 1 (a second convention, also measured) the crossovers are u = 167.7 and
313.9.

Grade: measured, pinned to 1e-9 in u. Limitation: one published remainder,
one convention for the strip side; a sharper published remainder moves the
heights up and the exponents of sections 1 to 6 not at all.

## 8. Li's criterion under a strip: nothing usable at finite n

`zeta/li.py` carries lambda_n = sum_rho [1 - (1 - 1/rho)^n] over the
nontrivial zeros, paired symmetrically, and Bombieri and Lagarias (1999):
RH iff lambda_n >= 0 for every n. For rho = beta + i gamma,

    |1 - 1/rho|^2 = ((1 - beta)^2 + gamma^2) / (beta^2 + gamma^2),

below 1 iff beta > 1/2. The functional equation pairs a zero at beta + i gamma,
beta > 1/2, with one at rho' = (1 - beta) + i gamma, and for the partner

    r^2 := |1 - 1/rho'|^2 = 1 + (2 beta - 1) / ((1 - beta)^2 + gamma^2) > 1,

the algebra checked numerically at three points to 1e-35. The pair's
contribution to lambda_n is 2 - 2 r^n cos(n phi') with phi' = arg(1 - 1/rho'),
bounded below by 2 - 2 r^n, which is as negative as r^n is large.

**Under QRH(theta):** beta <= theta, so every zero at height gamma has

    r <= r_cap(theta, gamma) = sqrt((theta^2 + gamma^2) / ((1 - theta)^2 + gamma^2)),

and that is the whole of what a strip says about lambda_n. Three
consequences, all derived:

- A strip bounds neither the number nor the heights of hypothetical off-line
  zeros. The sum over zeros of 1 diverges, so "the growth rate of lambda_n"
  from per-zero caps is not even a well-posed quantity without a zero-density
  input, which a strip is not.
- At small height the cap is useless: r_cap(theta, 0) = theta/(1 - theta) = 7
  at theta = 7/8 (11 at 11/12), so a hypothetical zero near the real axis
  would double its factor at n below 1. What excludes that is the verified
  height, not the strip: RH is verified to T_0 = 3 x 10^12 (Platt and
  Trudgian 2021, cited from `docs/05`), and above T_0 the cap is
  1 + 4.2e-26 under QRH(7/8) against 1 + 5.6e-26 with no strip at all.
- For gamma >> 1, log r_cap(theta, gamma) tends to (2 theta - 1)/(2 gamma^2),
  against 1/(2 gamma^2) with no strip. **The strip multiplies the per-zero
  growth exponent of a hypothetical off-line zero by 2 theta - 1, 3/4 at
  theta = 7/8 and 5/6 at 11/12, and does nothing else.** Any finite-n
  positivity statement for lambda_n rests on the verified height and on a
  count of zeros above it; the strip improves the hypothetical negative part
  of such a statement by that constant factor and supplies no lower bound on
  lambda_n at any n on its own.

Numeric illustration (measured, dps 30, a what-if at the first ordinate):

| height | theta | r_cap - 1 | n at which r_cap^n = 2 | log r ratio to no strip |
| --- | --- | --- | --- | --- |
| gamma_1 = 14.1347 | 7/8 | 1.8751e-3 | 370.0 | 0.7504 |
| gamma_1 | 11/12 | 2.0833e-3 | 333.1 | 0.8336 |
| gamma_1 | none (beta < 1) | 2.4995e-3 | 277.7 | 1 |
| T_0 = 3e12 | 7/8 | 4.1667e-26 | 1.66e25 | 3/4 to the 12 digits stored (at gamma_1 the second-order term of log(1 + x) shifts it by 4e-4) |
| T_0 | 11/12 | 4.6296e-26 | 1.50e25 | 5/6 |
| T_0 | none | 5.5556e-26 | 1.25e25 | 1 |

So the honest answer the task anticipated is the one the algebra gives:
nothing usable at finite n, because |1 - 1/rho'| exceeds 1 by an amount the
strip caps only through the factor 2 theta - 1, with the height and count of
such zeros outside its reach. The equivalence RH iff Re(xi'/xi) > 0 on
Re s > 1/2 and Li's criterion are statements at 1/2 and are untouched
(document 38 section 6).

## 9. Does not move, cited and not recomputed

- **The de Bruijn-Newman record.** Under a zero-free half-plane Re s > 7/8,
  Lambda <= 9/32 = 0.28125 (document 38 section 6, from de Bruijn 1950
  Theorem 13 in the normalisation of `docs/05`); the record is 0.2 (Platt
  and Trudgian 2021, `docs/05`). 9/32 > 0.2, so **the record does not move**;
  only the comparison is done here.
- **The registered and candidate simple-zero proportions** (`README.md`,
  `hunts/four_point_pressure/`) take no zero-free strip as input; nothing
  moves (document 38 section 6).
- **Lambda_DH** (`hunts/lambda_dh_bounds/`, `hunts/lambda_dh_exact/`,
  `docs/29`): Davenport-Heilbronn is a linear combination of two L-functions
  without an Euler product; the claim says nothing about it in either
  direction (document 38 section 6).
- **Hunt #118's out-of-band wall** (`HANDOFF.md`, walls section): the two
  inputs it names as reopening it, an unconditional in-band evaluation of the
  ordinate pair correlation and an unconditional out-of-band upper bound on
  the form factor, are not consequences of a strip by anything derived here.
  Not a claim that they cannot be.
- **The equivalence RH iff Re(xi'/xi) > 0 on Re s > 1/2** (stated in
  `hunts/epp_herglotz/RESULTS.md`) is a statement at 1/2 and is untouched
  (document 38 section 6). Until 2026-10-09 this entry and the end of
  section 8 cited it as PR #268's, which is not merged.

## 10. The table

| wall or conditional result | where | recorded | under QRH(7/8) | under QRH(11/12) | short of its target by | grade |
| --- | --- | --- | --- | --- | --- | --- |
| rank 1, the q = 1 mixed moment T_N | UPPER_BOUND.md s.7, SW_EFFECTIVE.md | N^3 L^{-2H} | **moves** to N^{11/4} L^4 | N^{17/6} L^4 | 3/4 (5/6) of a power; closes only at theta = 1/2 | derived |
| completed bound (1), polylog arcs | UPPER_BOUND.md s.5 | N^3 L^{-C} | unchanged at polylog Q; **moves** to N^{35/12} L^6 with Q = N^{1/12} | N^{53/18} L^6 | 11/12 (17/18) of a power | derived, unreviewed |
| rank 2, I_Q and Z_{q > R_0} | UPPER_BOUND.md s.6 | N^{13/5} L^6 | **does not move** | does not move | 3/5 of a power, as before | derived (input reading) |
| rank 3, 2 <= q <= R_0, square-root arcs | RANK3_SCOPE.md | no estimate | **does not move** | does not move | unknown, as before | derived |
| Theorem A, W(N) | RESULTS.md s.17 | N^{Theta + Theta_chi} L^4, empty | **moves** to N^{7/4} L^4 | N^{11/6} L^4 | 3/4 (5/6) of a power from (T) | derived |
| Theorem B, lower bound | RESULTS.md s.18 | Omega(N^{1 + 2 Theta_chi - eps}) | capped at N^{11/4 - eps}; not improved | N^{17/6 - eps} | not a target | derived |
| signed mean M_N | FRONTIER_2026_09_12.md | RH iff M_N << N^{2 + eps} | **moves** to N^{11/4} L^4 | N^{17/6} L^4 | 3/4 (5/6) of a power | derived |
| ineffective constants in (1) | UPPER_BOUND.md s.1, SW_EFFECTIVE.md | ineffective at 2 <= q <= L^B | **moves**: effective in principle, uncomputed | same | not an exponent | derived |
| SIEGEL_UNIFORMITY.md (1) | its header | exceptional terms if a Siegel zero exists | reduces to its no-exception form | same | still N^{3 - o(1)} | derived from header |
| de Bruijn-Newman record 0.2 | docs/05, document 38 s.6 | 0.2 | 9/32 = 0.28125: **does not move** | 25/72 = 0.3472, same formula with half-width 5/6, arithmetic done here | above the record | cited |
| simple-zero proportions | README.md, four_point_pressure | no strip input | **does not move** | does not move | n/a | cited |
| Lambda_DH | lambda_dh_bounds, lambda_dh_exact | no L-function | **does not move** | does not move | n/a | cited |
| #118 out-of-band wall | HANDOFF.md walls | needs pair correlation inputs | **does not move** by anything here | same | n/a | derived (input reading) |
| Li coefficients lambda_n | zeta/li.py | nonnegative as far as computed | per-zero growth exponent times 3/4; **nothing usable at finite n** | times 5/6 | no lower bound at any n | derived, measured |
| crossover vs Johnston-Yang, C = 1 | this hunt | n/a | log x = 35.11 | log x = 98.22 | convention-dependent | measured |

The 11/12 de Bruijn-Newman cell is document 38's formula with the half-width
2 (11/12 - 1/2) = 5/6 in `docs/05`'s normalisation, Lambda <= (5/6)^2 / 2 = 25/72;
the arithmetic is done here, not cited, and nothing else on this page depends
on it.

## 11. Kill conditions, evaluated

None fired. The hypothesis stands exactly where document 38 left it: an
ordinary mathematical argument of about 195 pages that no person is known to
have reviewed, plus a Lean development whose compile is asserted by its
producer. If an independent replay withdraws or refutes it, every "Under
QRH" sentence on this page is void, the table's "moves" column is empty, and
the only surviving content is section 0's dependency list, section 7's two
root-findings as arithmetic, and section 8's algebra.

## The doors

This hunt measures no ceiling of its own; it re-prices other hunts' ceilings
under a hypothesis. The analysis below is therefore about the conditional
exponents as functions of theta, which is the one parameter the hypothesis
has.

### 1. Active constraints at the optimum

Ranked by the slope of the conditional exponent in theta, the only shadow
price available.

| rank | constraint | binds through | slope in theta | what would close it |
| --- | --- | --- | --- | --- |
| 1 | rank 1's gap 2 theta - 1 | the oscillation theorem: T_N >= N^{1 + 2 Theta - eps} if Theta = theta | 2 (each 0.01 off theta buys N^{0.02}) | theta = 1/2 only; no strip short of RH closes it, and that is structural, not quantitative |
| 2 | the fourth-power constraint a <= (2 - 2 theta)/3 on the widened major arcs | the (1 + N|beta|) partial-summation factor in the strip form of (17) | -2/3 in a, so 2/3 on the total exponent (7 + 2 theta)/3 | a mean-value bound for int |R|^4 on major arcs that does not go through sup |R|; not attempted |
| 3 | rank 2's N^{13/5}, Vaughan's Type I/II balance | (V), which reads no zeros | 0 | outside any strip; unchanged from the prime-pair hunt's own doors |

### 2. The frozen-constant inventory

| constant | value | trade shape |
| --- | --- | --- |
| C, the strip-side constant in section 7 | 1, labelled convention | genuine trade: each factor e in C moves the 7/8 crossover about 24 in log x near C = 1; the exponents of sections 1 to 6 do not see it |
| the Johnston-Yang triple (9.39, 1.515, 0.8274) | as published | a sharper published remainder moves both crossovers up; no exponent moves |
| T in the explicit formula | T = x | changes logarithms only; the power 1 + 2 theta is not T's |
| Q = N^a | a = (2 - 2 theta)/3 at the balance | genuine trade between the fourth-power term (rising in a) and the minor arcs (falling in a); the cross term is slack by 1 - theta - a = (1 - theta)/3 |
| the log powers L^4 and L^6 | not optimized | free to trim; never buys a power |
| T_0, the verified height | 3e12, cited | the per-zero Li cap scales as T_0^{-2}; a higher verified height buys quadratically, the strip buys the fixed factor 2 theta - 1 |
| the grid pitch 1/4 in u | fixed | a root pair closer than 1/4 would be missed; the observed root separations are 28 and 93 |

### 3. The information class

- Rank 1's door needs Theta = 1/2 read into the argument: RH itself, outside
  every strip. The door is the hypothesis, not a technique.
- The circle-total door stays inside the data a strip supplies ("every
  Delta(x; q, a) is pointwise small") but its binding term reads only
  sup |R|; reading int |R|^4 as a mean value over the arcs would read more
  than pointwise size, of the Bombieri-Vinogradov kind, which a strip does not
  carry and which the hunt's existing inputs carry only on average at level
  1/2 with a logarithmic saving.
- Rank 2's door reads (V), outside any zero-free input.
- The Li door reads the count of zeros above the verified height, a
  zero-density datum; a strip carries none.
- The non-movers of section 9 read no zero-free region at all, which is why
  they do not move and why a replay of the claim, either way, leaves them
  where they are.
