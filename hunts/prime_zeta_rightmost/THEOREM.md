# THEOREM.md: the replacement theorem (WP3, WP4)

**Hunt: prime_zeta_rightmost. Written 2026-08-16.** This file states and
proves the replacement for the two conjectures in OEIS A107311, against the
verbatim text pinned in `SOURCE.md` section 2. Its numeric inputs are the
decided enclosures in `decided.json` and `theorem_inputs.json`, each stated
with backend and precision; everything else is proved here or cited with an
access note (section 7). Vocabulary per `MISSION.md`: the strongest words
used are *measured*, *observed* and *decided* (an enclosure with exact
endpoint sign logic). Nothing in this file is a repo-level result until the
case log in `hunts/README.md` says how the hunt ended.

The claims under attack, word for word as served (SOURCE.md section 2):

> Conjecture 1: the real parts of the zeros of the prime zeta function are
> not greater than this constant.
> Conjecture 2: the real parts of the zeros of the anyone subset of the
> prime zeta function are not greater than this constant.

where "this constant" is x*, the real root of zeta(x) = 2. Both are false.
Theorems A and B below replace Conjecture 1: the true supremum of the real
parts is sigma_c = 1.77954465354699... > x* + 1/20, approached but not
attained. Theorems C1 and C2 replace Conjecture 2: the subset {p >= 3}
already has zeros beyond sigma_c, and tail subsets {p >= p_k} have
thresholds growing without bound.

## 0. Setting, notation, and the decided inputs

Throughout, p ranges over primes. For a prime q let

    S_q  = {p prime : p >= q},
    P_q(s) = sum_{p >= q} p^{-s},

so P_2 = P is the prime zeta function and P_3 is the {p >= 3} subset
series. Each series converges absolutely and locally uniformly in
Re s > 1 (comparison with sum n^{-sigma}), so P_q is analytic there. Every
statement in this file concerns zeros with Re s > 1. By the
reading-independence argument of SOURCE.md section 2, a zero with
Re s > 1 is a zero of the defining series itself, where every reading of
"the prime zeta function" (series, Glaisher continuation, any branch)
agrees; so the refutations below hold under every reading at once.

The balance functions, on (1, infinity):

    h_q(sigma) = sum_{p > q} p^{-sigma}  -  q^{-sigma},
    g_q(sigma) = q^sigma * h_q(sigma) = sum_{p > q} (q/p)^sigma  -  1.

Since q^sigma > 0, h_q and g_q have the same sign and the same roots. For
q = 2 and q = 3 these are the functions bisected in `decide.py`:

    h(sigma) = P(sigma) - 2^(1-sigma)              = h_2(sigma),
    u(sigma) = P(sigma) - 2^(-sigma) - 2*3^(-sigma) = h_3(sigma).

`sigma_c := sigma_c(2)` and `sigma_3 := sigma_c(3)` denote the unique roots
of h_2 and h_3 (uniqueness is Lemma 1 below; the decided derivative guards
in decided.json confirm it independently on the bracketed ranges).

### T1. Decided inputs

Backends: flint = python-flint (arb) at 350 bits; iv = mpmath.iv at
dps 40. Both legs decided every row below.

From `decided.json` (2026-08-16):

    x*      in [1.7286472389981836181351030102976660,
                1.7286472389981836181351030102977450]   (flint, 350 bits)
            in [1.7286472389981835995, 1.7286472389981836884]  (iv, dps 40)
            OEIS A107311's 102-digit value interval lies inside both
            backend intervals (decided); the flint interval lies inside
            the iv interval (decided).
    sigma_c in [1.7795446535469941164458987869654405,
                1.7795446535469941164458987869655195]   (flint, 350 bits)
            in [1.7795446535469636, 1.7795446535470547]  (iv, dps 40)
    sigma_3 in [1.8252259560738457623878727108889264,
                1.8252259560738457623878727108890054]   (flint, 350 bits)
            in [1.8252259559929, 1.8252259560861]        (iv, dps 40)

    sigma_c - x* > 1/20   decided on both backends (exact rational compare
                          of enclosure endpoints; the difference exceeds
                          0.0508974145 on the flint leg).
    h(x*) > 1/60          decided on both backends, with h evaluated over
                          the whole x* enclosure (flint enclosure
                          [0.016907377213856298105802854273997,
                           0.016907377213856298105802854274113]).
    endpoint signs        h(17/10) > 0, h(19/10) < 0, u(9/5) > 0,
                          u(37/20) < 0: decided on each backend before its
                          bisection started (decided.json,
                          bracket_endpoint_signs; a bracket with undecided
                          endpoint signs raises, and no raise occurred).
    guards                h'(s) < 0 on [1.7, 1.9] and u'(s) < 0 on
                          [1.8, 1.85], decided on both backends;
                          zeta'(x) < 0 on (1, 2) termwise-exactly.

From `theorem_inputs.json` (2026-08-16):

    D1  h(7/4) in [0.009465637293734518587514821979513,
                   0.009465637293734518587514821979514] (flint, 350 bits;
        iv dps 40 confirms to 14 digits); h(7/4) > 1/128 decided on both.
    D2  u(9/5) in [0.004312491729413063275865581947004,
                   0.004312491729413063275865581947005] (flint, 350 bits;
        iv confirms); u(9/5) > 1/256 decided on both.
    D3  log2(69/(5 log 23)) in [2.137903503656002856060611381367,
                                2.137903503656002856060611381368]
        (flint, 350 bits; iv dps 40 agrees to all displayed digits);
        > 17/8 decided on both.
    W1  hi(x* enclosure) < 173/100 on both backends: any zero with
        Re s >= 1.73 has Re s > x*.
    W2  lo(sigma_c enclosure) > 7/4 on both backends.
    W3  lo(sigma_c enclosure) > 177/100 on both backends: the window
        (1.73, 1.77) sits inside (1, sigma_c).
    W4  hi(sigma_c enclosure) < 89/50 on both backends: any zero with
        Re s >= 1.78 has Re s > sigma_c.
    W5  lo(sigma_3 enclosure) > 91/50 on both backends: the window
        (1.78, 1.82) sits inside (1, sigma_3).

W1-W5 are exact Fraction comparisons against outward-rounded decimal
endpoints; outward rounding only widens an enclosure, so each comparison
also holds for the underlying enclosure. Everything else in this file is
mathematics, proved below or cited in section 7.

## 1. Lemmas

### Lemma 1 (the balance function and its unique root)

Let q be prime. On (1, infinity):

(i) the series defining g_q converges locally uniformly, and g_q is
continuous;
(ii) g_q is strictly decreasing;
(iii) g_q(sigma) -> -1 as sigma -> infinity, and g_q(sigma) > 0 for some
sigma > 1;
(iv) hence g_q has exactly one root sigma_c(q) in (1, infinity), and

    h_q > 0 on (1, sigma_c(q)),   h_q(sigma_c(q)) = 0,
    h_q < 0 on (sigma_c(q), infinity).

*Proof.* (i) For [a, b] contained in (1, infinity) and sigma in [a, b],
each term satisfies (q/p)^sigma <= (q/p)^a, and sum_{p > q} (q/p)^a
<= q^a * sum_{n >= 2} n^{-a} < infinity; the Weierstrass M-test gives
uniform convergence on [a, b], and a uniform limit of continuous functions
is continuous.

(ii) For 1 < sigma < sigma', g_q(sigma) - g_q(sigma') =
sum_{p > q} [(q/p)^sigma - (q/p)^{sigma'}]. Every term is strictly
positive because 0 < q/p < 1, and the sum of a convergent series of
positive terms is positive. So g_q(sigma) > g_q(sigma').

(iii) For sigma >= 2,

    0 < g_q(sigma) + 1 = sum_{p > q} (q/p)^sigma
      <= sum_{n > q} (q/n)^sigma
      <= (q/(q+1))^sigma + q^sigma * int_{q+1}^infinity x^{-sigma} dx
      =  (q/(q+1))^sigma * (1 + (q+1)/(sigma - 1))  ->  0

as sigma -> infinity, since q/(q+1) < 1. For positivity near 1: by
Lemma 1a below, sum_{p > q} 1/p diverges, so there are finitely many
primes q < p_1 < ... < p_J with q * sum_{j <= J} 1/p_j > 2. Then

    liminf_{sigma -> 1+} g_q(sigma)
      >= lim_{sigma -> 1+} sum_{j <= J} (q/p_j)^sigma - 1
      =  q * sum_{j <= J} 1/p_j - 1  >  1  >  0,

so g_q(sigma) > 0 for sigma close enough to 1.

(iv) By (iii) there are points where g_q > 0 and points where g_q < 0
(any sigma large enough that g_q(sigma) < -1/2); by (i) and the
intermediate value theorem g_q has a root; by (ii) the root is unique and
the sign pattern is as stated. Multiplying by q^{-sigma} > 0 transfers the
sign pattern to h_q. QED.

For q = 2 and q = 3 the decided endpoint signs in T1 (h(17/10) > 0,
h(19/10) < 0; u(9/5) > 0, u(37/20) < 0) place the roots in (1.7, 1.9) and
(1.8, 1.85), and the decided bisection brackets in T1 locate them to the
stated widths. The bisection invariant maintained decided opposite endpoint
signs at every step, so each reported bracket contains a root of the
respective function; by Lemma 1(iv) that root is the only one, so the
brackets locate sigma_c and sigma_3 themselves. (No monotonicity of h or u
enters this location argument, only sign logic; the decided derivative
guards are an independent confirmation on the bracketed ranges.)

### Lemma 1a (Euler: the prime harmonic series diverges)

sum_p 1/p diverges; hence so does sum_{p > q} 1/p for every q.

*Proof.* For an integer N >= 2, every n <= N factors into prime powers
with all primes <= N (fundamental theorem of arithmetic, cited in
section 7), so expanding each geometric factor,

    prod_{p <= N} (1 - 1/p)^{-1} = prod_{p <= N} (1 + 1/p + 1/p^2 + ...)
      >= sum_{n <= N} 1/n > log N.

Taking logarithms, sum_{p <= N} -log(1 - 1/p) > log log N. For
0 < x <= 1/2,

    -log(1 - x) = x + x^2/2 + x^3/3 + ...
                <= x + (x^2/2) * (1 + x + x^2 + ...) = x + x^2/(2(1-x))
                <= x + x^2,

so sum_{p <= N} 1/p > log log N - sum_p 1/p^2 > log log N - 1, which is
unbounded in N. Removing the finitely many primes <= q changes the sum by
a constant. QED.

### Lemma 2 (polygon lemma)

Let r_1 >= r_2 >= ... >= r_N > 0 with N >= 2 and r_1 <= r_2 + ... + r_N.
Then there are real phases theta_1, ..., theta_N with

    sum_{j <= N} r_j * e^{i theta_j} = 0.

*Proof.* N = 2: the hypothesis gives r_1 <= r_2, and the ordering gives
r_2 <= r_1, so r_1 = r_2; take (theta_1, theta_2) = (0, pi).

N >= 3: partition into three groups. Group a is {r_1}, with sum a = r_1.
Distribute r_2, r_3, ..., r_N in this order, each to whichever of the two
piles b, c currently has the smaller sum (ties arbitrarily). After placing
r_2 the pile difference is |b - c| = r_2; inductively, placing r_j (which
satisfies r_j <= r_2) onto the smaller pile changes the difference from d
to |d - r_j| <= max(d, r_j) <= r_2. So at the end |b - c| <= r_2 <= r_1,
and b + c = r_2 + ... + r_N >= r_1 by hypothesis, and b >= r_2 > 0,
c >= r_3 > 0 (the first two placements land on empty piles). The three
sums (a, b, c) therefore satisfy all three triangle inequalities:

    a <= b + c   (hypothesis),
    b <= a + c   (since b - c <= r_2 <= a),
    c <= a + b   (same).

Consequently |a - b| <= c <= a + b, which is equivalent to
|a^2 + b^2 - c^2| <= 2ab, so

    phi = arccos( (a^2 + b^2 - c^2) / (2ab) )

is well defined in [0, pi]. Then

    |a + b e^{i(pi - phi)}|^2 = a^2 - 2ab cos(phi) + b^2 = c^2,

so a + b e^{i(pi - phi)} = c e^{i xi} for some real xi, and

    a + b e^{i(pi - phi)} + c e^{i(xi + pi)} = 0.

Assign theta_j = 0 for the member of group a, theta_j = pi - phi for every
member of group b, and theta_j = xi + pi for every member of group c; the
grouped sum is the displayed one, so it vanishes. QED.

This is the classical closing-polygon fact ("a polygon with prescribed
side lengths closes iff no side exceeds the sum of the others"); the proof
is included so no citation carries load.
### Lemma 3 (multiplicative independence of the primes)

Let q_1 < q_2 < ... < q_n be distinct primes and m_1, ..., m_n integers
with q_1^{m_1} * ... * q_n^{m_n} = 1. Then every m_j = 0. Equivalently,
{log q_1, ..., log q_n} is linearly independent over Q.

*Proof.* Move the factors with negative exponents to the other side:

    prod_{m_j > 0} q_j^{m_j} = prod_{m_j < 0} q_j^{-m_j}.

Both sides are positive integers, and their prime supports are disjoint
subsets of {q_1, ..., q_n}. By the uniqueness half of the fundamental
theorem of arithmetic (section 7), an integer larger than 1 cannot have
two factorizations with disjoint prime supports, so both sides equal 1 and
all exponents vanish. For Q-linear independence: a rational relation
sum c_j log q_j = 0 clears denominators to an integer relation
sum m_j log q_j = 0, which exponentiates to prod q_j^{m_j} = 1. QED.

### Lemma 4 (phase steering with positive density; Kronecker via Weyl)

Let q_1 < ... < q_n be distinct primes, alpha_1, ..., alpha_n real
targets, and 0 < delta <= 1. Let

    G = { t in R : |e^{-i t log q_j} - e^{i alpha_j}| <= delta
                   for every j <= n }.

Then G has positive lower density: with |.| Lebesgue measure,

    liminf_{T -> infinity} |G intersect [0, T]| / T >= (delta/(2 pi))^n.

In particular G is unbounded above, and for every spacing Delta > 0 it
contains an increasing sequence t_1 < t_2 < ... with t_{k+1} - t_k >= Delta.

*Proof.* Since |e^{ia} - e^{ib}| = 2 |sin((a - b)/2)| <= dist(a - b, 2 pi Z),
it suffices to steer angles: t belongs to G whenever

    dist( -t log q_j - alpha_j , 2 pi Z ) <= delta      for every j.

Work on the n-torus T^n = (R/Z)^n with coordinates

    y_j(t) = ( -t log q_j - alpha_j ) / (2 pi)   mod 1.

The angle condition says y(t) lies in the closed box B of points whose
j-th coordinate is within delta/(2 pi) of 0 (mod 1), for every j; B has
measure (delta/pi)^n. Let B' be the shrunk box with half-width
delta/(4 pi) per coordinate, of measure (delta/(2 pi))^n, and let phi be
the product of per-coordinate continuous tent functions equal to 1 on the
B' interval, 0 outside the B interval, linear between; then
1_B >= phi >= 1_{B'} pointwise and int phi >= (delta/(2 pi))^n.

Fix eta > 0. By the Stone-Weierstrass theorem (trigonometric polynomials
are dense in continuous functions on T^n, sup norm; section 7) there is a
finite sum p_eta(y) = sum_{m in M} c_m e^{2 pi i m . y} with
sup |phi - p_eta| <= eta. For the mean along the flow:

    (1/T) int_0^T e^{2 pi i m . y(t)} dt,
    m . y(t) = -( t / (2 pi) ) * sum_j m_j log q_j
               - (1/(2 pi)) * sum_j m_j alpha_j.

For m != 0 the coefficient omega_m = -(sum_j m_j log q_j)/(2 pi) of t is
nonzero by Lemma 3, so the integral has modulus at most
2 / (2 pi |omega_m| T) -> 0 as T -> infinity. For m = 0 the integrand is
the constant c_0, and |c_0 - int phi| = |int (p_eta - phi)| <= eta. Since
M is finite,

    (1/T) int_0^T phi(y(t)) dt
      >= (1/T) int_0^T Re p_eta(y(t)) dt - eta
      ->  Re c_0 - eta  >=  int phi - 2 eta.

Using 1_B >= phi,

    liminf_T (1/T) |{ t in [0, T] : y(t) in B }|
      >= int phi - 2 eta >= (delta/(2 pi))^n - 2 eta,

and eta was arbitrary, so the lower density is at least (delta/(2 pi))^n.
A set of positive lower density is unbounded (a subset of [0, T_0] has
density 0), and greedily picking points separated by at least Delta from
an unbounded set never terminates. QED.

Provenance: this is Kronecker's approximation theorem in its flow form,
with Weyl's equidistribution method giving the density; sources in
section 7. The proof is included so the citations carry no load.

### Lemma 5 (equality in the triangle inequality)

Let (a_k) be complex numbers, countably many, with sum |a_k| finite and
positive. If |sum a_k| = sum |a_k|, then there is a single unit complex
number w with a_k = |a_k| * w for every k.

*Proof.* Let A = sum a_k and w = A / |A| (defined since
|A| = sum |a_k| > 0). Then

    sum |a_k| = |A| = Re( conj(w) * A ) = sum Re( conj(w) * a_k ),

so sum ( |a_k| - Re(conj(w) a_k) ) = 0 with every summand nonnegative
(since Re z <= |z|). Hence Re(conj(w) a_k) = |a_k| for every k, which
forces conj(w) a_k = |a_k|, that is a_k = |a_k| w. QED.

## 2. Theorem A: the wall

**Theorem A.** Let q be prime and sigma_c(q) the unique root from
Lemma 1(iv). Then:

(a) for every s with Re s = sigma > sigma_c(q),

    |P_q(s)| >= q^{-sigma} - sum_{p > q} p^{-sigma} = -h_q(sigma) > 0;

(b) P_q has no zero with Re s = sigma_c(q).

Hence every zero s of P_q with Re s > 1 satisfies Re s < sigma_c(q), and
there are no zeros with Re s >= sigma_c(q).

In particular, for q = 2: every zero of the prime zeta function P with
Re s > 1 has Re s < sigma_c, and there are no zeros with Re s >= sigma_c,
where sigma_c is located by the decided enclosures of T1
(1.77954465354699411644589878696544... , flint 350 bits, iv dps 40
confirming). For q = 3 the same holds with sigma_3
(1.82522595607384576238787271088892... , same backends).

*Proof.* (a) By the triangle inequality, for Re s = sigma,

    |P_q(s)| = | q^{-s} + sum_{p > q} p^{-s} |
             >= |q^{-s}| - sum_{p > q} |p^{-s}|
             =  q^{-sigma} - sum_{p > q} p^{-sigma} = -h_q(sigma),

and h_q(sigma) < 0 for sigma > sigma_c(q) by Lemma 1(iv).

(b) Suppose P_q(s) = 0 with s = sigma_c(q) + i t. Then
q^{-s} = - sum_{p > q} p^{-s}, and taking moduli,

    q^{-sigma_c(q)} = | sum_{p > q} p^{-s} |
                    <= sum_{p > q} p^{-sigma_c(q)}
                    =  q^{-sigma_c(q)},

the last equality because h_q(sigma_c(q)) = 0. So the triangle inequality
holds with equality for the infinite sum, and Lemma 5 gives a unit w with
p^{-s} = p^{-sigma_c(q)} w for every p > q. Pick any three primes
q < p1 < p2 < p3 (there are infinitely many primes). Equal phases mean

    t * log(p2/p1) = 2 pi m,    t * log(p3/p1) = 2 pi n

for some integers m, n. If t != 0 then m != 0 and n != 0 (the logarithms
are nonzero); eliminating t,

    n * log(p2/p1) = m * log(p3/p1),
    i.e.  p2^n * p1^{m-n} * p3^{-m} = 1,

so by Lemma 3 m = n = 0, a contradiction. Hence t = 0; but then
P_q(sigma_c(q)) = q^{-sigma_c(q)} + sum_{p > q} p^{-sigma_c(q)}
= 2 q^{-sigma_c(q)} > 0, contradicting P_q(s) = 0. So no such zero
exists. Combining (a) and (b): no zeros with Re s >= sigma_c(q); since
sigma_c(q) > 1, every zero in Re s > 1 has Re s < sigma_c(q). QED.

Grades: Theorem A's proof is exact mathematics with no numeric input. The
numerics enter only in *locating* sigma_c and sigma_3 (the T1 enclosures,
decided on both backends) and in comparing them with x* (the decided
separation), which is what turns Theorem A into a statement about the
conjectures.

## 3. Theorem B: existence of zeros up to the wall

**Theorem B.** Let q be prime, and let sigma_1 and eps > 0 satisfy
(sigma_1 - eps, sigma_1 + eps) contained in (1, sigma_c(q)). Then P_q has
infinitely many zeros with Re s in (sigma_1 - eps, sigma_1 + eps); indeed
infinitely many with |Re s - sigma_1| < eps/2, with imaginary parts
unbounded above. (Coefficients are real, so zeros come in conjugate
pairs.)

*Proof.* Write sigma_- = sigma_1 - eps/2. Note sigma_- > 1: the window
hypothesis gives sigma_1 - eps >= 1, so sigma_- = sigma_1 - eps + eps/2
>= 1 + eps/2 > 1.

Step 1 (ring margin). sigma_1 < sigma_c(q), so h_q(sigma_1) > 0 by
Lemma 1(iv):

    q^{-sigma_1} < sum_{p > q} p^{-sigma_1}.

No numerics are needed for general sigma_1; for the two demonstration
instances used later the margin is also decided directly, on both
backends: h_2(7/4) > 1/128 (T1, D1) and h_3(9/5) > 1/256 (T1, D2).

Step 2 (aggregated tail and the twisted series). Let
T_X = sum_{p in S_q, p > X} p^{-sigma_1}, a tail of a convergent series,
strictly positive (there are infinitely many primes) and decreasing to 0
in X. Choose X large enough that T_X <= q^{-sigma_1} and that some prime
lies in (q, X]. Consider the finite list of positive reals

    q^{-sigma_1};   p^{-sigma_1} for p in S_q, q < p <= X;   T_X.

Its largest member is q^{-sigma_1} (every p-term with p > q is smaller;
T_X <= q^{-sigma_1} by choice of X), and by Step 1

    q^{-sigma_1} < sum_{q < p <= X} p^{-sigma_1} + T_X,

which is the sum of the other members. Lemma 2 applies (N >= 3) and gives
phases theta_q, theta_p (q < p <= X), theta_* with

    q^{-sigma_1} e^{i theta_q}
      + sum_{q < p <= X} p^{-sigma_1} e^{i theta_p}
      + T_X e^{i theta_*} = 0.

Set theta_p := theta_* for every p in S_q with p > X, and define the
twisted series

    P_theta(s) = sum_{p in S_q} e^{i theta_p} p^{-s}.

At s = sigma_1 the tail sums to e^{i theta_*} T_X, so P_theta(sigma_1) = 0
exactly.

Step 3 (the twisted series is analytic and not identically zero). The
same M-test as Lemma 1(i) shows the series converges locally uniformly in
Re s > 1, so P_theta is analytic there (locally uniform limits of analytic
functions are analytic). It is not identically zero: the wall bound is
phase-blind, so for Re s = sigma > sigma_c(q),

    |P_theta(s)| >= q^{-sigma} - sum_{p > q} p^{-sigma} > 0

exactly as in Theorem A(a).

Step 4 (an isolating circle). The zeros of the analytic, not identically
zero P_theta are isolated, so the compact disk |s - sigma_1| <= eps/2
(inside Re s > 1, since sigma_1 - eps/2 = sigma_- > 1) contains finitely
many of them, giving finitely many moduli |z - sigma_1|. Choose

    rho in (0, eps/2]  with  rho != |z - sigma_1| for every zero z,

so P_theta has no zero on the circle C = {|s - sigma_1| = rho}, and

    m := min_{s on C} |P_theta(s)| > 0

(a continuous, nonvanishing modulus on a compact circle).

Step 5 (cutting the free tail). Every s on or inside C has
Re s >= sigma_1 - rho >= sigma_-. Since sum_{p} p^{-sigma_-} converges,
choose Y >= X with

    2 * sum_{p in S_q, p > Y} p^{-sigma_-}  <=  m/2.

Step 6 (steering). Let C_Y = sum_{p in S_q, p <= Y} p^{-sigma_-} (finite,
positive) and delta = min(1, m/(4 C_Y)). Apply Lemma 4 to the finitely
many primes p in S_q with p <= Y, targets theta_p: the set G of times t_0
with

    | p^{-i t_0} - e^{i theta_p} | <= delta   for all p in S_q, p <= Y

has positive lower density.

Step 7 (comparison and Rouche). Fix t_0 in G. For s on C,

    P_q(s + i t_0) - P_theta(s)
      = sum_{p in S_q} ( p^{-i t_0} - e^{i theta_p} ) p^{-s},

and splitting at Y, using |p^{-s}| = p^{-Re s} <= p^{-sigma_-} and
|p^{-i t_0} - e^{i theta_p}| <= 2:

    | P_q(s + i t_0) - P_theta(s) |
      <= delta * C_Y + 2 * sum_{p > Y, p in S_q} p^{-sigma_-}
      <= m/4 + m/2 < m <= |P_theta(s)|.

Both s -> P_q(s + i t_0) and P_theta are analytic on an open neighborhood
of the closed disk bounded by C (the disk lies in Re s > 1, and
translation by i t_0 preserves the half-plane). The strict inequality
|f - g| < |g| on C (with f = P_q(. + i t_0), g = P_theta) is Rouche's
hypothesis (section 7; it also forces g != 0 on C, consistent with
Step 4). Therefore f and g have the same number of zeros inside C,
counted with multiplicity; g has at least one (sigma_1, Step 2). So there
is s' with |s' - sigma_1| < rho and P_q(s' + i t_0) = 0, i.e. a zero of
P_q at s'' = s' + i t_0 with

    Re s'' in (sigma_1 - rho, sigma_1 + rho)
           subset [sigma_1 - eps/2, sigma_1 + eps/2],
    Im s'' in (t_0 - rho, t_0 + rho).

Step 8 (infinitude). By Lemma 4, G contains t_1 < t_2 < t_3 < ... with
consecutive gaps larger than 2 rho. The zeros produced for distinct t_k
have imaginary parts in pairwise disjoint intervals, so they are pairwise
distinct, and their imaginary parts tend to infinity. Every one of them
has Re s within eps/2 of sigma_1, hence inside
(sigma_1 - eps, sigma_1 + eps). QED.

**Corollary B1 (the supremum).** For every prime q,

    sup { Re s : P_q(s) = 0, Re s > 1 } = sigma_c(q),

and the supremum is not attained. *Proof.* Theorem A gives Re s <
sigma_c(q) for every zero. For any sigma_1 < sigma_c(q) choose eps with
(sigma_1 - eps, sigma_1 + eps) inside (1, sigma_c(q)); Theorem B gives
zeros with Re s > sigma_1 - eps, and sigma_1 was arbitrary below
sigma_c(q). QED.

**Corollary B2 (Conjecture 1 is false).** Take q = 2, sigma_1 = 7/4,
eps = 1/50. The window (1.73, 1.77) lies inside (1, sigma_c): its right
end is below sigma_c because lo(sigma_c enclosure) > 177/100 (decided,
W3, both backends), and its left end exceeds 1. Theorem B: P has
infinitely many zeros with Re s in (1.73, 1.77). Every such zero has
Re s > x*, because hi(x* enclosure) < 173/100 (decided, W1, both
backends). Hence the real parts of the zeros of the prime zeta function
are not bounded by x*: Conjecture 1 of OEIS A107311 is false. By
Corollary B1 the correct bound is sigma_c, which exceeds x* by more than
1/20 (decided separation, T1), and it is a supremum, not a maximum.
## 4. Theorem C: subsets

### Theorem C1 (the subset {p >= 3} refutes Conjecture 2)

Theorems A and B hold verbatim for q = 3 (their proofs never use q = 2:
Lemmas 1-5 are stated for a general prime q, and the independence in
Lemmas 3 and 4 holds for any finite set of distinct primes). Hence:

(a) every zero of P_3(s) = sum_{p >= 3} p^{-s} with Re s > 1 has
    Re s < sigma_3, and none has Re s >= sigma_3;
(b) taking sigma_1 = 9/5, eps = 1/50: the window (1.78, 1.82) lies inside
    (1, sigma_3) because lo(sigma_3 enclosure) > 91/50 (decided, W5, both
    backends), and the ring margin at 9/5 is decided directly
    (u(9/5) > 1/256, D2). P_3 has infinitely many zeros with Re s in
    (1.78, 1.82).

Every zero from (b) has Re s > 1.78 > 1.73 > x* (decided, W1). So the
subset S = {p >= 3} violates Conjecture 2 of OEIS A107311: its zeros'
real parts are not bounded by x*.

Remark (a subset out-walls the full series). By W4 (hi(sigma_c enclosure)
< 89/50, decided, both backends), every zero from (b) also has
Re s > sigma_c: removing the prime 2 moves the wall right, and the subset
series has zeros strictly beyond the supremum for the full series. The
decided enclosures give sigma_3 - sigma_c > 0.045 (exact rational compare
of lo(sigma_3) - hi(sigma_c) on the flint leg gives at least
1.8252259560738457... - 1.7795446535469942 > 0.0456813); the subset
conjecture is not merely false, it fails by more than the full-series one.

### Theorem C2 (tail subsets have unbounded walls)

For the k-th prime p_k let S_{p_k} = {p : p >= p_k} and let sigma_c(p_k)
be its wall (Lemma 1(iv), which applies to every q since Lemma 1a gives
the divergence for every tail). Then for every p_k >= 23,

    sigma_c(p_k) >= log2( 3 p_k / (5 log p_k) ),

and the right side tends to infinity with k. Consequently, for every real
M there is a k such that P_{p_k} has infinitely many zeros with Re s > M.

*Proof.* The count input is Rosser and Schoenfeld's Corollary 3 of their
Theorem 2, inequality (3.8) (section 7):

    3x / (5 log x) < pi(2x) - pi(x)      for 20.5 <= x.

Apply it at x = p_k >= 23 > 20.5: the interval (p_k, 2 p_k] contains more
than 3 p_k / (5 log p_k) primes, each a member of S_{p_k} exceeding p_k
and at most 2 p_k. Hence for any T > 1,

    sum_{p > p_k} p^{-T} >= sum_{p in (p_k, 2 p_k]} p^{-T}
                         >= (3 p_k / (5 log p_k)) * (2 p_k)^{-T}.

Since (2 p_k)^{-T} = 2^{-T} p_k^{-T}, the right side exceeds p_k^{-T}
exactly when 2^{-T} * 3 p_k / (5 log p_k) > 1, that is when

    T < B_k := log2( 3 p_k / (5 log p_k) ).

So h_{p_k}(T) > 0 for every T in (1, B_k). If sigma_c(p_k) were smaller
than B_k, any T in (sigma_c(p_k), B_k) would have h_{p_k}(T) < 0 by
Lemma 1(iv), a contradiction; hence sigma_c(p_k) >= B_k. (When B_k <= 1
the inequality is trivially true since sigma_c(p_k) > 1.)

Unboundedness: x / log x is increasing for x > e (its derivative is
(log x - 1)/log^2 x) and unbounded, and p_k -> infinity, so B_k ->
infinity. Decided instance, k = 9, p_9 = 23:

    B_9 = log2(69 / (5 log 23))
        in [2.137903503656002856060611381367,
            2.137903503656002856060611381368]
    (flint, 350 bits; mpmath.iv at dps 40 agrees to all displayed digits),
    B_9 > 17/8 decided on both backends (D3):

the wall of {p >= 23} exceeds 2.125, already far beyond x* and sigma_c.

Zero production: given M, choose k with B_k > max(M, 3/2) (possible since
B_k -> infinity), so sigma_c(p_k) > max(M, 3/2). Set

    sigma_1 = ( max(M, 3/2) + sigma_c(p_k) ) / 2,
    eps     = ( sigma_c(p_k) - max(M, 3/2) ) / 4;

then (sigma_1 - eps, sigma_1 + eps) is contained in
(max(M, 3/2), sigma_c(p_k)), which lies inside (1, sigma_c(p_k)).
Theorem B for q = p_k gives infinitely many zeros of P_{p_k} with
Re s > max(M, 3/2) >= M. QED.

### Corollary C3 (Conjecture 2 fails without bound)

For every real M there is a subset S of the primes (a tail {p >= p_k})
such that sum_{p in S} p^{-s} has infinitely many zeros with Re s > M. No
constant, in particular not x*, bounds the real parts of the zeros over
all subsets. Conjecture 2 is false for every possible replacement
constant, not just for x*.

Scope note: the refuting subsets are infinite. Nothing in this file is
claimed about finite subsets (whose series are exponential polynomials
with walls of their own); the conjecture quantifies over all subsets, so
the infinite witnesses settle it.

## 5. What exactly is refuted

**Conjecture 1** ("the real parts of the zeros of the prime zeta function
are not greater than [x*]"): **false.** Theorem B (Corollary B2) produces
infinitely many zeros of P with Re s in (1.73, 1.77), every one exceeding
x* (decided compares W1, W3). Theorem A plus Corollary B1 identify the
true threshold: sup of the real parts is sigma_c = 1.779544653546994...
(decided enclosures, T1), strictly above x* by more than 1/20 (decided
separation), approached but not attained. The zeros produced lie in
Re s > 1, where every reading of "the prime zeta function" agrees with
the series (SOURCE.md section 2), so the refutation is
reading-independent.

**Conjecture 2** ("... the anyone subset ..."): **false, twice over.**
First, the concrete subset {p >= 3}: infinitely many zeros with Re s in
(1.78, 1.82) (Theorem C1), beyond x* and even beyond sigma_c. Second, the
tails {p >= p_k}: walls at least log2(3 p_k/(5 log p_k)) -> infinity
(Theorem C2), with zeros beyond every fixed bound (Corollary C3). The
{p >= 23} instance is decided: its wall exceeds 17/8 (D3).

**What is not claimed.** No explicit zero is exhibited; existence is by
Rouche, and the first witnesses may sit at astronomical heights
(MISSION.md; the value margins are parts in a thousand). Nothing is
claimed about zeros with Re s <= 1, about the continuation beyond the
series' half-plane, or about finite subsets. None of this bears on the
Riemann Hypothesis: the zeros produced are zeros of P and of subset
series in Re s > 1, not zeros of zeta, and x* keeps its correct role as
the partial-sums threshold of Borwein, Fee, Ferguson and van der Waall
(SOURCE.md section 3). The error in the OEIS comment is a transplant: a
constant from a family whose wall is never attained (partial sums, with
rationally dependent frequencies log n) was conjectured onto a family
with independent frequencies, where the wall is different, larger, and
actually approached.

## 6. Which step carries which grade

Per the vocabulary contract in MISSION.md, the replacement theorem is a
composite: decided inequalities glued by classical arguments, with the
glue proved in this file. The grade of each step:

**Decided** (interval/ball enclosure with exact endpoint sign logic;
python-flint (arb) at 350 bits and mpmath.iv at dps 40, independent code
paths, every item decided on both backends):

  - the enclosures of x*, sigma_c, sigma_3 (T1; decided.json);
  - endpoint signs h(17/10) > 0, h(19/10) < 0, u(9/5) > 0, u(37/20) < 0;
  - the separation sigma_c - x* > 1/20 and the margin h(x*) > 1/60;
  - the derivative guards on [1.7, 1.9] and [1.8, 1.85] (confirmation
    only; Lemma 1 supersedes them);
  - D1 (h(7/4) > 1/128), D2 (u(9/5) > 1/256), D3 (B_9 > 17/8);
  - W1-W5 (exact rational compares against decided endpoints).

**Proved in this file** (complete proofs, no numeric content): Lemmas 1,
1a, 2, 3, 4, 5; Theorems A, B, C1, C2; Corollaries B1, B2, C3.

**Cited without reproof** (textbook or classical, hypotheses checked
explicitly where used; access notes in section 7): the fundamental
theorem of arithmetic (Lemmas 1a, 3); Rouche's theorem (Theorem B,
step 7); Stone-Weierstrass on the torus (Lemma 4); Rosser-Schoenfeld
Corollary 3, inequality (3.8) (Theorem C2); and standard facts of
analysis (M-test, intermediate value theorem, analyticity of locally
uniform limits, isolation of zeros of analytic functions).

**Composite grade**: every numeric input is decided on both backends; no
claim rests on a measured-only number. The remaining steps are classical
mathematics, proved here or standard. Nothing in this file is
kernel-checked, and nothing in this file uses or may use the reserved
enclosure vocabulary of zeta/rigor.py.

## 7. Citations, with access notes

1. J. B. Rosser and L. Schoenfeld, "Approximate formulas for some
   functions of prime numbers", Illinois J. Math. 6 (1962), no. 1,
   pp. 64-94. Used: Corollary 3 of Theorem 2, inequality (3.8):
   3x/(5 log x) < pi(2x) - pi(x) for 20.5 <= x. Access note (2026-08-16):
   a scanned copy served at denise.vella.chemla.free.fr
   /Rosser-Schoenfeld-1962.pdf was fetched and its text extracted; the
   corollary block reads "COROLLARY 3. We have 3x/(5 log x) < [pi](2x) -
   [pi](x) (3.8) ... for 20 1/2 <= x" (OCR of the scan; Greek pi
   transcribed). The neighboring Corollary 1 in the same extraction
   carries x/log x < pi(x) for 17 <= x and pi(x) < 1.25506 x/log x for
   1 < x, the constants universally quoted from this paper, which
   cross-checks the OCR.
2. G. H. Hardy and E. M. Wright, An Introduction to the Theory of
   Numbers, 6th ed., Oxford University Press, 2008. Used: the fundamental
   theorem of arithmetic (Theorem 2 there) for Lemmas 1a and 3; Chapter
   XXIII (Kronecker's theorem) and Section 22.7 (Mertens) as provenance
   for Lemmas 4 and 1a. Access note: theorem and chapter numbers quoted
   from memory, not re-checked against a copy in this session; no load
   rests on the numbering, since the proofs used here are included above.
3. H. Weyl, "Uber die Gleichverteilung von Zahlen mod. Eins", Math. Ann.
   77 (1916), pp. 313-352. Provenance for the equidistribution method in
   Lemma 4; the flow argument used is the standard Weyl-criterion
   computation, written out in full above. Access note: not consulted in
   this session.
4. Rouche's theorem, in the form: f and g analytic on an open set
   containing a closed disk, |f - g| < |g| on the boundary circle; then f
   and g have equally many zeros (with multiplicity) inside. Standard
   texts: E. C. Titchmarsh, The Theory of Functions, 2nd ed., Oxford,
   1939, Chapter III (argument principle and Rouche); L. V. Ahlfors,
   Complex Analysis, 3rd ed., McGraw-Hill, 1979, Chapter 4, Section 5.
   Access note: section placements from memory, not re-checked in this
   session; the hypotheses are checked explicitly in Theorem B, step 7.
5. Stone-Weierstrass theorem (trigonometric polynomials dense in the
   continuous functions on the n-torus, sup norm), e.g. W. Rudin,
   Principles of Mathematical Analysis, 3rd ed., McGraw-Hill, 1976,
   Chapter 7 (the complex, self-adjoint form). Access note: chapter from
   memory, not re-checked in this session.
6. H. Bohr, "Zur Theorie der allgemeinen Dirichletschen Reihen", Math.
   Ann. 79 (1918), pp. 136-156. Provenance only: the vertical-translation
   method behind Theorem B descends from Bohr's work on general Dirichlet
   series; no statement of his is invoked. Access note: not consulted in
   this session.
7. P. Borwein, G. Fee, R. Ferguson, A. van der Waall, "Zeros of Partial
   Sums of the Riemann Zeta Function", Experimental Mathematics 16
   (2007), no. 1. Context only (the provenance of x*); pinned with access
   notes and two independent secondary quotes in SOURCE.md sections 1
   and 3. No step of Theorems A-C depends on it.
8. S. M. Gonek and A. H. Ledoan, "Zeros of partial sums of the Riemann
   zeta-function", IMRN 2010, no. 10, pp. 1775-1791; D. J. Platt and
   T. S. Trudgian, "Zeroes of partial sums of the zeta-function", LMS J.
   Comput. Math. 19 (2016). The secondary sources for the partial-sums
   wall, quoted verbatim in SOURCE.md section 3; context only.
9. C.-E. Froberg, "On the prime zeta function", BIT 8 (1968), no. 3,
   pp. 187-202. The only prior literature found on zeros of P (four
   observed roots, Table I); pinned via the zbMATH review in SOURCE.md
   section 4. Nothing above uses it.
10. OEIS A107311, revision 55 (2024-12-29), fetched 2026-08-15 and
    2026-08-16 (byte-identical): the conjecture text under refutation and
    the 102 digits of x*, pinned byte-for-byte in SOURCE.md section 1.

## 8. Gaps and honesty notes

- **The Rouche step closes.** MISSION.md kill condition 1 (the tail
  control fails to close for the infinite series) did not fire. The
  standard failure mode arises when the model function is a finite
  truncation: its tail is fixed by the cutoff, and the minimum m on the
  isolating circle can be smaller than that tail. Step 2 avoids this by
  phasing the *whole* series (the tail aggregated as one polygon side of
  modulus T_X), so the model P_theta carries the tail inside itself and
  vanishes exactly at sigma_1; the only errors left are the steering term
  (shrinkable via delta) and the beyond-Y remainder (shrinkable via Y,
  independent of X). Both are cut after m is fixed, so there is no
  circularity. No assumption was left undischarged.
- **Citation numbering.** Items 2, 4, 5 in section 7 carry access notes:
  their theorem/section numbers are from memory. The load they carry is
  bibliographic, not mathematical: every argument that uses them either
  includes a complete proof (Lemmas 1a, 3, 4) or checks the theorem's
  hypotheses explicitly against a stated standard form (Rouche). The one
  externally load-bearing count, Rosser-Schoenfeld (3.8), was re-checked
  against the paper's text this session (item 1).
- **No explicit witness zero.** WP6 (a steered witness at sigma about
  1.75, decided by a box count) remains open and optional; per MISSION.md
  its absence changes nothing here.
- **Not kernel-checked.** No Lean formalization of any step exists; the
  certainty ladder's top rung is untouched. A natural later rung would be
  Lemma 2 plus Theorem A (the wall is elementary); Theorem B needs
  equidistribution, which is a larger formalization lift.
- **Instrument defect, found and fixed during this work package.** The
  first run of the D3 decision produced disjoint enclosures on the two
  backends. Per MISSION.md kill condition 3 that marks the instrument,
  and it did: `iv_endpoints` in instrument.py converted interval
  endpoints through the global mp context (default dps 15), collapsing
  both endpoints of an iv result to one 53-bit float. Sign decisions were
  never at risk (rounding to nearest at relative precision cannot move a
  value across zero), so every decision in decided.json stands; value
  enclosures, however, were misreported beyond 15 digits. The fix reads
  the raw `_mpi_` endpoint pair (exact); `decide.py` re-run after the fix
  reproduced `decided.json` identically except timings, and the re-run D3
  enclosures agree on both backends to all displayed digits. Details in
  the docstring of `iv_endpoints` and in theorem_inputs.json notes.
- **Calibration (WP5) is not this file.** The same-code-path control
  against the partial-sums threshold is a separate work package; this
  file's claims do not depend on it, but the hunt's verdict should not be
  read before WP5 runs.
