# The barrier: what is proved, what is measured, what a proof needs

**Session 2026-09-07. Companion to RESULTS.md.** Everything in Sections 1
and 2 is proved (elementary, finite, checkable by `barrier_lemmas.py` and
`tests/test_certificate_lp_barrier.py`). Section 3 is measured. Section 4 is
the honest statement of the open step. Nothing here is about RH.

Notation as in RESULTS.md: c supported on [1, y], W(n) = sum_j c_j floor(n/j),
feasible means W(n) >= 1 for every integer cell 1 <= n <= N, and

    E(c) = B(N) - psi(N) = sum_{n=1}^{N} (W(n) - 1) m_n,
    m_n  = psi(N/n) - psi(N/(n+1))   (prime-power mass landing in cell n).

V*(y, N) - psi(N) = min over feasible c of E(c).

## 1. The dual lemma and its complete parametrization

**Lemma 1 (dual).** Let delta: {1,...,N} -> R satisfy
sum_n delta_n floor(n/j) = 0 for j = 1..y and delta_n >= -m_n for all n. Then
E(c) >= sum_n delta_n for every feasible c.

*Proof.* W - 1 >= 0 and m_n >= -delta_n give
E >= -sum_n (W(n) - 1) delta_n = -sum_j c_j sum_n delta_n floor(n/j) + sum_n delta_n
= sum_n delta_n. QED.

By LP duality the best such delta attains V*(y,N) - psi(N) exactly; the
primes are the point delta = 0.

**Lemma 2 (parametrization).** Write U(k) = sum_{n >= k} delta_n. Then the
moment conditions are sum_{m >= 1} U(jm) = 0 for j <= y, and for ANY function
T on (y, N] the choice

    U(k) = sum_{m >= 1} mu(m) T(km)

satisfies them, with gain sum_n delta_n = U(1) = sum_{m > y} mu(m) T(m).
Conversely every admissible U arises this way (Mobius inversion of
T(k) := sum_m U(km), which vanishes for k <= y). The only remaining constraint
is

    U(k) - U(k+1) >= -m_k     (k = 1..N),                                   (C)

i.e. the fake tail sum u* + U may rise from k to k+1 by at most the prime mass
m_k of that cell, and may fall freely.

`barrier_lemmas.py::restricted_dual` maximizes the gain over T supported on
(y, Y]; with Y = N it reproduces V*(y,N) - psi(N) to all printed digits at
(10^3, 31), which is the numerical check that the parametrization is complete.

**Lemma 3 (rough spikes).** For y-rough q in (y, N] take T(q) = -m_q. Then
U(1) = sum_q m_q, U(q) = -m_q, U = 0 elsewhere, (C) holds, and

    E(c) >= sum_{y < q <= N, q y-rough} m_q.

This is the primal statement W(q) >= 2 at every y-rough q (the jump of W at q
is c_1 = W(1) >= 1). Size about N/(y log y). Values: 4.23 (10^3, 31),
15.46 (10^4, 100), 35.81 (10^5, 316), 103.0 (10^6, 1000).

**What Lemma 3 cannot do.** The natural next construction, T = tau mu(m) on
(y, 2y], needs (C) at every k <= 2y with U(k) - U(k+1) < 0, and those include
cells with m_k = 0 as soon as 2y exceeds the range where every interval
(N/(k+1), N/k] contains a prime power (about k <= N^{0.32} by Baker-Harman-
Pintz, and in practice much less: at (10^4, 100) the largest feasible tau is
0). So the sign-alternating dual is dead at y = sqrt(N) for a structural
reason: beyond about N^{1/3} the fake measure may only rise at the sparse
prime cells floor(N/d), and any lower bound of order N/y or better at
y = sqrt(N) must route its gain through the slack in the cells below y.

## 2. The excess constant of a balanced certificate is a Mobius constant plus a
log-weighted deviation

For the all-N (lifted, regularized) version the excess per unit N is
H(c) = -sum_j c_j log j / j - 1 with sum_j c_j / j = 0. Writing c = mu_{<= y} + d:

**Proposition 4.** With M1(y) = sum_{j<=y} mu(j)/j and
I(y) = sum_{j<=y} mu(j) log(y/j)/j - 1 = sum_{j>y} mu(j) log(j/y)/j,

    H(c) = I(y) + sum_{j<=y} d_j log(y/j) / j - C(1) log y,

and C(1) = 0 for a balanced certificate, where sum_{j<=y} d_j / j = -M1(y).

*Proof.* H = -sum_j (mu(j) + d_j) log j/j - 1 = [-sum mu(j) log j/j - 1]
- sum d_j log j/j. The bracket is I(y) - M1(y) log y (partial summation of the
tail sum defining I), and -sum d_j log j/j = sum d_j log(y/j)/j - log y
(C(1) - M1(y)). QED. (Pinned as a finite identity in the tests.)

The point: I(y) is a fixed function of y (its Mellin kernel is 1/s^2, so it
is O(y^{-1/2}) under RH with no epsilon and Omega(y^{-1/2-eps})
unconditionally), and the whole freedom of a certificate is the log-weighted
harmonic sum of its deviation from mu. The balance forces the deviation to
carry harmonic mass -M1(y); feasibility (W >= 1) restricts where it may sit.
Measured at the LP optimum (10^4, 100): sum d_j log(y/j)/j = +0.0216,
I(100) = +0.0010, harmonic mass of d = -0.0271 against -M1(100) = -0.0311,
so the finite-N optimum is NOT balanced (C(1) = +0.0041) and pays a residual
drift of about C(1) N log(N/y) ~ 190 of its 324. Both candidate laws below
are consistent with this identity; it does not by itself decide the exponent.

## 3. Measured: the floor at support sqrt(N), and the two candidate laws

| N | y = sqrt N | E | E / (0.32 N / sqrt y) | E / (N |M1(y)|) |
|---:|---:|---:|---:|---:|
| 10^3 | 31 | 62.9 | 1.10 | 1.00 |
| 10^4 | 100 | 323.6 | 1.01 | 1.04 |
| 2 10^4 | 141 | 603.4 | 1.12 | 3.86 |
| 10^5 | 316 | 1781.7 | 0.99 | 4.73 |

The fluctuation law 0.32 N / sqrt(y) fits all four points to 12%; the drift
N |M1(y)| coincides with it exactly when M1(y) is of its typical size 0.3/sqrt(y)
(y = 31, 100) and undershoots by 4-5x at the two zero-crossings (y = 141, 316).
So the drift is a lower envelope, the fluctuation is the law:

    Conjecture (barrier).  V*(y, N) - psi(N) >= c N / sqrt(y)  for y <= sqrt N,
    with c about 0.3, for all large N.

The CI batch `.github/workflows/certificate-lp-barrier.yml` tests it at
(10^6, 1000) and (10^7, 3162), where the two laws predict 10.1k vs 4.4k and
57k vs 41k respectively; see RESULTS.md for the numbers when they land.

**Where the gain lives.** Restricted duals on (y, Y] as a fraction of the
full floor:

| (N, y) | Y = 2y | 4y | 10y | 30y | N |
|---|---:|---:|---:|---:|---:|
| (10^3, 31) | 0.46 | 0.65 | 0.90 | | 1.00 |
| (10^4, 100) | 0.20 | 0.51 | 0.73 | 0.90 | 1.00 |

Ninety percent of the barrier is decided by cells within a factor 30 of y.
A proof can work on (y, Cy] for bounded C.

**What the optimum looks like** (dense LP at (10^4, 100), `results/`):
c = mu(j) exactly for j <= 16 and irregular fractional coefficients after
that; W > 1 on 9889 of the 10^4 cells, with bumps up to 3.5 below y; beyond
y the elevation W - 1 averages 1.7 against a prime mass psi(N/y) ~ 94,
which is half the excess, the other half being the bumps below y weighted
by N/n^2. The fake prime measure of the dual puts zero mass in cells 17, 19,
20 (real mass 38, 26, 25), exactly where W > 1 (complementary slackness), and
+401 extra mass in cell 1.

## 4. The open step, stated precisely

The floor is E = sum_n (W(n) - 1) m_n with W(n) = n C(1) - sum_j c_j {n/j}
(sawtooth form). Beyond the Mobius prefix the sum of ~y unit-size sawtooths
has variance about (1/12) sum_{j,k} c_j c_k gcd(j,k)^2/(jk), whose diagonal is
sum c_j^2 / 12 >= 0.05 y' for a prefix y'. The measured E/(N/y) grows like
0.33 sqrt(y), i.e. the elevation W - 1 beyond y averages a constant times the
standard deviation of that sum: the pointwise constraint W >= 1 costs a
"three sigma" offset.

What is proved above gives only the variance-over-maximum offset
(mean elevation >= Var/(max W - 1), order N/y), because the L^2 inequality
cannot see a lower tail. The missing ingredient is an anti-concentration
statement:

    for every feasible c, the sawtooth sum sum_j c_j {n/j} lies at least
    c sqrt(sum c_j^2) below its mean on a positive proportion of the cells
    n in (y, Cy], weighted by m_n.

For a random-like c this is a fourth-moment (Paley-Zygmund) statement about
4-point correlations of sawtooths, which are elementary arithmetic sums. The
difficulty is that c is chosen by the adversary to defeat exactly this:
Chebyshev's period-30 seed has W in {0, 1}, no Gaussian behaviour at all, and
the LP optimum has a heavy upper tail (W up to 112 at (10^5, 316)). Any proof
must therefore either (a) show that reducing the lower-tail fluctuation of
sum_j c_j {n/j} below sqrt(y) forces c away from mu on the prefix at a cost
of order N sum (W(n) - 1)/n^2 that is itself >= N/sqrt(y), or (b) build a
dual T on (y, Cy] whose gain is N/sqrt(y) while routing every rise of
u* + U through the slack N/k^2 of the cells k <= y. The restricted-dual
numbers say (b) exists; the dense-LP dual says it moves prime mass from
prime cells (mu = -1) to composite ones (mu = 0, +1) and toward cell 1.
Neither construction is in hand.

Unconditionally, M1(y) = Omega(y^{-1/2 - eps}) infinitely often, and every
measured floor sits above N |M1(y)|; if that envelope is a theorem
(E >= c N |M1(y)|), the floor is infinitely often >= N^{3/4 - eps} at
y = sqrt N regardless of RH, which closes the route at that support. That
envelope statement is weaker than the conjecture and may be the provable one:
it is the assertion that cancelling the Mobius drift with staircases
supported above the prefix costs the drift itself, which is a statement about
the growth of W_mu(n) = n M1(y) - sum_{j<=y} mu(j) {n/j} on (y, 2y] where
W_mu(n) = 1 - (M(n) - M(y)) is literally the Mertens function.
