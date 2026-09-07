# The exact LP floor of the factorial-certificate route

**Correction and continuation, 2026-09-07:** Section 4.2's dimension-count
argument is false: N=27,y=9 has eight constrained cells but minimum excess
log(2), by an exact row relation and attaining vector. The inferred zero
for the uncomputed N=10^6 case is therefore unsupported by that argument.
The Section 5 exponent remains a conjecture, and the all-cell family also
admits a relaxation using attainable quotients without prime locations.
See the [counterexample, relaxed ceilings, and barrier audit](../../../../quotient_certificate/RESULTS.md).
The original session record below is retained.

**Session 2026-09-06/07. Grade: measured (floating LP, HiGHS dual simplex),
with every reported certificate re-verified cell by cell and every excess
recomputed directly from the von Mangoldt function. One rigorous inequality
(Section 5). No asymptotic theorem. No claim about RH.**

Input state: the adaptive block frozen as `research/adaptive-block-v1`
(PR #201, main `fae9dd6`), leading constant 1.03411910, unreviewed beyond the
producing session. This note does not review it. It asks a prior question:
what is the best any construction of that kind can do, and why.

## 1. The move, in plain English

Every construction in this hunt (balanced seeds, radix-15 lifts, consecutive
and reciprocal carries, small-prime masks, greedy repairs) produces one object:
a finite floor sum W(t) = sum_j c_j floor(t/j) with W >= 1 on the integer cells
1..N, and the ceiling B(N) = sum_j c_j log floor(N/j)!. For a fixed cutoff N and
a fixed support bound y, the set of all such W is a polytope and B is linear on
it. So the best possible certificate is a linear program, and its value is a
hard floor for the whole family at that (y, N):

    V*(y, N) = min  sum_{j<=y} c_j log floor(N/j)!
               s.t. sum_{j<=y} c_j floor(n/j) >= 1     (n = 1, ..., N).

Nothing in the family can have excess B(N) - psi(N) below V*(y,N) - psi(N).
The hunt spent its effort on hand-built feasible points of this LP; the LP
itself was never solved. Solving it answers "how far is the floor" and its
dual answers "where does the freedom the constructions cannot use sit".

## 2. The dual: fake primes that pass y Chebyshev tests

The dual LP is

    V*(y, N) = max  sum_n nu_n
               s.t. sum_n nu_n floor(n/j) = log floor(N/j)!   (j = 1..y),  nu >= 0.

Write u_n = sum_{m >= n} nu_m. Then sum_n nu_n floor(n/j) = sum_m u_{jm}, so
the dual asks for a nonincreasing u >= 0 whose sums over multiples match
log floor(N/j)! for j <= y, and maximises u_1. The primes are feasible:
u_n = psi(N/n) satisfies sum_m psi(N/(jm)) = log floor(N/j)! for every j (the
Chebyshev identity), with u_1 = psi(N). That single line is the statement
B(N) >= psi(N). The gap V* - psi(N) is exactly how much more total mass a
nonnegative measure on [1, N] can carry while passing the first y Chebyshev
tests. It is a moment problem, and the certificate route is its primal.

Reading it in the primal, with w = c * 1 (Dirichlet convolution):

    B(N) - psi(N) = sum_{m>=2} w(m) psi(N/m)
                  = sum_n [W(n) - 1] [psi(N/n) - psi(N/(n+1))].              (E)

So the excess is the elevation W(n) - 1 on each cell, weighted by the prime
mass that lands in the cell. For n < sqrt(N) that mass is about N/n^2; for
n > sqrt(N) it is Lambda(d) if n = floor(N/d) for a prime power d and zero
otherwise. Two-thirds of the cells above sqrt(N) carry no prime at all.

## 3. Method-imposed versus problem-imposed

From (E): the problem needs W >= 1 only at cells where a prime looks, that is
all n <= sqrt(N) (in practice) plus the ~2 sqrt(N)/log N cells floor(N/d) with
d <= sqrt(N) a prime power. The rule "W >= 1 on every integer cell" is what
makes a certificate prime-blind, and it is method-imposed. Everything else the
hunt fixed (radix 15, seed period, the carry shapes, the mask set, the repair
menu) is a choice of feasible subset inside the LP and is dominated by V*.

The relaxed LP with constraints only on the prime-looking cells S(N) is a
valid ceiling that uses the primes below sqrt(N) as input:

    P*(y, N) = min c.L  s.t.  W_c(n) >= 1 for n in S(N),   |S(N)| ~ 1.2 sqrt(N).

## 4. What was measured

All values are B - psi(N) with W re-verified on every constrained cell.
Files: `results/*.json`. Scripts: `lp_frontier.py` (dense, N <= 10^4),
`lp_allcells_cg.py` (constraint generation, reproduces the dense values to
all printed digits), `lp_prime_cells.py`, `lp_dictionaries.py`.

### 4.1 Prime-blind floor V*(y, N) - psi(N)

| N | y | y as N^a | excess | excess/N | excess/N^{3/4} | mobius prefix | nnz(c) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 10^3 | 31 | 0.50 | 62.92 | 0.0629 | 0.354 | 10 | 20 |
| 10^3 | 100 | 0.67 | 8.97 | 0.0090 | | | 67 |
| 10^3 | 200 | 0.77 | 0.000 | 0 | | | 168 |
| 10^4 | 31 | 0.37 | 781.94 | 0.0782 | | | 20 |
| 10^4 | 100 | 0.50 | 323.65 | 0.0324 | 0.324 | 16 | 88 |
| 10^4 | 316 | 0.63 | 32.54 | 0.0033 | | 47 | 254 |
| 10^4 | 500 | 0.67 | 9.04 | 0.0009 | | | 350 |
| 10^4 | 1000 | 0.75 | 0.693 = log 2 | | | | 679 |
| 10^4 | 2000 | 0.83 | 0.693 = log 2 | | | | 1268 |
| 10^5 | 100 | 0.40 | 4126.50 | 0.0413 | | 16 | 92 |
| 10^5 | 316 | 0.50 | 1781.75 | 0.0178 | 0.317 | 30 | 277 |

Three readings.

**The law at y = sqrt(N).** 0.354, 0.324, 0.317 times N^{3/4} over three
decades; the fitted exponent between 10^4 and 10^5 is 0.74. The best
prime-blind certificate with support sqrt(N) has excess of order N^{3/4}, not
N^{1/2}. This is the number the route needed and did not have.

**The fixed-support constant.** At y = 100 the excess ratio is 0.009 (N=10^3,
finite-N regime), 0.032 (10^4), 0.041 (10^5) and still rising, so the all-N
constant of a support-100 family is at least 0.041. The hunt's 1.034 uses seed
denominators up to about 3000 and a lift; Section 4.4 gives its family's floor.

**Where the optimum puts its coefficients.** c equals mu(j) exactly on an
initial segment (the "mobius prefix": 16 at y=100, 30 at y=316, 47 for
y=316 at N=10^4) and then departs from mu with fractional coefficients. The
prefix is where W = 1 exactly; the departure is the price of controlling W
beyond y. This is the shape the hunt's constructions approximate by hand.

### 4.2 Prime-aware floor P*(y, N) - psi(N)

| N | cells | y = sqrt(N) | y = N^{0.55} |
|---:|---:|---:|---:|
| 10^4 | 135 | 106.9 (= 1.07 sqrt N) | 0.000 |
| 10^5 | 398 | 233.6 (= 0.74 sqrt N) | 0.000 |
| 10^6 | 1193 | 633.0 (= 0.63 sqrt N) | (not run: see note) |
| 10^7 | 3645 | 4204.2 (= 1.33 sqrt N) | 0.000 (at y = N^{0.53} = 5129; CI, 2026-09-07) |

At y = sqrt(N) the prime-aware excess is of order sqrt(N), and it is exactly
zero once y exceeds the number of prime-looking cells, because then the LP
solves W = 1 on all of them. So, of the 324 at (10^4, 100), 217 is the price
of being prime-blind and 107 is the price of support; at (10^5, 316) the split
is 1548 to 234.

The zero is not progress. Writing the tail of the optimal c through the cells
m = floor(N/j) < sqrt(N) shows the identity it recovers:

    psi(N) = sum_{j<=sqrt N} mu(j) log floor(N/j)!
             - sum_{d<=sqrt N} Lambda(d) [W_0(N/d) - 1],
    W_0(t) = sum_{j<=sqrt N} mu(j) floor(t/j),

which is the Dirichlet hyperbola form of Lambda = mu * log split at sqrt(N).
The prime-aware certificate is that identity. It compresses the Mobius
identity from N terms to 1.2 sqrt(N) terms and it is circular for a proof:
the tail coefficients are determined by the sieve counts W_0(N/d), which is
where the information about primes above sqrt(N) sits.

Note: at N = 10^6 with y > 1193 HiGHS reports unbounded; that is a floating
artifact of an underdetermined system (kernel directions with objective of
order 1e-9 times log N!), not a mathematical statement. The value there is
zero by the same dimension count verified at N = 10^5.

### 4.3 Enlarging the dictionary: Selberg's identity as a test function

Selberg's Lambda log + Lambda*Lambda = mu*log^2 gives, for every j,

    sum_{d<=N} Lambda(d) g_j(N/d) = sum_{n<=N/j} log^2 n,
    g_j(t) = log floor(t/j)! + log(N/t) floor(t/j),

(re-checked to residual 0.0 at N = 10^4). These are exactly evaluable test
functions outside the floor-sum span: they contribute the pure linear and
logarithmic functions t/j and log t, which floor sums cannot produce without a
sawtooth attached. Because log(N/t) varies inside a cell, the constraint is
imposed at both cell endpoints (W is affine in log(N/t) on a cell), so the
resulting certificate is valid at every real t in [1, N+1).

| N | y | floor only | with Selberg columns | ratio | Selberg coefficient mass |
|---:|---:|---:|---:|---:|---:|
| 10^4 | 31 | 781.94 | 532.43 | 0.68 | 153 |
| 10^4 | 100 | 323.65 | 230.19 | 0.71 | 3380 |

A constant factor of about 0.7 at both points, with large coefficients on the
new columns. The y = 316 run was still queued behind a load average above 100
when this was written. A constant-factor gain is what the picture in Section 5
predicts: the new functions are smooth, and the cost in (E) is sawtooth
fluctuation. Two points do not exclude an exponent change; the y = 316 row
is the one that would show it.

### 4.4 The hunt's own family: seed of support y, radix-15 lift

`lp_dictionaries.py --lift 15`: coefficients a_j (j <= y) repeated at every
scale, W(t) = sum_k sum_j a_j floor(t/(j 15^k)), all cells <= N.

| N | y | excess | excess/N |
|---:|---:|---:|---:|
| 10^4 | 31 | 559.9 | 0.0560 |
| 10^4 | 100 | 298.5 | 0.0298 |
| 10^5 | 31 | 5994.0 | 0.0599 |
| 10^5 | 100 | 3705.9 | 0.0371 |
| 10^5 | 1000 | 183.6 | 0.0018 (CI, 2026-09-07; y = N^{0.6}, finite-N regime, see below) |

The lift helps (3706 against 4126 for plain support 100 at N = 10^5, because
the support now reaches j 15^k <= N), and the floor at seed support 100 is
already 3.7% of N at N = 10^5, above the hunt's all-N 3.4%. Their seeds reach
about 3000. The seed-1000 row at N = 10^5 (0.18%) is a cutoff-10^5
certificate with y = N^{0.6}: in that regime the LP exploits the sparse prime
cells above sqrt(N) and the number is not a bound on any all-N constant. The
all-N floor of a seed-3000 family is the limit N -> infinity at fixed seed,
visible only for N well beyond 3000^2 ~ 10^7, which this batch does not
reach; the (10^6, 3000) row, if it lands, is still inside the finite-N
regime. The fair comparison for the adaptive block therefore remains open;
what is settled is that at fixed seed support the floor rises with N
(3.0% -> 3.7% from 10^4 to 10^5 at seed 100).

## 5. What is rigorous, and the picture behind the law

**Lemma (rough spikes).** Let c be supported on [1, y] with W_c >= 1 on the
cells 1..N. For every m in (y, N] all of whose prime factors exceed y, the
jump of W at m is w(m) = sum_{j | m, j <= y} c_j = c_1 = W(1) >= 1, hence
W(m) >= 2, and by (E)

    B(N) - psi(N) >= sum_{y < m <= N, m y-rough} [psi(N/m) - psi(N/(m+1))].

Values: 4.23 (10^3, 31), 15.46 (10^4, 100), 35.81 (10^5, 316), 103.0 (10^6,
1000). Rigorous, prime-blind-universal, and weak: 2 to 5 percent of the LP
value. Its size is about N/(y log y), which at y = sqrt(N) is sqrt(N)/log N.

**Why N^{3/4} (heuristic, not proved).** For balanced c the identity
floor(t/j) = t/j - {t/j} gives W(n) = -sum_j c_j {n/j}, a sum of sawtooths.
Its mean over n is -C(0)/2 with C(0) = sum_j c_j, and for j's without much
common structure its fluctuation has variance about sum_j c_j^2 / 12. The
constraint W >= 1 at every cell then forces the mean to sit about three
standard deviations above 1, so W - 1 is of order ||c||_2 on the cells beyond
the Mobius prefix y', and (E) with prime mass N/n^2 gives excess of order
N ||c||_2 / y'. With c = mu on the prefix, ||c||_2^2 >= 0.6 y', so excess is
at least of order N / sqrt(y') >= N / sqrt(y). At y = sqrt(N) that is N^{3/4},
with the measured constant 0.32. The LP can and does exploit correlations
among sawtooths (the mask-210 and period-30030 constructions are exactly
that), which is why the true constant is below the naive Gaussian one; the
measured exponent says it does not escape the order.

This is the missing estimate stated as a conjecture about a linear program:

    Conjecture (barrier). V*(y, N) - psi(N) >= c N / sqrt(y)  for y <= sqrt(N),
    for an absolute c > 0 and all large N.

If true, a prime-blind factorial certificate with excess N^{1/2+eps} needs
support y >= N^{1-2 eps}, at which point the certificate is the Mobius
identity itself and its evaluation is the Mertens problem, not Stirling.

## 6. The implication chain, with the missing arrow marked

    Established:  sum_{d|n} Lambda(d) = log n;  W >= 1 on cells  =>  psi(N) <= B(N);
                  LP duality; the primes are dual-feasible.
    Derived here: the excess of ANY floor-sum certificate at (y, N) is >= V*(y,N) - psi(N);
                  V* is computable; measured 0.32 N^{3/4} at y = sqrt N (three decades);
                  the prime-aware relaxation is the hyperbola identity (exact, circular);
                  the rigorous lemma gives ~N/(y log y).
    Needed:       excess <= N^{1/2+eps} at support and mass <= N^{1/2+eps}.
    ==> MISSING:  either a proof of the barrier conjecture (closes the route with a
                  theorem), or a family outside the floor-sum span whose prime sums
                  are exactly evaluable and whose fluctuation is not sawtooth-shaped.
    Target:       psi(N) <= N + O(N^{1/2+eps}) for all large N  =>  RH (one-sided
                  oscillation argument, DIRECT_ATTACK.md).

The gap between "needed" and "measured" is a factor N^{1/4}. Reducing the
leading constant of a fixed construction from 1.046 to 1.034 does not touch
it. This is not a judgement on the adaptive block; it is the reason no
adaptive block can be the bridge.

## 7. What this does and does not establish

Established at measured grade: the LP floors in 4.1 and 4.2, the identity in
4.2, the Selberg admissibility check, the lifted-family floors in 4.4.
Established rigorously: the rough-spike lemma. Not established: the barrier
conjecture, any statement for N beyond 10^5 (10^6 was queued), any claim
that the Selberg dictionary cannot change the exponent (one data point).

Nothing here is evidence for or against RH. Nothing here changes the reviewed
status of PRs #199 and #200 or reviews the post-#200 chain.

## 8. The doors

1. **Active constraint at the optimum.** The cells immediately beyond the
   Mobius prefix, where W must rise above 1 to control the sawtooth
   fluctuation of sum_j c_j {n/j} on every later cell. The dual measure moves
   mass out of the cells n in [5, 10) and into [1, 2) and just above y (the
   N = 10^3 dual bands in `results/lp_N1000.json`): the fake primes are denser
   near N and near N/y than the real ones.
2. **Frozen-constant inventory.** The hunt's constructions froze: radix 15;
   seed period 30030; mask set {1,2,6,30,210}; the carry shapes; the repair
   menu; nonnegativity of intermediate pieces (already relaxed). All of these
   are feasible-subset choices inside V*, so relaxing any of them can gain at
   most the distance to V*(y, N) at their support, which 4.1 and 4.4 measure.
   The only frozen constant with trade shape is the support bound itself,
   and the trade is N/sqrt(y) of excess against y of mass.
3. **Information class.** Every door above stays inside the floor-sum span
   and under the N^{3/4} ceiling. The two doors that read more information
   are: (a) prime-awareness below sqrt(N), which collapses to the hyperbola
   identity; (b) test functions with exactly evaluable prime sums outside the
   span. Selberg's identity is one such family and bought 32% at one point.
   The question worth a session is whether there is an exactly-evaluable
   dictionary whose fluctuation is not sawtooth-shaped; the divisor-sum
   functions D(t/j) = sum_{i<=t/j} d(i) are evaluable to O(N^{0.315}) by
   Huxley's bound on the divisor problem, but their fluctuation is
   Voronoi-shaped (frequencies sqrt(nt)), which cannot cancel sawtooths.

The follow-up hunt goes through the barrier conjecture first: a proof closes
the route with a theorem, and a counterexample to it would be a construction
worth more than any block.

## 9. Reproduce

    OPENBLAS_NUM_THREADS=1 .venv/bin/python lp_frontier.py --N 1000 --y 31 100 200 --output out.json
    OPENBLAS_NUM_THREADS=1 .venv/bin/python lp_allcells_cg.py --N 10000 --y 100 316 --output out.json
    OPENBLAS_NUM_THREADS=1 .venv/bin/python lp_prime_cells.py --N 10000 100000 --alpha 0.5 0.55 --output out.json
    OPENBLAS_NUM_THREADS=1 .venv/bin/python lp_dictionaries.py --N 10000 --y 31 --selberg --output out.json
    OPENBLAS_NUM_THREADS=1 .venv/bin/python lp_dictionaries.py --N 100000 --y 31 100 --lift 15 --output out.json

`tests/test_certificate_lp_frontier.py` pins the (10^3, 31) floor, the
(10^4, 158) prime-aware zero, the rough-spike value and the Selberg residual.
Timings in `RUNS.md`. scipy 1.18.0, numpy 2.5.2, HiGHS via scipy.
