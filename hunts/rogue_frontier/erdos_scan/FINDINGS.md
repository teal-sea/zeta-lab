# Erdos problem scan: where this laboratory's built machinery has an edge

Sub-study of `hunts/rogue_frontier/`. Opened 2026-08-18.

**Status: exploratory. Nothing here is a result.** This is a feasibility survey,
not mathematics. Every "best known" line below carries the URL actually fetched
while writing it; anything not fetched is marked UNVERIFIED.

## Question

Of the ~1100 problems on erdosproblems.com, which OPEN ones does this tree's
existing, validated machinery make unusually cheap to attack, such that a first
signal is reachable in hours rather than months?

The bar is deliberately not "interesting problem". It is: *this specific tooling
changes what is feasible here.*

## Method (reproducible)

1. `https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml`
   gives structured status/prize/tags for 1217 problems (604 `open`, plus the
   finite-computation classes below). Fetched 2026-08-18.
2. All 1217 problem pages fetched from `https://www.erdosproblems.com/<n>`
   (a plain user agent is required; the default agent gets 403), rendered to
   text, split into statement and remarks.
3. The site carries a status field that is exactly the discriminator this scan
   wants, and it is not visible from the YAML alone:
   - `open` (604): "cannot be resolved with a finite computation"
   - `falsifiable` (27): "could be disproved with a finite counterexample"
   - `verifiable` (7): "could be proved with a finite example"
   - `decidable` (9): "resolved up to a finite check"
   - plus `not provable` / `not disprovable` / `independent` (set-theoretic)
4. Page metadata also gives a **mining indicator** the YAML lacks: comment
   count, who has flagged "currently working on this problem", and the
   "looks tractable" / "looks difficult" votes. Recorded per candidate below.
5. Pool restricted to number-theory / analysis / combinatorics tags where this
   tree's tools could bite: 437 open-ish problems. Statements read in full.

## What this laboratory actually brings

| Tool | Where | What it buys |
|---|---|---|
| exact rational / integer engines, generating-function collapse | `hunts/rogue_frontier/fkappa/` | 14-fold combinatorial sums in polynomial time, validated exactly to i=81 |
| exact finite-N lattice counts, Wick/pairing enumeration | `hunts/rogue_frontier/sine_gram/` | exact finite-N combinatorial objects, no floating point |
| ball / interval arithmetic (Arb via python-flint) | `zeta/rigor.py` | rigorous enclosures, proven signs, safe failure |
| high-precision mpmath, sympy, scipy | repo-wide | thousands of digits, symbolic reduction, constrained optimisation |
| exact Sturm sequences in Q[X] | `zeta/li.py` | exact real-root counting without floating point |
| Lean 4 + Mathlib, pinned and building | `lean/` | kernel-checked finite lemmas; Mertens I/II and Hardy-Ramanujan already in tree |
| large exact prime / arithmetic-function computation | repo-wide | sieves to 1e7+ demonstrated, segmented sieving routine |
| structure-matched negative controls | `zeta/epstein.py`, `hunts/README.md` | a claim a matched rival also satisfies has distinguished nothing |

## Scoring

Each candidate carries: **F** feasibility of a first signal in hours (0-5),
**N** chance anything new comes out (probability, honest), **M** how heavily
mined (0 = untouched, 5 = crowded), **V** value if it lands.

---

# Tier 1 candidates

## C1. Problem 647: is there n > 24 with max_{m<n}(m + tau(m)) <= n + 2?

- **URL**: https://www.erdosproblems.com/647
- **Status / prize**: VERIFIABLE ("could be proved with a finite example"). Erdos
  offered GBP 25 in [Er92e], rendered by the site as $44. Erdos and Selfridge.
- **Best known, verified against the source page (fetched 2026-08-18)**: the site
  records that n = 24 works, that n+2 is best possible since
  max(tau(n-1)+n-1, tau(n-2)+n-2) >= n+2, that Erdos called it "extremely
  doubtful" that infinitely many such n exist, and that he conjectured
  lim_n max_{m<n}(tau(m)+m-n) = infinity. **The page records no computational
  search bound at all.** That absence is the opening.
- **Tool**: large exact arithmetic-function computation. A segmented divisor-count
  sieve with a running maximum. Nothing more exotic is needed.
- **Smallest experiment, already run here**: a segmented tau sieve in C,
  `scratchpad/e647/tau647c.c`, tracking
  D(n) = max_{m<n}(m + tau(m)) - n, reporting the per-decade minimum.
  **Measured, 3 min 20 s to N = 10^9 on one core:**

  | n below | min D | attained at |
  |---|---|---|
  | 10^2 | 3 | 35 |
  | 10^3 | 3 | 120 |
  | 10^4 | 5 | 1078 |
  | 10^5 | 8 | 13440 |
  | 10^6 | 10 | 106464 |
  | 10^7 | 11 | 4989600 |
  | 10^8 | 12 | 15919596 |
  | 10^9 | 12 | 444444000 |

  So: **no n with 24 < n <= 10^9 has D(n) <= 2**, and D(n) >= 12 throughout the
  last decade. Extrapolating the same code: 10^10 is about 35 min, 10^11 about
  6 h, 10^12 about 2.5 days on one core, less with the obvious pruning (n-1 must
  be 1, a prime, or a prime square, so the running max only has to be maintained
  near primes).
- **Negative result**: almost certainly what you get. It is worth recording
  anyway, in two forms. (i) "no example with n <= 10^11" is a bound the database
  currently lacks entirely, and it is exactly what a VERIFIABLE problem's page
  should carry. (ii) the decade table is direct evidence on Erdos's *stronger*
  conjecture that D(n) -> infinity; the growth 3, 3, 5, 8, 10, 11, 12, 12 is
  slow and non-monotone across decades, which is itself a fact worth publishing
  next to the conjecture.
- **P(anything new)**: finding an n > 24 -- under 1%. Erdos's heuristic is
  overwhelming and our data agrees. Producing a search bound and a growth table
  the database does not have -- around 70%, conditional on nobody having posted
  one in the 13 comments (which are not served in the static HTML, see risk).
- **Mined**: 13 comments, four users flagged "currently working on this problem"
  (Ritvik_Nayak, pommeret, ScottHughes and others). **This is the main risk**: a
  search bound may already exist inside the comment thread. Check the live
  comments before spending a day of compute.

## C2. Problem 311: the exponential rate of delta(N)

- **URL**: https://www.erdosproblems.com/311
- **Status / prize**: OPEN, no prize.
- **Statement**: delta(N) is the minimal non-zero value of |1 - sum_{n in A} 1/n|
  over A a subset of {1,...,N}. Is delta(N) = e^{-(c+o(1))N} for some c in (0,1)?
- **Best known, from the source page (fetched 2026-08-18)**: trivially
  delta(N) >= 1/lcm(1..N) = e^{-(1+o(1))N}; Tang has shown
  delta(N) <= exp(-c N/(log N log log N)^3). Kovac showed in the comments that
  the extra condition in [ErGr80] is redundant. **No table of exact values of
  delta(N) is recorded, and OEIS returns nothing for it.**
- **Tool**: exact integer arithmetic and a meet-in-the-middle subset-sum engine,
  precisely the shape `sine_gram/exact_finite_N.py` already uses. Multiply by
  L = lcm(1..N): delta(N) = min non-zero |L - sum_{n in A} L/n| / L, an exact
  closest-subset-sum problem in Z.
- **Smallest experiment, already run here**: pure-Python meet-in-the-middle,
  exact ints, no floating point. **Measured runtimes: N = 36 in a few seconds,
  N = 44 in 14.6 s.** Values of -ln delta(N)/N:

  | N | 4 | 12 | 20 | 28 | 34 | 38 | 40 | 42 | 44 |
  |---|---|---|---|---|---|---|---|---|---|
  | -ln delta/N | 0.621 | 0.645 | 0.550 | 0.583 | 0.510 | 0.533 | 0.507 | 0.506 | 0.488 |

  (delta(44) = 4.785294e-10, computed as an exact rational, not a float.)
  The sequence sits near 0.5
  and drifts downward, which is what a *non-constant* rate would look like, and
  is the interesting reading: it is mild evidence against the conjectured
  e^{-(c+o(1))N} shape and consistent with Tang's polylog correction being real.
- **Cost of the next rung**: naive scaling is x2.4 per +2 in N, so N = 52 is about
  8 min and N = 56 about 45 min with Python ints. Replacing the sort key with
  numpy `longdouble` (80-bit, absolute resolution about 2e5 at L ~ 1e24, while
  the expected spacing between distinct subset sums near the target is enormous)
  and verifying the handful of window candidates in exact Z pushes N to 58-60
  inside 15 GB. That roughly doubles the range of the table.
- **Negative result**: the honest likely outcome is "the exponent keeps drifting,
  so the data neither confirms nor refutes". That is still worth recording,
  because the table itself is the missing artifact. A table of exact delta(N) for
  N <= 56 is a contribution to the problem page and to OEIS regardless of which
  way it points.
- **P(anything new)**: producing the first exact table -- 90%. Producing a
  statement that moves the conjecture -- 10-15%.
- **Mined**: 8 comments, nobody flagged as working on it, no OEIS entry. Lightly
  mined. Kovac and Tang have both engaged, so the analytic side is watched, but
  the arithmetic side appears untouched.

## C3. Problem 710 (and 711): exact values of the Erdos-Pomerance function f(n)

- **URL**: https://www.erdosproblems.com/710 , https://www.erdosproblems.com/711
- **Status / prize**: OPEN. Erdos offered 2000 rupees in [Er92c] for an asymptotic
  formula (the site renders it as $78).
- **Statement**: f(n) is minimal such that the open interval (n, n+f(n)) contains
  distinct integers a_1,...,a_n with k | a_k for every k <= n.
- **Best known, from the source page (fetched 2026-08-18)**: Erdos and Pomerance
  [ErPo80] proved
  (2/sqrt(e) + o(1)) n (log n / log log n)^{1/2} <= f(n) <= (1.7398... + o(1)) n (log n)^{1/2}.
  The gap between the two ends is a factor (log log n)^{1/2}. **No values of f(n)
  are recorded on the page, and OEIS returns nothing for the sequence.**
- **Tool**: exact finite-N combinatorics. f(n) is a system-of-distinct-
  representatives question: bipartite graph with left vertices 1..n, right
  vertices the integers in (n, n+L), edge k -- a iff k | a. f(n) is the least L
  admitting a perfect matching saturating the left side. Hopcroft-Karp, or Hall's
  condition directly. The lab has no matching code, but this is 60 lines.
- **Smallest experiment**: compute f(n) for n <= 2000 by binary search on L with a
  matching test. Edge count is about L log n; at n = 2000 and L ~ 3n the graph has
  order 10^5 edges, so each matching is milliseconds and the whole table is
  minutes. n <= 10^5 is an afternoon. **Estimated first signal: under 1 hour**,
  including writing the code.
- **What it buys**: the two proven bounds differ by (log log n)^{1/2}, which at
  n = 10^5 is only about 1.5, so exact values across four decades genuinely
  discriminate between "f(n)/n(log n)^{1/2} tends to a constant" and
  "f(n)/n(log n/log log n)^{1/2} tends to a constant". Erdos asked for the
  asymptotic formula and offered money for it; the data would say which shape to
  aim at, and the constants 2/sqrt(e) = 1.213 and 1.7398 are close enough
  together to be tested numerically.
- **Negative result**: if f(n)/n grows too slowly to separate the two shapes over
  the reachable range, that is a clean statement to record ("four decades do not
  separate them; here is the fitted exponent"), and the table still stands as the
  first computation of an Erdos prize function.
- **P(anything new)**: first table of f(n) -- 85%. A statement that visibly picks
  one of the two shapes -- 35%. Proving anything -- under 5%.
- **Mined**: 7 comments on 710, 8 on 711; one user flagged as currently working on
  each (SkyYang on 710, skominers on 711) and one flagged 710 "looks tractable"
  (Prasannam); no OEIS sequence for f(n) was found. Lightly mined, but not
  untouched: correct that against the earlier draft of this file.

## C4. Problem 879: exact values of G(n), the maximal sum of a pairwise-coprime set

- **URL**: https://www.erdosproblems.com/879
- **Status / prize**: OPEN, no prize.
- **Statement**: S in {1,...,n} is admissible if its elements are pairwise coprime;
  G(n) = max over admissible S of sum of S; H(n) = sum_{p<n} p + n pi(n^{1/2}).
  Is G(n) > H(n) - n^{1+o(1)}?
- **Best known, from the source page (fetched 2026-08-18)**: Erdos and Van Lint
  proved H(n) - n^{3/2-o(1)} < G(n) < H(n) and (H(n)-G(n))/n -> infinity, and got
  G(n) > H(n) - n^{1+o(1)} only under "plausible (but hopeless) assumptions about
  the distribution of primes". **No values of G(n) are recorded.**
- **Tool**: exact finite-N combinatorial optimisation. G(n) is an exact integer
  program: one binary variable per integer m <= n, one packing constraint per
  prime p <= n ("at most one chosen m is divisible by p"), objective sum m x_m.
  n variables, pi(n) constraints, totally structured. `scipy.optimize.milp`
  (HiGHS) is in the venv. The LP relaxation of a set-packing this sparse is
  usually near-integral, so the solve is cheap.
- **Smallest experiment**: solve for n = 100, 200, 500, 1000, 2000, 5000 and
  tabulate (H(n) - G(n))/n. Estimated **under 30 minutes** to first numbers;
  n = 10^5 (10^5 variables, 9592 constraints) is plausible in an afternoon.
- **What a signal looks like**: Erdos and Van Lint's own theorem says
  (H(n)-G(n))/n -> infinity, so the data must show growth; the open question is
  whether H(n)-G(n) is n^{1+o(1)} or genuinely larger. Fitting
  log(H(n)-G(n))/log n across four decades tests exactly that exponent.
- **Negative result**: a fitted exponent that sits stubbornly above 1 would be
  evidence *against* the conjecture, which is more interesting than confirmation
  and is exactly the sort of thing this tree is built to say carefully. Either
  direction is publishable as measurement.
- **P(anything new)**: first table -- 85%. A defensible read on the exponent --
  40%.
- **Mined**: 1 comment, nobody working, no OEIS. Essentially untouched.

## C5. Problem 307: the 2-cycle reformulation, and why the search is now structured

- **URL**: https://www.erdosproblems.com/307
- **Status / prize**: VERIFIABLE, no prize. Asked by Barbeau [Ba76].
- **Statement**: are there finite sets of primes P, Q with
  (sum_{p in P} 1/p)(sum_{q in Q} 1/q) = 1?
- **Best known, from the source page (fetched 2026-08-18)**: P and Q must be
  disjoint, sum over P union Q of 1/p >= 2, hence |P union Q| >= 60. Cambie has
  examples for the weakened version where the elements need only be coprime, e.g.
  1 = (1 + 1/5)(1/2 + 1/3). No examples are known for the coprime version with
  1 not in P union Q.
- **Reduction (derived and checked here, elementary, quite possibly already
  known)**: for any finite set of primes S, write s(S) = sum_{p in S} 1/p =
  a_S/prod(S). Reducing mod p for p in S shows gcd(a_S, prod S) = 1, so that
  fraction is already in lowest terms. **Confirmed numerically on 2000 random
  prime sets: the denominator of s(S) is exactly prod(S), every time.**
  Then s(P)s(Q) = 1 with P, Q disjoint forces a_P a_Q = prod(P) prod(Q) with
  a_P coprime to prod(P) and a_Q coprime to prod(Q), hence
  **a_P = prod(Q) and a_Q = prod(P) exactly.** Define the partial map
  T(S) = the set of prime factors of numerator(s(S)), defined exactly when that
  numerator is squarefree. The problem is then precisely:
  **does T have a 2-cycle?** T(P) = Q and T(Q) = P.
- **Why this changes the search**: the site's bound |P union Q| >= 60 leaves a
  search over subsets of primes. The 2-cycle form makes Q a *function* of P, so
  the search is one cheap deterministic check per candidate P (compute an exact
  rational, factor its numerator, test squarefreeness, sum reciprocals, compare),
  instead of a search over pairs.
- **Tool**: exact rational arithmetic plus factorisation, both in the venv.
- **Smallest experiment, already run here**: all P of size 2 to 4 drawn from the
  primes below 60 (1886 with T defined), no 2-cycles, seconds. Extending to size
  <= 8 over primes below 200 is minutes.
- **The honest feasibility read, which is negative**: T maps a set of size k to a
  set of size omega(a_P), and a_P is a number of size about prod(P). For
  sum_{q in Q} 1/q to be near 1 while Q omits 2 (P and Q are disjoint and one of
  them lacks 2), Q needs roughly 40 or more small primes, so a_P must be an
  extremely smooth squarefree number of size about prod(P). For a random P that
  is astronomically unlikely, and a blind enumeration over subsets of the first
  60-100 primes is 2^60 and infeasible. **So this is not a candidate for finding
  a solution.** It is a candidate for a small structural note plus a bounded
  negative ("no 2-cycle with |P| <= 8 and max P <= 500"), and it should be
  scored as such.
- **P(anything new)**: finding P, Q -- essentially 0. The reduction being new --
  maybe 20%, it is a two-line exercise and Cambie has clearly thought about this
  page.
- **Mined**: 6 comments, three users flagged as currently working (aditya,
  will0708, Ary300), two flagged "looks difficult". Moderately busy.

## C6. Problem 912: the constant in h(n) ~ c (n/log n)^{1/2}

- **URL**: https://www.erdosproblems.com/912
- **Status / prize**: OPEN, no prize. Erdos and Selfridge.
- **Statement**: h(n) counts the distinct exponents in the prime factorisation of
  n!. Prove h(n) ~ c (n/log n)^{1/2} for some c > 0.
- **Best known, from the source page (fetched 2026-08-18)**: Erdos and Selfridge
  proved h(n) is of order (n/log n)^{1/2} (see [Er82c]). **A heuristic of Tao
  using the Cramer model, given in the comments on that page, predicts
  c = sqrt(2 pi) = 2.5066...** No numerical check of that prediction is recorded.
- **Tool**: large exact arithmetic-function computation. h(n) is Legendre's
  formula plus a distinct-count; nothing else is needed.
- **Smallest experiment, already run here** (numpy, one core, sieve to 10^8):

  | n | 10^3 | 10^4 | 10^5 | 10^6 | 10^7 | 10^8 |
  |---|---|---|---|---|---|---|
  | h(n) | 31 | 87 | 252 | 723 | 2087 | 6169 |
  | h(n)/(n/log n)^{1/2} | 2.577 | 2.640 | 2.704 | 2.687 | 2.650 | 2.648 |

  **Total runtime 7.2 s including the sieve.** The ratio sits near 2.65, which is
  about 5.6% above Tao's sqrt(2 pi) = 2.5066 and is not visibly falling toward it.
- **The honest caveat, which is the whole game here**: a secondary term of
  relative size 1/log n is 5.4% at n = 10^8, which is *exactly* the size of the
  discrepancy. So the present data is fully consistent with c = sqrt(2 pi) and a
  1 + O(1/log n) correction, and claiming otherwise now would be a mistake. The
  experiment that matters is pushing n to 10^12 to 10^15, where 1/log n falls to
  3.6% and 2.9%. That is feasible without a bigger sieve: for p > sqrt(n) the
  exponent is floor(n/p), so the distinct values there are the v <= sqrt(n) for
  which the interval (n/(v+1), n/v] contains a prime, which is sqrt(n) short
  interval tests, and for p <= sqrt(n) there are only pi(sqrt(n)) primes to
  handle directly. At n = 10^12 that is about 10^6 short-interval prime tests,
  minutes of work.
- **Negative result**: the likely outcome is "the ratio is 2.6x and falling like
  1 + a/log n; fitting a two-term model gives c = 2.5 +/- 0.1, consistent with
  sqrt(2 pi)". That is a *good* outcome to record: it is the first numerical
  support for a named heuristic constant on this problem, and the fit itself is
  the artifact. The other outcome, that the ratio stabilises visibly above
  sqrt(2 pi), would be evidence against the Cramer-model heuristic, which is a
  more interesting thing to say and would need care and an independent
  recomputation before saying it.
- **P(anything new)**: first numerical test of the predicted constant, with a
  fitted two-term model -- 85%. A defensible statement that the heuristic
  constant is wrong -- 10%.
- **Mined**: 2 comments (one of them Tao's heuristic), nobody flagged as working,
  no OEIS sequence for h(n) found. Lightly mined, and the heuristic is fresh
  enough that nobody has checked it.

## C7. Problem 1074 (with 1072 and 1073): EHS numbers and Pillai primes

- **URLs**: https://www.erdosproblems.com/1074 , /1072 , /1073
- **Status / prize**: all three OPEN, no prize.
- **Statement (1074)**: S is the set of m such that some prime p with
  p not congruent to 1 mod m divides m!+1. Does |S cap [1,x]|/x converge, and to
  what? Same question for the Pillai primes P relative to pi(x).
- **Best known, from the source page (fetched 2026-08-18)**: Erdos, Hardy and
  Subbarao proved S and P are both infinite. **"Hardy and Subbarao computed all
  EHS numbers up to 2^10"** and expected the density of S to be 1, and the
  density of P to be perhaps between 0.5 and 0.6. OEIS A064164 (EHS numbers) has
  a b-file of only **120 terms** (Amiram Eldar); OEIS A063980 (Pillai primes) has
  10000 terms (Greathouse, first 1000 from Noe). Verified at
  https://oeis.org/A064164 and https://oeis.org/A063980 , fetched 2026-08-18.
- **The asymmetry worth exploiting**: OEIS computes A064164 by *fully factoring*
  m!+1 (the PARI line on the page is `factor(n!+1)`), which is why it stops at
  120 terms. But the conjecture is that the density of S is **1**, and a density
  *lower* bound needs only one witness prime per m, not a factorisation. So the
  right computation is: for every prime p up to B, run k! mod p for k < p and
  record every k with k! congruent to -1 mod p and p not congruent to 1 mod k.
  That establishes membership in S from below and never needs a factorisation.
- **Tool**: large exact modular computation. Cost is sum over p <= B of p, which
  is B^2/(2 log B): B = 10^6 is 3.6e10 multiply-mods (about a minute in C),
  B = 10^7 is 3.1e12 (about an hour in C on one core, or 15 min on four).
  The same single sweep answers all three problems: f(p) from 1072 is the least
  k in the sweep, the composite u from 1073 come from the same table, and the
  Pillai primes from 1074 are the p with a qualifying k.
- **Smallest experiment**: sweep to B = 10^6 first (a minute), reproduce the 10000
  known Pillai primes as a control, then report the observed
  |P cap [1,x]|/pi(x) across decades and a lower bound on the density of S.
- **Negative result**: if the lower bound on the density of S plateaus well below
  1 the conjecture is in trouble, and that is publishable. If it climbs toward 1
  that is the first quantitative support since 2002. Either way the table is new.
- **P(anything new)**: extending the recorded EHS data past m = 120 -- 80%. A
  density statement that moves either question -- 30%.
- **Mined**: 5 comments on 1074, 1 on 1072, 0 on 1073, nobody flagged as working.
  The prime side (A063980) has been computed by serious people; the m side has
  not, because everyone reached for factorisation.

## C8. Problem 168: more digits of the {n,2n,3n}-free density constant

- **URL**: https://www.erdosproblems.com/168
- **Status / prize**: OPEN, no prize.
- **Best known, verified at OEIS (fetched 2026-08-18)**: A386439 gives 35 digits,
  0.80096575500655898909042032638808241..., contributed by **Sean Eberhard,
  18 Sep 2025**, with keyword `more`. His method is on the OEIS page: A004059
  computed to 3335 terms via one Gurobi integer program per 3-smooth number
  (https://oeis.org/A004059 , script at https://oeis.org/A004059/a004059.py.txt),
  then a `RealIntervalField(1000)` partial sum with a tail bound
  (https://oeis.org/A386439/a386439.py.txt). Graham, Spencer and Witsenhausen
  [GSW77] proved the limit equals (1/3) sum over K of 1/d_k.
- **Tool**: exact finite-N lattice enumeration (`sine_gram/exact_finite_N.py` is
  the same shape: the constraint is exactly "no lattice corner
  (a,b), (a+1,b), (a,b+1) all chosen" on the staircase 2^a 3^b <= x), plus
  interval arithmetic for the tail. The lab has `scipy.optimize.milp` (HiGHS) but
  **not** Gurobi.
- **Smallest experiment**: reproduce Eberhard's 35 digits with HiGHS to check the
  pipeline, then attack the algorithmic bottleneck. Doubling the digits needs
  3-smooth numbers to 10^70, which is only about 18500 lattice points; the
  obstacle is solving 18500 integer programs of that size, not the arithmetic.
- **Honest feasibility read**: this is the candidate most likely to be *slower*
  here than where it already lives. Eberhard is a strong researcher, he did this
  eleven months ago, and he had a commercial solver. Our edge would have to be a
  genuinely better algorithm (a transfer-matrix or column-generation argument on
  the staircase), not more compute. **Score it as a maybe, not a lead.**
- **Negative result**: "HiGHS reproduces 35 digits and does not get past 40" is a
  perfectly fine thing to learn in an afternoon and should be recorded as a cost
  measurement, not a result.
- **P(anything new)**: 15%.
- **Mined**: 9 comments, nobody flagged as working, but Eberhard, Alexeev, Cambie
  and Chapman are all thanked on the page. Actively watched.

## C9. Problem 317: exact minima of |sum delta_k / k| with delta in {-1,0,1}

- **URL**: https://www.erdosproblems.com/317
- **Status / prize**: OPEN, no prize.
- **Statement**: (i) is there c > 0 such that for every n some choice of
  delta_k in {-1,0,1} gives 0 < |sum_{k<=n} delta_k/k| < c/2^n? (ii) is it true
  that for large n every non-zero |sum delta_k/k| exceeds 1/lcm(1..n)?
- **Best known, from the source page (fetched 2026-08-18)**: the second claim
  fails for small n, e.g. 1/2 - 1/3 - 1/4 = -1/12 with lcm(1..4) = 12. Kovac and
  van Doorn prove in the comments a weak version of (i) with upper bound
  2^{-n (log log log n)^{1+o(1)}/log n}, and van Doorn gives a heuristic that this
  may be the truth.
- **Why it is a good fit**: multiplying by L = lcm(1..n) turns (ii) into a pure
  integer question: is +/-1 representable as sum delta_k (L/k)? And (i) becomes a
  shortest-vector / closest-subset-sum problem in Z. The lab has exact integer
  arithmetic, and sympy 1.14's `DomainMatrix.lll` is present in the venv
  (confirmed), so LLL on the lattice generated by the L/k is directly available.
- **Smallest experiment**: exhaustive meet-in-the-middle over 3^n up to n = 30
  (3^15 = 14.3M per half, minutes), recording (a) the minimum non-zero
  |sum delta_k (L/k)| and (b) every n where that minimum equals 1. That answers
  (ii) empirically over a range nobody has published, and gives the first exact
  data for (i). LLL then extends the *upper* side of (i) far past n = 30 by
  exhibiting short vectors, which is exactly what question (i) asks for.
- **Negative result**: "the minimum is 1 only for n in a short list" would be the
  expected shape of an answer to (ii), and is worth recording. If LLL finds
  vectors much shorter than the Kovac-van Doorn bound at moderate n, that is a
  concrete data point against van Doorn's heuristic being tight.
- **P(anything new)**: first exact table -- 80%. Something that bears on the
  heuristic -- 25%.
- **Mined**: 8 comments, nobody flagged as working, no OEIS sequence found. The
  analytic side is being worked by Kovac and van Doorn; the lattice side is not.

## C10. Problem 1210: pairwise coprime sets and sum 1/(n-a)

- **URL**: https://www.erdosproblems.com/1210
- **Status / prize**: OPEN, no prize.
- **Statement**: if A is a subset of [1,n) with pairwise coprime elements, is
  sum_{a in A} 1/(n-a) <= sum_{p<n} 1/p + O(1)?
- **Best known, from the source page (fetched 2026-08-18)**: the page records only
  Erdos's own remark that he "did not state [this] quite correctly" earlier, plus
  the related prime-interval form. **No bounds and no computation are recorded.**
- **Tool**: the same exact set-packing integer program as C4 (one binary per
  integer, one constraint per prime), with objective sum 1/(n-a) instead of
  sum a. Rational weights, so solve with float objective and re-verify the optimal
  set exactly.
- **Smallest experiment**: maximise sum 1/(n-a) over pairwise-coprime A for
  n = 100, 200, ..., 12800, and plot the excess over sum_{p<n} 1/p. Given C4 ran
  n = 51200 in 10.8 s with the identical constraint matrix, **the first signal is
  under 30 minutes**, most of which is writing the objective.
- **Negative result**: if the excess grows like log log n rather than staying
  bounded, that is evidence against the conjecture as stated and is a genuinely
  useful thing to report, since Erdos himself flagged that he had misstated it.
- **P(anything new)**: first table -- 85%. A read on boundedness -- 40%.
- **Mined**: 3 comments, nobody flagged as working, but three users including the
  database owner (TFBloom, Basile_Beyer_de_Ryke, hunterbates) have flagged it
  "looks tractable", which is a mild warning that others see the same opening.

## C11. Problem 302 (and 301): the density of 1/a = 1/b + 1/c free sets

- **URL**: https://www.erdosproblems.com/302
- **Status / prize**: OPEN, no prize.
- **Best known, from the source page (fetched 2026-08-18)**: f(N) >= (5/8+o(1))N
  (Cambie, odd integers up to N/4 together with everything in [N/2,N]) and
  f(N) <= (9/10+o(1))N (van Doorn, with a linked note). Erdos asked whether
  f(N) = (1/2+o(1))N, which the (5/8) construction already refutes.
- **Tool**: exact finite-N combinatorial optimisation. f(N) is a maximum
  independent set in the 3-uniform hypergraph on {1,...,N} whose edges are the
  triples with 1/a = 1/b + 1/c. Enumerating the triples is a divisor computation;
  the optimisation is an integer program in HiGHS.
- **Smallest experiment**: exact f(N) for N up to 200-400 (triples number
  O(N log N), the IP is small), then f(N)/N against the 5/8 = 0.625 and
  9/10 = 0.9 brackets. **Under an hour.**
- **Honest read**: finite N will not settle an asymptotic density, and the
  interesting quantity is whether f(N)/N at N = 400 already exceeds 5/8 by a
  visible margin, which would say the current record construction is not optimal
  and would point at a better one. That is the realistic prize here: **an improved
  lower-bound construction read off an exact optimum**, which is a standard and
  respectable way for a computation to beat a human construction.
- **P(anything new)**: an improved construction -- 25%. A table -- 85%.
- **Mined**: 1 comment, but **three users flagged as currently working**
  (Woett, Quanyu_Tang, khanukov), and both current records are recent. Busy.

## C12. Problem 985: is there always a prime primitive root below p?

- **URL**: https://www.erdosproblems.com/985
- **Status / prize**: OPEN, no prize.
- **Best known, from the source page (fetched 2026-08-18)**: the page cites only
  Artin's conjecture, Hooley under GRH, and Heath-Brown's result that one of
  2, 3, 5 is a primitive root for infinitely many p. **No computational
  verification bound is recorded.**
- **Tool**: exact prime computation. For each prime p, factor p-1 (cheap with a
  smallest-prime-factor sieve) and test successive primes q < p for primitive
  root order.
- **Smallest experiment**: verify for all p <= 10^8. The least primitive root is
  almost always tiny and usually prime, so the expected work per p is a couple of
  modular exponentiations. **Minutes to 10^7, an hour or two to 10^9.**
- **Negative result**: a counterexample would be a genuine surprise and would
  settle the problem. Failing that, "verified for all p <= 10^9" is a bound the
  database does not currently carry. The interesting derived statistic is the
  largest observed *prime* primitive root relative to p, which bears on how much
  room the conjecture has.
- **P(anything new)**: counterexample -- under 1%. A recorded bound -- 60%,
  discounted because this is the kind of thing that has plausibly been done
  informally and never written down.
- **Mined**: 2 comments, nobody working.

## C13. Problem 114: the Erdos-Herzog-Piranian lemniscate

- **URL**: https://www.erdosproblems.com/114
- **Status / prize**: FALSIFIABLE, $250 (reported by Borwein [Bo95]).
- **Best known, verified**: the site's remarks give the chain
  Dolzhenko f(n) <= 4 pi n, Pommerenke f(n) << n^2, Borwein f(n) << n,
  Eremenko-Hayman f(n) <= 9.173 n and the full conjecture for n = 2,
  Danchenko f(n) <= 2 pi n, Fryntov-Nazarov f(n) <= 2n + O(n^{7/8}) plus
  z^n - 1 is a local maximiser, and **Tao [Ta25] proved z^n - 1 is the unique
  maximiser for all sufficiently large n**. Tao's paper is arXiv:2512.12455,
  "The maximal length of the Erdos-Herzog-Piranian lemniscate in high degree",
  December 2025 (https://arxiv.org/abs/2512.12455).
- **The blocker, and why it does not close**: a fetch of the abstract page reports
  **no explicit threshold n_0**; the result is stated for "sufficiently large n".
  So the shape "prove it asymptotically, then finish the small cases by machine"
  is *not* available: without an effective n_0 there is no finite check to do.
  Worse, checking a single degree n means a global optimisation over monic
  degree-n polynomials, 2n-3 real parameters after killing translation and
  rotation, with a contour-length functional. That is a genuine global
  optimisation, not a finite verification.
- **What the lab could still honestly do**: multistart local optimisation of the
  lemniscate length at n = 5..12 with mpmath contour integration, followed by
  interval enclosure of the length at the reported optimum via `zeta/rigor.py`,
  producing "no configuration beating z^n - 1 was found at degree n <= 12, with
  enclosure-carrying lengths for the candidates examined". That is a bounded
  negative and is worth exactly what it says.
- **P(anything new)**: finding a counterexample -- under 2% (Fryntov-Nazarov local
  maximality plus Tao's asymptotic uniqueness leaves very little room). Producing
  an effective n_0 -- that is analysis, not computation, and is out of scope.
- **Mined**: 7 comments, **three users flagged as currently working**
  (KMendoza, dahlkebj, Sam_Petkov). This page got busy immediately after Tao's
  paper. Crowded.

# Tier 3 candidates: real but lower yield

## C14. Problem 170: the sparse ruler constant

- **URL**: https://www.erdosproblems.com/170
- **Status / prize**: OPEN, no prize.
- **Statement**: F(N) is the least size of A in {0,...,N} with
  {0,...,N} contained in A - A. Find lim F(N)/N^{1/2}.
- **Best known, from the source page (fetched 2026-08-18)**: the limit exists
  (Erdos and Gal [ErGa48]) and lies in **[1.56, sqrt(3)]**, lower bound Leech
  [Le56] (1956), upper bound Wichmann [Wi63] (1963). Pegg's computations [Pe20]
  suggest sqrt(3) = 1.7320... is the truth. A general web search turned up
  Wolfram's 2020 sparse-ruler work and OEIS A004137 but **no verified improvement
  on the 1.56 lower bound**, so treat "1.56 is still the record" as the site's
  claim, not as independently confirmed.
- **Tool**: exact finite-N combinatorial optimisation (the same set-packing
  machinery as C4 and C10, but as a covering program), plus the lab's habit of
  structure-matched controls.
- **Why the ceiling is low**: improving the *lower* bound 1.56 means an exhaustive
  argument over all rulers of a given length, and the state of the art here is a
  heavily engineered SAT/branch-and-bound community effort (OEIS A004137 and the
  Wolfram work). Our HiGHS setup would be re-entering a crowded, well-optimised
  search from behind.
- **Smallest experiment**: reproduce F(N) for N <= 200 from the ILP as a
  calibration against A004137, an afternoon. If the solver is competitive, only
  then consider the frontier.
- **P(anything new)**: 10%. **Mined**: 3 comments here, but the underlying
  sequence is a long-running community computation. Crowded outside the database.

## C15. Problem 1142: n such that n - 2^k is prime for every 1 < 2^k < n

- **URL**: https://www.erdosproblems.com/1142
- **Status / prize**: OPEN, no prize.
- **Best known, from the source page and OEIS (both fetched 2026-08-18)**: the only
  known such n are 4, 7, 15, 21, 45, 75, 105; **Mientka and Weitzenkamp [MiWe69]
  proved there are no others up to 2^44** (about 1.76 x 10^13). OEIS A039669
  (https://oeis.org/A039669) lists the same seven terms, cites the same 1969
  paper, and **has no b-file and no later extension**. Vaughan [Va73] gave a
  density bound. The page also mentions further discussion on the Prime Puzzles
  site, which was not reachable in this scan.
- **Tool**: exact prime computation plus an elementary congruence sieve.
- **The structural point that makes it cheap**: if q is an odd prime for which 2
  is a primitive root, then {2^k mod q} covers every non-zero residue, so once
  2^k ranges far enough, n must be divisible by q. For n up to 10^25 that forces
  n to be a multiple of 3.5.11.13.19.29.37.53.59.61.67.83, about 4.6 x 10^16, so
  only about 2 x 10^8 candidates survive before the further partial constraints
  from primes like 7 and 17 (where <2> is a proper subgroup) cut it down again.
- **Smallest experiment**: reproduce the seven known values, confirm the forced
  divisibility, and estimate the surviving candidate count to 10^20. **An hour.**
  A full search to 10^20 or beyond then costs a day at most.
- **Negative result**: near-certain, and worth recording: replacing a 1969 bound of
  2^44 with 10^20 or more on a database page is a clean, checkable improvement.
- **P(anything new)**: an eighth value -- under 1%. A much larger recorded bound --
  50%, discounted hard because the Prime Puzzles community very plausibly did this
  already and it is simply not cited on the page. **Check that first.**
- **Mined**: 5 comments, nobody flagged as working.

## C16. Problem 676: integers not of the form a p^2 + b

- **URL**: https://www.erdosproblems.com/676
- **Status / prize**: OPEN, no prize.
- **Statement**: is every sufficiently large integer of the form a p^2 + b with p
  prime, a >= 1, 0 <= b < p? Equivalently, is there always a prime p <= sqrt(n)
  with (n mod p^2) < p?
- **Best known, from the source page (fetched 2026-08-18)**: the Brun-Selberg sieve
  gives at most x/(log x)^c exceptions in [1,x]; Erdos thought it "rather
  unlikely" that all large integers qualify; **Selfridge and Wagstaff made a
  "preliminary computer search"** for the variant without the primality
  requirement. Erdos also asked about c_n, the least c with n = a p^2 + b and
  0 <= b < c_n p, suggesting limsup c_n = infinity and asking whether
  c_n < n^{o(1)}.
- **Tool**: segmented sieve. For each prime p, the condition marks p residues out
  of every p^2, so the exceptional set is a plain sieve computation.
- **Smallest experiment**: sieve to 10^10 recording the exceptional n, their count
  by decade, and the record values of c_n. **Under an hour to 10^9 in C**, given
  that the C6 sieve for problem 647 covered 10^9 in 3 minutes.
- **Negative result**: the deliverable *is* the exceptional-set data, so there is
  no negative outcome, only a more or less interesting exponent. The record values
  of c_n directly probe Erdos's limsup c_n = infinity suggestion, which no
  recorded computation addresses.
- **P(anything new)**: first recorded exception counts and c_n records -- 75%.
  Something that shifts belief about the conjecture -- 20%.
- **Mined**: 9 comments, nobody flagged as working.

## C17. Problem 1094 (with 1093): least prime factor of binomial coefficients

- **URL**: https://www.erdosproblems.com/1094
- **Status / prize**: OPEN, no prize.
- **Best known, from the source page (fetched 2026-08-18)**: Erdos, Lacampagne and
  Selfridge [ELS88] conjecture that for n >= 2k the least prime factor of C(n,k)
  is at most max(n/k, k) with exactly **14 listed exceptions**, the largest being
  C(284,28); in [ELS93] they add computational evidence and note it is consistent
  with max(n/k, 13) and 12 exceptions. Selfridge [Se77] conjectured the n >= k^2-1
  form with the single exception C(62,6). **The range over which ELS actually
  verified this is not stated on the page and I did not obtain [ELS88]:
  UNVERIFIED.**
- **Tool**: large exact arithmetic. The search is efficient because of Kummer's
  theorem: the least prime factor of C(n,k) exceeds k exactly when, for every
  prime p <= k, adding k and n-k in base p produces no carry. That is a strong
  digit condition that can be enumerated directly per k rather than tested per n,
  which is what makes a modern range reachable.
- **Smallest experiment**: for each k <= 40, enumerate the n <= 10^7 satisfying the
  no-carry condition for all p <= k (cheap, the surviving density is tiny), then
  test the primes in (k, n/k]. **A few hours** to a range that is very likely well
  past 1988 hardware.
- **Negative result**: a 15th exception would be a real finding on a named
  conjecture; no new exception over a stated range is a citable strengthening of
  the evidence, and the page has no range at all.
- **P(anything new)**: a new exception -- 10%. A stated verification range -- 60%.
- **Mined**: 1 comment, one user flagged as working (will0708).

# Killed, with reasons

These looked good on the way in. Recording why they died is the point of the
scan; several of them are the kind of candidate that would have eaten a week.

| # | Why it dies |
|---|---|
| 242 (Erdos-Straus 4/n) | verified to n <= 10^18 [MiDu25]; a search adds nothing and the theory is the whole problem. https://www.erdosproblems.com/242 |
| 373 (n! = a_1!...a_k!) | no solutions known below **10^3000** (Caldwell, Habsieger). Computation is finished as a tool here. https://www.erdosproblems.com/373 |
| 398 (Brocard-Ramanujan) | no solutions below 10^9 and finiteness needs ABC; the open part is Diophantine theory, not search. https://www.erdosproblems.com/398 |
| 364, 366 (powerful triples / 2-full next to 3-full) | already excluded to 7.38 x 10^28 and 10^22 by OEIS A076445, A060355. https://www.erdosproblems.com/364 |
| 375 (Grimm) | verified for all n <= 1.9 x 10^10 [LaSh06], and the conjecture implies Legendre's, so it is out of reach by design. https://www.erdosproblems.com/375 |
| 779 (P + p prime) | Cambie's own note: the failure probability is exp(-n^{-cn}); a search cannot fail and each test is a pseudoprime test on a 3000+ digit number. https://www.erdosproblems.com/779 |
| 854 (differences of coprimes to primorials) | Ziller, arXiv:2007.01808, gives exhaustive results on non-occurring differences for **all primorials to k = 44** and a conjectured threshold. The "Lacampagne and Selfridge computed k=6" line on the page is forty years out of date. https://arxiv.org/abs/2007.01808 |
| 389 (n(n+1)...(n+k-1) divides the next k) | OEIS A375071 was extended to a(27) = 5048891644620 by Sharvil Kesarwani in **March 2026**; two users are actively working the page. Crowded and compute-bound. https://oeis.org/A375071 |
| 458 (lcm inequality at prime gaps) | a counterexample needs a prime gap containing two prime squares, i.e. a gap of size about sqrt(p) log p, against known maximal gaps of size about (log p)^2. Unreachable by search, and the page marks it falsifiable only in principle. https://www.erdosproblems.com/458 |
| 488 (density of multiples of a finite set) | **Run here**: exhaustive over all A contained in {1,...,12} of size <= 4 with m,n <= 4000, the best ratio found is 1.9167 at A = {12}, n = 23, m = 24, and every top slot is a singleton A = {a} with n = 2a-1, m = 2a giving (2a-1)/a. The extremal family is the known one and nothing composite beats it. Also 30 comments and two users actively working. Dead. |
| 307 (product of two prime reciprocal sums) | kept as C5 for the reduction only; the search itself is 2^60 and hopeless. |
| 412 (iterated sigma orbits merge) | testing a merge needs the factorisation of sigma_i(n), which outgrows ECM within a few iterations. Wrong tool set. https://www.erdosproblems.com/412 |
| 470 (odd weird numbers, $10) | long-running community search; not our edge. |
| 478 (socialist primes, k! mod p) | already verified to 10^11 (Andrejic and Tatarevic 2016), and the density claim needs O(p) work per prime. https://www.erdosproblems.com/478 |
| 1095 (Erdos-Selfridge function g(k)) | an active dedicated computational literature exists (arXiv:1907.08559). Crowded. |
| 1038, 1041, 1045, 848, 396, 686, 684 | 141, 47, 48, 48, 35, 36 and 27 comments respectively, with users actively working. These are the database's current hot spots and we would be the last party to arrive. |
| 1135 (Collatz, $500), 3 ($5000), 142 ($10000), 30 ($1000) | famous, deep, and mined by everyone. Say so plainly: no computational handle this tree has changes anything about them. |
| 256 (Erdos-Szekeres product) | the specific question asked has already been answered no by Belov and Konyagin (log f(n) << (log n)^4); what remains is estimating f(n), a min-max over integer tuples with no cheap exact structure. https://www.erdosproblems.com/256 |
| all `not provable` / `not disprovable` / `independent` problems (474, 736, 739, 1119, 1123, 1127, 1154, 1169, 1174, 1176) | set-theoretic. No computational handle at all. |
| the 140 open graph-theory and 61 geometry problems | mostly Ramsey-type or extremal-graph searches where the state of the art is dedicated SAT solvers and years of compute. Not this tree's tooling. |

# Ranking

F = feasibility of a first signal in hours (0-5). N = honest probability that
something new comes out. M = how heavily mined (0 untouched, 5 crowded).
V = value if it lands.

| rank | # | candidate | F | N | M | V |
|---|---|---|---|---|---|---|
| 1 | 710/711 | exact Erdos-Pomerance f(n) | 5 | 0.85 | 0.5 | high |
| 2 | 912 | constant in h(n) ~ c(n/log n)^{1/2} | 5 | 0.85 | 1 | high |
| 3 | 879 | exact G(n), pairwise-coprime max sum | 5 | 0.85 | 0.5 | med-high |
| 4 | 311 | exact table of delta(N) | 5 | 0.90 | 1 | med |
| 5 | 647 | search bound and D(n) growth table | 5 | 0.70 | 4 | med |
| 6 | 1074/1072/1073 | EHS density from below, one sweep for three problems | 3 | 0.80 | 2 | med-high |
| 7 | 1210 | pairwise coprime sum 1/(n-a) | 5 | 0.85 | 0.5 | med |
| 8 | 317 | exact minima of sum delta_k/k, plus LLL | 4 | 0.80 | 1 | med |
| 9 | 676 | exceptional set for a p^2 + b | 4 | 0.75 | 1 | med |
| 10 | 1094 | least prime factor of C(n,k), Kummer enumeration | 3 | 0.60 | 1 | med |
| 11 | 985 | prime primitive root below p | 5 | 0.60 | 1 | low |
| 12 | 1142 | n - 2^k prime, past the 1969 bound | 4 | 0.50 | 2 | low-med |
| 13 | 302/301 | 1/a = 1/b + 1/c free sets, improved construction | 4 | 0.25 | 4 | med |
| 14 | 168 | more digits of the {n,2n,3n} constant | 2 | 0.15 | 3 | med |
| 15 | 170 | sparse ruler constant | 3 | 0.10 | 4 | med |
| 16 | 307 | the 2-cycle reduction, bounded negative | 4 | 0.20 | 3 | low |
| 17 | 114 | lemniscate, bounded negative at small degree | 2 | 0.02 | 4 | low |

## Top three, with reasoning

**1. Problem 710 (and 711): exact values of the Erdos-Pomerance function f(n).**
This is the best-shaped item in the whole scan. Erdos put money on an asymptotic
formula. Erdos and Pomerance proved bounds whose *ratio* is only
(log log n)^{1/2}, which at n = 10^5 is about 1.5, so exact values across four
decades genuinely discriminate between the two shapes. The object is a system of
distinct representatives, which is a bipartite matching, which is exact finite
combinatorics of precisely the kind `sine_gram/` already does. Almost
nothing is recorded: no values on the problem page, no OEIS sequence, 7 comments,
and one self-declared worker (SkyYang). And the first signal is already in hand: a correct Kuhn
matching computed f(n) for n up to 4000 in **2.1 seconds**, giving

  n:                                100    200    500   1000   2000   4000
  M_min:                            160    340    877   1816   3814   7900
  M/(n sqrt(log n)):              0.7456 0.7386 0.7036 0.6910 0.6917 0.6858
  M/(n sqrt(log n / log log n)):  0.9214 0.9537 0.9510 0.9606 0.9851 0.9975

The two normalisations move in *opposite* directions, the upper-bound shape
drifting down and the lower-bound shape drifting up. That is the sharpest single
signal produced anywhere in this scan, and it says the experiment is already
discriminating. Hopcroft-Karp instead of Kuhn takes this to n = 10^5 in an
afternoon. Risk: the trend may not resolve, and the constants 1.213 and 1.7398
sit in different normalisations so care is needed comparing them.

**2. Problem 912: the constant in h(n) ~ c (n/log n)^{1/2}.**
Chosen because it is the cheapest test of a *named prediction* in the database.
Tao's Cramer-model heuristic in the comments predicts c = sqrt(2 pi) = 2.5066;
nobody has checked it. Seven seconds of numpy gives the ratio at 2.65 across five
decades, about 5.6% high, which at n = 10^8 is exactly the size a 1/log n
correction would be. So this is not yet a disagreement, and saying it were would
be the classic error the certainty ladder exists to prevent. What makes it a top
pick is that the discriminating experiment is also cheap: for p > sqrt(n) the
exponent is floor(n/p), so h(n) at n = 10^12 costs about 10^6 short-interval
prime tests rather than a sieve. A two-term fit over 10^3 to 10^15 either
supports sqrt(2 pi) with a measured secondary coefficient, or does not, and both
are worth writing down. The tooling required is exactly what this tree has.

**3. Problem 879: exact values of G(n), the largest sum of a pairwise-coprime
subset of {1,...,n}.**
Chosen for the ratio of value to effort. One comment on the page, nobody working,
no OEIS sequence, and the exact optimum is a set-packing integer program with one
variable per integer and one constraint per prime, which HiGHS solves at
**n = 51200 in 10.8 seconds**. First numbers, produced here:

  n:                    3200    6400   12800   25600   51200
  H(n) - G(n):          3714   10285   22205   31473   69934
  (H-G)/n:             1.161   1.607   1.735   1.229   1.366
  log(H-G)/log n:     1.0185  1.0541  1.0582  1.0203  1.0288

Erdos and Van Lint *proved* (H(n)-G(n))/n tends to infinity, so the very slow and
non-monotone growth visible here is a real feature to explain rather than a bug,
and the measured exponent sitting at 1.02 to 1.06 is direct evidence on the open
question, which asks exactly whether H(n) - G(n) is n^{1+o(1)}. The same
constraint matrix immediately serves problem 1210 (rank 7), so the two should be
done together.

## What the next two would be

Problem 311 (rank 4) if the goal is a clean artifact with near-certain delivery:
the first exact table of delta(N), already computed here to N = 44 in 15 seconds,
extendable to N = 56 or so, with -ln delta(N)/N drifting from 0.62 to 0.49 in a
way that is mild evidence against the conjectured pure exponential shape.

Problem 647 (rank 5) if the goal is a prize and a database gap: 3 minutes 20
seconds of C already establishes no example with 24 < n <= 10^9 and produces the
per-decade growth table for Erdos's stronger conjecture. It is ranked below 311
only because 13 comments and four self-declared workers make it likely someone
has already run the search and not published it. **Read the live comment thread
before spending compute there.**

# Scan accounting

- 1217 problems in the database; 604 `open`, plus 27 `falsifiable`,
  9 `decidable`, 7 `verifiable` and 4 `open (Lean)`.
- 437 open-ish problems in the number-theory / analysis / combinatorics tag pool.
  **All 437 statements read.**
- 45 problems read in full including remarks and activity metadata.
- 17 candidates survive with a stated experiment, runtime and probability.
- 20 killed rows covering roughly 35 named problems plus two whole tag families
  (graph theory, geometry), with the reason recorded in each case.
- 7 candidates had a first-signal experiment actually run during the scan:
  647, 311, 307, 488, 710, 879, 912. Two of those (488, 307) were killed *by*
  their own experiment, which is the scan working as intended.

# Reproduction

Code written during this scan lives in the session scratchpad, not in the repo:
`scratchpad/e647/tau647c.c` (segmented tau sieve, problem 647) and the inline
scripts quoted above for 311, 307, 488, 710, 879 and 912. All of them are short
enough to retype from the descriptions here; none of them is a repository
artifact yet and none should be committed until a candidate is actually chosen.

**Git state, recorded honestly.** This scan committed nothing. However, a
*concurrent session working the same checkout* ran a broad `git add` and swept the
58-line header of this file into commit `d775e48`
("hunts(rogue_frontier): the pairing count, proved in Lean with zero sorrys",
2026-08-18 22:20:05 +0000) while it was still being written. Everything from
"Tier 1 candidates" onward is uncommitted working-tree content at the time of
writing. That collision is exactly the hazard `CLAUDE.md` warns about under
"Multiple agents / parallel sessions": two agents in one checkout rather than
separate worktrees. It has not been undone here, because rewriting another
session's history is worse than recording what happened.
