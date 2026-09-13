# Baseline review: the combined-weight repair in `certificate_route_test`

Date: 2026-09-06. Reviewer: a Claude Code session working from the repository, not the
session that produced the package. Status: **an independent written and computational
review of an archived package.** It re-derives every all-cutoff argument the package relies
on, establishes every finite hypothesis of those arguments by its own exact computation, and
reproduces the recorded numbers by two routes. It is not a Lean check, not an external human
review, and not a claim of novelty. Nothing here is a prime-counting record and nothing here
bears on RH: the leading constant stays above one.

The object under review is the **final combined-weight repair** recorded in
`aggregate_results.json`, with parameters M = 15, R = 100000, mask 210, and corrections at
p = 17, 19, 23, 29, 31. It is the current candidate baseline. The earlier seed-positive
repair (`original_results.json`, `ORIGINAL_REFINEMENT.md`) is an input to it, not the object.

## 1. Verdict

**Survives.** Every claimed quantity reproduces, every finite hypothesis holds under
independent exact arithmetic, and every written all-cutoff argument is correct as an
elementary argument. No repair is needed. Section 5 lists what this verdict does not cover.

| Quantity | Recorded | Reproduced here | How |
|---|---|---|---|
| leading constant C | 1.0486636637932206282... | enclosed in an interval of width 9.7e-59 whose endpoints both begin 1.048663663793220628233678560567956282917 | mpmath interval logs; the recorded 60-digit value lies inside, and a 60-digit float route agrees |
| finite coefficient mass | 2641/3 | 2641/3 | exact Fraction sum over the 930 recorded coefficients, and over the reconstruction |
| tail coefficient | 15 | 15 | five stages, H_p = 3 each, by full-period enumeration |
| repairs | 537 (78, 172, 156, 33, 98) | 537, same cells and same amounts stage by stage | independent greedy reconstruction |
| negative seed cells below R | 705 | 705, first at t = 299 | divisor-increment table of the recorded seed |
| lifted prefix minimum on [1, R) | 1 | 1 (scaled 3/3) | from the recorded coefficients, not the reconstruction |
| final sufficient bound | psi(N) <= C N + (2641/3) S1(N) + 225 S2(N) | same, and B_N <= U_N at the four recorded N | section 3.5 |

The reconstruction produced the recorded 930 final coefficients exactly. The recorded
`aggregate_repair.py`, rerun in a scratch extraction, wrote a file identical to the archived
`aggregate_results.json` except for the `seconds` field (`review/rerun_aggregate_results.json`).

## 2. What was run

- **Reproduction.** `aggregate_repair.py` run in a scratch copy of the package with the
  recorded output set aside first. Leaf-by-leaf comparison with the archived output: one
  differing leaf, `seconds`. The two upstream packages were rerun the same way and their
  outputs are in `review/upstream_reruns/`; `refine.py` reproduces its recorded output except
  `seconds`, and `probe.py` plus `check_and_compare.py` reproduce both seeds and all
  constants (section 4 records one provenance wrinkle there).
- **Independent checker.** `review/baseline_check.py`, output `review/baseline_check.json`.
  It imports nothing from the package and uses no numpy. Seeds and lifted weights are
  evaluated by divisor increments (floor(t/j) counted as the multiples of j up to t, then a
  prefix sum), a different route from the package's numpy floor arrays. Logarithms are
  enclosed with mpmath's interval context, a different route from the package's rational
  atanh series. Runs in about 25 s on a laptop; no heavy compute.
- Environment: Python 3.14.0, mpmath 1.3.0, numpy 2.5.2, scipy 1.18.0.

## 3. The arguments, one at a time

Notation as in `ROUTE_ASSESSMENT.md`: g_0 is the period-30030 seed, g_* the period-2310
repair seed (both from `inputs.json`), b_n the carry function, h_p the masked correction,
W_g(t) = sum_{k>=0} g(t/M^k), and the final seed is g = D + 15 W_*(t/R) with D a finite
balanced floor sum.

### 3.1 W_g(t) = sum_{k>=0} g(t/M^k)

Locally finite because every seed here vanishes on [0, 1): D has only floor(t/j) terms with
j >= 1, and W_*(t/R) vanishes for t < R. Every breakpoint of g, and hence of W_g, is an
integer (each term is floor(t/q) for an integer q, and t/M^k crosses an integer cell of g
exactly at multiples of q M^k). So both g and W_g are constant on [n, n+1), and checking
integer cells checks all real t. Used throughout; correct.

### 3.2 Prefix coverage plus tail nonnegativity implies global coverage

Claim: W_g(t) >= 1 for 1 <= t < R and g(t) >= 0 for t >= R together give W_g(t) >= 1 for
every t >= 1. Proof: for t >= R write W_g(t) = g(t) + W_g(t/M) and iterate while the
argument is at least R; every term removed is g at an argument >= R, hence nonnegative; the
first argument below R is at least R/M >= 1 because R >= M, so its lifted weight is at
least one by the prefix condition. Correct. The two hypotheses it needs, R >= M and g = 0 on
[0, 1), both hold (R = 100000, M = 15).

### 3.3 The greedy repairs and the tail shield establish those two conditions

Carry function: b_n(t) = floor(t/n) - floor(t/(n+1)) - floor(t/(n(n+1))) is
floor(u+v) - floor(u) - floor(v) with u = t/(n+1), v = t/(n(n+1)), so it takes only the
values 0 and 1; it vanishes for t < n and equals 1 at t = n. Checked exhaustively for
n = 2..120 over two periods and on 2000 random (n, t) pairs up to 10^12.

Prefix: at the first cell n with W(n) < 1 the algorithm adds lambda_n b_n to the seed with
lambda_n = 1 - W(n) > 0. On the lifted weight this adds lambda_n sum_k b_n(t/M^k), which is
nonnegative, zero for t < n, and exactly lambda_n at t = n (the k >= 1 terms vanish there
since n/M^k < n). So the cell is corrected and no earlier cell moves; later repairs, at
larger n, cannot move it either. After the scan every cell in [1, R) has W >= 1. My scan
reproduces the recorded 537 repairs cell for cell and amount for amount, and a fresh rebuild
from the recorded coefficients has lifted minimum exactly 1 on [1, R). The seed itself is
negative at 705 of those cells (first at t = 299), which is the relaxation being tested, and
the lifted weight covers anyway.

Tail: for t >= R, g(t) = g_0(t) - sum_p h_p(t) + [patches](t) + 15 W_*(t/R). The pieces:
g_0 >= 0 everywhere (balanced, so periodic with period 30030; all 30030 cells checked
exactly); each h_p <= 3 everywhere (period 210 p (p+1); all 651000 cells over the five
periods checked exactly, and H_p = 3 is the true supremum, not the generic 8); every patch
is lambda_n b_n >= 0; and W_*(x) >= 1 for x >= 1 because g_* >= 0 (all 2310 cells) and
g_* >= 1 on [1, 15) (checked), so the k with 1 <= x/M^k < 15 supplies a term of at least
one. Hence g(t) >= 0 - 15 + 0 + 15 = 0. Correct, and stage-wise the same argument gives
validity after each stage with the accumulated H. Sixty-six exact samples of the seed and of
the lifted weight at t between R and 10^12 agree; they are a diagnostic, the proof does not
use them.

### 3.4 Integrability of the signed seed and the leading-constant formula

D is a balanced floor sum, so D(t) = -sum_j d_j {t/j} is bounded by its mass 2641/3, and
15 W_*(t/R) = O(1 + log t). So the integral of |g(t)| t^-2 over [1, oo) is finite, and
sum_k of the integral of |g(t/M^k)| t^-2 is sum_k M^-k times that, also finite. Fubini then
justifies the exchange, and the same substitution on each term gives

    integral_1^oo W_g(t) t^-2 dt = kappa(g) / (1 - 1/M) = C,
    kappa(g) = kappa(D) + 15 kappa(g_*) / (R (1 - 1/M)).

Two identities underneath were re-derived: for a balanced floor sum, kappa = -sum a_j log j
/ j (the constant term drops by balance), and the integral of W_*(t/R) t^-2 equals C_*/R.
Both are used in the checker's evaluation of C, which agrees with the package's to all
recorded digits. The formula itself does not need g >= 0. What does need a sign is the
error budget's dropping of geometric tails (3.5): that needs kappa(D) > 0 and
kappa(g_*) > 0, and the enclosure gives kappa(D) > 0.9785, kappa(g_*) > 0 trivially.

### 3.5 The factorial identity and the full error budget

Identity: log(floor(x)!) = sum_{d <= x} Lambda(d) floor(x/d), so with c_q the lifted
coefficients (index j M^k with weight d_j, and index R j M^m with weight 15 (m+1) a*_j, the
m+1 counting the ways two rescalings sum to m), B_N = sum_q c_q log(floor(N/q)!) =
sum_{d <= N} Lambda(d) W_g(N/d) >= psi(N), the inequality by 3.2 and 3.3. Checked two ways:
the prime-exponent form of the identity at every prime up to 2000 and up to 10000 (1532
exact identities, each requiring W_g >= 1 at the arguments it touches), and directly, B_N
computed at 60 digits against an exact Chebyshev psi(N) at fourteen cutoffs between 10^3 and
10^6, B_N >= psi(N) at all of them.

Error budget: the package cites the pilot's inequality

    | sum_j a_j log(floor(x/j)!) - kappa x | <= A (1 + log^+ x),   A = sum |a_j|,

for balanced seeds. Because the seed is now signed, this reviewer re-derived it without a
sign assumption. For each j put m = floor(x/j) and Phi(y) = y log y - y. If m >= 1 then
log(m!) - Phi(m) lies in [1, 1 + log m] (compare the sum of log n with its integral) and
Phi(m) - Phi(x/j) = -theta log xi for some xi in [m, x/j], so the total deviation of
log(m!) from Phi(x/j) lies in [1 - log(x/j), 1 + log(x/j)]; if m = 0 the deviation is
-Phi(x/j) in (0, 1). Balance makes sum_j a_j Phi(x/j) = kappa x exactly. So the inequality
holds for every real x >= 1 and every balanced seed, signed or not. Applying it to D at
each level N/M^k (k <= floor(log_M N)) and to g_* at each tail level with weight 15 (m+1),
and dropping the positive geometric tails (kappa(D) > 0, kappa(g_*) > 0), gives

    psi(N) <= B_N <= C N + (2641/3) S1(N) + 225 S2(N)

with S1 and S2 exactly as defined in `REFINEMENT.md`. The four recorded comparison rows
(N = 10^4, 10^6, 10^8, 10^12) were recomputed from the lifted coefficient dictionary rather
than level by level; they agree with the recorded strings to better than 1e-40 relative
and satisfy B_N <= U_N. The budget is complete: the infinite tail is in 225 S2, and nothing
is dropped with an uncertain sign.

### 3.6 The fixed-recipe ceiling applies only under its stated restrictions

Arithmetic, all verified exactly or by enclosure: kappa(h_p) = (8/35) k_p (the mask's
Moebius sum is 8/35, and the interval for kappa(h_p) meets the interval for (8/35) k_p at
each of the five p); gross gain (12/49) k_p; k_n <= (1 + log n)/n^2 for n = 33..3000 by
enclosure and for all n by the two elementary inequalities in the note; the integral bound
(2 + log 31)/62 < 11/124 using log 31 < 7/2 (enclosed); (12/49)(11/124) = 33/1519;
21/20 - 33/1519 = 31239/30380 > 1.028; the old five-stage constant is above 21/20 and the
new one above 131/125, both by enclosure; 131/125 - 33/1519 > 1.026.

Scope, stated as the note states it and as the argument actually needs: the cap holds for
continuations that (a) use each prime p > 31 at most once with the same amplitude 1,
(b) keep the mask 210 and M = 15, (c) charge only nonnegative repairs and tail shields, and
(d) start from the recorded seed. Under (c) every repair raises kappa, so the gross gain of
a stage is an upper bound on its net gain; the cap sums gross gains over every odd integer
above 31, which is generous. It says nothing about signed or coordinated corrections,
changed amplitudes, revisiting earlier cells, other masks or radices, or other majorants,
and the note says so.

Early-excess view: for the combined-weight final seed the lifted weight exceeds one below
37 exactly at t = 18, 19, 20, 21, 24, 25, 32 with the values the note lists, and the weighted
excess sum_{t<37} (W(t) - 1)/(t(t+1)) is exactly 23977/1441440. The same cells and the same
sum hold for the old five-stage seed: the two constructions coincide below 37. The floor
C >= 1 + 23977/1441440 for the once-per-new-prime continuation is valid because W >= 1
everywhere (so the excess elsewhere is nonnegative) and because a correction at p >= 37,
its repairs, and its tail shield all vanish below 37, so that prefix is frozen. Correct,
and again restricted to that menu.

## 4. Observations that are not failures

- The structural-step package's recorded `results.json` carries two keys, `C_60digit` and
  `comparisons`, that the shipped `probe.py` does not emit; the rerun lacks them. The
  coefficients, constants and every other field agree, and `check_and_compare.py` passes on
  the rerun. So the shipped script is not byte-for-byte the one that wrote the recorded
  file. This does not touch the baseline: the route test takes its seeds from `inputs.json`,
  and this review re-verified those seeds over their full periods.
- `C_float` for the period-2310 seed prints as 1.0698544525734643 here and
  1.069854452573464 in the record: a last-digit float repr difference between scipy
  versions, with identical rational coefficients underneath.
- The LP in `probe.py` (scipy HiGHS) reproduced both seeds exactly on this machine. That is
  a reproduction, not an optimality statement; the package claims none.
- The prefix below 37 is identical for the seed-positive and combined-weight constructions,
  which is consistent with the first deficit appearing at t = 189 in both.

## 5. What this review does not establish

- Any rate: C - 1 does not tend to zero in any family shown here, and the package claims no
  such rate. The ceiling in 3.6 is a ceiling on one menu, not a theorem about all menus.
- Optimality of the five corrections, the mask, R, or M. The mask was chosen after an
  exploratory comparison (`exploration.json` in the refinement package) and held fixed.
- Novelty. No literature search was run; the carry identity, floor-sum majorants and
  Chebyshev's construction are classical, and the package says so.
- Formal verification. Nothing here was checked by Lean. The finite checks are exact
  integer and rational arithmetic and interval enclosures (two independent routes, so the
  numbers are hardened in the laboratory's vocabulary); the all-cutoff arguments are
  elementary and were walked by one reviewer. External verification is pending.
- Anything about the total CHHL error E(N) or about RH.

## 6. Reproduce

From the repository root, with the laboratory's virtual environment:

    cd hunts/prime_pair_error/frontier/2026-09-06/certificate_route_test/review
    OPENBLAS_NUM_THREADS=1 ../../../../../../.venv/bin/python baseline_check.py

writes `baseline_check.json` beside itself and exits non-zero on any failed check. To rerun
the package's own script, copy the package to a scratch directory first: its default output
name is the archived record and must not be overwritten. `tests/test_combined_weight_baseline_review.py`
pins the numbers in section 1 on every run.

## 7. Boundary

This review checks the baseline as recorded. It does not extend the construction to more
primes, rerun the objective comparisons of PR #196, switch criteria, or propose the next
construction; the coordinated signed correction discussed in `ROUTE_ASSESSMENT.md` section 6
is a separate design that this review neither implements nor prejudges.
