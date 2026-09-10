# li_dh_onset: the Li coefficients of the Davenport-Heilbronn function

**Hunt, not a result.** Everything below is exploratory (`hunts/README.md`).
**Nothing here is evidence about the Riemann Hypothesis** (`docs/08`): the
Davenport-Heilbronn function is not zeta, has no Euler product, and already
violates its own analogue of the hypothesis. That is why it is the subject.

**Lexical note.** The reserved enclosure word does not appear in this directory
and no quoted artifact required masking, so no mask was applied. Nothing here
carries enclosures; the grade of every number is stated where it is claimed.

## What was asked and what was measured

Bombieri and Lagarias (1999, Theorem 1) make "lambda_n >= 0 for every n" and
"every zero has real part 1/2" the same statement for a multiset closed under
`rho -> 1 - rho`. The Davenport-Heilbronn function has a measured off-line pair,
so some lambda_n(DH) is negative. No lambda_n(DH) existed anywhere in this
repository before this hunt, and no literature search was run, so nothing here
claims the sequence is new to the world. What is claimed is that these numbers
were produced here, from the function rather than from a target handed over.

| question | answer | grade |
|---|---|---|
| how far can n be pushed here | **n = 5000**, in 1472 s of contended wall time; the cost model puts n = 20000 at about 3.7 h and n = 3.3e5 at about 20000 h | measured, plus a fitted cost model |
| are all computed lambda_n(DH) positive | **yes**, for every n from 1 to 5000; the minimum over the whole table is lambda_1 = 0.0976, nowhere near zero | hardened in the sense of independent routes agreeing, not in the enclosure sense |
| where is the first negative index | **n = 328997**, from a background fitted to the coefficients measured here plus the fifteen off-line quadruples this repository holds | measured inputs, extrapolated conclusion |

The first four coefficients, at dps 25, agreeing across the Cauchy route, the
literal n-th derivative definition, and (for n = 1) a closed form:

    lambda_1(DH) = 0.09763614680951967118155
    lambda_2(DH) = 0.3888255141255960075677
    lambda_3(DH) = 0.8684689300375514689369
    lambda_4(DH) = 1.528259116943152270966

and at the ends of the table, at dps 30,

    lambda_200(DH)  = 467.6848865502381460808
    lambda_2000(DH) = 6957.90885215558997602910140982041
    lambda_5000(DH) = 19674.8045389958757346421990391843

The full tables are `artifacts/lambda_dh_n2000_r0.9.json` (n <= 2000, radius
0.9) and `artifacts/lambda_dh_n5000_r0.95.json` (n <= 5000, radius 0.95).

## The route, and why it never reads a zero

`dhli.py` mirrors `zeta.li._li_cauchy` on the completed function
F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s). Substituting s = 1/(1-z) maps
|z| < 1 onto Re s > 1/2, and lambda_n = n [z^n] log F(1/(1-z)) is read off one
equispaced trapezoid pass around |z| = r. The branch of the logarithm is built
by continuity from z = r, where F is real and positive, and the winding number
around the circle is checked. Working precision and node count follow
`zeta.li`'s own rules verbatim: w = dps + 2*guard + n_max*log10(1/r) and
N = w*ln10/ln(1/r) + n_max + 8.

No zero list enters. That matters here more than it does for zeta, because a
sign-change scan of Z_f *undercounts* the Davenport-Heilbronn zeros by
construction, and a coefficient route built on such a list would be summing the
wrong multiset.

## The radius, established before anything was extracted

Under z = 1 - 1/s the modulus is |z| = |s-1|/|s|, so |z| <= r is exactly the
Apollonius disc |s - 1/(1-r^2)| <= r/(1-r^2). Three consequences carry the whole
argument and none of them assumes anything unproved:

* a zero with Re s = 1/2 has |s-1| = |s|, so it lies on |z| = 1 exactly and can
  never enter the contour at any r < 1;
* a zero with Re s < 1/2 has |z| > 1;
* a zero with |s| >= 1/(1-r) has |z| >= r.

So only zeros with Re s > 1/2 and modulus below 1/(1-r) matter. Measured
(`artifacts/radius_scan.json`):

| leg | measurement |
|---|---|
| coefficient bound | sum_{n>=2} \|a_n\| n^{-2} = **0.2666639461309748574** by the Hurwitz form, 0.26653553822880422209 by direct summation to n = 4000; below 1, so f has no zero with Re s >= 2 |
| r = 0.9 | disc centre 5.26315789, radius 4.73684211; the rectangle [0.5203, 2] x [-3.5036, 3.5036] containing its Re s <= 2 part holds **0 zeros** (argument principle, 2.2 s) |
| r = 0.95 | disc centre 10.25641026, radius 9.74358974; rectangle [0.50682, 2] x [-5.2439, 5.2439] holds **0 zeros** (2.9 s) |
| Re s > 1, extended | [1.0001, 4] x [0, 120] in six windows: **0 zeros** in every one |

Both radii used for the tables are therefore admissible, and the winding check
inside every extraction returned zero on the actual contour, which is the same
statement made a second time on the exact curve rather than on a rectangle
containing it.

## The controls, all of which ran

**The positive control ran first and passed.** The identical pipeline pointed at
`zeta.core.xi` reproduces the committed table
`data/li_lambda_dps25_methodcauchy_n400_radius0.5.json` with a worst relative
difference of **4.4174238e-28** over all 400 indices, at radius 0.5 (166 working
digits, 960 nodes) and again at radius 0.9 (64 digits, 1807 nodes). It returns
lambda_1 = 0.02309570896612103381431, lambda_50 = 43.53109648837402 and
lambda_300 = 519.7019656192496, which are the values `zeta/li.py` states in its
own docstrings.

**Radius independence.** lambda_n(DH) for n <= 200 at dps 30, extracted at
r = 0.5, 0.7 and 0.9, is **bit identical** across all three, which is what
`zeta/li.py` reports for zeta. The n = 5000 table at r = 0.95 is likewise bit
identical to the n = 2000 table at r = 0.9 over their common range. A branch
error or a missed winding is a property of the contour, so four contours
agreeing to the last stored bit leaves no room for one. The registered kill
condition on this oracle did not fire.

**The definition itself.** The generating-function substitution is a derivation,
so `defect_check.py` compares it against Li's literal definition,
lambda_n = (1/(n-1)!) d^n/ds^n [s^{n-1} log F(s)] at s = 1, evaluated by mpmath's
Cauchy-integral differentiator on a disc of radius 0.4 about s = 1. Defects at
n = 1, 2, 3, 4 are 2.05e-28, 2.34e-27, 4.25e-27 and 3.69e-27 at dps 25, and
lambda_1 also matches the closed form
-log(pi/5)/2 - euler/2 + f'(1)/f(1) to 2.05e-28.

**The evaluator.** `dhli.completed_dh_fast` agrees with
`zeta.epstein.completed_dh` to 6.6e-46 at twelve points spread around the r = 0.9
contour. `zeta.epstein.dh_functional_equation_defect` at dps 40 underflows to
zero at four scattered points, and `dh_mean_value_defect(1.001, 0.25)` at dps 30
is 1.34e-51, which is the no-pole check that lets the contour cross Re s = 1
without dodging anything.

**Parallelism.** A three-process run and a serial run of the same circle produce
bit-identical samples and bit-identical coefficients; values cross the process
boundary as mpmath's exact triples.

**A structural check that was not registered but is worth recording.** Running
the same pipeline on xi at n <= 2000 gives a measured difference

    lambda_n(DH) - lambda_n(zeta) - (n/2) log 5  in  [-16.89, +21.83],  mean -1.54,

over 1 <= n <= 2000. The (n/2) log 5 is exactly the conductor: the smooth
Davenport-Heilbronn zero density is (1/2 pi) log(5t/2 pi), zeta's with 2 pi
replaced by 2 pi/5. That the residual stays O(1) times the expected oscillation
rather than drifting is a check on the completion, the Gamma factor and the
constant kappa all at once.

## The background, measured rather than borrowed

Fitting a n log n + b n + c to the computed coefficients over n in [2500, 5000],
with a pinned at 1/2:

    b_fitted   = -0.3253007230577492
    b_derived  = -0.32561174453685604 = (log(5/(2 pi)) + euler - 1)/2

agreeing to 3.1e-4, well inside a residual whose root mean square over that
window is 6.69 and whose extremes are -18.88 and +18.42. The free fit gives
a = 0.5018940923597734, which is 1/2 to within the same oscillation. This is the
conductor-5 analogue of `zeta.li.li_asymptotic`, and it is measured here rather
than assumed. It is also the reason the answer below is not simply the previous
estimate repeated: the earlier figure used the zeta-shaped background, whose
b is -1.1303, a constant 0.805 per unit n away from the right one.

## Where the first negative index sits

Group the zeros into quadruples. With sigma = 1 - rho and u = 1 - 1/sigma, the
identity (1 - 1/rho)(1 - 1/sigma) = 1 collapses the four Li terms to

    Q_n = 4 - 2 (R^n + R^-n) cos(n psi),   R = |u| > 1 exactly when Re rho > 1/2.

For n small enough that R^n is near 1 this is bounded and the background fit
absorbs it. What the fit cannot see is the growing part, so

    lambda_n  =  background(n)  -  sum_k 2 (R_k^n + R_k^-n - 2) cos(n psi_k),

and `onset.py` scans that expression from n = 5000 upward. The subtraction of the
2 is what stops each quadruple being counted twice.

The fifteen off-line zeros this repository holds, ranked by growth
(`artifacts/onset.json`), are led by the lowest of them:

| quadruple | beta | gamma | R - 1 | psi | resonance period in n |
|---|---|---|---|---|---|
| pair1 | 0.8085171825 | 85.6993484854 | **4.2006164e-05** | -0.0116684165 | 538.5 |
| pair2 | 0.6508300806 | 114.1633427308 | 1.1572523e-05 | -0.0087593078 | 717.3 |
| pair4 | 0.7242576946 | 176.7024612429 | 7.1822338e-06 | -0.0056592065 | 1110.3 |
| pair5 | 0.8695305796 | 240.4046723514 | 6.3938591e-06 | -0.0041596371 | 1510.5 |

**The answer: n = 328997**, with the model value there -2216.9 against a
background of 1982732.9, a dip of 0.112 per cent. It is the same index under
every background variant tried except the zeta-shaped one:

| background | first negative index |
|---|---|
| fitted, all fifteen quadruples | **328997** |
| fitted, dominant quadruple alone | 328997 |
| fitted on the lower window [500, 2500] | 328997 |
| derived (no fitting), all quadruples | 328997 |
| zeta-shaped, all quadruples | 325229 |

and it moves by at most 533 under a plus or minus 0.05 shift in b, by 1 under a
plus or minus 0.001 shift in a, and to 336005 / 321997 under a plus or minus
2 per cent shift in the dominant quadruple's log R. So the index is set almost
entirely by one measured number, log R for the pair at 85.699, and the
background enters only through the 1 per cent gap between the fitted and
zeta-shaped forms.

**Why no unfound quadruple can move it** (`artifacts/dominance.json`). A rival
needs R larger than pair 1's. Three pieces close the question:

* below height 90, the argument-principle box count equals the grid-refined
  critical-line sign-change count in every window of 10 except [80, 90], where
  the excess is exactly 2, the two upper-half zeros of pair 1. There is no other
  off-line zero below 90;
* above height 188.97, the coefficient bound gives 2 beta - 1 <= 3 and hence
  R - 1 <= 3/(2 gamma^2) < 4.2006e-05 automatically;
* between them a rival needs beta > 0.8403 at gamma = 90, rising with gamma, and
  the box [0.83, 2] x [90, 190] holds **0 zeros** in five windows of 20.

**The grade.** The coefficients are hardened: two independent contours agree bit
for bit, an independent implementation of the definition agrees to round-off,
and the pipeline reproduces a table this repository pinned before the hunt
existed. The index 328997 is not. Its inputs are measured, its arithmetic is
elementary, and its conclusion is an extrapolation sixty-six times past the
largest coefficient anyone has computed. It is stated as such and it is not a
theorem.

**Against the prior datum.** `hunts/jensen_clock` phase 3 Q6 put this at
"n ~ 3.3e5" from the zeta-shaped background, hedged on its own page as an
order-of-magnitude claim. That hedge was right and the number survives: with the
Davenport-Heilbronn background measured rather than substituted, and with all
fifteen quadruples and their phases rather than one amplitude, the estimate moves
by 1.2 per cent. The envelope-crossing indicator that page declares useless was
not reused; the degeneracy that made it fire at n = 1 is guarded here by refusing
to evaluate the background below the top of its fit window, which is recorded in
`onset.py`.

## The zero side, as an independent second route

`zero_side.py` sums the multiset instead, and shares nothing with the Cauchy
route but the definition. It locates 313 critical-line ordinates of f below
height 430 by sign change and bisection, adds the nine off-line quadruples below
that height, takes the tail from the smooth Davenport-Heilbronn density
[Re psi(3/4 + it/2)/2 - log(pi/5)/2]/pi, and uses the k-independent boundary term
`zeta.li._li_zeros` derives.

**The multiset is complete below the truncation.** The argument-principle box
count over [-1, 2] x [0, T] equals (line zeros found) + 2 per off-line quadruple
exactly, at all four heights checked:

| T | box count | line zeros | quadruples below | accounted | unaccounted | theta_f(T)/pi |
|---|---|---|---|---|---|---|
| 100 | 54 | 52 | 1 | 54 | **0** | 53.867 |
| 200 | 130 | 122 | 4 | 130 | **0** | 129.673 |
| 300 | 214 | 204 | 5 | 214 | **0** | 213.807 |
| 430 | 331 | 313 | 9 | 331 | **0** | 331.040 |

The smooth count is theta_f(T)/pi with **no additive constant**, unlike zeta's
theta(T)/pi + 1; the difference is the s(s-1) factor in xi that F has no
analogue of. Measured discrepancies are +0.133, +0.327, +0.193 and -0.040, which
is the S(T) oscillation and nothing else.

**The two routes agree.** Against the Cauchy table:

| n | Cauchy | zero side | relative difference |
|---|---|---|---|
| 1 | 0.09763614680951967 | 0.09763614589454547 | 9.37e-09 |
| 4 | 1.528259116943152 | 1.528259102303762 | 9.58e-09 |
| 8 | 5.708722548659805 | 5.708722490104758 | 1.03e-08 |
| 12 | 11.53518732522694 | 11.53518719348752 | 1.14e-08 |

The residual grows smoothly with n, which is the signature of the truncation
term rather than of a disagreement: the neglected piece is the integral of
f_n'(t) S(t) above T = 430, and f_n' grows like n^2/t^2. This is the same shape
and the same order of accuracy that `zeta.li` reports for its own two routes at
comparable truncation.

## What did not happen

No kill condition fired. The radii agree bit for bit rather than merely inside
the stated round-off amplification; the xi control reproduces the committed
table; the argument-principle scan found nothing that would push the radius
below 0.7, and in fact licensed 0.95; and no computed lambda_n(DH) is negative
at any n up to 5000, so the "treat it first as a defect" branch was never
entered.

Two things this hunt did not do and should be read as not having done. It did
not compute a negative coefficient: the sign change is an extrapolation and the
table is uniformly positive. And it carries no enclosures anywhere, so no number
here is more than float grade in the ball-arithmetic sense; where the text says
*hardened* it means independent routes agree, not that any step carried an
interval.

## The doors

The ceiling measured here is the largest n at which lambda_n(DH) can be computed
on this container, and the cost model behind it is in `artifacts/ceiling.json`.

### 1. Active constraints at the optimum

Ranked by how much moving them moves n_max.

1. **Working precision, w = dps + 2*guard + n_max * log10(1/r).** This binds
   hardest, because the evaluator cost grows as w^1.97 (measured: 0.0924 s at
   142 digits, 0.3226 s at 279, warm, single-threaded) while the node count only
   grows as N = (dps + 2*guard)/log10(1/r) + 2*n_max + 8. Total cost is therefore
   roughly n_max^3 at fixed r. Shadow price: doubling n_max at fixed r costs
   about eightfold.
2. **The radius r.** It enters only through log10(1/r), and it enters the two
   terms with opposite signs, so there is an interior optimum. At n_max = 5000
   the model's cheapest radius is 0.99 (0.24 h) against 0.95 (measured 0.41 h)
   and 0.9 (model 0.99 h). The radius actually used was the largest one whose
   Apollonius disc had been measured zero-free.
3. **Effective cores.** The observed parallel speedup during the main sampling
   was close to 1: the container was carrying other tenants at load average 8 to
   13 against 4 vCPU, so three worker processes shared roughly one core. This is
   a factor of 3 to 4 sitting on the table for anyone with a quiet machine, and
   it is the only constraint on this list that costs nothing mathematical to
   relax.
4. **The evaluator.** Four Hurwitz zeta values at the working precision per
   node. `zeta.epstein.completed_dh` was measured at 0.58 s per call at 142
   digits against 0.092 s for the same mathematics with kappa cached once per
   process, a factor of six that came entirely from a precision-keyed
   `lru_cache` being handed a precision that varies with the distance from s to
   1.

### 2. The frozen-constant inventory

| constant | value used | what relaxing it trades |
|---|---|---|
| `dps` of the output | 30 | linear in w. Dropping to 15 saves 15 of 162 digits at n = 5000, about 9 per cent of the sampling cost, and costs nothing the onset analysis reads: the fit needs four digits, not thirty. **Genuine trade shape**, this is slack being spent on nothing. |
| guard digits | 2 x 10, inherited from `zeta.li` | same lever, another 20 digits. Untested here; `zeta.li` chose it for zeta and nobody has measured whether the DH evaluator needs it. |
| the node rule N = w ln10/ln(1/r) + n_max + 8 | `zeta.li`'s verbatim | this drives aliasing to 10^-w when it only has to reach below 10^-dps. At n = 5000, r = 0.95 that is 7227 nodes of aliasing headroom where about 1600 would do, so **roughly 45 per cent of all evaluations are buying aliasing suppression nobody reads**. The largest single saving on this table, and the trade is real: less headroom for a cheaper run. |
| radius | 0.9 and 0.95 | see constraint 2. The cost-optimal 0.99 needs the rectangle [0.50251, 2] x [-12.11, 12.11] measured zero-free, whose left edge sits 0.0025 from the critical line. That is the awkward part: the contour approaches a region where zeros are dense, and the argument principle needs care there. |
| the sigma cap of 2 in the radius scan | 2.0 | set by sum_{n>=2} \|a_n\| n^{-2} = 0.2667. The bound holds with margin 0.733, so the cap could come down to about 1.55 and shrink every scanned rectangle, at the cost of re-measuring the sum. Small money. |
| off-line census ceiling | height 90 full strip, 190 in the wedge | fixes which quadruple dominates. Relaxing it upward is the only door on this list that could change the *answer* rather than the cost. |
| zero-side truncation | T = 430, 313 ordinates, 55 bisections, grid at 1/24 of the mean spacing | sets the 1e-8 agreement of the two routes. Raising T improves it like 1/T^2 at linear cost in the box counts, which is where that script spends most of its time. |
| background fit window | [n_max/2, n_max] | tested at [n_max/10, n_max/2] as well; the onset index does not move. |
| onset scan floor n_lo | n_max | not cosmetic. Scanning from n = 1 makes a three-parameter background fitted in the thousands return a negative value at n = 1 and the scan "finds" a sign change immediately. This is the same degeneracy `hunts/jensen_clock` recorded. |
| checkpoint block | 64 nodes | chosen so a killed sampling run loses at most about a minute. No trade found. |

### 3. The information class of each door

**Inside the family** (they change only how efficiently the same contour integral
is computed, and can never change the answer): dps, guard digits, the node rule,
the radius, the number of effective cores, and the evaluator implementation.
Together the model says they are worth about a factor of 5 to 10 in wall time,
which moves the reachable n_max from 5000 to somewhere between 10000 and 20000.
They cannot get anywhere near 328997: at that index the family needs about 1490
working digits and 670000 nodes, which the calibration puts at roughly 20000
core-hours. **The direct route does not reach the onset. That is the wall.**

**Requires reading more.** Three doors, and the follow-up hunt goes through the
first:

1. **Off-line zeros above height 190.** The dominance argument closes the window
   below 190 and the coefficient bound closes everything above it *for pair 1's
   growth rate*. But the whole answer rests on one measured number, log R for a
   single quadruple. A systematic off-line census at greater height would either
   leave pair 1 as the measured maximiser of (2 beta - 1)/((1-beta)^2 + gamma^2)
   or replace it, and replacing it is the only thing that moves 328997 by more
   than a per cent. This reads new zeros and is outside the configuration
   ceiling of the present family.
2. **A route to lambda_n that is not a contour integral of log F.** The n^3 cost
   is entirely the r^{-n} amplification. A method that computed the Taylor
   coefficients of log F(1/(1-z)) by recursion from the Dirichlet coefficients,
   or that summed the zero side with a rigorous tail at large n, would have a
   different exponent. The zero side already agrees to 1e-8 at n <= 12 and its
   error at large n is set by the S(t) oscillation, not by precision, so it is
   the more promising of the two.
3. **Enclosures.** Nothing here carries them. An interval version of the DFT
   plus an enclosure for the winding number would move the positivity statement
   for n <= 5000 up a rung. `zeta.rigor` has both backends live on this machine
   and the contour is entire and zero-free by a measured argument, so the
   obstacle is engineering rather than mathematics.
