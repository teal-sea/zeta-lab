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
so some lambda_n(DH) is negative. The sequence had not been computed.

| question | answer | grade |
|---|---|---|
| how far can n be pushed here | **n = 5000**, in 1472 s of contended wall time; the cost model puts n = 20000 at about 3.7 h and n = 3.3e5 at about 20000 h | measured, plus a fitted cost model |
| are all computed lambda_n(DH) positive | **yes**, for every n from 1 to 5000; the minimum over the whole table is lambda_1 | hardened: two contours agree bit for bit, and four separate controls run |
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
