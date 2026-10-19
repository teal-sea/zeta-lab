# jensen_wedge: independent review of the phase 1 derivations

**Nothing here bears on RH.** This file reviews `RESULTS.md` sections 11 and 12 of
hunt #135 as merged on `main` at `d0ce271b` (PR #308). The reviewer is a separate
session that did not write them, started from a blank context, read Holland's PDF
itself, and reproduced every numerical claim it checks with its own code
(`review/wedge_review.py`), which does not import `probe.py` or `probe_phase1.py`.
The brief was to find where the derivations break, not to confirm them.

## Verdict, step by step

| step | verdict | the one-line reason |
| --- | --- | --- |
| 11.1 leading-order reduction | **holds** | every identity rederived; Holland's four constants recovered; the k = 5, 6 derivative constants it assumes (not in Holland) measured to 1/L, see R1 |
| 11.3 the [2/2] Pade point in Holland's family | **holds** | Pade algebra rederived; every table entry reproduced on an independent route; the "measured, not derived" reflection symmetry is a consequence of Pade uniqueness (R6) |
| 11.5 restricted-class obstruction | **holds** | the Cauchy-Schwarz contradiction is exact; the compactness step needs one tightening (R7); the mesoscopic configurations reproduce, with a sharper description (R7) |
| 12.1 Proposition 2.2 for m points | **holds** | a one-line change to Holland's proof, checked line by line against the PDF |
| 12.2 Lemma A | **holds** | proof checked; bound holds with positive slack on adversarial root sets, including a 1e-6 near-collision |
| 12.3 Lemma B | **holds** | constants rederived (2.47 = 32/13 rounded up, 6.07); at the edge of its hypotheses the true gap is 1.55 to 1.98 times the bound; its hypothesis A >= 8B is load-bearing (R4) |
| 12.3 Lemma C and the combination | **holds, with two unstated hypotheses** | MFMP Proposition 2.17 says exactly what is cited; the combination needs Holland's (77) for (C, D) and D > 64d (R2), both automatic once H1 holds |
| 12.4 sixth-order residual | **holds, conditional on H1 and H3** | the decomposition and the L^1 bound are right; gap total times L reproduces and rises to 1.86 at n = 1e7 |
| 12.5 the chain | **holds as a conditional derivation; its list of open inputs is incomplete** | H1's proof needs the leading constant of h^(5), which Holland does not state and which is neither H1 nor H3 as written (R1); one wording error about A (R3) |

**Overall: no step is broken.** No counterexample was found to any lemma, no constant
is wrong, and every reproduced number agrees with phase 1. The conditional wedge
`n^4 log^2(n+2) >= K d^6 log^12(d+2)` follows from sections 11 and 12 **given H1,
H3 and the extra input R1**, and the exponent comparison (2/3 against Holland's 3/5)
is stated correctly. It remains a conditional derivation, not a theorem: H1 is
unproved, H3 and R1 are routine but unwritten, and this is one internal review, not
an external one. The weakest link is H1, so the composite claim takes H1's status.

## What was read, and how the numbers were reproduced

- **Holland**, arXiv:2608.08682v1, downloaded as PDF on 2026-10-19 (SHA-256
  `3fc31ba84fb113bc0b3109fb0e569bd1d7183018485aca1eb1dab565c839b49d`, identical to
  the file phase 1 recorded), extracted with `pdftotext -layout` into a scratch
  directory outside the tree and read as data: Proposition 2.2 and its proof,
  section 4 (eqs. (14) to (29)), Lemmas 4.3 and 5.1 to 6.2, section 7 (eqs. (74) to
  (80)), Lemmas 8.1 and 9.1, sections 10 and 12.
- **Martinez-Finkelshtein, Morales, Perales**, arXiv:2309.10970v3 (SHA-256
  `23f228e0682430c1ae6285be4abed4d730e9a08accad6c3f540fbdf4eb5bb4a3`), Propositions
  2.7, 2.11 and 2.17, read the same way.
- **The target sequence, by a route the hunt did not use.** gamma(n) is
  const * n! M_n/(2n)! (Holland eq. (10)) with M_x the Mellin moment of Riemann's kernel
  phi(u) = sum_k (2 pi^2 k^4 e^(9u/2) - 3 pi k^2 e^(5u/2)) exp(-pi k^2 e^(2u)),
  integrated by 48 Gauss-Legendre panels of 40 nodes across +-50 saddle widths. Phase
  1's route A integrates u^(2k) e^(u/4) omega(e^u) by a trapezoid rule and route B is a
  saddle expansion; this route shares no integrand, rule or node with either. Against
  `zeta.li.xi_taylor_coefficients` (dps 50) the ratios gamma(n+1)/gamma(n), n = 20..31,
  agree to 1.5e-51, and a planted 1e-30 error in one log gamma is seen (test). The
  integrand at the panel ends is below 4e-376 of its peak at every n used.
- **Solvers.** Newton in the logs of (A, B, C, D) with an analytic Jacobian, started
  from the leading-order [2/2] Pade configuration, recovers a planted two-factor model
  to 1e-40 and a planted sixth-order defect of either sign (test).

Reproduce:

```bash
.venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/review     # 30 tests, about 15 s
.venv/bin/python hunts/jensen_wedge/review/wedge_review.py       # about 100 s, rewrites review/results_review.json
```

Compute: everything above ran locally in under two minutes per script (one log gamma
window costs about 0.6 s); nothing heavy was run, so no `RUNS.md` manifest is owed
by this review, and that file was not touched.

## 11.1 The leading-order reduction: holds

**Checked.** (i) The derivative formula: from Holland (14),
log gamma(n+z) = h(n+z) - log Gamma(b+z) + linear, so E^(k) is as written, and it
agrees with Holland's (46) and (83) at k = 4, 5. (ii) The bracket: with
psi^(k-1)(p) = (-1)^k (k-2)!/p^(k-1) (1 + O(k/p)) and h^(k) as stated, the bracket is
beta_(k-1) + O(1/L^2) + O(1/n). (iii) E(m) = E^(m)(xi): when E vanishes at 0..m-1,
E(m) is the m-th forward difference, which equals E^(m)(xi) by the mean-value form
of divided differences. (iv) The moment and Pade rewritings, term by term,
including (1 - z)^(eps - 1) = int dlambda(x)/(1 - xz) with lambda = Beta(1 - eps, eps)
(moments (1 - eps)_k/k!). (v) The sign-change count. (vi) Holland's constants: one
interval gives D_n ~ 2/(n^2 L); two give alpha = beta = eps/2, A_J ~ nL,
B_J ~ n(1 + 1/L), E_J(4) ~ -2/(n^3 L), all as in his (30), (41), (42), (48). The
11.2 first-order family was rederived in exact fractions at omega = 3/2, 2, 5, and
at omega = 2 gives (6/5, 1/3, 1/24) (test).

**R1, the one input Holland does not supply.** 11.1 takes
h^(k)(x) = (-1)^k (k-2)! (2/L)/x^(k-1) (1 + O(1/L)) for k = 5 and 6 from "(28)
differentiated beyond". Holland states the constant only through k = 4; for k = 5
his (25) and (29) are O-bounds. An asymptotic relation on the real axis cannot be
differentiated in general. Here it can, because h is analytic on a sector and the
relative O(1/L) error of h'' holds on that sector (G_0 is explicit, R obeys (19)), so
Cauchy's inequality carries it to every fixed k. That argument is routine and
unwritten. Measured from k-th differences of log M_x on this route (Delta^k h(n) is
h^(k)(n + k/2) up to a relative O(k/x^2)), the ratio rho_k of h^(k) to the stated leading term:

| n | rho_2 | rho_3 | rho_4 | rho_5 | rho_6 |
| --- | --- | --- | --- | --- | --- |
| 50 | 0.680 | 0.798 | 0.869 | 0.920 | 0.962 |
| 3200 | 0.853 | 0.958 | 1.022 | 1.069 | 1.108 |
| 1e4 | 0.872 | 0.968 | 1.027 | 1.069 | 1.104 |
| 1e6 | 0.916 | 0.987 | 1.027 | 1.056 | 1.078 |

(rho_k - 1) L stays between -0.92 and 0.86 at every entry: consistent with a 1/L
approach for every k, including the two Holland does not state. Measured, not
proved. This matters for 11.2's and 11.4's leading constants and for H1 (see 12.5);
the chain's stability step needs only O-bounds.

## 11.3 The [2/2] Pade point inside Holland's family: holds

**Checked.** The [2/2] approximant was computed from its Hankel system at
eps = 0.9, 0.5, 0.342, 0.1, 0.01, 1e-4, 1e-8. At each: 0 < a1 < b1 < a2 < b2 < 1,
beta_1..beta_4 vanish to 1e-45, beta_5 < 0, and beta_5/eps -> -1/24 (Simpson's error
on t^4); the gaps tend to eps/6, 2eps/3, eps/6 (Lobatto). Interlacing is classical for
Stieltjes functions: [2/2] f = f(0) + z [1/2] g with g the Stieltjes transform of
x dlambda(x), so the poles are its two Gauss nodes in (0, 1), and the zeros
interlace them (one in each gap between poles, one below the first).

**On the finite-n system, every reproduced number agrees** (independent route,
residuals below 1e-59):

| n | D/B_J here | RESULTS | A/(nL) | (B - C) L/n | rho_CD | gap total x L | n^5 L E_S(6) here | RESULTS |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 50 | 0.7940523418 | 0.794052342 | 7.392 | 3.629 | 0.2441 | 1.366 | -0.2577 | -0.258 |
| 200 | 0.840604629899 | 0.840604630 | 5.546 | 3.755 | 0.2866 | 1.539 | -0.6141 | -0.614 |
| 800 | 0.8730934562 | 0.873093456 | 4.763 | 3.914 | 0.3221 | 1.641 | -0.9070 | -0.907 |
| 3200 | 0.895770429343 | 0.895770429 | 4.343 | 4.065 | 0.3496 | 1.706 | -1.1125 | -1.112 |
| 1e4 | 0.909546900033 | 0.909546900 (route B) | 4.122 | 4.173 | 0.3673 | 1.744 | -1.2350 | -1.235 |

D/B_J at n = 100 is 0.819287720988 here, against phase 0's bisected crossing 0.81929
and section 10's 0.81928772: the identification of phase 0's crossing with the Pade
point reproduces. Holland's theta = 1/2 family gives n^4 L E_F(5) = -0.6978 (n = 50)
and -4.207 (n = 3200), as section 4 reports. **Sign scan:** E_S(6) < 0, every
parameter positive and 0 < w_A < w_B < w_C < w_D < 1 at all 127 values n = 50, 75, ..,
3200 and at n = 1e4, 1e5, 1e6, 1e7, where n^5 L E_S(6) = -1.235, -1.406, -1.517,
-1.594, still approaching -2 (`review/results_review.json`). This is a second route
agreeing with phase 1's routes A and B at those points; whether that earns them the
hardened grade is the owner's call, not this review's.

**R6 (an upgrade, not a defect).** 11.3 calls a1 + b2 = b1 + a2 = 1 "measured and
not derived". It is derived: the matching conditions are int t^j (mu - tau) dt = 0,
j = 0..3, with tau = (1 - eps) 1_[0,1]. The reflection t -> 1 - t fixes tau and maps
polynomials of degree 3 to polynomials of degree 3, so the reflected configuration
(zeros 1 - b2, 1 - b1; poles 1 - a2, 1 - a1) solves the same problem; the [2/2]
approximant of a Stieltjes function is unique, so the two coincide, and the ordering
forces a1 = 1 - b2, a2 = 1 - b1. It holds for every eps in the leading-order model
(measured: defect below 1e-40 at all seven eps; pinned by a test).

**What 11.3 does and does not need.** The identification is "D-fixed family at
theta_star equals the four-parameter solution", which is a tautology once both are
solved; the substance is that the solution reached from the Pade guess is the one
Holland's family reaches from theta = 1/2, and that reproduces. "Inside Holland's
family" means the parametric form F_j only: the point is far outside his eq. (57)
window and outside Lemma 9.1, as 11.3 itself says.

## 11.5 Near-identity factors: obstruction holds; mesoscopic part reproduces

**The obstruction.** The first-order equations are rederived exactly as written.
With m_k = b - 1/(k+1): m_1 >= 0 needs b >= 1/2 and m_2^2 <= m_1 m_3 is
(b - 1/2)(b - 1/4) - (b - 1/3)^2 = (1/6 - b)/12 >= 0, so b <= 1/6; contradiction. A
non-negative least-squares check over 400 nodes omega in (0, 10] and b in [-2, 2] finds
no solution (residual above 1e-3), and dropping the sign constraint recovers the hole
b = 1/6, omega = 1/2, g = -2/3 exactly (tests).

**R7, the compactness step, tightened.** "A sequence of exact solutions with bounded
scaled parameters converges to a first-order solution": the limit has g_j >= 0, not
g_j > 0, which still contradicts (all g_j = 0 gives b = 1/2 = 1/3). If the number of
auxiliary factors may grow with n, "bounded scaled parameters" must mean bounded
total mass sum g_j, and the limit is a positive measure on a compact set of omega;
the same two inequalities apply. With both stated the obstruction is sound for its
class. The class excludes omega_j -> 0 or infinity and deviations larger than
order 1/L, as the text says.

**Mesoscopic configurations (leading-order model).** An independent continuous
optimisation (SLSQP, 400 starts, minimising the larger auxiliary relative gap X
subject to the four moment equations) finds X = 0.1717, 0.1809, 0.1437, 0.1073,
0.0749, 0.0531 at eps = 0.342, 0.1, 0.03, 0.01, 0.003, 0.001, each just below the
grid upper bounds in 11.5 (0.173, 0.182, 0.145, 0.109, 0.077, 0.055), and the same
eps^0.30 fall. Two descriptive additions: at every optimum the two auxiliary factors
**coincide** (one auxiliary Jacobi factor convolved with itself), and the main
factor's right end sits at w = 0.42 (eps = 0.342), 0.79 (eps = 0.01) and 0.90
(eps = 0.001), so the main factor is far from Holland's (w = 1 - eps/2). These configurations are not
perturbations of Holland's construction in any factor. Existence at finite n is
still unexamined, as 11.5 says.

## 12.1 Proposition 2.2 for m points: holds

Read against the PDF: Holland's proof uses the five vanishing conditions only to
start the sum (8) at k = 5. (9) needs only c holomorphic on Omega_r and k <= d, and
the bound sum_{k=m}^d 2^(-k) < 2^(1-m) gives eps < 2^(m-1); the sign alternation at
0, the d - 1 critical points and infinity is unchanged. Planted check: p with ten
random positive roots, c(z) = 1 + kappa z(z-1)...(z-5) with kappa set so that
sup over Omega_r of |c - 1| = 31 (outside Holland's eps < 16, inside 2.2_6's
eps < 32), r the exact need of (6): |P/p - 1| at every critical point is below 31/32
and the exact Sturm count (`zeta.li.is_hyperbolic`, method sturm) gives 10 real roots
(test). The verdict "trivial" is right; "same radius" means Proposition 2.2's radius
is inherited from (6), which is all 12.1 claims.

## 12.2 Lemma A: holds

Both claims were checked line by line. |e_k(x)| <= e_k(|x|) <= (sum |x_j|)^k/k! is
Maclaurin's inequality for non-negative numbers. In the second claim, the other zeros
on each side contribute at most H_d/g, p'(y) = 0 gives 1/delta_1 <= 1/delta_2 + H_d/g
because the left-hand terms are positive, and the total is (4 + 3H_d)/g. On ten
adversarial sets in the exploratory run (five are pinned in tests) (30 equally spaced roots, a geometric progression, a planted
collision at distance 1e-6, two far clusters, Chebyshev nodes, five random sets) the
need max_k |T_k|^(1/k), Lemma A's y sum 1/|y - y_j| and the explicit
y(4 + 3H_d)/g are ordered at every critical point with positive slack (smallest absolute
slack: the two-cluster set, 0.77). T_k is checked against direct differentiation, with a planted
wrong point that the check catches (tests).

## 12.3 Lemmas B and C and their combination

**Lemma B: holds.** The operator J, the Liouville form, and the bounds on
[B/2, 3B/2] rederive: 1 - y/A >= 13/16 from A >= 8B; |P| <= B/2 + 3(d - 1)/16 <= 0.501B
from B >= 256d; Q <= 32d/(13B) + (0.501 + 1.5)B/(2 (13B/32)^2) = (2.4615d + 6.062)/B,
so 2.47 and 6.07 are correct roundings up. The localisation uses Holland's (79), whose
derivation does not need his (57) (checked: it needs only U >= V + d, V >= 32d).
Exact rational tests at the edge of the hypotheses, A = 8B and B = 256d, d = 2 to 16:
all roots real, inside [B/2, 3B/2] and inside B +- 8 sqrt(Bd), and the smallest gap is
1.98 (d = 2) down to 1.55 (d = 16) times the bound.

**R4 (a pin, not a defect): A >= 8B is load-bearing.** With A = B + d and B = 32d
(Holland's (77) holds, A >= 8B does not), the smallest gap is 0.159, 0.074 and 0.036
times the Sturm bound at d = 4, 8, 16. For the Pade model A/B tends to 1.5 L, so the
hypothesis holds only from some n_0: measured A/B = 5.88 at n = 50, 7.36 at 200, 8.003
at 346 (first n with A/B >= 8 in a bisection between 200 and 800), 10.79 at 3200,
21.7 at 1e7.

**Lemma C: holds as cited.** MFMP Proposition 2.17 (v3, attributed to Katkova,
Shapiro and Vishnyakova) reads: for p, q in P(R>0), lmesh(p box q) >= lmesh(p).
Holland's convolution is the reciprocal form, and lmesh is invariant under
reciprocation. Random check: rational positive-root pairs of degree 2 to 8 in Holland's
convention (about 200 in the exploratory run, up to 60 in the test);
lmesh(p box q)/max(lmesh p, lmesh q) >= 1 in every case, minimum 1.001.

**The combination: holds, with two hypotheses it does not state (R2).** The step
"zeros of the normalised second factor in [1 - eta, 1 + eta], eta = 8 sqrt(d/D) by (79)"
needs Holland's (77) for (U, V) = (C, D), that is D >= 32d and C >= D + d, and the
gap bound (1 - eta) g_1/3 is useful only for eta < 1, that is D > 64d. Neither is
written in 12.3. Both follow once H1 gives D ~ n and C - D ~ n with d = o(n), so the
chain is not affected; they should be written down before the constants are made
explicit. The rest of the combination (zeros of p_F in [(B/2)(1 - eta), (3B/2)(1 + eta)]
by Lemma 7.1, smallest gap >= (B/2)(1 - eta)(lmesh(p_1) - 1) >= (1 - eta) g_1/3, and the
displayed r) rederives exactly.

**R5, how loose the explicit constants are**, at the route's own Pade parameters,
n = 3200 (B = 7540.4):

| d | gap x sqrt(d/B) | r needed | Lemma A | explicit (largest critical point) | 12.3's displayed r | actual gap / chain's lower bound |
| --- | --- | --- | --- | --- | --- | --- |
| 6 | 3.905 | 0.837 | 1.550 | 3.034 | 60.7 | 10.4 |
| 12 | 3.981 | 0.928 | 1.865 | 3.613 | 91.5 | 12.4 |
| 24 | 4.011 | 0.993 | 2.197 | 4.324 | 181.0 | 18.9 |

(radii in units of sqrt(Bd)). The first four columns reproduce 12.6 (its "explicit"
uses the largest zero rather than the largest critical point, hence 3.055 and 4.337
there). The displayed r of 12.3 is 72 to 182 times what (6) needs. Lemma A itself costs a
factor 1.9 to 2.2 over the need; using the minimum gap costs 2 more; the rest, a
factor of about 20, is the gap lower bound (the actual gap is 10 to 19 times
(1 - eta) g_1/3: the factor 3 of the lmesh transfer, the Sturm bound's 1.6 to 1.7,
and the crude eta = 8 sqrt(d/D), against the second factor's actual spread of 0.034
to 0.086) and the bound on y_max. The exponent does not care; phase 2's effective
constant will: a radius 182 times too large is a factor 182^6 in sup |E|, so about
182^12 in K, if left as is.
The multiplier sizes of 12.6 also reproduce: max_{j<=d} |c_j - 1| = 5.67e-19,
5.21e-16, 7.53e-14 (Pade, d = 6, 12, 24) and 4.11e-14, 5.40e-12, 2.87e-10 (Holland).

## 12.4 The sixth-order residual: holds, conditional on H1 and H3

**Checked.** psi^(5)(p + z) = 24/(p + z)^5 + O(p^(-6)) = f_z(n/p) + O(p^(-6)) for
|z| <= eta n; f_z(0) = 0 turns the five psi terms into
int f_z'(t)(mu - 1_[0, n/b]) dt; f_z'(w) = 120 w^4 n/(n + zw)^6, so
|f_z'| <= 1920/(n^5 (1 - 2 eta)^6) on 0 <= t <= 2. With disjoint intervals inside [0, 1]
(true at every n checked, see the sign scan) the L^1 distance is the total gap, which
measures 1.366/L at n = 50 rising to 1.858/L at n = 1e7, toward 2/L. Hermite-Genocchi
needs E holomorphic on the convex Omega containing 0..5, which holds once d + 2r = o(n).
The step needs H1 (parameters within O(1/L) of the Pade configuration, for the L^1
bound) and H3 (h^(6) on the complex neighbourhood), as stated. The bound is the same
mechanism as Holland's Lemma 8.1, where the pairs (B, b) and (C, D) are close; here
the close pairs are (D, b) and (B, C), and the L^1 form makes that pairing
unnecessary.

## 12.5 The chain: holds as a conditional derivation; open inputs incomplete

The chain was walked end to end: Lemma A to C give (6) with r = O(sqrt(Bd) log d);
12.4 gives sup |E| <= C (d + 2r)^6/(6! n^5 log n) = C d^3 log^6 d/(n^2 log n); at most 1/2
under n^4 log^2(n+2) >= K d^6 log^12(d+2); then |c - 1| <= 1 < 32 and Proposition 2.2_6
applies to the Pade model (simple positive zeros of p_F by MFMP 2.7(iii) and Lemma C,
p_F(0) = 1, c(d) > 0). Small n is absorbed into K as in Holland's section 10. The
delta against Holland's Theorem 1.1 (exponent 3/5 to 2/3, at the cost of log^12 d) and
the m = 5 cross-check (his wedge with a log^10 d loss) are both right.

**R1 again, as an omission from the list of open inputs.** H1's proof by Holland's
Lemma 6.1 contraction scales the four matching equations by nL, n^2 L, n^3 L, n^4 L.
The fourth component's target is a fifth difference of log gamma, so its limit
requires the leading constant of h^(5), -12/(x^4 L)(1 + O(1/L)), uniformly. Holland
supplies that constant only through h^(4) (his Lemma 5.4 is exactly the k = 4 case);
for h^(5) he has O-bounds. This input is neither H1 as described nor H3 (which is the
sixth derivative bound). It is routine (R1's Cauchy argument) and measured above
(rho_5 = 1.069 at n = 3200, 1.056 at 1e6), but it is a third unwritten input and
belongs in the list.

**R3, a wording error.** "Every parameter condition of 12.3 holds (all parameters are
of order n and d = o(n))": A is of order n log n, and A >= 8B holds because
A/B ~ 1.5 L grows, only from n of a few hundred (R4). The conclusion stands for
n >= n_0; the parenthesis is wrong for A.

**H1's limiting system.** Nonsingular in two coordinate systems: phase 1's quadrature
coordinates (determinant -1/24, its test) and this review's (a1 = eps x1,
b2 = 1 - eps x4, interior gap eps g centred at nu; determinant 1 at x1 = x4 = 1/6,
g = 2/3, nu = 1/2, test). Note that at first order the equations depend on b1 and a2
only through nu and g, so the contraction must use (nu, g), not (b1, a2) scaled
separately, or its limit is singular. Not a defect; a constraint on how H1 is written.

## Overall verdict on the conditional wedge

**The conditional wedge stands.** Every step listed holds; none is broken; no
counterexample was found to Lemmas A, B or C, Proposition 2.2_6, the reduction or the
obstruction. Its status after this review: a conditional derivation with three open
inputs, not two,

1. **H1** (matching at every large n within O(1/L) of the Pade configuration):
   unproved; measured here on a second route at 127 integers n in 50..3200 and at
   1e4..1e7;
2. **H3** (Proposition 4.1 at r = 6): routine, unwritten;
3. **R1** (leading constant of h^(5), needed by H1): routine, unwritten, measured;

plus two hypotheses of 12.3 to write down (R2) and one wording fix (R3). One
internal review, no external one; no novelty search was run by phase 1 or here.
Nothing in it bears on RH.

## What this review did not do

- It did not attempt H1, H3 or R1.
- It did not reproduce route B's values from 1e8 to 1e20 (this route stops at 1e7),
  section 10's theta map, or the d = 48, 96 rows of 12.6.
- It did not review 11.2, 11.4, 12.6 and 12.7 as steps, though their numbers
  reproduced wherever this code touched them.
- It edited no existing file. Files: this one, `review/wedge_review.py`,
  `review/test_wedge_review.py`, `review/results_review.json`.
