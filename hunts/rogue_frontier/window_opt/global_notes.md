# global_notes: working checkpoint for the global-optimality study of F(v)

Session scratch log, updated incrementally. Nothing here is a result until it
reaches RESULTS.md section 9 with a grade. No em dashes; the reserved word of
`zeta/rigor.py` is not used in this directory.

## 0. Validation gate (done)

- `functional.py` battery: all validations pass (run 2026-08-17, this session).
- Exact rational reproduced: F(v*) = 2245228120295149280/3276332462159207451
  for v* = 1 - (1467/1000)s^2 + (1159/1000)s^4.
- TODO: independent mpmath evaluator must match to 25+ digits before any new
  number is trusted (gate inside global_landscape.py).

## 1. Reformulation used by the bound work (derivation notes)

With l1 = int v = 1 (scale invariance) and m_k the limiting spectral moments
of A = H/l1 (the source paper's framework, hardened closed forms in
functional.py):

    m0 = 1, m1 = 1, m2 = 1 + D2, m3 = 1 + 3 D2 + D3

so D2 = m2 - 2 m1 + m0 and D3 = m3 - 3 m2 + 3 m1 - m0 are the second and
third central moments of the spectral measure mu_v about 1:

    D2 = int (lam - 1)^2 dmu,   D3 = int (lam - 1)^3 dmu,
    F  = 2 m2 - m3 = 1 - int lam (lam - 1)^2 dmu.

Since A is PSD, mu_v lives on [0, inf), so lam (lam-1)^2 >= 0 and F <= 1
(per-N: E nu_N is a positive measure with these moments; Cauchy-Schwarz and
positivity hold at every N, then pass to the limit that defines m_k).

Cauchy-Schwarz (m2^2 <= m1 m3 for a positive measure on [0, inf)) gives

    F <= 2 m2 - m2^2 = 1 - D2^2        (pointwise in v)

and 1 - D2^2 is decreasing in D2 >= 0, so

    sup F <= 1 - (inf D2)^2.

D2 = <v, (I - T) v> / l1^2 with (T f)(xi) = int_B tri(xi - eta) f(eta) deta,
tri(t) = 1 - |t| on |t| <= 1, B = [-1/2, 1/2]. T is PSD (Fourier multiplier
sinc^2 >= 0), ||T||_HS^2 = tr T^2 = 1/2 exactly, so ||T|| <= 1/sqrt(2) < 1.

Lower bound for inf D2 via the quadratic dual: for any c,
    <v, (I-T) v> >= 2 c <1, v> - c^2 <1, (I-T)^{-1} 1>,
so with U >= <1, (I-T)^{-1} 1> = sum_k t_k, t_k := <1, T^k 1>:
    inf_{int v = 1} D2 >= 1/U.
t_k are exact rationals (T maps polynomials to polynomials, degree + 2).
Tail bound for even K: sum_{k >= K} t_k <= t_K / (1 - lam_max) and
lam_max <= 1/sqrt(2) <= 707107/1000000 (since 707107^2 >= 5*10^11).

Everything in the chain is exact rational. Status: derivation written, code
next (global_bound.py).

## 2. Landscape plan (global_landscape.py)

- EL system: g(s) = dF/dv(s) = 0 on supp v (quadratic integral equation;
  explicit form in functional.gradient_field). Critical point finders:
  (a) cosine spectral basis v = 1 + sum c_k cos(2 pi k s), solve the
      projected system P_k(c) = int g cos(2 pi k s) = 0 by least squares
      from many random starts; classify roots by positivity of v.
  (b) squared Chebyshev v = w^2: solve grad_a F = 0 (finds saddles too).
  (c) pw-linear cone KKT (Fischer-Burmeister residual) plus L-BFGS-B
      multistart with diverse inits including compact-support ones.
- Hessian eigenvalues at the optimum (expect: one zero mode from scaling,
  rest negative).
- Best-F-ever-seen tracker across all runs.

## 3. Slice plan (global_slice.py)

- Quartic slice 1 + q1 s^2 + q2 s^4: exact critical system via sympy
  resultants, count real critical points in the admissible region, exact
  algebraic slice supremum.
- Degree 6..10 slices: high-precision multistart (measured).

## Findings so far

### F1 (prototype, 2026-08-17): exact rational bound chain works

t_k = <1, T^k 1> computed exactly (t_1 = 2/3, t_2 = 9/20 match hand
derivation). Ratios t_{k+1}/t_k converge to lam_1(T) = 0.6755169434391893,
comfortably below the exact HS bound 1/sqrt(2) used only for the tail.
With K = 44: U = 3.0534416857, 1/U = 0.32749929520,
    sup F <= 1 - (1/U)^2 = 0.8927442116.
Every constant is an exact rational. Note inf D2 = 0.3274993 sits close to
D2(v*) = 0.3280521: the F-optimum is nearly the D2 minimizer.

### F2 (prototype): cosine spectral landscape, J = 6, 40 starts

All 40 least-squares runs on the projected EL system converged; 3 distinct
critical points: the known optimum (38 hits, v > 0, F = 0.685275 at this
truncation), and two sign-changing solutions outside the cone
(F = 0.5243, 0.4303). Unique interior critical point in this span.
Truncation note: the cosine basis converges slowly for this problem
(the optimum's periodic extension has endpoint derivative kinks), so the
restricted critical value sits below 0.68528703 at small J; J up to 12 in
the production run.

### F4 (2026-08-17, global_bound.py run complete): derived outer bound

Gate: T-machinery agrees with functional.py exactly (D2(v*) = m2 - 1 as an
identity of Fractions between two independent codes). Results:
- U = 3.053441685709720 exact rational (partial sum K = 44 plus tail
  bounded via lam_max <= 1/sqrt(2) <= 707107/1000000, tail <= 1.1e-7).
- inf D2 >= 1/U = 0.327499295198614; bracket from above by the explicit
  nonnegative Neumann window w_24: D2(w_24) = 0.327499296325274, so the
  bracket on inf-over-cone D2 has width 1.1e-9.
- sup F <= 1 - (1/U)^2 = 0.892744211644411 exact rational. Grade: derived
  chain (per-N Cauchy-Schwarz on the expected empirical spectral measure,
  plus the quadratic dual bound), on top of the hardened moment closed
  forms; all constants exact rationals.
- The 1 - D2^2 route is saturated: it cannot give better than 0.8927442109
  whatever the numerics, since inf D2 is pinned to 1e-9.
- Sanity (measured): (D2 + D3) - D2^2 >= 0.2069 at 60 random admissible
  windows; at v* the Cauchy-Schwarz step gives away 0.892 vs 0.685, i.e.
  the slack of this route is the m3 >= m2^2 inequality, not the numerics.

### F5 (2026-08-17, global_slice.py run complete): quartic slice EXACT

- Exactly ONE admissible interior critical point:
  q = (-1.46701866547, 1.15904242554),
  F4* = 0.685287023289616136327866177020 (isolated real algebraic number;
  q2 component is a root of 53574903041239 q2^4 - 7719414292779072 q2^3 -
  126958598530649600 q2^2 + 34764906650381107200 q2 -
  40111525465989120000, per the exact lex Groebner eliminant).
  Four other real critical branches, all inadmissible (v < 0 somewhere),
  with F = 0.4675, -1.396, -371.9, -41041.9.
- Boundary of A exact: family (a) endpoint-zero segment max 0.62175582 at
  its unique admissible critical point; corner (1-4s^2)^2 gives exactly
  610/3003; family (b) double-root curve entirely below -0.21.
- Arc at infinity exact: max -0.19549 (all negative).
- Hence sup over the quartic slice = F4*, attained at the unique interior
  critical point. Grade: derived (exact arithmetic; compactification
  argument as in the file docstring).
- Consistency: F(v*) = 0.685287023288068 (the rational witness) sits
  1.5e-12 below F4*, and F4* sits 8.887e-9 below the full-space measured
  sup 0.6852870321770, exactly as RESULTS.md section 5 predicted.
- Degree 6/8/10 slices (measured, 30 starts each): best F =
  0.6852870319222 / 0.6852870321770 / 0.6852870321769. The degree-8 slice
  already attains the claimed full sup to all 13 digits and nothing beat
  it. Higher slices show a flat near-optimal ridge (many endpoints within
  1e-6), consistent with a single basin plus soft directions.

### F6: the relaxation value is itself pinned (both sides)

The outer bound is the exact value of a relaxation: among positive measures
on [0, inf) with mean 1 and second central moment >= inf D2, the maximum of
int (2 lam^2 - lam^3) is exactly 1 - (inf D2)^2, attained by
mu = (d/(1+d)) delta_0 + (1/(1+d)) delta_{1+d}, d = inf D2 (the dual
polynomial lam (lam - (1+d))^2 >= 0 touches at both atoms). With the inf D2
bracket [1/U, D2(w_24)] this pins the relaxation value to
[0.8927442109, 0.8927442116]. So the derived bound cannot be improved by
computing harder; it can only be improved by adding facts the relaxation
does not know, i.e. by excluding near-two-point spectral measures for
actual windowed sine-Gram operators. That exclusion is genuine spectral
theory (the transition-layer behavior of band-limiting Gram operators) and
is the honestly-open part of the global question.

### F7: exact factor bookkeeping for the slice critical point

The admissible root q2 = 1.15904242554051 is a root of the quartic factor
53574903041239 q2^4 - 7719414292779072 q2^3 - 126958598530649600 q2^2
+ 34764906650381107200 q2 - 40111525465989120000 of the eliminant (the
cubic factor's single real root 67.389 is inadmissible). Exact separation
F4* - F(v*) = 1.5483e-12 > 0, and F4* < measured full sup by 8.887e-9.

### F8: exact rational witness on the degree-8 slice (sup lower bound)

v8(s) = 1 - (36773/25000) s^2 + (744/625) s^4 + (1341/25000) s^6
        - (3397/6250) s^8
is exactly admissible (Sturm: psi(u) = 1 + q1 u + ... has zero roots in
[0, 1/4], psi(1/4) = 141077/200000 > 0, so v > 0 on B) and achieves, in
exact rational arithmetic,

  F(v8) = 8273865220036096559249598473358/12073576226528772158039668492375
        = 0.685287032176620,

within 3.5e-13 of the measured sup 0.6852870321770. Together with F4:

  0.685287032176620 <= sup F <= 0.892744211644411,

both ends exact rationals: the lower end by an explicit admissible witness,
the upper end by the derived chain.

### F9: exact evaluation of the recorded Chebyshev witness

The best_window.json Chebyshev coefficients define w exactly (dyadic
rationals); v = w^2 is a degree-28 even polynomial, nonnegative by
construction. Exact rational evaluation:

  F = 0.6852870321769988738698323 (25 digits; exact fraction available)

so the two-sided bracket tightens to

  0.685287032176999 <= sup F <= 0.892744211644412  (both ends exact).

The lower end is 2.0e-12 below the float-measured sup 0.6852870321770008.

### F3 (prototype): quartic slice is exactly solvable

Symbolic F(q1, q2) rational of degree 3/3; sympy reproduces the exact
rational F(v*) from functional.py. Critical system Groebner basis: lex,
univariate element of degree 7 in q2 with 5 real roots:
q2 = -62.573, 1.1590424255405073, 67.389, 87.446, 118.055.
The second is the optimizer's basin. Admissibility of the others TBD in
global_slice.py; boundary families and directional limits at infinity to be
solved exactly (plan in section 3 above, expanded):
- admissible region A in (q1,q2): psi(u) = 1 + q1 u + q2 u^2 >= 0 on
  [0, 1/4]; cells C1 {q1 >= 0}, C2 {q1 <= 0 <= q2, q2 <= -2q1} (min at
  endpoint u = 1/4, contains the optimum, compact), C3 {q2 > 0, q1 < 0,
  q2 >= -2 q1, disc <= 0}, C4 {q2 <= 0}, all intersected with
  L = 16 + 4 q1 + q2 >= 0.
- recession cone of A: {alpha >= 0, alpha + beta/4 >= 0}; the denominator
  leading form alpha/12 + beta/80 is strictly positive there except at 0,
  so F extends continuously to the arc at infinity with limit
  F_inf(direction) = ratio of leading forms = F of the limit window
  h = alpha s^2 + beta s^4. Slice sup = max over finite exact list:
  interior critical values, boundary-family univariate critical values,
  arc-at-infinity univariate max.
