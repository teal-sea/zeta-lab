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

(to be filled as runs complete)
