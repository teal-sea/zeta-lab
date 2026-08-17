# window_opt: optimizing the window in the 7.5(g) distinct-zeros count

Exploratory study under `hunts/rogue_frontier/`. Per `hunts/README.md`,
nothing here is a promoted result; every number below carries its rung on the
repo's certainty ladder, stated inline and collected in section 8.

**Subject.** The 10 Aug 2026 preprint "More than two thirds of the zeros of
the Riemann zeta function lie on the critical line" (single author, not peer
reviewed) proves in its section 7.5(g), under RH, the distinct-zeros bound

    Nd(T)/N(T) >= 1/2 + (2 m2 - m3)/18 + (4/9)(19/27) = 0.85082...

where m_k = m_k(1, v) are spectral moments of the windowed sine-kernel Gram
matrix over the sine process, and the window is v(s) = cos(8s/5) on
[-1/2, 1/2], for which the paper prints 2 m2 - m3 = 0.68524... The weight
psi(m) is LP-optimal, but the window is a hand-picked guess. Any gain delta
in F(v) := 2 m2 - m3 over an admissible window lifts the constant by
delta/18. This study re-derives m2 and m3 as functionals of v, validates the
derivation two independent ways, tests whether cos(8s/5) is optimal, and
optimizes the window.

**Headline.** cos(8s/5) is not a critical point of F. The optimum over even
v >= 0 is an interior critical point with

    sup F = 0.6852870321770        (measured; three parametrizations agree)

versus 0.685243875537318 for the paper's window: a gain of 4.316e-5. The
clean rational window

    v*(s) = 1 - (1467/1000) s^2 + (1159/1000) s^4

achieves, in exact rational arithmetic,

    F(v*) = 2245228120295149280/3276332462159207451 = 0.685287023288068,

within 8.9e-9 of the measured sup, and the RH-conditional constant becomes

    1/2 + F(v*)/18 + (4/9)(19/27)
        = 50176758585216887915/58973984318865734118
        = 0.850828702939872  (15 digits; exact rational)

against the paper's 0.850826305842608, a lift of 2.3971e-6 (enclosure-checked
in both ball backends; see `enclose.py` output). The improvement is real but
small: it moves the sixth decimal of the proportion.

## 1. Setup and derivation

Points x_j are the unit-density sine process, S(x) = sin(pi x)/(pi x),
with determinantal correlations rho_2 = 1 - S^2 and
rho_3 = 1 - S12^2 - S13^2 - S23^2 + 2 S12 S13 S23. The windowed Gram kernel
is H_{jj'} = K_v(x_j - x_{j'}), K_v(x) = int_{-1/2}^{1/2} v(xi) e^{2 pi i x
xi} d xi, and m_k(1, v) = lim E tr H^k / (N l1^k) with l1 = K_v(0) = int v.

Expanding E tr H^k over coincidence patterns of the index tuple and moving
every distinct-point integral to the Fourier side (Parseval; the transform of
the product S K_v is the convolution 1_B * v with B = [-1/2, 1/2]):

    E tr H^2 / N = l1^2 + [int v^2 - int W^2],          W := 1_B * v,
    E tr H^3 / N = l1^3 + 3 l1 [int v^2 - int W^2]
                   + [int v^3 - 3 int (tri*v) v^2 + 2 int W^3],

tri := 1_B * 1_B. The three rho_3 pieces map as: the constant term gives
int v^3; the three -S^2 terms each give -int (tri*v) v^2 (equivalently
-int (1_B*v)(1_B*v^2)); the +2 S12 S13 S23 term gives +2 int W^3. Hence with

    D2 := (int v^2 - int W^2)/l1^2,
    D3 := (int v^3 - 3 int (tri*v) v^2 + 2 int W^3)/l1^3,

    m2 = 1 + D2,    m3 = 1 + 3 D2 + D3,    F = 2 m2 - m3 = 1 - D2 - D3.

The m2 formula agrees with the coordinator's sketch; the m3 formula is the
new derivation. Both are validated below. Everything reduces to the
antiderivatives V0(x) = int_0^x v and P0(x) = int_0^x t v(t) dt through

    W(eta) = V0(1/2) + V0(1/2 - eta)                (0 <= eta <= 1),
    (tri*v)(s) = l1 - [2 s V0(s) - 2 P0(s) + 2 P0(1/2)]   (|s| <= 1/2),

so for polynomial v every quantity is an exact rational.

Per-term anchor at v = 1: int v^2 = 1, int W^2 = int tri^2 = 2/3,
int v^3 = 1, int (tri*v) v^2 = 2/3, int W^3 = 1/2, giving D2 = 1/3, D3 = 0,
m2 = 4/3, m3 = 2: exactly the published sine-Gram moments m_k(1) = 1, 4/3,
2, 13/4 quoted in the paper's section 7.5(f).

## 2. Validation evidence

Four mutually independent routes agree (`functional.py` battery, all pass):

1. **Float engine** (vectorized Gauss-Legendre, exact for polynomial v up to
   rounding): cos(8s/5) gives m2 = 1.328018448999629, m3 = 1.970793022461940,
   F = 0.685243875537319. **All printed digits of the paper's 0.68524...
   are reproduced.**
2. **Symbolic closed forms** (sympy, antiderivative identities verified by
   differentiation): F(cos(8s/5)) =
   (878 cos(16/5) - 450 sin(8/5) - 495 sin(16/5) - 2960 cos(8/5) + 2082)
   / (1200 (cos(8/5) - 1)^2) = 0.685243875537318196018420884208 (30 digits),
   m2 = 1.32801844899962925344205522171,
   m3 = 1.97079302246194031086568955921.
3. **Exact rational route** (Fraction polynomial arithmetic, no sympy) equals
   the sympy route exactly on the rational window, and the float engine
   matches both to < 1e-14.
4. **Windowed circular model, exact finite-N CUE** (`crosscheck_finiteN.py`):
   using the exact joint trace moments E prod Tr U^{h_j} from
   `../sine_gram/exact_finite_N.py` (read-only import), the windowed lattice
   sum E tr H^k = N^{-k} sum prod v(m_i/N) E prod Tr U^{h_j} at
   N = 21, 25, 29, 33, 37, 41, extrapolated in 1/N (degree-4 fit):

   | window | m2 extrap | m2 closed | diff | m3 extrap | m3 closed | diff |
   |---|---|---|---|---|---|---|
   | cos(8s/5) | 1.3280184490 | 1.3280184490 | -4.4e-11 | 1.9707930221 | 1.9707930225 | -3.8e-10 |
   | rational v* | 1.3280521177 | 1.3280521180 | -2.6e-10 | 1.9708172125 | 1.9708172127 | -1.6e-10 |

   This model shares no step with the continuum derivation (no rho_3, no
   Parseval, no quadrature: integer lattice counts), so the agreement at two
   different windows is a genuine cross-check of the m3 formula, including
   its boundary structure at band lambda = 1.

Grade of the closed forms after this: **hardened** (independent routes
agree). Had 0.68524 failed to reproduce, the protocol was to stop and
report; it did not fail.

## 3. Euler-Lagrange test at cos(8s/5)

F is scale invariant (degree-0 homogeneous), so at a critical point over
{v >= 0} the first-variation field g(s) = delta F / delta v(s) vanishes on
the support of v, with no multiplier (the Euler identity int g v = 0 holds
identically; the engine reproduces it to 4e-15, and g was verified against
finite differences in four directions to 7 digits).

At v = cos(8s/5): **max|g| = 5.64e-2, ||g||_2 = 2.01e-2.** The residual is
structured (positive at s = 0, negative near s = 0.35, positive at the
endpoint), so cos(8s/5) is **not** a critical point of F. For contrast the
optimizer's window has max|g| = 3.1e-9.

Within its own one-parameter family v = cos(c s): dF/dc at c = 8/5 equals
+1.4892581773e-4 (exact symbolic derivative), so 8/5 is not even
family-critical, but it is close: the family optimum is c* =
1.602374198452608 with F(c*) = 0.685244052480639, only 1.77e-7 above c = 8/5.
The paper's guess was an excellent cosine but the cosine family itself is the
binding restriction: the full-space gain is 244 times the in-family gain.

## 4. Optimization outcome

Three parametrizations, `optimize.py`:

- **(a) Squared Chebyshev** (v = w^2, w an even Chebyshev series, positivity
  free): BFGS with the analytic gradient, 13 starts (projection of the paper
  window + 12 random). **All 13 converge to the same point**,
  F = 0.685287032177, stable under basis growth J = 4..12 to 12 digits
  (J = 4: ...31978; J >= 6: ...32177).
- **(b) Piecewise-linear v >= 0** on 41 knots with an exact lattice-aligned
  evaluator: L-BFGS-B, 8 starts, all converge to F = 0.685287031812,
  which is the same optimum up to the pw-linear representation bias (~4e-10).
  Cautionary note recorded: against the smooth-panel float quadrature
  instead of the exact evaluator, the optimizer "found" F = 0.685777 by
  exploiting kink quadrature error; the exact evaluator shows that window is
  actually worse than cos (F = 0.684814). Optimizing against a quadrature is
  only safe when the quadrature is exact for the search space.
- **(c) Cosine family and low-degree even polynomials**: quartic
  1 + q1 s^2 + q2 s^4 reaches F = 0.685287023290 at
  q = (-1.46701891, 1.15904325); adding s^6 reaches 0.685287031922.

The optimum is an interior critical point of the cone {v >= 0}: strictly
positive (v(1/2)/v(0) = 0.70539), strictly decreasing in |s|, even, and
smooth; the positivity constraint is inactive. Normalized profile:

    s        0      0.1      0.2      0.3      0.4      0.5
    v*/v0    1   0.98541  0.94307  0.87726  0.79499  0.70539
    cos ref  1   0.98723  0.94924  0.88699  0.80210  0.69671

**sup F = 0.6852870321770** (measured; single basin found by every start in
every parametrization; no claim beyond the searched classes).

## 5. The rational window and exact arithmetic

Rounding the quartic to q1 = -1467/1000, q2 = 1159/1000 costs 8.9e-9 of F.
For v*(s) = 1 - (1467/1000) s^2 + (1159/1000) s^4, exact rational arithmetic
(Fraction route, confirmed by sympy exactly, cross-checked at finite N):

    m2 = 95695869320/72057314637            = 1.328052117985286
    m3 = 6457052410893815440/3276332462159207451 = 1.970817212682504
    F  = 2245228120295149280/3276332462159207451 = 0.685287023288068

Exact admissibility facts (rational arithmetic, `enclose.py`):
2 q1 + q2 = -71/40 < 0, so v' = s(2 q1 + 4 q2 s^2) < 0 on (0, 1/2]: v is
strictly decreasing in |s|; v(1/2) = 11291/16000 > 0: v is strictly positive;
v is even with sup v = v(0) = 1; phi = sqrt(v) is smooth on the closed
interval since v >= 11291/16000.

Strict improvement, enclosure-checked in both ball backends (Arb prec 200
and mpmath.iv dps 60, which agree and contain the 30-digit references):

    F(v*) - F(cos(8s/5)) = 4.3147750749594648584e-5   (ball, both backends)

## 6. The new constant

Keeping the paper's LP-optimal weight psi(m) = m/2 + m^2/9 - m^3/18 +
(4/9) 1_{m=1} (re-derived: the vertex is pinned by psi(1) = psi(2) = psi(3)
= 1 plus the boundary admissibility beta = -2 gamma, so it does not depend
on the window; an LP re-solve at the new (m2, m3) returns the same vertex),
and the BHB simple-zeros input 19/27 unchanged:

    Nd/N >= 1/2 + F(v*)/18 + (4/9)(19/27)
          = 50176758585216887915/58973984318865734118
          = 0.850828702939872078905...        (exact rational)

versus the paper's 0.850826305842608212536... The lift is

    delta = 2.3970972638663694e-6              (ball, both backends).

At the measured sup the constant would be 0.8508287034337 (measured grade
only). Both round to 0.85083 at five decimals, as does the paper's value at
its sixth digit: the honest statement is that the headline "more than two
thirds" and even "0.8508..." are untouched; the sixth decimal moves.

## 7. Admissibility analysis (task 4)

What the paper's proof imposes on the window, with sources (line numbers
refer to the OCR text of the preprint; quotes reassembled where the OCR
interleaves display math):

1. **The window class, section 7.1** (lines 3191-3196): "Nothing in Sections
   4-5 used that phi is flat-topped, only: phi in C^2_c, even, 0 <= phi <= 1,
   supp phi = [-L/2, L/2], phi nonincreasing in |u| (so ||phi'||_1 <= 2,
   ||(phi^2)'||_1 <= 2), and ||phi''||_1, ||(phi^2)''||_1 << 1." With
   "phi^2(u) = v(u/L)", the window v must be: **even**, **nonnegative**
   (structural: v = phi^2, and H must be PSD for the majorisation step),
   **bounded** (0 <= v <= 1, WLOG by scale invariance of F),
   **nonincreasing in |s|** (used only to bound the variation norms), with
   sqrt(v) of class C^2 and controlled second-derivative norms.
2. **Endpoint vanishing is glossed by the paper itself.** A strict reading
   of phi in C^2_c with supp phi = [-L/2, L/2] forces phi(+-L/2) = 0, i.e.
   v(+-1/2) = 0. But both of the paper's own windows violate this:
   section 7.1's maximiser "v*_lambda(s) = cos(sqrt(2) lambda s) > 0
   (|s| <= 1/2)" (line ~3230, stated as attaining "c*_lambda := sup_{v>=0}
   c_lambda(v)"), and 7.5(g)'s "v(s) = cos(8s/5) 1_{|s|<=1/2}" with
   v(+-1/2) = cos(4/5) = 0.6967 > 0. Remark 4.3 (sharp cutoff: "some
   tapering is necessary") shows some smoothing at the edge is genuinely
   needed. The implicit repair is standard: taper over a width delta L
   (then ||phi''||_1 = O(1/(delta L)) -> 0 for fixed delta as L grows, so
   the class conditions hold), and let delta -> 0 after T -> infinity; F is
   continuous in the taper. Measured here (C^2 ramp, exact pw evaluator):

       delta:   0.04       0.02       0.01       0.005
       F*-F:    2.47e-2    1.20e-2    5.91e-3    2.93e-3    (slope ~0.59)

   The loss is O(delta), so sup over the strictly admissible subclass equals
   the endpoint value; the bound survives in the lim inf form the theorem
   already carries. **Our window needs exactly this argument and no more;
   it inherits the same status as the paper's own windows.**
3. **The band endpoint lambda = 1 and the triple-correlation input.**
   7.5(g) (line ~3819): "Under the Riemann hypothesis, the third trace
   tr G^3 (equivalently, the triple correlation of zeros in the band
   lambda < 1) is available as a theorem [Hej94, RS96]". The k = 3 test
   function built from v on [-lambda/2, lambda/2] has Fourier support of
   total spread <= 2 lambda, and the Hejhal / Rudnick-Sarnak theorems (under
   RH) cover the open range < 2, i.e. **lambda < 1 strictly**; at lambda = 1
   the support touches the boundary (a null set, since v(+-1/2) != 0 puts
   mass at the edge of the closed band). The certificate is evaluated at
   m_k(1, v), i.e. at lambda = 1. Remark 6.1 states endpoint admissibility
   only for the Theorem 5.8 machinery ("A reader who prefers to keep a power
   saving everywhere may take lambda < 1 fixed and let lambda -> 1-; the
   limits ... are unaffected"); for the third trace the corresponding
   lambda -> 1- limit (rescale v_lambda(s) = v(s/lambda); m_k(lambda,
   v_lambda) -> m_k(1, v) by continuity, verified numerically by our band
   formulas) is used but not spelled out. **The paper's cos(8s/5) at
   lambda = 1 needs this limiting argument; ours needs the identical one.**
   Unconditionally the Rudnick-Sarnak range k lambda < 2 would cap k = 3 at
   lambda < 2/3 (7.5(e), line ~3786: "for lambda in (1/2, 1) this allows at
   most k = 3 (and only for lambda < 2/3)"); 7.5(g) is explicitly the
   RH-conditional branch, which is why the whole chain is stated under RH.
4. **What was held fixed.** The weight psi (LP vertex window-independent,
   re-checked), the BHB 19/27 input, and Proposition 4.4(iii) with the
   Schur-Horn majorisation of the admissible cubic (boundary case
   beta = -2 gamma). The paper notes its m2, m3 constants are verified from
   closed forms with interval arithmetic; our replacements carry exact
   rationals plus two-backend enclosures, which is the same standard or
   better.
5. **Conclusion on admissibility.** The optimization was run over even,
   nonnegative windows; the found optimum additionally satisfies, and the
   rational window provably satisfies, boundedness, monotonicity, smoothness
   of sqrt(v), and the variation-norm bounds. Within the class the paper
   itself uses (including its own two endpoint-nonvanishing cosines and the
   glossed lambda -> 1- limit), **v* is admissible, and the improved
   constant is legitimate RH-conditional arithmetic inside the Prop
   4.4(iii) + BHB chain.**

## 8. Grading and caveats

| claim | grade |
|---|---|
| m2, m3 closed forms in v | hardened: continuum derivation cross-checked by the exact finite-N CUE lattice count at two windows; per-term v = 1 anchors |
| F(cos(8s/5)) = 0.685243875537318196... | exact closed form (sympy), enclosure-checked in both ball backends; reproduces all the paper's printed digits |
| cos(8s/5) not a critical point; residual 5.6e-2 | measured (gradient validated against finite differences) |
| sup F = 0.6852870321770 | measured: three parametrizations, multistart, one basin; no global claim beyond the searched classes |
| F(v*) = 2245228120295149280/3276332462159207451 | exact rational arithmetic, two independent implementations, finite-N cross-check |
| F(v*) > F(cos(8s/5)), delta = 4.31478e-5 | enclosure-checked (Arb and mpmath.iv agree) |
| new constant 0.850828702939872 | exact rational, **conditional on RH and on the source paper's 7.5(g) machinery** |

Caveats, stated plainly:

- The source paper is a preprint dated 10 Aug 2026 and is **not peer
  reviewed**. Everything here inherits its Proposition 4.4(iii), its trace
  asymptotics, its use of Hejhal / Rudnick-Sarnak triple correlation under
  RH, and the Bui and Heath-Brown 19/27 simple-zeros proportion. If any of
  that fails, the constant fails with it; only the window mathematics (the
  m_k functionals and their optimization) is independently validated here.
- The whole statement is **conditional on RH**. Nothing in this directory
  is evidence for or about RH itself (docs/08 discipline).
- The improvement is quantitatively small (sixth decimal of the
  proportion). Its interest is structural: the hand-picked window is not
  optimal, the optimal window is characterized as an interior critical
  point of 1 - D2 - D3, and the remaining headroom within this certificate
  at k <= 3 is bounded by the searched sup, 0.68528703, so the paper's
  choice was already within 6.3e-5 of everything this branch can give.
- The lambda -> 1- and endpoint-taper limiting arguments are the paper's
  own glosses; this study measured the relevant continuity (section 7,
  items 2 and 3) but proves neither asymptotic; they remain inherited
  analytic debts of the source, shared equally by its window and ours.

## 9. Global optimality: landscape, exact slices, and a derived outer bound

Section 4's caveat said plainly that 0.6852870321770 was a local-search
outcome and that global optimality over the admissible class was not
claimed. This section settles as much of the global question as honest
rigor allows. Scripts: `global_bound.py` (derived outer bound, exact
rational arithmetic), `global_landscape.py` (EL landscape, measured),
`global_slice.py` (exact quartic-slice supremum, measured higher slices);
working log `global_notes.md`. Every script re-verifies the exact rational
F(v*) of section 5 before computing anything, and the landscape script
carries a freshly written mpmath Gauss-Legendre implementation of the
closed forms (no shared engine with `functional.py`) that agrees with the
exact rational to 50 digits (the gate demanded 25).

### 9.1 The outer bound: sup F <= 0.892744211644 (derived, exact rationals)

The chain runs through a central-moment identity. With l1 = 1 and
m0 = m1 = 1, m2 = 1 + D2, m3 = 1 + 3 D2 + D3, the quantities D2 and D3
are the second and third central moments about 1 of the limiting spectral
measure mu_v of A = H/l1, so

    F = 2 m2 - m3 = 1 - int lam (lam - 1)^2 dmu_v(lam).

For every finite N the moments m_k^(N) = E tr A^k / N are moments of the
expected empirical spectral measure, a positive measure on [0, inf)
because H is Gram, hence PSD. Three consequences survive the limit that
defines m_k:

1. F <= 1 (lam (lam-1)^2 >= 0 on [0, inf)): the concentration divergence
   and the flat-window 2/3 both sit under an unconditional ceiling.
2. F <= 1 - D2^2 pointwise in v (Cauchy-Schwarz (m2)^2 <= m1 m3).
3. sup F <= 1 - (inf D2)^2, since 1 - D2^2 is decreasing in D2 >= 0.

inf D2 is a quadratic problem solved with exact rational arithmetic:
D2 = <v, (I - T) v>/l1^2 with T the tri-kernel operator on B (Fourier
multiplier sinc^2 >= 0, tr T^2 = 1/2 exactly, so ||T|| <= 1/sqrt(2) < 1),
and for any c and any window normalised to int v = 1,

    <v, (I-T) v> >= 2 c - c^2 <1, (I-T)^{-1} 1>.

T maps polynomials to polynomials, so t_k = <1, T^k 1> are exact
rationals; with K = 44 terms and the tail bounded by
t_44 / (1 - 707107/1000000) (valid since 707107^2 >= 5 * 10^11 makes
707107/1000000 an upper bound for 1/sqrt(2) >= lam_max), the exact
rational U = 3.053441685709720... satisfies U >= <1, (I-T)^{-1} 1>, and
c = 1/U gives

    inf D2 >= 1/U = 0.327499295198...,
    sup F <= 1 - (1/U)^2 = 0.892744211644411...   (exact rational).

Grade: derived inequality chain, exact rational constants end to end,
resting on the hardened closed forms of section 2 inside the source
paper's framework. Cross-checks: the T-route D2 equals m2 - 1 from
`functional.py` as an exact identity of Fractions at two windows; a
trapezoid-grid discretization of (I-T) v = c converges to the same U with
O(h^2); and the Neumann window w_K = sum_{k<=K} T^k 1 (nonnegative
because T preserves nonnegativity) gives the exact upper bracket
D2(w_24) = 0.327499296325..., so the cone infimum of D2 is pinned to a
window of width 1.1e-9 and the grid minimizer is strictly positive
(edge/center = 0.760), making the positivity constraint inactive for the
D2 problem.

The bound is sharp for its inputs: among positive measures on [0, inf)
with mean 1 and second central moment d, the maximum of
int (2 lam^2 - lam^3) is exactly 1 - d^2, attained by
(d/(1+d)) delta_0 + (1/(1+d)) delta_{1+d}. With inf D2 pinned to 1e-9,
the value of this relaxation lies in [0.8927442109, 0.8927442116]:
further progress on the outer bound requires excluding near-two-point
spectral measures for actual windowed sine-Gram operators (a
transition-layer statement in the spirit of time-band limiting theory),
not more computation. That exclusion is the honestly-open part.

For calibration, the same chain pointwise at v* gives 1 - D2(v*)^2 =
0.892381..., against the true F(v*) = 0.685287...: essentially the whole
gap of the method is the Cauchy-Schwarz step, which charges nothing for
third-central-moment structure. The F-optimizer is close to but distinct
from the D2 minimizer: at the (exactly evaluated) Neumann window w_12,
D2 = 0.327499354, F = 0.684255566: the optimum spends 5.5e-4 of D2 to
buy back 1.0e-3 of F through D3.

### 9.2 The first-order landscape (measured)

The EL stationarity system g = dF/dv = 0 (a quadratic integral equation;
explicit form in `functional.gradient_field`) was SOLVED, not merely
maximized, from random starts in three parametrizations
(`global_landscape.py`), so saddles and boundary stationary points were
findable, not just maxima:

- Cosine spectral, v = 1 + sum_{k<=J} c_k cos(2 pi k s), J = 6/8/10/12,
  150 starts, all converged (Levenberg-Marquardt on the projected system
  P_k = int g cos(2 pi k s) = 0). At every J exactly ONE root has v > 0,
  and it is the known optimum; the restricted critical value climbs
  0.685275 / 0.685282 / 0.685284 / 0.685285 with J (this basis carries an
  endpoint-kink truncation bias; its role here is root counting, not
  precision). Every other root (2 to 4 per J) is sign-changing, i.e.
  leaves the cone, with F <= 0.598 and 46/50, 45/50, 22/25, 19/25 of the
  starts landing on the positive root.
- Squared Chebyshev, v = w^2, J = 6/8/10, 120 starts, 118 converged
  (least squares on the analytic gradient dF/da). The strictly positive
  stationary point is unique at every J and identical to twelve digits,
  F = 0.685287032177 (59 hits across J). All other stationary points (12
  to 16 per J) are windows TOUCHING ZERO at 1 to 8 isolated points;
  the best of them sits far below the optimum (0.6460 at J = 6, 0.6644 at
  J = 8, 0.6723 at J = 10), and the family decays with contact count down
  to strongly negative F (plus one degenerate l1 -> 0 artifact).
- Piecewise-linear cone with the exact lattice-aligned evaluator,
  n = 41 and 81 knots, 42 deliberately diverse starts (flat, cosine,
  quartic, three compact-support widths, bimodal, increasing profile,
  edge-heavy, randoms): every start converges to the SAME maximum,
  zero active knots (positivity inactive), KKT residual <= 5e-8,
  F = 0.685287031812 (n = 41) and 0.685287032154 (n = 81), the known
  pw-representation bias below the optimum. A separate Fischer-Burmeister
  stationarity solve (n = 21, 8 starts, 6 converged) finds exactly one
  KKT point, the optimum again: no stationary point with active
  positivity constraints was found anywhere.

Hessian at the optimum (cosine basis, 11 directions including the scaling
ray): one numerically exact zero eigenvalue along the scaling ray
(|H . ray| ~ 1e-10, eigenvalue 4e-12) and ten negative eigenvalues in
[-2.06, -1.76]; signature 0 positive / 1 zero / 10 negative, i.e. a
genuine local maximum modulo scale invariance, not a saddle.

Landscape verdict (measured): 336 stationarity, KKT, and maximization
starts across three parametrizations and ten basis resolutions produced exactly
one strictly positive stationary window, the reported optimum. Every
other stationary object either leaves the cone (sign-changing) or touches
v = 0 at isolated points with F at most 0.6723. The best F ever seen by
anything in this study is 0.685287032177002 (float evaluation of the
Chebyshev stationary point), i.e. the claimed sup was never beaten beyond
2e-15 of float noise.

### 9.3 Exact slice suprema and a two-sided witness bracket

The quartic slice v = 1 + q1 s^2 + q2 s^4 is settled exactly
(`global_slice.py`). On it F is a rational function of (q1, q2) of degree
3/3, the admissible region is A = {psi(u) = 1 + q1 u + q2 u^2 >= 0 on
[0, 1/4]}, and sup_A F is located by compactification: interior critical
points, the two exact boundary families (endpoint zero v(1/2) = 0, i.e.
q2 = -16 - 4 q1 with q1 >= -8; interior double root (q1, q2) =
(-2/u, 1/u^2), u in (0, 1/4]), and the arc at infinity, where along
admissible recession directions h = alpha s^2 + beta s^4 >= 0 the limit
of F is F(h) by scale invariance and continuity (the denominator's
leading form l1(h) = alpha/12 + beta/80 is strictly positive there).
Results, all in exact arithmetic:

- The lex Groebner eliminant of the critical system factors as
  (cubic) * (quartic) with 5 real roots in q2; exactly ONE critical pair
  is admissible: q2 = 1.15904242554051... (root of 53574903041239 q2^4
  - 7719414292779072 q2^3 - 126958598530649600 q2^2
  + 34764906650381107200 q2 - 40111525465989120000), q1 =
  -1.46701866547..., with

      F4* = 0.685287023289616136327866177020...

  The four inadmissible critical branches carry F = 0.4675, -1.396,
  -371.9, -41041.9.
- Boundary: the endpoint-zero family peaks at F = 0.62175582 (its unique
  admissible critical point); the corner window (1 - 4 s^2)^2 gives
  exactly 610/3003 = 0.203130...; the double-root family stays below
  -0.21.
- Arc at infinity: everything is <= -0.195 (worst case -10.5 on the
  double-root family's concentration end).

So sup over the quartic slice = F4*, attained at the unique admissible
critical point (derived, exact arithmetic; compactification argument as
above). Consistency: the rational witness v* of section 5 sits 1.55e-12
below F4* (exact separation), and F4* sits 8.887e-9 below the full-space
measured sup, exactly the gap section 5 already reported.

Higher slices (measured, 30 starts each): degree 6 reaches
0.6852870319222, degree 8 reaches 0.6852870321770 (all thirteen digits of
the claimed sup), degree 10 the same to 1e-13. Nothing beat it. Polishing
the degree-8 optimum and rounding to clean rationals gives an exactly
admissible witness (Sturm count: psi has no root in [0, 1/4]):

    v8(s) = 1 - (36773/25000) s^2 + (744/625) s^4 + (1341/25000) s^6
            - (3397/6250) s^8,
    F(v8) = 8273865220036096559249598473358
            / 12073576226528772158039668492375  =  0.685287032176620,

within 3.5e-13 of the measured sup. Pushing harder (Chebyshev J = 16,
then exact rational evaluation of the resulting degree-44 dyadic-
coefficient polynomial window, v = w^2 >= 0 automatic) gives the
sharpest exact witness:

    F = 0.685287032176998885912082211843   (exact rational, 208-digit
                                            numerator and denominator),

2.1e-15 below the float-measured sup. The global question is therefore
bracketed by exact rationals on both sides:

    0.685287032176998  <=  sup F  <=  0.892744211644412.

### 9.4 Verdict on the section 4 caveat

What changes:

| statement | grade |
|---|---|
| sup F <= 1 (ceiling for every admissible window) | derived |
| sup F <= 1 - (1/U)^2 = 0.892744211644411, U exact rational | derived chain on hardened closed forms |
| inf D2 in [0.3274992952, 0.3274992963] | derived two-sided, exact rationals |
| sup over quartic slice = F4* = 0.68528702328961614..., at the unique admissible critical point | derived, exact arithmetic |
| sup F >= 0.685287032176998885912... (degree-44 dyadic witness; clean degree-8 witness v8 gives 0.685287032176620) | exact rational arithmetic at explicit witnesses |
| unique strictly positive stationary window across 336 starts, 3 parametrizations, 10 resolutions; everything else leaves the cone or touches v = 0 with F <= 0.6723 | measured |
| the optimum is a genuine local maximum (Hessian: one zero mode = scaling, all other eigenvalues negative) | measured |

What does not change: global optimality over the full admissible class
remains open. The honest state is a factor-1.30 window
[0.685287, 0.892744] whose upper end is the exact value of the
(m1, m2)-moment relaxation; closing it requires spectral information
beyond the second moment (ruling out near-two-point limiting spectral
measures for windowed sine-Gram operators), which is research, not
computation. Within everything searched or solved exactly, the reported
optimum is the unique candidate: RF-C003's caveat can be upgraded from
"local search outcome, global optimality not claimed" to "unique interior
critical point across all parametrizations tried, exactly unique on the
quartic slice, never exceeded anywhere, and globally capped by a derived
bound 0.2075 above it; global optimality itself remains open".

## Files

- `functional.py`: derivation notes, four evaluators (float GL, exact
  pw-linear, exact Fraction, sympy), validation battery.
- `crosscheck_finiteN.py`: exact finite-N windowed CUE cross-check
  (imports, read-only, from `../sine_gram/exact_finite_N.py`).
- `optimize.py`: EL residual, cosine family, three optimization routes,
  writes `best_window.json`.
- `enclose.py`: two-backend ball enclosures, exact positivity and
  monotonicity, the strict inequality, the new constant.
- `global_bound.py`: the derived outer bound sup F <= 0.892744211644411
  (exact rational chain; section 9.1).
- `global_landscape.py`: EL landscape, KKT search, Hessian, best-ever
  tracker, and the independent 50-digit evaluator gate (section 9.2).
- `global_slice.py`: exact quartic-slice supremum and degree 6..10 slice
  multistarts (section 9.3).
- `global_notes.md`: the working checkpoint log for section 9.

All four scripts are runnable standalone with `.venv/bin/python` from the
repo root and re-produce every number in this file.
