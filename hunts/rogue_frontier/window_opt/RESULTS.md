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

## Files

- `functional.py`: derivation notes, four evaluators (float GL, exact
  pw-linear, exact Fraction, sympy), validation battery.
- `crosscheck_finiteN.py`: exact finite-N windowed CUE cross-check
  (imports, read-only, from `../sine_gram/exact_finite_N.py`).
- `optimize.py`: EL residual, cosine family, three optimization routes,
  writes `best_window.json`.
- `enclose.py`: two-backend ball enclosures, exact positivity and
  monotonicity, the strict inequality, the new constant.

All four scripts are runnable standalone with `.venv/bin/python` from the
repo root and re-produce every number in this file.
