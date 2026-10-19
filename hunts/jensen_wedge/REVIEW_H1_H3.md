# jensen_wedge: independent review of H1_H3.md (H1, H3, R1)

**Nothing here bears on RH.** This file reviews `H1_H3.md` and `RESULTS.md` section 16
of hunt #135 as merged on `main` at `81ce5921` (PR #311). The reviewer is a separate
session that did not write them, started from a blank context, read Holland's PDF
itself, and reproduced every numerical claim it checks with its own code
(`review_h1h3/review_h1h3.py`), which imports nothing from `probe.py`,
`probe_h1_h3.py` or `review/`. The brief was to find where the derivations break, not
to confirm them.

## Verdict, piece by piece

| piece | verdict | the one-line reason |
| --- | --- | --- |
| Lemma S(a), every derivative on complex disks | **holds** | each Cauchy estimate rederived; the main-term part is in fact bounded pointwise by (P2) with explicit constants (below); one radius nit (N1) |
| Lemma S(b), the real-axis asymptotic | **holds** | follows from (a)'s ingredients and the exact main-term structure |
| Lemma S(c), the `(H_(k-2) - 1)/L_x` correction | **holds, exactly** | the derivatives of G_0 computed symbolically: first-order constant `H_(k-2) - 1` at k = 2..8 with no rounding; the identity `G_0' = log L + rho_G` simplifies to 0 |
| H3, route 1 (one Cauchy step on Holland's (25)) | **holds** | the disk geometry and the factor `2/eta` check |
| H3, route 2 and the residual bound of section 3.3 | **holds** | (19) at r = 6 by Cauchy; items 1 to 4 rederived; every number reproduced; one asymptotic-only step (N2) |
| R1, the leading constant of h^(5) | **holds** | Lemma S(b) at k = 5: `(-1)^5 2 * 3! = -12` |
| H1: the exact rewrite as gap moments `tau_j` | **holds** | rederived line by line; at 13 values of n the system solved in this form and in Holland's quotient form (52) gives the same root to the working precision (relative 1e-46 or better) |
| H1: the Simpson limit with `det J = -1` | **holds, exactly** | Simpson's rule is the only zero of `Phi_inf`; J, `det J`, `J^-1` exact; `J = -diag(1,2,3,4)` times phase 1's moment matrix |
| H1: the weighted-box contraction (Lemma C) | **holds** | the Banach argument and every bound of 4.2 check; attacked by sampling `DT` over the box and by Newton from random starts, with no counterexample; one threshold inconsistency (N3) |
| H1: `kappa = 4533/15625`, `nu_w = 86/9`, admissibility iff `eps < 2/3` | **holds, exactly** | recomputed in rationals; `sigma(eps)` matches the hunt's four rationals exactly |
| (P1) as Holland's | **holds** | his Proposition 4.1 states it, (18) with (19) at r = 0, on "a slightly smaller closed sector" |
| (P2) as Holland's | **not stated by Holland; true and elementary** | he says only that complex `L_x` means GORTTW's continued branch; the bounds `\|L_N\| >= 4`, `\|L_N/N\| <= 1/8` are nowhere in the paper. A fixed-point derivation is given below, so the chain loses nothing (N4) |
| (P3) as Holland's | **holds** | his (25), used exactly as he states it |

**Overall: no piece is broken.** No counterexample was found to Lemma S, H3, R1, Lemma C,
Lemma T or H1; no exact constant is wrong; every measured number in `H1_H3.md` that this
review recomputed agrees with it to the digits printed. Four nits (N1 to N4) change no
verdict.

**On the question the brief asked: does the conditional six-coefficient wedge now rest
only on Holland's own inputs?** Yes, with two qualifications. Its external inputs are
Holland's Proposition 4.1 (which he derives from the complex form of GORTTW (3.2)), his
(79) and Lemma 7.1, and MFMP Propositions 2.7 and 2.17, all of which Holland's own
Theorem 1.1 also uses. The first qualification is (P2): it is not Holland's statement,
but it follows from his (16) alone by the argument in section 4 below, so it is a missing
paragraph, not a missing input. The second is `REVIEW_PHASE1.md` R2: the two hypotheses
of `RESULTS.md` 12.3 that H1 makes automatic are still not written into 12.3's statement.
Every step the chain uses has now had one internal review (sections 11 and 12 by
`REVIEW_PHASE1.md`, `H1_H3.md` here). The grade of the composite is that of a derivation
reviewed internally once, **not a theorem**, pending external review. This review ran no
novelty search. The hunt's own search (`NOVELTY.md`, `RESULTS.md` section 17, merged after
the commit reviewed here) found earlier, unreviewed deposits of the wedge and of the Pade
point; that bears on the delta against Holland, not on whether these derivations hold.

## 1. What was read, and how the numbers were reproduced

- **Holland**, arXiv:2608.08682v1, downloaded as PDF on 2026-10-19 (SHA-256
  `3fc31ba84fb113bc0b3109fb0e569bd1d7183018485aca1eb1dab565c839b49d`, the file phase 1
  and the phase 1 review recorded), extracted with `pdftotext -layout` into a scratch
  directory outside the tree and read as data: section 3 (eq. (10)), section 4 (eqs. (14)
  to (33), Proposition 4.1, Lemmas 4.2 and 4.3), section 6 (eqs. (49) to (66), Lemma 6.1).
- **Four routes this hunt had not used.**
  1. *G_0 symbolically.* The derivatives of Holland's main term are exact rational
     functions of (N, L), produced by sympy from `D = d/dN + (L/Q) d/dL`. The hunt measured
     them by Cauchy's formula on 64 points.
  2. *The targets from Titchmarsh's kernel.* `h(z) = log M_z` with
     `M_z = int_0^oo Phi(u) u^(2z) du`,
     `Phi(u) = sum_k (2 pi^2 k^4 e^(9u) - 3 pi k^2 e^(5u)) exp(-pi k^2 e^(4u))`, by tanh-sinh
     quadrature in the saddle variable, all shifts n..n+6 from one set of integrand values.
     The u-scale is half Holland's, which adds a linear function of z to h and changes no
     `Delta^m`, m >= 2. Against `zeta.li`'s Cauchy route (no Mellin representation) at
     n = 20..26: `Delta^2..Delta^6 log gamma` agree to relative 9e-62 or better. A planted
     1e-30 error in one log moment moves `Delta^5 h(1e7)` by 10 percent; two quadratures at
     different precision and window agree to 1e-20 (test).
  3. *Holland's (15) on a complex circle*, `F(s)` integrated along the real axis with the
     large phase `s log y_c` taken out explicitly and the residual phase checked to stay
     below 1, so no branch jump can pass unseen.
  4. *The matching system solved twice*: in the gap-moment form (4.2) through exact finite
     differences of log, and in Holland's quotient form (52) at k = 0..3 in the unknowns
     log A..log D. The two share no formula.
- **Precision.** Working precision `50 + 7 log10 n` digits (190 at n = 1e20), chosen so
  `Delta^6 h` keeps at least 30 digits after the cancellation in the differences.

Reproduce:

```bash
.venv/bin/python hunts/jensen_wedge/review_h1h3/review_h1h3.py             # about 80 s, writes results_review_h1h3.json
.venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/review_h1h3          # 39 tests, about 20 s
```

## 2. Lemma S: holds

**Checked line by line.** The remainder bound (Cauchy on the disk of radius `eta x`, with
`|zeta| >= (1 - 2 eta) x`), the elementary terms `E_l^(k)`, the identity `L' = L/Q`
(from (16): `dx/dL = Q/L`), the collapse to `G_0' = log L + rho_G`, the factorisation
`Q = N L (1 + u)` with `|u| <= 11/32` under (P2), the bound `|rho_G| <= 2/|N|` (it holds
only after the cancellation `rho_G = [(1 + L) - (1 - 3L/(2N))/(1 + u)]/(2Q)`, which gives
about `1.3/|N|`; the term-by-term triangle inequality gives `3.2/|N|`, so the write-up
should show the combined form), the Leibniz step `phi^(m) = (-1)^m m!/(N^(m+1) L)(1 + H_m/L + ...)`
(the `i >= 1` terms sum to `m! H_m`), `(phi v)^(m)`, and the passage back to z.

**Strengthened, not just confirmed.** Symbolically, with `a = 1/L` and `b = L/N`,

```
    f_k(a, b) := (-1)^k N^(k-1) L G_0^(k)(N)/(k-2)! = P_k(a, b) / (c_k (4 + 4a - 3b)^(2k)),
```

with `P_k` a polynomial and `c_k` a rational constant, for k = 2..8. Since `4 + 4a - 3b = 4(1 + u)`,
(P2) gives `|4 + 4a - 3b| >= 21/8`, and bounding `P_k` by its monomials on
`|a| <= 1/4, |b| <= 1/8` gives, **pointwise at every N where (P2) holds**,
`|G_0^(k)(N)| <= C_k (k-2)!/(|N|^(k-1) |L_N|)` with `C_2..C_6 = 13.9, 65.9, 294.8, 1287, 5548`
(exact rationals in the JSON; crude, since `|f_k|` near the real axis is about 1.1).
The main-term part of (a) therefore needs no disk at all, and its constant is explicit;
only R's Cauchy estimate needs disks, and its constant inherits `C_R`.

**(c), exactly.** `f_k(a, 0) = 1 + c_1(k) a + c_2(k) a^2 + ...` with

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `c_1` (here) | -1 | 0 | 1/2 | 5/6 | 13/12 | 77/60 | 29/20 |
| `H_(k-2) - 1` | -1 | 0 | 1/2 | 5/6 | 13/12 | 77/60 | 29/20 |
| `c_2` (here, new) | 1 | -2 | -5/2 | -5/2 | -7/3 | -21/10 | -331/180 |

For h rather than G_0 the difference is `O(L/x)` (elementary terms), `O(1/x)` (the factor
`(x/(x-1))^(k-1)`) and `O(L x^(-2+eps_0))` (R), all beyond every power of `1/L`, so (c)
holds for h with the same constants. The `b`-dependence is likewise beyond every power of
`1/L` on the real axis, since `L/N ~ e^(-L)`. A planted wrong saddle identity,
`L' = L/(Q + N)`, moves the k = 3 constant from 0 to -1 (test).

**Measured, reproduced.** The ratios of `G_0^(k)` to the leading term at N = 1e3, 1e20,
1e50 and `(ratio - 1) L` at 1e50 (-0.9909, -0.0179, 0.4773, 0.8105, 1.0618) agree with
section 2's quoted values to every printed digit; the gap to `H_(k-2) - 1` is the second-order
term (k = 6: `13/12 - (7/3)/109.29 = 1.0620`). On the rays `arg N = 0.25, 0.5` the modulus
agrees with the real value to 1.37e-3 (1e3), 3.3e-6 (1e20) and 1.9e-7 (1e50), as quoted.
On the measured targets, `(tau_j L/2 - 1 - c_1/L - c_2/L^2) L^3` stays between -6.1 and
4.8 over all 13 values of n and j = 0..4, and at n = 1e20 it reads -0.977, 4.79, 2.57,
0.21, -1.78 against the third-order coefficients -1, 5, 5/2, 0, -49/24: Lemma S's
expansion explains the targets through third order, well beyond what `H1_H3.md` claims.

**N1 (radius, harmless).** The disk argument says `|L|` changes by a factor in
`[5/6, 7/6]` along N-disks of radius `rho |N|` "for `rho <= 1/4`". Such a disk about
`N = 2(x + w) - 2` stays inside `{2z - 2 : z in S}` only for `rho` up to about `eta`, which
is `min(sin theta, 1/4)/2` and can be far below 1/4 when `theta` is small. Taking
`rho = eta` changes constants only, and with the pointwise bound above the main term does
not need the disks.

## 3. H3 and R1: hold

**Route 1.** For `|w| <= eta x/2` the disk of radius `eta x/2` about `x + w` lies in
`{x + w' : |w'| <= eta x}`, where Holland's (25) applies; Cauchy with m = 1 gives
`|h^(6)| <= (2C/eta)/(x^5 log x)`. Correct, and it uses (25) exactly as Holland states it
(absolute `eta`, `C`, for x large).

**Route 2.** With `delta = min(sin(theta/2), 1/2)` the disk `|zeta - z| <= delta |z|` about
`z` in the half-angle sector stays in S (angle at most `theta/2 + theta/2`, modulus at
least `x_0`), and the displayed bound `720 delta^(-6)(1 - delta)^(-1+eps_0) C_R |z|^(-7+eps_0)`
follows. Nothing in Holland's proof of (19) restricts r; he stated r <= 5 because that is
all he used.

**Section 3.3.** Item 1: `psi^(5)(y) - 24/y^5 = int_0^oo t^4 e^(-yt)(t/(1 - e^(-t)) - 1) dt`
and `0 <= t/(1 - e^(-t)) - 1 <= t` (equivalent to `(1 + t) e^(-t) <= 1`); the nine quoted
ratios (0.81734306 at y = 1 down to 0.00050523513 at 10 + 30i) reproduce to 8 digits.
Item 2: `f_z(n/p) = 24/(p + z)^5`, `f_z(0) = 0`, and the five terms are `-int_G f_z'` over
the signed gap set; at n = 3200 the exact sum and the gap integral are -9.2806146 and
-9.2728605 (times `n^-5`), difference `24.813/n^6`, all as quoted. The quoted bound
`599.44/n^6` is `600 (n/b)^6`, every parameter replaced by the smallest, b; with each
parameter's own value it is `201.6/n^6`. Item 3: `f_z'(t) = 120 n t^4/(n + z t)^6`. Item 4:
`|G| = eps(g0 + gx + g1) - 1/(2n + 1)` on the box, so the stated
`eps(1 + 13r/4) + 1/(2n + 1)` is a valid, slightly loose bound. `(tau_4 L/2 - 1) L` is
0.861 at n = 1e6 and 1.027 at 1e20, as quoted.

**N2 (asymptotic step, harmless).** The explicit second term of the final bound uses
`eps <= 2/L_n`. That holds for n beyond a non-explicit n_1 (the first-order term of
Lemma S(c) at k = 2 is `-1/L`, negative) and is measured at all 13 values of n here
(`eps L/2` from 0.663 to 0.977), but it is not a derived inequality at any stated n. The
bound needs only `eps = O(1/L)`, which Lemma T gives, so nothing breaks.

**R1.** Lemma S(b) at k = 5 is `h^(5)(x) = -12/(x^4 L_x)(1 + 5/(6 L_x) + O(1/L_x^2))`.
This is the input `REVIEW_PHASE1.md` R1 asked for, and its first-order constant is now
exact.

## 4. (P1), (P2), (P3) and Lemma 6.1 against the paper

**(P1): stated by Holland.** Proposition 4.1 gives a sector `S_theta` on which `M_z` is
nonzero, the branch `h = log M_z` real on the positive axis, the decomposition (18), and
(19): for every fixed `0 < eps_0 < 1/2` and `0 <= r <= 5`, `R^(r) = O(|z|^(-r-1+eps_0))`
uniformly on a slightly smaller closed sector, with constants depending on `eps_0, r, theta`.
(P1) is the case r = 0 on that smaller sector. Holland's proof is a short derivation from
the complex form of GORTTW (3.2), which neither the hunt nor this review checked; his own
Theorem 1.1 rests on the same input.

Measured support for (P1), all on this review's routes:

- On the real axis, Holland's main term `G_0(2z - 2) + log(32 z (2z - 1))` reproduces
  `Delta^m h(n)`, m = 2..6, to relative 1.8e-4 (n = 50), 1.7e-7 (3200), 7.8e-14 (1e7) and
  7.5e-39 (1e20). That is the size `L/n^2` expected if `R^(m) = O(n^(-m-1))`.
- On the circle `|z - n| = n/8`, from Holland's (15): `R + c_sad` at the centre is
  1.669524288 (n = 400) and 1.669034388 (3200); its largest deviation on the circle is
  `0.0283/n` and `0.0384/n`; `sup |h^(6)|` on `|z - n| = n/16` is 1.52200 and 1.54447 times
  `48/(n^5 L_n)` (the same with half the points); the Taylor ratios at the centre for
  k = 2..7 match. Every one of these equals the hunt's value to the digits it prints. A
  planted `1e-3 z` term in R would vary by about `0.1 n` on this circle and is caught
  (test).
- Holland's (15) against the Titchmarsh-kernel moment: `Delta^2..Delta^6 h` from the circle's
  Taylor coefficients agree with the real-axis quadrature to relative 7.5e-33 or better at
  n = 400 and 3.5e-28 or better at 3200. So (15) is right up to the linear normalisation
  that Holland's own text discusses.

**(P2): not stated by Holland (N4).** Off the real axis Holland says only that `L_x` means
the holomorphic continuation of the saddle that GORTTW use in their section 3. The bounds `|L_N| >= 4` and `|L_N/N| <= 1/8` appear nowhere in
the paper. `H1_H3.md` section 1 is candid about this ("uses this without separate
statement"), but it lists (P2) among the inputs "from the paper", and `RESULTS.md`
section 16's closing list of what the wedge rests on leaves it out. It is in fact a
consequence of (16) alone:

> **(P2) from (16) (reviewer's derivation, self-reviewed).** Let `|arg N| <= pi/2` and
> `l := log |N| >= 13`. On `D = {L : |L - l| <= l/2}` put `T(L) = log(N/L - 3/4) - log pi`
> (principal log). For L in D: `|L|` lies in `[l/2, 3l/2]`, `|arg L| <= pi/6`, and
> `e := |3L/(4N)| <= (9/8) l e^(-l)`, so `arg(N/L - 3/4)` lies within `pi/2 + pi/6 + asin e < pi`
> of 0 and T is holomorphic. Then `|Re T - l| <= log(3 pi l/2) + log(1/(1 - e))` and
> `|Im T| <= pi/2 + pi/6 + asin e`, whose sum is at most `l/2` once `l >= 13` (slack 0.29 at
> l = 13; negative, -0.13, at l = 12). Also `|T'(L)| = 1/|L (1 - 3L/(4N))| <= (2/l)/(1 - e) <= 0.154`.
> So T is a contraction of D into itself, with a unique fixed point, which solves
> `N = L(pi e^L + 3/4)`. The iterates of `log N` (which lies in D) are holomorphic in N and
> converge uniformly, so the fixed point `L_N` is holomorphic; it is real for real N, hence
> equal to the positive root of (16) there, hence GORTTW's continued branch by uniqueness of
> continuation. Finally `|L_N| >= l/2 >= 6.5` and `|L_N/N| <= (3l/2) e^(-l) < 1/8`.

So (P2) holds on Holland's sector once `x_0 >= 2.3e5` (derived); numerically, along every ray
of `|arg z| <= 1` from `|z| = 346` to `1e30`, the continued branch has `|L_N| >= 4.0010` and
`|L_N/N| <= 0.0059`, while `|L_N| >= 4` already fails at `|z| = 50` (smallest 2.50). Since
(P1)'s `x_0` is not explicit anyway, enlarging it costs nothing. **Recommendation:** write
this paragraph into `H1_H3.md` section 1 and drop (P2) from the list of inputs.

**(P3): stated by Holland.** His (25): absolute `eta, C > 0` with
`|h^(5)(x + w)| <= C/(x^4 log x)` whenever `|w| <= eta x`, x large.

**Lemma 6.1: not used, confirmed.** It solves the D-fixed three-equation system (52) in the
scaled variables (a, b, c) on a sup-norm cube of radius 3/20, with its own constants
(`||J^-1||_inf = 66/25`, contraction factor below 2/5). H1 is a different, square
four-equation system with its own matrix, norm and box; it borrows the method only. The
equations H1 does use: (31) at every k follows from (14) (`gamma = sqrt(pi) M_z/(4^z Gamma(z + 1/2))`
by duplication, so `log q_k = l(b + k) - Delta^2 h(n + k)`), and (58) is (52) in logs,
`f_k(U) = -l(U + k)`. (21) to (23) are Lemma S(b) at k = 2..4, and (24), (25), (29) are
consistent with Lemma S(a); R1 sharpens (29) at k = 5 from an O-bound to an asymptotic.

## 5. H1: holds

**4.1, the gap-moment form.** Rederived: `log qq_k(U, V) = l(V + k) - l(U + k)`, so (52) at
k = 0..3 is the displayed system; applying `(-1)^j n^(j+1)/j! Delta^j` at k = 0 is triangular
and invertible; `l(p + k) = Delta log(p + k)`; `Delta^(j+1)(1/p) = (-1)^(j+1)(j+1)!/(p (p+1) ... (p+j+1))`;
and with `p = n/w`, `u_j'(w) = (j + 1) w^j prod_(i=1)^(j+1) (1 + i w/n)^(-1)`, `u_j(0) = 0`. The
system is exactly `tau_j = int_G u_j'`. At all 13 values of n from 50 to 1e20 the root of
(4.2) and the root of (52) solved independently agree to relative 1.1e-46 (n = 50, at 61
digits), 2.0e-65 (n = 3200) and 8.9e-115 (n = 1e20), and the root satisfies
`0 < w_A < w_B < w_C < w_D < 1`.

**4.2, the decomposition.** `S_j` derived from the gap endpoints by sympy equals the
display for j = 0..3, and `Phi_inf = 1 - P_j(X; 0)`, so the decomposition is exact. The
bounds `-(j+1)(j+2)t/(2n) <= rhohat_j <= 0` (from `prod (1 + a_i)^(-1) >= 1 - sum a_i`), on
`beta_j`, on `rho_j` and on its four partial derivatives each rederive. The x-derivative
bound `(j+1)^2 (j+2)/(n eps)` is crude (it ignores that the two endpoint values nearly
cancel), which only costs room.

**4.3, the constants.** Simpson's rule is the only zero of `Phi_inf` (sympy `solve`).
J, `det J = -1` and `J^-1` are as displayed, and `J = -diag(1,2,3,4) M` with M the matrix
pinned at determinant -1/24 in `test_jensen_wedge_phase1.py`. The matrix
`I - J^-1 D Phi_inf(X* + d)` equals the display entry by entry. Its monomial row bounds are
3472/15625, 177/625, 1736/15625 and **4533/15625** (row x), so `kappa = 4533/15625`; the
largest value on a 21 x 21 grid is **177/625** (row gx at a corner), as quoted.
`nu_w` row sums are 86/9, 10/3, 17/9, 8: **`nu_w = 86/9`**. The four row bounds of
`sigma(eps)` are polynomials with nonnegative coefficients and the x-row dominates the
others coefficientwise, so `sigma(eps)` is that one polynomial,
`33053/93750 eps^3 + 778139/281250 eps^2 + 12/5 eps`; at 1/32, 1/16, 1/8 and 1/6 it equals
the hunt's rationals exactly. `J^-1 (eps S)(X*; eps) = eps (1 - eps)(1/18, -1/9, 1/18, 0)`
exactly. **Admissibility:** on the box, `w_A < w_B` binds at `eps = 11/15` and
`w_C < w_D` at `eps = 2/3`; an exact corner check passes at `2/3 - 1e-9` and fails at `2/3`.

**Lemma C, the proof.** `DT = (I - J^-1 D Phi_inf) + J^-1 D(eps S) + J^-1 D rho` has the
right signs (`D Phi_n = D Phi_inf - D(eps S) - D rho`; t and beta do not depend on X); the
operator norm of the weighted max norm is the weighted row sum; the mean-value inequality
on the convex box, the self-map step `q r + d_0 <= r` and Banach's theorem are standard.
Uniqueness is in B only, as stated.

**Lemma C, attacked.** The derivative bound is the step most likely to be quietly wrong, so
it was tested against the exact `Phi_n` on measured data. At n = 1e7 (q = 0.688) the
largest `||DT||_w` over 120 random points of B is 0.550, and at n = 1e20 (q = 0.408) it is
0.357; the largest `||T(X) - X*||_w` over the same points is 0.0405 and 0.0195, inside
r = 0.08; Newton from 24 random starts in B reaches one root every time (spread 9e-76 and
1e-107 in the weighted norm). With a planted wrong `J^-1` (one entry changed from -2 to -3)
the sampled `||DT||_w` exceeds q, so the probe can fail (test).

**N3 (threshold inconsistency, harmless).** Section 4.3 says the lemma applies at
`eps <= 1/16`, `n eps >= 1e5` whenever `||J^-1 t||_w <= 7/200`; section 4.5 says `9/250`.
With the bounds 4.3 displays (eps part at most `eps/9`, the `rho` tail summed over the
box) the exact threshold is 0.0359766, so 7/200 holds and 9/250 does not, by 2.3e-5. With
the sharper `eps (1 - eps)/9` and the tail at X* it is 0.0364727 and both hold. One of the
two numbers should change; nothing else depends on it.

**4.4, Lemma T and the first order.** Lemma T is the integral form of the finite
difference with Lemma S(b) inserted; `dL_x/dx = 1/((x - 1)(1 + u)) <= 1/(x - 1)` since
`u > 0` for large x. Symbolically: `J^-1 (0, 1, 3/2, 11/6) = (1/3, 0, -1/3, -1/4)`,
`(X_n - X*) L -> (-2/9, -2/9, 4/9, 1/4)`, and with `eps L/2 = 1 - 1/L` the expansions
`A/(nL) = 3 + 7/L`, `(D - n) L/n = 1/3 + 2/(3L)`, `(B - 2n) L/n -> 5/3`,
`(C - 2n) L/n -> -11/3`, `(B - C) L/n = 16/3 - 112/(9L)` all come out as displayed. Using
`X_n - X* = -J^-1 Phi_n(X*) + O(1/L^2)` with a shrinking box is legitimate: the entries of
`I - J^-1 D Phi_inf` are linear in the deviation, so `q = O(1/L)` there.

**4.5, H1 itself.** Lemma T gives `eps, t = O(1/L)` and `n eps -> oo`, so `sigma(eps)`,
`rho'` and `d_0` tend to 0 while `kappa < 1`; Lemma C applies for all large n, and the
parameter statements follow from its radius bound. Correct as stated, with `n_0` not
explicit for the reason given (it inherits `C_R`, `theta`, `x_0`). Absorbing `n < n_0` into
K is legitimate: for K large the wedge condition admits no `d >= 6` with `n < n_0`.

**4.6, the measured table, reproduced on an independent route.**

| n | `eps L/2` | `L t_1, L t_2, L t_3` | q | `d_0` | `(1 - q) r` | closes | `\|\|X_n - X*\|\|_w` | radius |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 50 | 0.66291 | 0.3110, 0.3792, 0.3155 | 43.15 | 10.59 | < 0 | no | | |
| 3200 | 0.85229 | 0.7172, 1.1498, 1.4667 | 2.146 | 0.2120 | < 0 | no | | |
| 1e6 | 0.91644 | 0.8398, 1.3209, 1.6665 | 0.7744 | 0.02551 | 0.01805 | no | | |
| 1e7 | 0.92905 | 0.8631, 1.3494, 1.6952 | 0.6879 | 0.02152 | 0.02497 | **yes** | 0.02432 | 0.06895 |
| 1e12 | 0.96000 | 0.9216, 1.4171, 1.7602 | 0.5000 | 0.01269 | 0.04000 | **yes** | 0.01283 | 0.02538 |
| 1e20 | 0.97667 | 0.9539, 1.4523, 1.7922 | 0.4081 | 0.007572 | 0.04735 | **yes** | 0.007232 | 0.01279 |

(At n = 50, `eps = 0.5296`. All 13 rows, n = 50, 200, 800, 3200, 1e4, 1e5, 1e6, 1e7, 1e8,
1e10, 1e12, 1e16, 1e20, are in `results_review_h1h3.json`.) Against the hunt's ten rows:
`tau_j` and `X_n` agree to the 10 digits stored here (relative 3e-10; the test pins
`tau_j` at 1e7 to 1e-13), `d_0` and the parameter columns to every digit, and the
holds/fails pattern is identical (fails at every n <= 1e6, holds from 1e7 to 1e20), as is
`||X_n - X*||_w` inside the radius at all six n where it holds. q differs by at most 1.2e-6:
the hunt evaluates `sigma` at `eps (1 + 1e-6)` as a deliberate rational upper bound. With
the `rho` tail at X* instead of over the box the pattern is unchanged. At n = 50, 200, 800
the parameters reproduce `RESULTS.md` 11.3's table (for example `A/(nL) = 7.3916, 5.5461,
4.7632`). The first-order columns of section 4.6's second table reproduce to the printed
digits and move monotonically toward `(-2/9, -2/9, 4/9, 1/4)`.

## 6. Nits, collected (none changes a verdict)

- **N1** (Lemma S): the N-disk radius must be at most about `eta`, not `1/4`; or use the
  pointwise main-term bound of section 2 here. Also show `rho_G` in its combined form, since
  the term-by-term bound is `3.2/|N|`, not `2/|N|`.
- **N2** (section 3.3): `eps <= 2/L_n` is asymptotic (beyond a non-explicit n_1), not a
  stated inequality; `eps = O(1/L)` suffices.
- **N3** (sections 4.3 and 4.5): 7/200 against 9/250; the displayed bounds support 7/200.
- **N4** (sections 1 and 5 of `H1_H3.md`, `RESULTS.md` 16): (P2) is not Holland's; it
  follows from (16) by the fixed-point paragraph of section 4 here.

## 7. What this review did not do

- It did not check the complex form of GORTTW (3.2), from which Holland derives
  Proposition 4.1, nor Holland's (79), Lemma 7.1 or MFMP Propositions 2.7 and 2.17.
- It did not re-review `RESULTS.md` sections 11 and 12 (`REVIEW_PHASE1.md` did) or write
  R2's hypotheses into 12.3.
- Its measurements are finite: 13 values of n, two circles. Lemma C "closing" at a
  measured n is a measurement at that n, since the inputs are not enclosed in balls.
- No novelty search here (see `NOVELTY.md` for the hunt's). The (P2) paragraph above is
  the reviewer's own derivation and has had no second reader.
- Compute: the script ran locally in about 80 s and the tests in about 20 s; nothing
  heavy. `MISSION.md` asks for a `runmanifest` in `RUNS.md` for every run, but this
  review's brief forbade editing existing files, so the run is recorded here instead and
  `RUNS.md` was not touched.
- It edited no existing file. Files: this one, `review_h1h3/review_h1h3.py`,
  `review_h1h3/test_review_h1h3.py`, `review_h1h3/results_review_h1h3.json`.
