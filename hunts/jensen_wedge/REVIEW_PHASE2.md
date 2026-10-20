# jensen_wedge: independent review of phase 2 (the explicit constants)

**Nothing here bears on RH.** This file reviews `EFFECTIVE.md` and `RESULTS.md` section 18
of hunt #135 as merged on `main` at `70d72a8e` (PR #314). The reviewer is a separate
session that did not write them, read the three primary sources itself, and reproduced
the four constants with its own code (`review_p2/reproduce_p2.py`), written from
`EFFECTIVE.md`'s formulas and from this review's own derivations of the steps that file
states only in words. That code does not import `effective.py`, `probe.py`, `review/` or
`review_h1h3/`. The brief was to find where phase 2 breaks, not to confirm it.

## Verdict

**No step is broken. All four constants and the c = 1 remark hold**, at the grade
"derivation, self-reviewed by phase 2 and now reviewed once by an independent session".
That is one internal review, not an external one: none of the four is a theorem, and this
file does not promote any of them. One finding is about the checking, not the mathematics:
the planted-weakening check covers the claimed constants, but **three of four formula faults
planted here pass phase 2's entire test suite** (item P). The steps it misses were
re-derived by hand here and are correct, so the constants stand; the suite's coverage claim
should be read as narrower than section 18 of `RESULTS.md` states it.

| constant or remark | verdict | independent recomputation (this review) | claimed |
| --- | --- | --- | --- |
| (5a) `n^3 log^2(n+2) >= K d^5`, with GORTTW Cor. 1.3 | **holds** | max K_req = 17 698 over 137 subintervals, n >= 9.9e33; n_min(K)/9.91e33 >= 12.647 | K = 17 900 |
| (5s) the same, standalone | **holds** | chain green from n_0 = 789 702 (max K_req = 2.43e5); absorption 9.0814e19 | K = 9.10e19 |
| (6a) `n^4 log^2(n+2) >= K' d^6 log^12(d+2)`, with Cor. 1.3 | **holds** | max K'_req = 3.70e9 over 130 subintervals, n >= 5.6e35; n_min(K')/5.65e35 >= 177.77 | K' = 7.21e9 |
| (6s) the same, standalone | **holds** | chain green from n_0 = 14 237 025 (max K'_req = 6.06e15); absorption 3.6058e30 | K' = 3.61e30 |
| c = 1 admissible in GORTTW Theorem 1.1 | **holds, with (5a)'s grade** | `e^(3d/2) (d/2)^2 >= 17 900 d^5` for every d > 9.36e20, margin `e^(1.4e21)` | |

Every number in the middle column is an upper end (lower end for n_min ratios) of an Arb
ball (python-flint, 256 bits, `zeta.rigor.BACKEND` checked). The (5a) requirement agrees with
phase 2's recomputation to 0.02 percent and (5s) to 2.5 percent (a finer cover here); the
two six-coefficient requirements come out a factor 1.95 (6a) and 2.4 (6s) lower, because this
review encloses the sixth-order bracket more tightly (R13).

## Item by item

| item | verdict | one line |
| --- | --- | --- |
| R1 Lemma V (the complex saddle) | **holds** | contraction, disk inside H_V, uniqueness by `\|Im F\| < pi`: rederived |
| R2 Lemma L: contour geometry | **holds** | holomorphy strip `\|Im v\| < pi/2`, the horizontal line through v_0, `arg g(t/v_0) = -2 arg(v_0 + u t)`: rederived |
| R2 Lemma L: the five majorants | **holds** | rederived with different intermediate bounds; C_rho agrees to 5 significant digits or better at all four thresholds |
| R3 Lemma R: uniformity on `\|z - x\| <= x/4` | **holds** | the union of the disks is the truncated sector `\|arg z\| <= asin(1/4)`, `\|2z\| >= 1.5 x_0` |
| R3 Lemma R: rate `\|z\|^(-1/2 + eps)` | **holds, and is loose** | the bound is `C_rho/sqrt(pi e^R)`; the measured remainder is `O(1/p)` |
| R3 "only `\|R\| < 1` enters" | **holds, stated slightly loosely** | what enters is an explicit finite bound on `\|R\|`; Cauchy turns any such bound into `O(n^-k)` |
| R4 Lemma D(i), D(ii) | **holds** | F_k rederived in sympy; first-order constants `H_(k-2) - 1`; Cauchy radius n/8 inside n/4 |
| R5 the targets T_j | **holds** | B-spline mean value; enclosed with the e-correlation kept |
| R6 Lemma M5 (Krawczyk) | **holds** | own parametric Krawczyk on every subinterval; the system equals Holland's (52) with D = n/2 to 1e-76 |
| R7 Lemma G, `C_loc <= 2.094` | **holds** | Gershgorin rows and both cases rederived; (75), (76), (78) checked; max 2.09318 |
| R8 Lemma 9.1-E, `K_6 = 2.53` | **holds** | (86), (87), (90), V_m checked exactly; `a + b + theta <= 0.99693`; `K_6 = 2.52` gives 1.0015 |
| R9 Lemma 8.1-E, `Theta_5 <= 1.034` | **holds** | signs, the psi^(4) remainder and Hermite-Genocchi rederived; max 1.03384 |
| R10 assembly and Lemma W | **holds** | `log 17`, `d^(5/2)/n^(3/2) <= log(n+2)/sqrt(K)`; W(i) to W(iii) reproved |
| R11 Lemma M6 (Krawczyk) | **holds** | own Krawczyk on every subinterval; the system equals (52) with D free, k = 0..3, to 1e-76 |
| R12 Lemmas A to C with R2's hypotheses | **holds** | 2.47, 6.07, `(1 - eta) g_1/3`, `c_H` rederived; MFMP Prop. 2.17 read; all five conditions on every subinterval |
| R13 `Theta_6 <= 0.066` | **holds, loose by a factor 1.4** | exact divided differences give 0.0477 (6a) and 0.403 (6s) |
| R14 the small-n hand-off | **holds** | every wedge pair below the chain has d below 9.36e20 |
| R15 the c = 1 remark | **holds** | follows from (5a) and Cor. 1.3 in two lines |
| P the planted-weakening check | **holds for constants; does not cover several formula steps** | 3 of 4 formula plants pass all 36 phase 2 tests |
| D1 to D3 documentation | **minor gaps** | listed at the end; none changes a number |

## What was read

- **Holland**, arXiv:2608.08682v1, PDF downloaded 2026-10-19, SHA-256
  `3fc31ba84fb113bc0b3109fb0e569bd1d7183018485aca1eb1dab565c839b49d` (the file phase 1
  recorded), extracted with `pdftotext -layout` into a scratch directory outside the tree
  and read as data: Proposition 2.2 and its proof, Proposition 4.1 and its proof,
  Lemma 4.2, Lemma 6.1 and (52), section 7 ((73) to (80)), Lemmas 8.1 and 9.1 with
  (82) to (93), section 10.
- **GORTTW**, arXiv:1910.01227v3, SHA-256
  `f203487acc45a58808462e897240ce4929c998d9f0230d9a4bedb6d3841c3b2c`: Theorem 1.1
  (`n >= c e^(d/2)`, c not computed), Theorem 1.2, Corollary 1.3 (`d <= 9.36e20`, every
  n >= 0, via Platt's RH verification to 3.06e10), section 3 ((3.1), (3.2), the
  regularised `R*_M`, Lemma 3.1).
- **Martinez-Finkelshtein, Morales, Perales**, arXiv:2309.10970v3, SHA-256
  `23f228e0682430c1ae6285be4abed4d730e9a08accad6c3f540fbdf4eb5bb4a3`: Propositions 2.7
  and 2.17.

## R1. Lemma V

Rederived. `F(v) = v + g(v)`, `g = log v + log pi + log(1 - (a/pi) e^-v)`, and on
`H_V = {Re v >= V, |Im v| <= 1}`, `|g'| <= 1/V + delta_a/(1 - delta_a) = q`. The map
`v -> v_1 + log(s/s_1) - (g(v) - g(v_1))` sends the disk of radius
`rho' = |log(s/s_1)|/(1 - q)` about `v_1(s_1)` into itself because
`|log(s/s_1)| + q rho' = rho'`. The disk stays in H_V: for `s_1 = |s| >= 1.5 x_0`,
`v_1(s_1) - rho' >= V + 1 - b > V`, and `rho' <= b <= 1` (b is 0.256 to 0.283 at the four
thresholds). Uniqueness: `|Im F| <= 1 + atan(1/V) + asin(delta_a) < pi` on H_V, so two
solutions have equal F, and `|F(v) - F(v') - (v - v')| <= q |v - v'|` on the convex H_V
forces `v = v'`. `F' = 1 + g' != 0` gives holomorphy. Nothing missing.

## R2. Lemma L: the contour, and the majorants

**Geometry.** The integrand `v^s e^(av - pi e^v) alpha(v)` is holomorphic on
`{Re v > 0, |Im v| < pi/2}` (the theta series in alpha converges there because
`Re e^v > 0`), and `|Im v_0| <= b < 0.29 < pi/2`, so `[0, inf)` deforms to
`[0, w_1]` followed by `v_0 + t`, `t >= -R/2`, with doubly exponential decay at the far
end. On the line, `phi(v_0 + t) - phi(v_0) = -s g(t/v_0) - P k(t)` exactly. The argument
bound is sharper than stated: `g(t/v_0) = t^2 int_0^1 (1-u)/(v_0 + u t)^2 du`, so every
integrand has argument `-2 arg(v_0 + u t)`, and `Re(v_0 + u t) >= R/2` gives
`|arg g| <= 2 atan(2b/R)` with all contributions on one side. With (i),
`Re(s g) >= 0` on both tails. Correct.

**Majorants.** Rederived with my own intermediate bounds (`Re Psi >= p cos b` instead of
phase 2's `p cos b - a/R`; `|Psi| <= p(1 + (1 + a/p)/R)`), and `C_rho` reproduces:

| x_0 | R_min | b | q | C_rho (this review) | C_rho (claimed) | lambda (this review) | lambda (claimed) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 789 702 | 10.2073 | 0.28246 | 0.10543 | 2.02881 | 2.029 | 6.9774e-3 | 6.978e-3 |
| 14 237 025 | 12.8799 | 0.27533 | 0.08227 | 1.98468 | 1.985 | 1.7892e-3 | 1.790e-3 |
| 9.91e33 | 72.9895 | 0.25623 | 0.01384 | 1.88761 | 1.888 | 1.5061e-16 | 1.507e-16 |
| 5.65e35 | 76.9800 | 0.25604 | 0.01312 | 1.88672 | 1.887 | 2.0471e-17 | 2.048e-17 |

The leading part is `(8/3) e^(1/2)/(sqrt(2 pi) cos^2 b) = 1.874` at b = 0.256: the 16/6
is `int |t|^3 e^(-c t^2) dt = 1/c^2` at `c = Re Psi/4`. The other four pieces times
`sqrt(p)` are below `10^-3700` at the smallest threshold (log10 of each: -4438, -5281,
-3778, -2.1e5). Each factor of the `rho_3` majorant decreases in R on `[R_min, inf)`
(`sqrt(R^2 + b^2)/(R - T)^3`, `1 + a/p`, `1/R`, and `sqrt(p) a_1`, which falls like
`e^(-R/2)`), so evaluating at R_min is valid.

**Measured, independently.** Quadrature of I(s) on a contour tilted by slope 0.1 (not
the lemma's), at `x = 789 702, 1e6, 1e8` and five points of each disk boundary: the worst
`|varrho|` is 1.29e-5 at x_0 = 789 702 (z = 0.75 x_0), against lambda = 6.98e-3, slack 540;
`|varrho| sqrt(p)` is 3e-3 to 4e-3, so the true remainder is `O(1/p)` and the lemma's
`O(1/sqrt(p))` is the price of bounding the cubic Taylor term without its odd cancellation.

## R3. Lemma R

- **Uniformity on `|z - x| <= x/4`.** For such z, `|arg z| <= asin(1/4) = theta` and
  `|2z| >= 1.5 x >= 1.5 x_0 = 2 x_0 (1 - rho)`, which is exactly Lemma V's range and
  Lemma L's `|arg s| <= theta`. Lemma L's majorant depends on s only through
  `R = Re v_0 >= R_min`, so one lambda serves the whole union of disks. The union is the
  sector `|arg z| <= theta` truncated by the first disk's arc (each disk is tangent to the
  two rays), which is convex. Correct.
- **The branch.** `G(2z) + log(1 + varrho(2z))` is holomorphic on the union (v_0
  holomorphic, `Re Psi > 0`, `|varrho| < 1`), real on the axis, and differs from any
  logarithm of `M_z/(2 pi^2 4^(-2z-1))` by a constant multiple of `2 pi i`, which the
  real axis fixes at 0. So it is the branch Holland names. Correct.
- **The rate.** `|R| <= -log(1 - C_rho/sqrt(pi e^R))` and `pi e^R ~ |2z|/log|2z|`, so
  `|z|^(-1/2) (log |z|)^(1/2)`: "`-1/2 + eps`" is right.
- **"Only `|R| < 1` enters."** True in substance, loosely worded. What enters is an explicit
  finite bound `lambda` on the disk: Cauchy on radius n/8 turns it into
  `|R^(k)| <= k! lambda (8/n)^k`, which is `O(n^-k)` against main terms of order
  `n^-(k-1)/log n`, so the rate in `|z|` never matters. Lambda itself does enter the
  numbers, through the remainder part of every `H_k` enclosure:
  `k(k-1) 8^k lambda v_1/(2n)` is 0.031 for k = 5 at the (5s) threshold (3 percent of
  `Theta_5`) and below `1e-40` at the assisted thresholds. Neither changes a verdict.

## R4 and R5. Lemma D, and the targets

Lemma D(i) was rederived from scratch in sympy (`derive_F`): `F_k(0,0) = 1`, first-order
constants `-1, 0, 1/2, 5/6, 13/12, 77/60` for k = 2..7, `F_2(e, 0) = 1/(1+e)`. Lemma D(ii):
for `|z - n| <= n/8`, the disk of radius n/8 about z lies in `|zeta - n| <= n/4`, where
Lemma R holds with x = n >= x_0. The targets: `Delta^m h(n)` is the B-spline average of
`h^(m)(n + sigma)`, so `T_j` lies in the hull of `H_(j+2)` over `[0, (j+2)/n]`. This review
encloses `T_j - T_0` as one function of e (mean-value form of `F_(j+2) - F_2`), which keeps
the `t_j` radii near 5e-5 on a 1e-4 subinterval; without it the Krawczyk boxes on the top
(5a) subinterval are about 14 times wider. That is a property of enclosures, not of the lemma.

## R6 and R11. The matching systems

Both systems were checked against Holland's own equations on real data, which phase 2's
measurements (Newton on the same reduced system) could not do: at n = 1000 and 20 000,
with `h` from quadrature at 80 digits, the solution of the reduced system `Phi_j = 0`
satisfies Holland's (52), `q_k(A,B) q_k(C,D) = q_k` (D = n/2, k = 0..2 for the five model;
D free, k = 0..3 for the six model), to 1e-76, and a direct solve of (52) agrees with it to
1e-62. The parametric Krawczyk test (my implementation: float Newton at the parameter
midpoints, inverse at the midpoint, strict inclusion `K(B)` inside `B`, parameter balls for
`eps, t_j, w_b, 1/n`) passes on every subinterval of all four covers; where a 5e-4
subinterval fails near `e_1 = 0` in (6s), its halves pass. The positivity conditions need
`eps > 0`, which the ball touching `e_1 = 0` cannot show; they hold because `e_1 > 0` at every
finite n, and `C - D >= d` is checked as `T_0 g_c/w_C >= (d/n) v_1(2n)`, which uses Lemma
W(ii)'s second clause. `effective.py` does the same (its `kappa`).

## R7. Lemma G and `C_loc`

Rederived: (78) as an exact identity (sympy), the off-diagonal inequalities
`(k + beta)(k + H) <= (2k+H)^2 - 1` and `(k + H)(H + 1) <= (2k+H)^2 - 1` for k >= 1, both
diagonal cases (`U >= 2V`: `a_k - V in [0, (d-1)(2U+V)/H]`; `U < 2V`: the second form), and
Gershgorin on the symmetric tridiagonal matrix, whose eigenvalues match the roots of
`2F1(-d, U; V; y/U)` to 2e-37 at (5405, 400, 10) and (900, 400, 12). The assembly through
Lemma 7.1 (MSS Theorem 1.13, an input) gives
`|y - B| <= max(2 beta_1 (1 - eta_-) + B eta_-, (abar_1 + 2 beta_1)(1 + eta_+) + B eta_+)`.
The reason C_loc tends to 2 rather than to Holland's `2(1 + sqrt 2)`: the second factor is
nearly degenerate, `C - D ~ n/(24 L)`, so its spread is `sqrt(d (C - D))`, not
`sqrt(d D)`. Max over the (5a) cover: **2.09318** (claimed 2.094). One remark: written
naively, `(1/w_A)/(1/w_A - delta - iota)` counts the box of w_A twice; this review's first
draft did that with wider boxes and got C_loc = 2.127 and `a + b + theta = 1.010` on the top
(5a) subinterval. Both codes now write the ratio as `1/(1 - (delta + iota) w_A)`.

## R8. Lemma 9.1-E and `K_6 = 2.53`

Every identity checked exactly in rational arithmetic at d = 3, 5, 6: Holland's
factorisation (86), the expansion of V_m with `beta_m`, `gamma_m`, and (90). The backward
substitution from `U_(d+1) = 0` gives `|U_m| <= eps_p c_V M r^(m+2)/(D(1 - r/D))` by
induction (the fixed point of `Y = (eps_p c_V M + Y r)/D`). The bounds behind `a`, `b`,
`theta` and `c_V` were rederived term by term (`|m + (d-1-2m) y/A| <= d(1 + y/A)`,
`|beta_m| <= A(d+1) + 5d^2 + 4d + 1`, `|gamma_m| <= (d^2/4)(d + A)`). The closing argument
needs only `a + b + theta < 1`: if `M > 1` its maximum sits at some k >= 2 and
`M <= (a + b + theta) M`. Holland's 1/4 each is a special case. Max over the (5a) cover:
**0.99693** at `K_6 = 2.53`; at 2.52 the top subinterval gives 1.0015. (5s): 0.99709 at 2.82.

## R9. Lemma 8.1-E and `Theta_5 <= 1.034`

Signs rederived from (82), (83): `psi^(4)(P + z) = -(6/n^4) omega(w_P) + r_4`, so
`n^4 E^(5)/(6 eps) = -H_5/T_0 + g_0 w_A^3 (1 + w_A y)^-4 + g_b <omega'>[w_B, w_b] - g_c <omega'>[w_C, 2] + rem`,
leading value `-1 + 8/3 - 8/3 = -1`. The remainder bound `|psi^(4)(y) + 6/y^4| <= 24/(Re y)^5`
holds for `Re y >= 5` (Euler-Maclaurin gives `12/(Re y)^5 + 60/(Re y)^6`); every `P + z`
here has real part above 3e5. Hermite-Genocchi: the convex hull of `{0, ..., 4, z}` lies in
the convex `Omega_r`, and `|z - j| <= d + 2r` there, so `C_E = T_0 Theta_5 (...)^5/10` as
stated. Max over (5a): **1.03384** (claimed 1.034); (5s): 1.5520 (claimed 1.571).

## R10. Assembly and Lemma W

`sup |c_F - 1| < 16` from `|E| < log 17` and `|e^E - 1| <= e^|E| - 1`; Proposition 2.2's
proof needs exactly `eps sum_(k>=5) 2^-k < 1`. Lemma W reproved: (i)
`v_1' = v_1/(n(1 + v_1) + a v_1^2/2)` and `1 + v_1 <= log(n + 2) - 1.03` for n >= 1000 (the
last step needs n >= 618); (ii) the logarithmic derivatives `-(2/5)(1 - 1/log(n+2))/n` and
`v_1'/v_1 <= 1/(5.88 n)`; (iii) the `0.715/(n log(d_max + 2))` term. `K_req` is formed per
subinterval and then maximised, not assembled from separate maxima. Correct.

## R12. Lemmas A to C with R2's hypotheses

Lemma A (`p^(k)/p = k! e_k(1/(y - y_j))`, Maclaurin, and the critical-point balance
`1/delta_1 <= (2 + H_d)/g`) and Lemma B (`d/R <= 32d/(13B) = 2.4615 d/B`,
`(P R' - P' R)/(2 R^2) <= 2.001 B/(2 (13B/32)^2) = 6.062/B`) were rederived; so was the
gap `(1 - eta) g_1/3` from Lemma C and the zero window `[(B/2)(1 - eta), (3B/2)(1 + eta)]`.
MFMP Proposition 2.17 reads exactly `lmesh(p ⊠ q) >= lmesh(p)` for `p, q in P(R>0)`, and
Holland's convolution is the reciprocal form of theirs, under which lmesh is invariant.
`H_d <= log(d + 2) + 0.6607` holds for every d >= 1 (from `H_d < log d + gamma + 1/(2d)`),
so `c_H = 3 + 5.9821/log(d_min + 2)`. All five conditions (`A >= 8B`, `B >= 256d`,
`C >= D + d`, `D >= 32d`, `D > 64d`) hold on every subinterval of both six-coefficient covers.

## R13. `Theta_6`, and a factor 1.95 in K'

The leading value `1 - 25/24 = -1/24` (Simpson's error on `5t^4`) and the signs were
rederived. Phase 2 encloses `<omega_5'>` over `[w_B, w_C]` and `[w_D, w_b]` by the hull of
`omega_5'` on the interval, which is valid but wide: at the top of the (6a) cover the two
hulls add about 0.02 to the modulus, half of the 1/24 being bounded. The exact divided difference,
`(u_2^5 - u_1^5)/(w_2 - w_1) = sum_i u_2^i u_1^(4-i)/((1 + w_1 y)(1 + w_2 y))` with
`u = w/(1 + w y)`, gives `Theta_6 <= 0.0477` (6a) and 0.403 (6s), against 0.0661 and 0.538,
and `K'_req = 3.70e9` for (6a). So K' = 7.21e9 holds with a factor 1.95 to spare, and the same
chain supports about 3.7e9. This is an input for phase 3's doors, not a defect.

## R14. The small-n hand-off to GORTTW Corollary 1.3

The question was whether the arithmetic covers every (d, n) below the chain's range. It
does. Take (d, n) in the (5a) wedge. If d <= 9.36e20, Corollary 1.3 applies for every
n >= 0. If d > 9.36e20, then `n^3 log^2(n+2) >= 17 900 d^5 > 17 900 (9.36e20)^5`, so
`n > n_min = 1.2534e35 >= 12.647 x 9.91e33`, inside the chain. Equivalently, at the chain's
start the wedge allows only `d <= 2.016e20`. For (6a): `n_min = 1.0044e38 >= 177.77 x 5.65e35`,
and at the start `d <= 3.35e19`. Both sides of each comparison increase in n and in d, so
the single comparison is enough. The standalone variants need no hand-off: at
n_0 = 789 702 the (5s) wedge allows `d <= 0.9996 < 1`, and at n_0 = 14 237 025 the (6s)
wedge at d = 1 needs `n^4 log^2(n+2)/K' >= log^12 3 = 3.0913` but has 3.0877, so both
wedges are empty below their n_0. Two remarks: Corollary 1.3 gives real zeros, and the
statements (5a), (6a) correctly claim only hyperbolicity there; and the six-coefficient
chain handles d >= 6, so (6s) at d <= 5 rests on the model matching every coefficient
(P_F = p_F, simple positive zeros by Lemma C), which `effective.py`'s docstring says and
`EFFECTIVE.md` does not (D2).

## R15. The c = 1 remark

For d <= 9.36e20, Corollary 1.3 covers every n. For d > 9.36e20 and `n >= e^(d/2)`:
`n^3 log^2(n+2) > e^(3d/2) (d/2)^2`, and `e^(3d/2) >= 71 600 d^3` (the log of the ratio is
1.40e21 at d = 9.36e20 and increases), so the pair is in the (5a) wedge. Hence
`J^{d,n}` is hyperbolic for every d >= 1 and `n >= e^(d/2)`: c = 1 is admissible in GORTTW
Theorem 1.1 (v3), with (5a)'s grade. Correct; the remark needs nothing beyond (5a).

## P. The planted-weakening check, and what it does not see

The kill condition as worded, "a planted weakening of an explicit constant does not turn the
effectivity check red", is not met: phase 2's 44 constant plants all turn it red (its own test, green here), and this
review's own plants (K at 0.999 of K_req for (5a) and (6a), `K_6 = 2.52`, a standalone K
below the absorption, a chain start where `R_min < 10`) turn this reproduction red too.

What the check cannot see, by construction, is a wrong formula: it compares claims with a
recomputation from the same formulas, and a fault that makes a bound optimistic lowers the
recomputation, which a claimed upper bound then still covers. Phase 2 says this and leans on
its measurements. Their reach was tested here by planting four formula faults into a copy of
`effective.py` in a temporary directory and running phase 2's own `test_effective.py` there
(`review_p2/plant_formula_faults.py`; nothing in the tree is edited):

| planted formula fault (each makes a bound unsoundly smaller) | phase 2 suite |
| --- | --- |
| none (control) | green, 36 of 36 pass |
| Lemma L: the cubic Taylor constant 8/3 replaced by 8/15 (C_rho 5 times too small) | **green, 36 of 36 pass** |
| Lemma L: 8/3 replaced by 8/30 (C_rho 10 times too small) | red, 1 failure (`slack > 100` threshold of the Laplace measurement) |
| Lemma D(ii): Cauchy radius n/4 where only n/8 is available (remainders `2^k` too small) | **green, 36 of 36 pass** |
| Lemma B: Sturm constants 2.47, 6.07 replaced by 0.247, 0.607 (r 3.2 times too small) | **green, 36 of 36 pass** |

So the steps whose formulas no phase 2 test pins are: Lemma L below a factor of about 8 (the
quadrature slack is 785, and the one test that reacts at 10x does so through a `slack > 100`
threshold); the Cauchy constant of Lemma D(ii) entirely (no measurement sees a remainder of
order lambda); Lemmas A to C up to the measured looseness of 36 to 44; and, by extension,
Lemma W, `c_H` and the psi remainders, which are checked only on samples or not at all.
This review rederived every one of those steps by hand (R2, R3, R4, R10, R12) and found them
correct, so no constant changes. The finding is about what section 8 of `EFFECTIVE.md` and
section 18 of `RESULTS.md` may claim for the checks: a green suite attests to the constants
against their formulas, and to a subset of the formulas against measurement; it does not
attest to the derivation.

## D. Documentation gaps (none changes a number)

- **D1.** `EFFECTIVE.md` Lemma W(ii) defines the six-coefficient `d_max` with `log^12 3`;
  `effective.py` uses `log^12(9.36e20 + 3)` for (6a), which is also valid because that chain
  only needs d > 9.36e20. Question: should Lemma W(ii) state both?
- **D2.** `EFFECTIVE.md` section 6 does not say how (6s) handles d <= 5; the code's docstring
  does (the model matches every coefficient). Question: add the sentence?
- **D3.** `RESULTS.md` section 18 says formula-level faults "are caught by independent
  measurements"; `EFFECTIVE.md` section 8 adds "by as much as their slack", but its table
  lists no step as uncovered. Item P names the uncovered steps. Question: add them to that
  table, and soften the sentence in section 18?

## Reproduce

```bash
.venv/bin/python hunts/jensen_wedge/review_p2/reproduce_p2.py               # about 2 min, writes results_review_p2.json
.venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/review_p2/test_review_p2.py   # 20 tests, about 2 min
.venv/bin/python hunts/jensen_wedge/review_p2/plant_formula_faults.py       # about 5 min, writes plants_review_p2.json
```
