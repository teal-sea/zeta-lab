# jensen_wedge: explicit constants for both wedges (phase 2, MISSION Q2, 2026-10-19)

**Nothing here bears on RH.** Every wedge of this shape leaves out n = 0, which is RH
itself (`MISSION.md`, "What success would mean"). This file makes the constants of
Holland's wedge (arXiv:2608.08682v1, Theorem 1.1) and of the hunt's six-coefficient wedge
(`RESULTS.md` section 12, `H1_H3.md`) explicit. **Grade: derivation, self-reviewed, not
reviewed by an independent session, not a theorem.** Every numeric step is an enclosure in
Arb ball arithmetic (`effective.py`, python-flint behind `zeta.rigor.BACKEND`); that makes
each number a bound, it does not review the derivation. A composite claim takes the grade of
its weakest step. Novelty: `NOVELTY.md` (claim C) found no explicit value of Holland's K or
of any constant of a wedge at exponent 3/5 or 2/3 in the searched set; that search is about
the searched set only.

*Grade, 2026-10-19 (phase 3):* `REVIEW_PHASE2.md` reviewed this file once, independently,
reproducing all four constants with its own code, and broke no step. The grade is now:
derivation, self-reviewed and reviewed once by an independent session, not a theorem,
pending external review. The paragraph above is kept as written.

## 0. The constants

| statement | explicit constant | the chain covers | small n handled by |
| --- | --- | --- | --- |
| (5a) `n^3 log^2(n+2) >= K d^5` implies `J^{d,n}` hyperbolic | **K = 17 900** | n >= 9.91e33 | GORTTW Cor. 1.3 (every n when d <= 9.36e20) |
| (5s) `n^3 log^2(n+2) >= K d^5` implies d distinct negative zeros | **K = 9.10e19** | n >= 789 702 | the wedge is empty below 789 702 |
| (6a) `n^4 log^2(n+2) >= K' d^6 log^12(d+2)` implies `J^{d,n}` hyperbolic | **K' = 7.21e9** | n >= 5.65e35 | GORTTW Cor. 1.3 |
| (6s) `n^4 log^2(n+2) >= K' d^6 log^12(d+2)` implies d distinct negative zeros | **K' = 3.61e30** | n >= 14 237 025 | the wedge is empty below 14 237 025 |

In (5a) and (6a) the zeros are distinct and negative whenever d > 9.36e20; for smaller d,
GORTTW's corollary gives real zeros, which are negative because every coefficient
`gamma(n+j)` is positive, and does not state that they are simple. (5s) is Holland's
Theorem 1.1 with its constant explicit. (5a) and (5s) are the closer delta against Holland;
(6a) and (6s) rest in addition on sections 11 and 12 (reviewed once, `REVIEW_PHASE1.md`)
and on this file's explicit form of H1 (Lemma M6). `NOVELTY.md` found earlier unreviewed
deposits of the six-coefficient wedge itself (Savva, Zenodo 2026-09-03), so (6a), (6s) are
explicit constants for a wedge already in the literature, not a new wedge.

**A consequence, derived and unreviewed.** `NOVELTY.md` section 2.3 remarks that any proved
`K <= e^(1e21)` makes `c = 1` admissible in GORTTW Theorem 1.1: for d > 9.36e20 and
`n >= e^(d/2)`, `n^3 log^2(n+2) >= e^(3d/2)(d/2)^2 > 17 900 d^5`. With (5a), `J^{d,n}` is
hyperbolic for every `n >= e^(d/2)` and every d >= 1, with the grade of (5a).

## 1. Inputs, and what is replaced

Used as stated in the literature (none has a constant to make explicit): Holland's
Proposition 2.2 (`sup |c - 1| <= eps < 16`) and its six-point form (`RESULTS.md` 12.1,
`eps < 32`); his Jacobi matrix (75), (76) and the factorisation (86) (both re-checked
in `test_effective.py`, (86) in exact rationals); his (79) inside Lemma B; his Lemma 7.1 (Marcus,
Spielman and Srivastava, Theorem 1.13); Martinez-Finkelshtein, Morales and Perales,
Propositions 2.7 and 2.17; and, for (5a) and (6a) only, GORTTW Corollary 1.3, which rests on
Platt's verification of RH to height 3.06e10.

Replaced by explicit versions here: Holland's Proposition 4.1 and Lemma 4.2 (by Lemmas V,
L, D), his Lemmas 4.3 to 6.1 (by Lemma M5 with `D = n/2`), 7.3 (Lemma G), 8.1 (Lemma 8.1-E),
9.1 (Lemma 9.1-E) and section 10 (section 5.5). For the six-coefficient wedge, H1's
contraction (`H1_H3.md` Lemma C) is replaced by Lemma M6, which encloses the data instead of
measuring them. Holland's (P1) and (P2) of `H1_H3.md` are not used: the main term below has
its own saddle.

Five departures from Holland's route, each a small self-reviewed step: the main term `G`
(not his `G_0`), the choice `D = n/2` (not `B_J/2`), sharper Gershgorin rows in Lemma G,
the closing condition `a + b + theta < 1` in Lemma 9.1 (not each at most 1/4), and
`sup |E| < log 17` (so `|c - 1| < 16`) in place of his `sup |E| <= 1/2`.

## 2. The main term (`effective.py` section B)

With Titchmarsh's kernel `Phi_T(u) = sum_k (2 pi^2 k^4 e^(9u) - 3 pi k^2 e^(5u)) exp(-pi k^2 e^(4u))`
and `v = 4u`, Holland's moment is, up to a constant factor,

    M_z = 2 pi^2 4^(-2z-1) I(2z),   I(s) = int_0^inf v^s e^(a v - pi e^v) alpha(v) dv,   a = 9/4,
    alpha(v) = sum_{k>=1} (k^4 - (3/(2 pi)) k^2 e^(-v)) e^(-pi (k^2 - 1) e^v).

So `h(z) := log M_z = const - (2z + 1) log 4 + log I(2z)`; only `h^(k)`, `k >= 2`, enters.
Measured: the second differences of this `h` agree with the tree's exact gamma table to 35
digits at n = 100 and 400.

**The saddle.** For complex s, `v_0(s)` solves `s/v_0 + a = pi e^(v_0)`. Put `e := 1/v_0`,
`m := 1/(pi e^(v_0))`, `Q := 1 + e - a e m`. Then exactly
`s = (1 - a m)/(e m)`, `Psi := -phi_s''(v_0) = s/v_0^2 + s/v_0 + a = Q/m`, and
`dv_0/ds = 1/(v_0 Psi) = e m/Q`. The main term is
`G(s) := s log v_0 + a v_0 - pi e^(v_0) + (1/2) log(2 pi/Psi)`.

> **Lemma D(i).** For k >= 2, `G^(k)(s) = (-1)^k (k-2)! e s^(-(k-1)) F_k(e, m)`, with
> `F_k = N_k(e, m)/(c_k (4 + 4e - 9em)^(2k-2))` an explicit rational function with exact
> rational coefficients, `F_k(0, 0) = 1`, and `dF_k/de (0, 0) = H_(k-2) - 1`
> (`F_2(e, 0) = 1/(1 + e)`).

*Proof.* By the envelope identity `d/ds phi_s(v_0(s)) = log v_0`, `G'(s) = log v_0 - Psi'/(2 Psi)`,
and on functions of (e, m), `d/ds = (e m/Q)(-e^2 d/de - m d/dm)` because `de/dv_0 = -e^2` and
`dm/dv_0 = -m`. Differentiating k - 1 times stays inside rational functions of (e, m)
times powers of `1/s = e m/(1 - a m)`. `derive_F` does this in sympy (5 s for k <= 7). QED.
**Status: derivation, self-reviewed; the coefficients are exact.** The first-order constants
`-1, 0, 1/2, 5/6, 13/12, 77/60` (k = 2..7) are `H1_H3.md` Lemma S(c)'s, reached here
independently with `v_0` as the scale, and `REVIEW_H1_H3.md` found the same constants for
Holland's `G_0` symbolically.

## 3. The saddle and the Laplace remainder (`effective.py` section C)

Fix `rho = 1/4`, `T = 1/2`, a threshold `x_0`, and put `theta = arcsin rho`,
`V := v_1(2 x_0 (1 - rho)) - 1` with `v_1(s)` the real saddle, `delta_a = (a/pi) e^(-V)`,
`q := 1/V + delta_a/(1 - delta_a)`, `b := theta/(1 - q)`, `R_min := V + 1 - b`.

> **Lemma V.** Let `|arg s| <= theta` and `|s| >= 2 x_0 (1 - rho)`. On the half-strip
> `H_V = {Re v >= V, |Im v| <= 1}` the equation `v(pi e^v - a) = s` has exactly one solution
> `v_0(s)`; `|v_0(s) - v_1(|s|)| <= |arg s|/(1 - q)`, so `Re v_0 >= R_min`, `|Im v_0| <= b`;
> more generally `|v_0(s) - v_1(s_1)| <= |log(s/s_1)|/(1 - q)` for real `s_1` in range;
> `v_0` is holomorphic in s.

*Proof.* `F(v) := log(v (pi e^v - a)) = v + g(v)`, `g = log v + log pi + log(1 - (a/pi) e^(-v))`,
has `|g'| <= q` on `H_V`. The map `v -> v_1 + log(s/s_1) - (g(v) - g(v_1))` sends the disk of
radius `|log(s/s_1)|/(1 - q)` about `v_1 = v_1(s_1)` into itself and contracts; its fixed
point solves `F(v) = log s`. Uniqueness on `H_V`: `|Im F| < pi` there, so two solutions
would have equal F, and `|F(v) - F(v') - (v - v')| <= q |v - v'|` forces `v = v'`. QED.
**Status: derivation, self-reviewed.**

> **Lemma L.** If `Re v_0 =: R >= R_min >= 10`, `|Im v_0| <= b`, `|arg s| <= theta` and the
> conditions (i) `theta + 2 atan(2b/R_min) <= pi/2`, (ii) `M_3 T/6 <= Re Psi/4` hold, then
> `I(s) = e^(phi_s(v_0)) (2 pi/Psi)^(1/2) (1 + varrho)` with
> `|varrho| <= C_rho/sqrt(pi e^(R_min))`, `C_rho` the sum of five explicit majorants below.

*Proof.* Deform `[0, inf)` to the segment `[0, w_1]`, `w_1 = R/2 + i Im v_0`, followed by the
horizontal line `v_0 + t`, `t >= -R/2` (the integrand is holomorphic for `Re v > 0`,
`|Im v| < pi/2`, and decays doubly exponentially along every horizontal line there). With
`P = pi e^(v_0) = s/v_0 + a`, along the line exactly
`phi(v_0 + t) - phi(v_0) = -s g(t/v_0) - P k(t)`, `g(y) = y - log(1 + y)`, `k(t) = e^t - 1 - t`.
Writing `g(y) = y^2 int_0^1 (1 - u)/(1 + u y)^2 du` gives `|arg g(t/v_0)| <= 2 atan(2b/R)` for
`-R/2 <= t`, so by (i) `Re[s g] >= 0` and `Re Delta <= -Re P k(t)` on both tails. Pieces,
each times `sqrt(p)`, `p = pi e^R`:

- `rho_3` (|t| <= T): Taylor with `|r(t)| <= M_3 |t|^3/6`, `M_3 <= 2|s|/(R - T)^3 + p e^T`; by
  (ii) `|e^(-Psi t^2/2 + r)| <= e^(-Re Psi t^2/4)`, so the error is at most
  `(1 + a_1)(16 M_3/6)/(Re Psi)^2 + a_1 (2 pi/Re Psi)^(1/2)`, `a_1` bounding `|alpha - 1|` there;
- `rho_G`: the Gaussian beyond `|t| = T`, `2 e^(-Re Psi T^2/2)/(Re Psi T)`;
- `rho_4` (t >= T): `(1 + a_1) e^(-Re P k(T))/(Re P (e^T - 1))`, k convex;
- `rho_2` (-R/2 <= t <= -T): length times `e^(-Re P k(-T))`;
- `rho_1` (the segment): `|v^s| <= |v|^(Re s) e^(|Im s| |arg v|)`, `|e^(-pi e^v) alpha(v)| <= A_1`,
  and the exponent `p [-cos(theta) lw R (1 - a/p) + 3 b sin(theta)(1 + b^2/(2R^2))(1 + a/p) + 1] - aR/2`
  with `lw = log 2 - (1/2) log(1 + 4b^2/R^2)`; the bracket is negative and decreasing.

Each majorant times `sqrt(p)` is a product of factors that decrease in R on `[R_min, inf)`,
so its value at `R_min` bounds it (`effective.py` comments name the factor for each). QED.
**Status: derivation, self-reviewed.** At every threshold used, `rho_3` is the only piece
above `1e-300`: `C_rho = 1.888` (x_0 = 9.9e33) to `2.029` (x_0 = 7.9e5).

> **Lemma R (an explicit form of Holland's Proposition 4.1).** For real `x >= x_0` and
> `|z - x| <= x/4`: `h(z) = const - (2z + 1) log 4 + G(2z) + R(z)`, h the branch real on the
> positive axis, and `|R(z)| <= lambda(x_0) := -log(1 - C_rho/sqrt(pi e^(R_min)))`.

The union of the disks is convex, `G` and `log(1 + varrho)` are holomorphic and real on the
axis, so the right side is the branch Holland names. **Compared with his (18), (19):** the
remainder decays like `|z|^(-1/2 + eps)` here, not `|z|^(-1 + eps_0)`; only `|R| < 1`
enters below, through Cauchy's inequality, so the weaker rate costs nothing that matters.
Values: `lambda = 6.98e-3` (x_0 = 789 702), `1.79e-3` (14 237 025), `1.51e-16` (9.91e33),
`2.05e-17` (5.65e35).

> **Lemma D(ii).** For `|z - n| <= n/8`, n >= x_0:
> `h^(k)(z) = (-1)^k 2 (k-2)!/(z^(k-1) v_0(2z)) F_k(1/v_0(2z), 1/(pi e^(v_0(2z)))) + R^(k)(z)`,
> `|R^(k)(z)| <= k! lambda/(n/8)^k`.

Cauchy on the disk of radius n/8 about z, inside `|zeta - n| <= n/4`. **Measured:** route B
of phase 0 (Laplace series and numerical differentiation, no quadrature) gives `h^(k)`,
k = 2..7, inside these enclosures at n = 1e8, 1e12, 1e20 (relative radii 1e-16 to 3e-4).

## 4. The cover and the targets (`effective.py` section D)

The parameter is `e_1 = 1/v_1(2n)`. `[0, e_1(n_0)]` is covered by closed subintervals of
length 1e-4 or 5e-4 (129 to 186 per variant); the one containing 0 is n = infinity. Every
quantity is enclosed for all n of a subinterval at once, using the enclosures of n, `1/n`,
`m <= 1/(pi e^(v_lo))`, and `n e_1` (increasing in n).

> **Lemma W (monotonicity used to bound a subinterval by its end).** For n >= 1000:
> (i) `log(n+2)/v_1(2n)` decreases; (ii) `d_max(n)/n` decreases, where
> `d_max(n)^5 = n^3 log^2(n+2)/K` (five) or `d_max(n)^6 log^12 3 = n^4 log^2(n+2)/K'` (six), and
> so does `(d_max(n)/n) v_1(2n)`; (iii) (six) `sqrt(d_max(n)/n) log(d_max(n) + 2)` decreases
> once `d_max(n) > 150`.

*Proof.* (i) `v_1' = v_1/(n(1 + v_1) + a v_1^2/2)`, so the claim is
`n(1 + v_1) + a v_1^2/2 < (n + 2) log(n + 2)`; for n >= 1000, `v_1 >= 4.88` and
`pi e^(v_1) = 2n/v_1 + a` give `1 + v_1 <= log(0.355 n + 1.95) <= log(n+2) - 1.03`, and
`a v_1^2/2 < 1.03 n`. (ii) The logarithmic derivative of `d_max/n` is at most
`-(2/5)(1 - 1/6.91)/n` (five) or `-(1/3)(1 - 1/6.91)/n` (six), and `v_1'/v_1 <= 1/(5.88 n)` is
smaller. (iii) With `delta = d_max/n`, `|delta'/delta| >= 0.2851/n` and
`d_max'/d_max <= 0.715/n` for n >= 1000, so the logarithmic derivative is at most
`-0.1426/n + 0.715/(n log(d_max + 2))`, negative once `log(d_max + 2) > 5.02`. QED. **Status: derivation, self-reviewed;** `n_lo >= 1000` is checked on every subinterval.

*Note, 2026-10-19 (phase 3, `REVIEW_PHASE2.md` D1):* for (6a), `effective.py` defines
`d_max(n)^6 log^12(9.36e20 + 3) = n^4 log^2(n+2)/K'`, not with `log^12 3`. That is valid
because the (6a) chain handles only d > 9.36e20, where `log^12(d + 2)` is at least
`log^12(9.36e20 + 3)`; (6s) uses `log^12 3` as written. (ii) and (iii) hold for both
definitions: their proofs use only logarithmic derivatives, which a constant factor in
`d_max^6` does not change, and the `d_max > 150` clause is checked with the definition the
chain uses.

**Targets.** `tau_j = (-1)^j n^(j+1)/j! Delta^(j+2) h(n)` is the cube average of
`2 e_1 H_(j+2)(sigma/n)`, `H_k(y) := (-1)^k h^(k)(n(1+y)) n^(k-1)/(2 (k-2)! e_1)`, so
`T_j := tau_j/(2 e_1)` lies in the hull of `H_(j+2)` over `y in [0, (j+2)/n]`, and Lemma D(ii)
encloses it. **Measured:** route B's `tau_0..tau_3` lie inside these balls at n = 1e8, 1e12,
1e20. `eps := tau_0` and `t_j := tau_j/tau_0 - 1` (`t_0 = 0` exactly) are the data of both
matching systems.

## 5. Five coefficients (`effective.py` section E)

### 5.1 The model, D = n/2 (Lemma M5)

Holland fixes `D = B_J/2`, which needs his Jacobi fit (Lemmas 4.3 to 5.4). Any D within
relative `O(1/L)` of n/2 serves his Lemma 6.1, and this file fixes `D = n/2`: the model is
still his `F_j(A, B, C, D, S)` of eq. (4), and the data enter only through `tau_0..tau_2`.
With `w_P := n/P`, `w_b = n/(n + 1/2)`, `w_D = 2` and unknowns `X = (g0, gb, gc)`,

    w_A = eps g0,   w_B = w_b - eps gb,   w_C = 2 - eps gc,

matching `R_0..R_4` is exactly (`H1_H3.md` 4.1, with the signed gap set
`[0, w_A] u [w_B, w_b]` minus `[w_C, 2]`)

    Phi_j(X) := (1/eps)[U_j(w_A) + U_j(w_b) - U_j(w_B) + U_j(w_C) - U_j(2)] - (1 + t_j) = 0,   j = 0, 1, 2,

`U_j(w) = int_0^w u_j'`, `u_j'(t) = (j+1) t^j prod_{i<=j+1} (1 + i t/n)^(-1)`. The limit is
linear, `(g0 + gb - gc, 2gb - 4gc, 3gb - 12gc) = (1, 1, 1)`, with the single solution
`X* = (5/12, 2/3, 1/12)` and determinant -12; it reproduces Holland's `6/5, 1/3, 1/24`.

> **Lemma M5.** On every subinterval of every cover, the interval Krawczyk operator
> `K(B) = x - Y Phi(x) + (I - Y DPhi(B))(B - x)`, evaluated with every parameter
> (eps, `w_b`, `t_j`, `1/n`) as a ball, lies inside the box B. Hence for every n there the
> system has exactly one solution in B, and `A > B > 0`, `C > D > 0`.

`Phi` is enclosed exactly up to the factors `prod (1 + i t/n)^(-1) in [prod(1 + i t_max/n)^(-1), 1]`,
and `DPhi` has the closed form `(u_j'(w_A), u_j'(w_B), -u_j'(w_C))`. **Status: the Krawczyk
test is a theorem; its application here is ball arithmetic plus a self-reviewed reduction.**
**Measured:** an mpmath Newton solve of the same system with route B data lies inside the
box at n = 1e8, 1e12, 1e20 (box radii 3e-6, 3e-10, 8e-13).

### 5.2 Root localisation (Lemma G, replacing Holland's 7.3)

> **Lemma G.** Let `U >= V + d`, `V >= 32 d`, `H = U - d - 1`. The roots of
> `q_{U,V}(y) = 2F1(-d, U; V; y/U)` are the eigenvalues of Holland's Jacobi matrix (75), (76),
> whose diagonal satisfies `a_k - V in [0, (d-1)(2U + V)/H]` when `U >= 2V` and
> `a_k - V in [-2(d-1)|U - 2V|/H, V(d-1)/H]` when `U < 2V`, and whose off-diagonal satisfies
> `b_k <= (U/H) sqrt((d-1)(d + V - 2))` (U >= 2V) and `b_k <= (U/H) sqrt(d(d + V)(U - V)/H)`.

*Proof.* (78) gives the diagonal; for the off-diagonal, `(k + beta)(k + H) <= (2k + H)^2 - 1`
and `(k + H)(H + 1) <= (2k + H)^2 - 1` for k >= 1. Gershgorin. QED. Holland's `C_J = 8` comes
from cruder row sums; the bound here tends to `2 sqrt(Vd)`, which the extreme Hermite zero
shows is the right order. For the model (first factor `(A, B)`, second `(C, D)`,
`p_2(y) = q_{C,D}(D y)`) and his Lemma 7.1, every root and critical point y of `p_F` has
`|y - B| <= C_loc sqrt(Bd)`, `C_loc` an explicit ball (`localize5`); also checked on every
subinterval: (77) for both factors, `eta_- < 1`, and the two cases `A >= 2B`, `C < 2D`. (A
first draft stated the second diagonal bound for every U; `test_effective.py` caught it on
`U = 5405`, `V = 400`, and the case conditions were added.) **Measured:** at n = 1e12 the actual
roots and critical points give `max |y - B|/sqrt(Bd)` = 1.52 (d = 10) and 1.79 (d = 40),
against the bound 2.16.

### 5.3 Holland's Lemma 9.1 with explicit constants

His proof, line by line, with every constant kept. With `T_k = y^k p_F^(k)(y)/p_F(y)` at a
critical point, `M = max_k |T_k|/r^k`, `r = K_6 sqrt(Bd)`: (87) and backward substitution give
`|U_m| <= eps_p c_V M r^(m+2)/(D(1 - r/D))`, where `eps_p = (C - D)/C` and

    c_V = 1 + r/A + (2d+3)/A + (d+1)/r + (5d^2 + 4d + 1)/(A r) + d^2/(4 r^2) + d^3/(4 A r^2)

(from `|beta_m| <= A(d+1) + 5d^2 + 4d + 1`, `|gamma_m| <= (d^2/4)(d + A)`); then (90) gives
`|T_(m+2)|/r^(m+2) <= (a + b + theta) M` with

    a = (C_loc + sqrt(d/B)(1 + y_+/A))/((1 - y_+/A) K_6),   b = (1 + d/A)(y_+/B)/((1 - y_+/A) K_6^2),
    theta = (y_+/D) eps_p c_V/((1 - y_+/A)(1 - r/D)),        y_+ = B + C_loc sqrt(Bd).

> **Lemma 9.1-E.** If `a + b + theta < 1`, `y_+ < A` and `r < D`, then `|T_k| <= r^k` for
> 0 <= k <= d at every critical point.

*Proof.* `T_0 = 1`, `T_1 = 0`; if `M > 1` its maximum is at some k >= 2, where
`M <= (a + b + theta) M`. QED (Holland's argument; he asks each of a, b, theta to be at most
1/4, which forces `K_6` large). **Status: derivation, self-reviewed;** (86), (90) and the
expansion of `V_m` re-checked in exact rational arithmetic. Smallest `K_6` that closes on every subinterval:
**2.53** (assisted cover; 2.52 fails) and **2.82** (standalone; 2.81 fails), with
`a + b + theta <= 0.9970` and `0.9977`. **Measured:** the radius (6) actually needs at n = 1e12
is 1.14 (d = 10) and 1.24 (d = 40) times `sqrt(Bd)`.

### 5.4 Holland's Lemma 8.1 with explicit constants

With `psi^(4)(y) = -6/y^4 + r_4(y)`, `|r_4| <= 24/(Re y)^5`, and `omega(w) = w^4/(1 + w y)^4`,
`y = z/n`:

    E_F^(5)(z) n^4/(6 eps) = -H_5(y)/T_0 + g0 w_A^3 (1 + w_A y)^(-4) + gb <omega'>_[w_B, w_b] - gc <omega'>_[w_C, 2] + rem,

`<omega'>_I` the average of `omega'(t) = 4 t^3/(1 + t y)^5` over I (in the convex hull of its
range), `|rem| <= (4/(n eps)) sum_P w_P^5/(1 - |y| w_P)^5`. At leading order this is
`-1 + 8/3 - 8/3 = -1`. `Theta_5` bounds its modulus over `|y| <= zeta`,
`zeta = (d + 2r)/n <= 1/8`. Hermite-Genocchi on the convex `Omega_r` gives

> **Lemma 8.1-E.** `sup over Omega_r of |E_F| <= C_E d^(5/2)/(n^(3/2) v_1(2n))`,
> `C_E = T_0 Theta_5 (sqrt(d/n) + 2 K_6/sqrt(w_B))^5/10`.

`Theta_5 <= 1.034` (assisted) and `1.571` (standalone), against the leading value 1.
**Measured:** the actual defects `E_F(j) = log(R_j/R_j^F)`, 5 <= j <= d, at n = 1e12 reach
0.795 of the Hermite-Genocchi bound built from `Theta_5`.

### 5.5 Assembly

Proposition 2.2 needs `sup |c_F - 1| < 16`, and `|e^E - 1| <= e^|E| - 1`, so
`sup |E_F| < log 17` suffices. Under `n^3 log^2(n+2) >= K d^5`,
`d^(5/2)/n^(3/2) <= log(n+2)/sqrt(K)`, and Lemma W(i) gives

    K_req = (C_E max(log(n+2)/v_1(2n))/log 17)^2   on each subinterval;   K >= max K_req.

d <= 4 needs no multiplier: the model matches every coefficient. The values of d/n that
enter every constant come from the claimed K itself (Lemma W(ii)); `smallest_K` bisects to
the least self-consistent K. **Assisted:** `max K_req = 17 701`, claimed `K = 17 900`; the
wedge allows `d > 9.36e20` only for `n > n_min(K) = 12.6 n_cover`. **Standalone:**
`max K_req = 2.49e5`, and `K >= 789 702^3 log^2(789 704) = 9.08e19` makes the wedge empty below
the cover (Holland's section 10 device with `n_0` explicit); claimed `K = 9.10e19`.

## 6. Six coefficients (`effective.py` section F)

**Lemma M6 (H1 with enclosed data).** The four-parameter Pade system of `H1_H3.md` (4.2),
unknowns `(g0, gx, g1, x)`, passes the interval Krawczyk test on every subinterval of both
covers, so for every n there it has exactly one solution in the box, with
`0 < w_A < w_B < w_C < w_D < 1`. `d/dx` uses the exact difference quotient
`(j+1) gx P_odd(j-1, x, eps gx)`; enclosing it by `u_j''` over `[w_B, w_C]` instead made the
operator diverge from n of about 1e10 down. The test holds from n = 1.4e7 (H1_H3's analytic
Lemma C holds on measured data from 1e7). **Measured:** mpmath Newton solutions lie inside
the boxes at n = 1e8, 1e12, 1e20.

**Lemmas A to C with R2's hypotheses** (`RESULTS.md` 12.3 as corrected): checked on every
subinterval: `A >= 8B`, `B >= 256 d`, `C >= D + d`, `D >= 32 d`, `D > 64 d`. Then
`r = (9/(2 pi)) ((1 + eta)/(1 - eta)) (4 + 3 H_d) sqrt(B(2.47 d + 6.07))`, `eta = 8 sqrt(d/D)`,
and `4 + 3 H_d <= c_H log(d + 2)` with `c_H = 3 + 5.983/log(d_min + 2)`
(`H_d <= log(d + 2) + 0.6607`): `c_H = 5.878` for d >= 6, `3.124` for d > 9.36e20.

*Note, 2026-10-19 (phase 3, `REVIEW_PHASE2.md` D2):* the residual step handles d >= 6
only. For (6s) at d <= 5 the model matches every coefficient of `J^{d,n}` (`R_0..R_5`), so
the Jensen polynomial is the model itself up to the change of variable, and its d zeros are
distinct and negative by Lemmas B and C; the five conditions above are checked for every d
up to `d_max`, so they cover d <= 5. `chain6`'s docstring said this; now this file does too.

**The sixth-order residual, keeping the Simpson cancellation.** With
`psi^(5)(y) = 24/y^5 + r_5`, `|r_5| <= 120/(Re y)^6` (`H1_H3.md` 3.3, item 1) and
`omega_5(w) = w^5/(1 + w y)^5`:

    E_F^(6)(z) n^5/(24 eps) = H_6(y)/T_0 - [g0 w_A^4 (1 + w_A y)^(-5) + gx <omega_5'>_[w_B, w_C] + (g1 - beta_b) <omega_5'>_[w_D, w_b]] + rem,

leading value `1 - 25/24 = -1/24`. `Theta_6 <= 0.0661` (assisted) and `0.538` (standalone);
the triangle inequality on the same pieces would give about 2. *Note, 2026-10-19
(phase 3, `REVIEW_PHASE2.md` R13):* these are loose by a factor of about 1.4. The hull of
`omega_5'` over `[w_B, w_C]` and `[w_D, w_b]` is valid but wide; the exact divided
difference gives `0.0477` and `0.403`, and (6a) would close at `K' = 3.70e9`. The claims are
kept, with that margin, and `effective.py` keeps the hull. Hermite-Genocchi with six
nodes, Proposition 2.2_6 (`sup |E| < log 33`), and
`d + 2r <= n sqrt(d/n) log(d + 2) [sqrt(d/n)/log(d_min + 2) + 2 rho_r sqrt(2.47 + 6.07/d_min)/sqrt(w_B)]`
give `sup |E_F| <= C_E d^3 log^6(d+2)/(n^2 v_1)` with `C_E = T_0 Theta_6 [..]^6/15`, and

    K'_req = (C_E max(log(n+2)/v_1)/log 33)^2.

**Assisted:** `max K'_req = 7.20e9`, claimed `K' = 7.21e9`, `n_min(K') = 178 n_cover`.
**Standalone:** `max K'_req = 1.48e16`, absorption
`14 237 025^4 log^2(14 237 027)/log^12 3 = 3.61e30`, claimed `K' = 3.61e30`.
**Measured:** at n = 1e12 the radius (6) needs is 0.82 (d = 10) and 0.89 (d = 40) times
`sqrt(Bd)`, and 12.3's r is 32 and 39 times it: K' carries about `36^12 = 5e18` of slack from
Lemmas A to C alone (`REVIEW_PHASE1.md` R5 measured the same looseness at n = 3200).
*Correction, 2026-10-19 (phase 3):* 32 and 39 are 12.3's r in units of `sqrt(Bd)`
(`results_effective.json`, `r_12_3_over_sqrt_Bd`), not in units of the need. Against the need
(0.815, 0.885) it is 39 and 44 times, so the slack is up to `44^12 = 5e19`, not `36^12 = 5e18`.
The sentence is kept as written; no constant changes.

## 7. The dependency chains

| constant | (5a) | (5s) | (6a) | (6s) |
| --- | --- | --- | --- | --- |
| cover: n_cover, subintervals | 9.91e33, 136 | 789 702, 186 | 5.65e35, 129 | 14 237 025, 149 |
| Lemma V: q, b | 0.0138, 0.2562 | 0.1054, 0.2825 | 0.0131, 0.2560 | 0.0823, 0.2753 |
| Lemma L: R_min, C_rho | 72.99, 1.888 | 10.21, 2.029 | 76.98, 1.887 | 12.88, 1.985 |
| Lemma R: lambda | 1.507e-16 | 6.978e-3 | 2.048e-17 | 1.790e-3 |
| Lemma G: C_loc | 2.094 | 2.220 | | |
| Lemma 9.1-E: K_6, a + b + theta | 2.53, 0.9970 | 2.82, 0.9977 | | |
| Lemma 8.1-E: Theta | 1.034 | 1.571 | 0.0661 | 0.538 |
| Lemmas A to C: bracket | | | 20.02 | 46.98 |
| C_E | 354.1 | 1121 | 2.794e5 | 3.466e8 |
| Lemma W: log(n+2)/v_1 | 1.065 | 1.263 | 1.062 | 1.228 |
| K_req (max over the cover) | 17 710 | 2.493e5 | 7.20e9 | 1.479e16 |
| threshold | n_min/n_cover >= 12.64 | absorption 9.082e19 | n_min/n_cover >= 177.8 | absorption 3.606e30 |
| **claimed K** | **17 900** | **9.10e19** | **7.21e9** | **3.61e30** |

All values are the claimed upper bounds of `effective.CLAIMS` (lower bound for n_min/n_cover),
each at or above its recomputation; `results_effective.json` has the recomputed balls.

## 8. The effectivity check and the kill condition

`effectivity_check(variant)` recomputes every constant above on every subinterval at the
claimed K (and K_6), and is green only if every claim covers its recomputation, every
condition of the chain holds, `K >= K_req`, and the threshold is consistent. **All four
variants are green.**

The MISSION's kill condition ("a planted weakening of an explicit constant does not turn the
effectivity check red"): `planted_weakenings` moves each claimed constant 0.1 percent past
its recomputation on the unsafe side, K to 0.999 of `K_req`, and `K_6` down by 0.01.
**44 of 44 plants turn the check red. The kill condition is not met.**

That check recomputes with the same formulas, so it cannot see a wrong formula. The
measurements beside it can, by as much as their slack; the tests plant formula faults and
require each to be caught:

| step | independent route | slack (bound/measured) | planted fault the tests require to be caught |
| --- | --- | --- | --- |
| Lemma L | quadrature of I(s) on another contour, n = 1e6 and 1e8, real and complex s | 785 to 6554 | `C_rho` divided by 1e4 |
| Lemma D | route B `h^(k)`, n = 1e8, 1e12, 1e20 | radius 1e-16 to 3e-4 | the first-order term of `F_5` removed |
| Lemmas M5, M6 | mpmath Newton on the exact systems | radius 1e-13 to 4e-4 | a 1e-3 shift in `t_1` |
| Lemma G | actual roots and critical points, n = 1e12 | 1.21 to 1.42 | `C_loc` halved |
| Lemma 9.1-E | actual derivative ratios | 2.27 to 2.47 | `K_6 = 1` |
| Lemma 8.1-E | actual `E_F(j)` | 1.26 | `Theta_5` halved |
| (75), (76), (86), (90), `V_m` | eigenvalues against polynomial roots (relative 1e-40); (86), (90) and the `V_m` expansion in exact rationals | exact | wrong sign of `eps_p`; Lemma G's second bound outside its case |

*Correction, 2026-10-19 (phase 3, `REVIEW_PHASE2.md` item P and D3):* the table lists the
plants phase 2 chose, and it names no step as uncovered. Three steps were: the review's
plants of a five times smaller `C_rho`, a Cauchy radius n/4 and Sturm constants divided by
10 each passed all 36 tests. Phase 3 checks those steps against their derivation, and the
suite replays the four review plants as source edits that must be rejected:

| step | check added in phase 3 | slack | review plant now rejected |
| --- | --- | --- | --- |
| Lemma L, the cubic piece | `(1/6) int abs(t)^3 e^(-t^2/4) dt = 8/3` by quadrature, and `C_rho >= k3 e^T/(sqrt(2 pi) cos^2 b)` at all four thresholds | 1.007 to 1.067 | 8/3 as 8/15, and as 8/30 |
| Lemma D(ii), the Cauchy part | the remainder ball, with `F_k` set to 0, is at least `k! lambda/((RHO - RHO_D) n)^k` normalised, k = 2..7, n = 1e8, 1e20; the n/4 circle about `n(1 + i/8)` leaves the sector holding every Lemma R disk | exact | radius n/4 |
| Lemma B, the Sturm constants | the factor the chain uses against the derived `(32/13) d + 2.001 (32/13)^2/2`, and the actual smallest gap of `2F1(-6, A; B; y/A)` at the chain's A, B (n = 2e7) against the gap bound it implies | 1.003 (constants), 1.75 (gap) | 2.47, 6.07 as 0.247, 0.607 |

Still not tested: Lemma W, `c_H` and the `psi` remainders of 5.4 and section 6 (samples
only, or none). The review rederived them by hand (R10, R12). The sentence above the table,
"the tests plant formula faults and require each to be caught", is kept as written.

## 9. What is not explicit, and what this does not show

- **Nothing in either chain is left non-explicit;** no step is graded attempt unresolved.
  The inputs of section 1 are statements without constants.
- **Grade.** Every lemma here is self-reviewed only. (6a), (6s) also take the grade of
  sections 11 and 12 (reviewed once) and of Lemma M6. Pending independent review, none of
  the four is a theorem. *(2026-10-19: reviewed once by an independent session,
  `REVIEW_PHASE2.md`, no step broken; still none of the four is a theorem, pending external
  review.)*
- **Where the constants are loose.** In the five-coefficient chain the binding step is
  `a + b + theta < 1` with `C_loc` near 2: `K_6 = 2.53` against a measured need of about
  1.2 at n = 1e12, and K scales like `K_6^10`, so up to `(2.53/1.24)^10 = 1.2e3` in K is
  this argument's, not the mathematics'. In the six-coefficient chain Lemmas A to C's radius
  is 36 to 44 times the need: up to about `5e18` in K'. *(2026-10-19: 39 and 44 times, up to `5e19`; see the
  correction in section 6.)* The standalone constants are the
  absorption `n_0^3 log^2 n_0` and `n_0^4 log^2 n_0/log^12 3`, set by where Lemma L
  (`R_min >= 10`) and Lemma M6 stop closing.
- **D = n/2.** K is a constant for Holland's statement, proved through his family with a
  different, equally convenient choice of D; it is not the constant of his exact model.
- **Not RH,** for the reason in the header.

## 10. Reproduce

```bash
.venv/bin/python hunts/jensen_wedge/effective.py --time-unit   # about 1 s
.venv/bin/python hunts/jensen_wedge/effective.py               # about 1 min, writes results_effective.json
.venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/test_effective.py
```
