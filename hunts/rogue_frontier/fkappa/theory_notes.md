# theory_notes.md, append-only working log (master generating function for C_{kappa,i})

Session date: 2026-08-17. Rules observed: no em dashes; the reserved word of
zeta/rigor.py appears nowhere in this file.

## Checkpoint 1: the collapse of the grand sum to an operator resolvent (derivation, pre-validation)

Notation. X = 2x. For i >= 3,

    C_{kappa,i} = 2^{i-1} [X^{i-1}] S(X) / i!,

where

    S(X) = sum_{l,k>=1} (-1)^{l+k} sum_{v in {1..kappa}^l, w in {1..kappa}^k}
           X^{|v|+|w|} (prod v_j!)(prod w_j!) [y^v z^w lam mu] Phi|_{t=1},

by the generating identity of closed_form.py (the (|v|+|w|+1)! sits outside
[X^N]: C(v,w) = prodfacs/(N+1)! [..]Phi, and 2^{i-1} x^i = (1/2)(2x)^{N+1}).
So G_kappa(x) = x - 4x^2 + (1/2) sum_{N>=2} B_N (2x)^{N+1}/(N+1)!, with
B_N = [X^N] S(X). S is the Borel-type preimage of G; if B_N ~ N! r^N then the
radius of G_kappa is 1/(2r).

Step 1 (marker extraction). With L = sum_{j,j'} log phi(y_j, z_{j'}; c_{jj'}),
phi(y,z;c) = (y+c)(z+c)/(c(y+z+c)), c_{jj'} = t - lam[j=l] - mu[j'=k]:

    [lam mu] Phi |_{t=1} = Phi_0 * [ (sum_{j'} psi(y_l, z_{j'}))
                                      (sum_j psi(y_j, z_k))
                                     + psi2(y_l, z_k) ],
    Phi_0 = prod_{j,j'} phi(y_j, z_{j'}; 1),
    psi  = d/dc log phi |_{c=1},   psi2 = d^2/dc^2 log phi |_{c=1}.

Step 2 (letters). Only -log(y+z+c) couples y to z, so at y=z=0, c=1:

    d^m/dy^m d^n/dz^n log phi |_0 = (-1)^{m+n} (m+n-1)!    (m,n >= 1),

and each d/dc shifts the index by one:

    d^m/dy^m log phi|_{y=0} = mu_m(z),  d^m/dy^m psi|_{y=0} = mu_{m+1}(z),
    d^m/dy^m psi2|_{y=0} = mu_{m+2}(z),
    mu_r(z) = (-1)^{r-1} (r-1)! (1 - (z+1)^{-r}),
    d^n/dz^n mu_r |_{z=0} = (-1)^{r+n} (r+n-1)! =: e(r,n).

All letters vanish at z=0. The whole grand sum is governed by the single
kernel e(r,n) = (-1)^{r+n}(r+n-1)!, which depends only on r+n. Note
(r+n-1)! = int_0^inf t^{r+n-1} e^{-t} dt makes the coupling rank one under a
t-integral; this is the continuous form (kept for later, checkpoint on the
asymptotics).

Step 3 (y-side geometric collapse). Fix the z-tuple. Write P(y) =
sum_{j'} log phi(y, z_{j'}; 1), Q(y) = sum_{j'} psi(y, z_{j'}). Each y-block
is extracted by T_y f = sum_{a=1}^{kappa} X^a f^(a)(0) (that is a! X^a [y^a]).
Since Phi_0 = prod_j e^{P(y_j)}, extraction factorizes per block. With

    A  = T[e^P],  Cq = T[e^P Q],  B = T[e^P psi(., z_k)],
    Dm = T[e^P Q psi(., z_k)],    D2 = T[e^P psi2(., z_k)],

the sum over l >= 1 of (-1)^l with the marked block last gives exactly

    F := sum_l (-1)^l (block products) = -(Dm + D2)/(1+A) + Cq B/(1+A)^2

(geometric series: sum (-1)^l A^{l-1} = -1/(1+A); the cross term Q(y_l) *
sum_{j<l} psi(y_j,z_k) contributes (l-1) B Cq A^{l-2}, summing to
+ B Cq/(1+A)^2). All five ingredients are explicit polynomials (X-graded) in
the z-side power sums

    s_r = sum_{j'} mu_r(z_{j'})   (r = 1..kappa+1 needed)

and the marked letters m_r = mu_r(z_k) (r = 2..kappa+2), via complete Bell
polynomials: A = sum_a X^a Bell_a(s_1..s_a), Cq = sum_a X^a sum_r C(a,r)
Bell_{a-r}(s) s_{r+1}, B likewise with m_{r+1}, D2 with m_{r+2}, and Dm the
double-product rule with s_{r+1} m_{r'+1}. F is linear in the marks m_r.

Step 4 (z-side operator resolvent). The z-blocks enter F only through the
sums s_r (all blocks) and the marks (block k). Every letter vanishes at z=0,
so the T_z extraction of each unmarked block acts on F as the SAME
constant-coefficient differential operator in the s-variables,

    D_u = sum_{n=1}^{kappa} X^n n! [eps^n] ( shift s_r -> s_r + jet_r(eps) ),
    jet_r(eps) = sum_{n>=1} e(r,n) eps^n / n!,

and the marked block acts as D_M (same substitution, also shifting the marks
m_r by jet_r(eps)). These operators commute (constant coefficients). The sum
over k >= 1 of (-1)^k with k-1 unmarked blocks is a Neumann series:

    S(X) = - [ (1 + D_u)^{-1} g ] (s=0),    g := (D_M F)|_{m=0},

X-adically convergent since D_u = O(X). Since F is linear in the marks,

    g = X sum_r e(r,1) F_r
      + X^2 [ sum_r e(r,2) F_r + 2 sum_r e(r,1) (grad_jet F_r) ] + ...
      (kappa terms; F = sum_r F_r m_r, grad_jet = sum_r e(r,1) d/ds_r).

For kappa = 2 explicitly (s = (s1,s2,s3) = (Sum mu_1, mu_2, mu_3), marks
(m2,m3,m4)):

    A  = X s1 + X^2 (s1^2 + s2)
    Cq = X s2 + X^2 (s3 + 2 s1 s2)
    B  = X m2 + X^2 (m3 + 2 s1 m2)
    Dm = 2 X^2 s2 m2
    D2 = X m3 + X^2 (m4 + 2 s1 m3)

    F2 = -2X^2 s2/(1+A) + Cq (X + 2X^2 s1)/(1+A)^2      (coeff of m2)
    F3 = -(X + 2X^2 s1)/(1+A) + Cq X^2/(1+A)^2          (coeff of m3)
    F4 = -X^2/(1+A)                                     (coeff of m4)

    e(2,1)=-2, e(3,1)=6, e(4,1)=-24, e(2,2)=6, e(3,2)=-24, e(4,2)=120,
    grad_jet = d/ds1 - 2 d/ds2 + 6 d/ds3   (e(1,1), e(2,1), e(3,1))

    g = X (-2 F2 + 6 F3 - 24 F4)
      + X^2 ( 6 F2 - 24 F3 + 120 F4 + 2 grad_jet(-2 F2 + 6 F3 - 24 F4) )

    D_u = X grad_jet + X^2 ( -2 d/ds1 + 6 d/ds2 - 24 d/ds3 + grad_jet^2 ).

Hand checks of conventions already done: N=2 gives C_{kappa,3} = 4 and N=3
gives C_{kappa,4} = -16 directly from the composition sum, matching the
recorded universal values.

Status: derivation complete on paper, not yet machine-validated. Next:
implement S(X) for kappa = 2 as truncated (X, s)-graded polynomial algebra
and compare 2^{i-1} [X^{i-1}] S / i! against coefficients.json
['corrected']['rows']['2'] for i = 3..20. Wrong-on-any = discard and say so
here.

## Checkpoint 2: kappa = 2 VALIDATED exactly, i = 1..20

theory_gf.py implements the operator-resolvent collapse. Output for
kappa = 2, nmax = 19: every C_{2,i}, i = 3..20, matches
coefficients.json['corrected']['rows']['2'] as exact rationals (the
reference row came from the independent bian_engine 14-fold sums, so this
is a genuine two-route agreement on 18 nontrivial values including
C_{2,5} = 52/3, C_{2,19} = -5142784/10854718875). Runtime seconds.
The master formula

    C_{kappa,i} = 2^{i-1}/i! * [X^{i-1}] ( -(1+D_u)^{-1} g |_{s=0} )

is therefore established at the strength of the generating identity it is
built on (hardened at instances, derived in general). Next: kappa = 3
validation, then push kappa = 2 to large i for the asymptotics.

## Checkpoint 3: kappa = 3 VALIDATED exactly, i = 1..20

Same run with --kappa 3 --nmax 19: every C_{3,i}, i = 3..20, matches
coefficients.json['corrected']['rows']['3'] exactly (18 nontrivial values,
e.g. C_{3,15} = 20977408/14189175). The collapse holds for kappa = 3 with
the same code path (s_1..s_4, marks m_2..m_5, third-order operators), so
the general-kappa structure is doing the work, not a tuned special case.
Next: extend kappa = 2 and kappa = 3 rows to large i via the collapsed
formula (this is now cheap), then asymptotics.

## Checkpoint 4: extended row 2 (i <= 81, exact) and the Gevrey-1/2 structure

Cost collapse: theory_gf.py reaches i = 26 in 0.7 s, i = 41 in 5 s, i = 81
in 81 s (bian_engine needed 760 s for i = 20). Rows stored in row2_ext.json
(i <= 81) and row3_ext.json (running, i <= 51).

Measured, kappa = 2, exact rationals through i = 81:

    i           20      40      60      80
    |C_2i|^1/i  0.643   0.424   0.338   0.291

still falling at i = 81, tracking the Farmer-Gonek kappa = 1 profile
sqrt(2e/i) (0.259 at i = 81) within 13 percent. Gevrey test: tau_i :=
(|C_2i| * Gamma(i/2+1))^{1/i} is nearly constant: 1.23 (i=20), 1.15 (40),
1.12 (60), 1.13 (81). So the data say |C_{2,i}| ~ tau^i / (i/2)! with
tau approx 1.1: the corrected kappa = 2 series is ENTIRE of order 2,
same Gevrey class as the kappa = 1 row (whose tau is 0.66), not merely
radius > 1. Sign pattern quasi-period approx 5.2 (complex pair of Borel
directions), consistent with the irregular signs noted in RESULTS section
5(c).

Bound quantity: 1 - 2 sum_{i<=I} C_{2,i}/((i+1)(i+2)) equals
0.9532610039 stable to 10 digits for every I in [30, 81] (exact partial
sums; value at I=81: 0.95326100393...). The i <= 20 value 0.953261 was
already right to 6 digits.

## Checkpoint 5: derivation that every corrected row is entire of order <= 2

Claim (derived; elementary proof outline, constants not optimized): for
every fixed kappa there is C_kappa with

    |C_{kappa,i}| <= C_kappa^i / floor(i/2)!    for all i,

hence limsup |C_{kappa,i}|^{1/i} = 0: G_kappa is entire of order <= 2 and
sum_i C_{kappa,i}/((i+1)(i+2)) converges absolutely with superexponential
tail.

Argument. In the resolvent formula S(X) = -(1+D_u)^{-1} g|_{s=0}:
1. Grading: every monomial X^n s^mu appearing in g (and preserved by D_u)
   has |mu| <= n. This is checked line by line: A = sum X^a Bell_a with
   deg Bell_a = a; Cq, B, D2, Dm likewise; products and the X-adic
   geometric series (1+A)^{-1} preserve it; the D_M extraction only adds
   X-order.
2. Coefficient growth: g is a fixed rational expression; its Taylor
   coefficients satisfy |g_{n,mu}| <= M gamma^n for explicit M, gamma
   (majorant series of a rational function with unit constant term in the
   denominator).
3. Consumption balance: a term of B_N = [X^N] arises from a g-monomial of
   s-degree d at X-order n0, fully consumed by j applications of D_u
   (evaluation at s = 0 kills anything not consumed). Each application
   extracts eps^{n_i} (1 <= n_i <= kappa) and consumes t_i s-factors with
   1 <= t_i <= n_i. Then sum t_i = d, sum n_i >= d, n0 >= d (grading), so
   N = n0 + sum n_i >= 2d, i.e. d <= N/2.
4. Size: each application multiplies by at most
   binomials(mu, t) * jet-constants^{n_i} * n_i! <= d^{t_i} * c^{n_i}, so
   the product of derivative factors is <= (N/2)^d <= (N/2)^{N/2}, which
   is (N/2)! times an exponential factor. Branching and the j-sum are
   exponential-times-polynomial. Hence |B_N| <= C^N (N/2)!.
5. Assembly: |C_{kappa,i}| = 2^{i-1}|B_{i-1}|/i! <= C'^i (i/2)!/i! <=
   C''^i/floor(i/2)!.

The balance in step 3 is the mechanism: one unit of X-cost per consumed
s-derivative, and one unit of X-cost per unit of s-degree created in g,
forces the factorial to (N/2)! instead of N!. This is the discrete
counterpart of backward-parabolic Gevrey-1/2 regularity: D_u is second
order in d/ds with X^2 coefficient, i.e. a backward heat operator in the
resolvent, and its formal Neumann series on analytic data has Gevrey
index 1/2, exactly what the tau_i fit sees.

Consequences.
(a) The prize question of the brief: limsup |C_{2,i}|^{1/i} < 1 holds with
    room to spare (the limsup is 0). The 0.9533 corrected kappa = 2 bound
    has an absolutely convergent series behind it; with the row measured
    exactly to i = 81 and the derived decay for the tail, the value is
    0.9532610039 to ten digits (each fixed truncation B of Bian Theorem 1,
    under RH, per RESULTS section 5).
(b) Same statement for kappa = 3: the series converges; the negative
    partial sums at i <= 20 are a transient of the oscillation, not
    genuine divergence. Deeper row 3 data (running) will show where it
    settles.
(c) Caveat kept honest: the growth claim is derived from the collapsed
    resolvent formula, whose own status is: machine-checked exactly
    against the independent engine for kappa = 2 and 3 through i = 20,
    and derived (not yet written as a formal proof) in general via the
    generating identity. No claim about letting B grow with T is made
    anywhere here.

## Checkpoint 6: row 3 extended to i = 51; alpha-optimized bounds; controls

Row 3 (exact, i <= 51, row3_ext.json): |C_{3,i}|^{1/i} falls to 0.424 at
i = 51; tau_i = (|C_{3,i}| Gamma(i/2+1))^{1/i} drifts near 1.4. Same
Gevrey-1/2 class as rows 1 and 2, larger type (tau approx 1.4 vs 1.13 vs
0.66). The kappa = 3 bound quantity at alpha -> 1 CONVERGES:
1 - 2 sum_{i<=I} C_{3,i}/((i+1)(i+2)) = -0.8555629894, ten digits stable
for I in [30, 51]. So the i <= 20 "negative and drifting" behavior was the
oscillating tail of a convergent (entire) series; the limit is simply
negative: vacuous at alpha -> 1.

General-alpha bound (Fejer kernel at parameter alpha in (0,1]):

    #simple/N >= 2 - 1/alpha - 2 sum_i C_{kappa,i} alpha^i/((i+1)(i+2)) + o(1)

Controls, all reproduced: kappa = 0 row gives 2/3 at alpha = 1
(Montgomery); kappa = 1 row gives 0.858384 with the optimum exactly at
alpha = 1 (Farmer-Gonek); the published (skip/figure, i <= 11) rows give
optimized 0.531 (kappa 2) and 0.147 (kappa 3), matching the prior
session's recorded values.

New numbers from the corrected extended rows (each under RH + Theorem 1
hypotheses at fixed truncation B, as everywhere in this hunt):

    kappa = 2: alpha -> 1 value 0.9532610039;
               optimized 0.9578404799 at alpha = 0.9723.
               Truncation-stable: i <= 41 and i <= 81 agree to 10 digits.
    kappa = 3: alpha -> 1 value -0.8555629894 (vacuous);
               optimized 0.4927221395 at alpha = 0.7464
               (positive but below Montgomery 2/3; not competitive with
               Conrey 0.9666 unconditional for xi''').

Note: the corrected kappa = 2 machinery with alpha optimized (0.9578)
exceeds both the alpha -> 1 corrected value (0.9533) and Bian's printed
headline (0.9544). alpha = 0.9723 is interior to (0,1), so no boundary
limit is involved.
