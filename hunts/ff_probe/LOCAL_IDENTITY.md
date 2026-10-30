# LOCAL_IDENTITY: Lemma 7.1 of the 7/8 paper over F_7[T], and the loss ledger

**Hunt #148, steps 2 and 4. Status: the F_7[T] transplant of the base probe is built; its
original, Poisson and Euler representations agree exactly at every checked degree triple,
up to total degree 9; the function-field Lemma 7.1 is checked exactly at the stated primes,
rows and degrees. Not reviewed by any person; files produced on branch `hunt/ff-probe`, not
landed.** Every count on this page is read from `results_step2.json` or
`results_ledger.json` and pinned by `test_ffprobe.py`. Grades as in `MISSION.md`.

## 1. The transplant

The template is Section 7 of the paper (lines 3723 to 4067 of the pinned `paper.tex`). Each
object of the number-field construction is replaced by its F_7[T] counterpart, and each
identity the paper's proof of Lemma 7.1 uses is checked before it is used.

| paper, over Q(sqrt(-3)) | here, over F_7[T] | check (results_step2.json) |
|---|---|---|
| primary generators, q_a = N(a) | monic polynomials, q_a = 7^deg a | |
| the sextic symbol chi_p(a) = a^((q_p-1)/6) mod p | the same, in two routes (Frobenius at each prime, resultant) | step 1 |
| e(z) = exp(2 pi i Tr(z/lambda)) | e(f) = exp(2 pi i a_-1(f)/7) | |
| S, b_*, xi nonprincipal at each prime of b_*, tau | S = {T}, b_* = T, xi = chi_T, tau = 7^(-1/2) g_xi(T, 1) | |
| alpha(a) = a/abs(a) | alpha(c) = lambda_alpha^deg c, lambda_alpha = (-tau(eps chi^2)/sqrt 7)^3, the Eisenstein-Weil value | gamma_2(c)^3 = mu(c) alpha(c) |
| G(c) = conj(chi_c(4)) Gamma(c) | the same definition; Gamma(c) depends only on deg c | closed form against brute force |
| R(a, b), the square-class bicharacter | R(a, b) = eps(chi(-1))^(deg a deg b) = (-1)^(deg a deg b) | sextic reciprocity |
| eta, a finite-order Hecke character | eta(a) = eps(a_0) zeta_7^(a_1/a_0), a character modulo T^2 | L(u, eta) = 1 + c_1 u, abs(c_1)^2 = 7 |
| the theta row gamma_2(c) conj(alpha(c n^3)) ... | the same formula; by step 1 it is the F_7(T) cubic theta row up to a factor depending on deg c | `SOURCES.md` |
| W_0, W_1 and the Mellin integral in Z | sharp cut-offs: deg m < D_X + D_s + 1, deg s = D_s, deg(c n^3) = D_A | |

The probe at degrees (D_X, D_s, D_A) is then the finite sum

    I = sum_{deg s = D_s} sum_{deg A = D_A, A = c n^3} w(s, A) sum_{deg m < D_X + D_s + 1} xi(m) chi_A(m) g_{chi_s}(s, -m),

with w(s, A) the paper's weight chi_s(T) (tau xi(s))^-1 gamma_2(c) conj(alpha(A)) eta(A)
Xi(A)^-1 R(A, s) conj(G(A)) 7^(-deg c/2 - deg n), Xi(a) = xi(a) chi_a(T), and s, A, c, n prime
to T (`ffprobe.probe_direct`). Finite Poisson summation modulo T s A is exact:

    sum_{deg m < N} f(m) = 7^(D_X + D_s - D_A) sum_{H != 0, deg H < D_A - D_X} F(s, A, H),

with F of eq. (local-F); the frequency H = 0 drops because xi is primitive at T, and H = u a^6
splits the frequencies into the rows of eq. (probe-poisson-identity).

## 2. What is checked

| identity | where in the paper | range | result |
|---|---|---|---|
| reciprocity chi_b(a) = R(a, b) chi_a(b) | Lemma fixed-gauss-phase | coprime monic a, b of degree 1 and 2 | 2,688 pairs, no mismatch |
| Gamma closed form against brute force | Lemma quadratic-four-term | every monic c of degree at most 3 | 400 moduli, no mismatch |
| gamma_2^3 = mu alpha, gamma_1 gamma_2 = mu alpha G, G = conj(chi(4)) gamma_3 | eq. (signal) | every squarefree c of degree at most 3 | 343 moduli, no mismatch in any of the three |
| G(vw) = G(v) G(w) R(v, w), all pairs, coprime or not | eq. (G-quadratic-refinement) | v, w of degree at most 2 | 3,249 pairs, no mismatch |
| G(p^2) = chi_p(4), G(p^3) = gamma_3(p), R(p,p) = gamma_3(p)^2 = chi_p(-1) | eq. (fixed-gauss-phases) | primes of degree at most 2 | 27 primes, no mismatch |
| F(s, A, H): definition = brute force = the paper's factorization by U_p and C_p | lines 3734-3753, 3927-3951 | deg s, deg A at most 2, deg s + deg A at most 3, every H != 0 of degree at most 1 | 30,576 cases, no mismatch in either comparison |
| the complete evaluation of C_p(t, k, j') | eq. (local-scalar-values) | four primes, t <= 7, j' <= 8 | 720 values, no mismatch |
| K(c, n, s, a; u) = product of the local summands of eq. (local-P) | lines 3953-3996 | eight rows u = 1, 3, T+1, (T+2)^2, T^2+1, (T+1)(T+2), (T+5)^3, 2(T+1)^5 with deg A <= 3, deg s <= 1, deg a <= 1; and the rows 1, 3, T+1 with deg A <= 2, deg s <= 2, deg a <= 1 | 120,344 and 44,247 tuples (72,319 and 29,134 of them nonzero), no mismatch |
| Lemma 7.1: P_p equals the closed form with the six J_j | eq. (old-eq:5.13a) | p = T+1 and T+4 for j = 0..5 to x^13 w^3 v^2, p = T^2+1 for j = 0..5 to x^13 w^2 v^2, three or four values of rho each | 72 (prime, row) cases, every coefficient equal |
| original = Poisson = Euler for the probe | eqs. (general-probe), (probe-poisson-identity), (probe-high) | 16 degree triples, total degree up to 9 | PROBE |

"Euler" evaluates every row through the product of the closed-form local factors, so the
last row checks Lemma 7.1 and the Poisson step end to end, against a sum that uses neither.

## 3. A function-field Lemma 7.1

**Statement (checked at the ranges above; derived in general by the paper's own argument,
every phase identity of which holds in F_7[T]; unreviewed).** With the transplant of
section 1, for every nonzero sixth-power-free u prime to T, unit factor included, and every
monic irreducible p != T, put Q = 7^deg p, j = v_p(u), rho = chi_p(u/p^j),
omega_p = chi_p(-1) = (-1)^deg p, a_p = conj(alpha(p))^3 eta(p)^3,
b_p = conj(alpha(p))^2 eta(p)^2 conj(chi_p(4)), V = Q^(-6z), R = a_p^2 Q^(4-6x-6z),
W_loc = rho Q^(-w). Then:

1. K(c, n, s, a; u) is the product over p of the summands of eq. (local-P): the
   coefficient separates into prime factors, with every pair phase cancelled.
2. The local factor P_p equals the closed form of eq. (old-eq:5.13a), with the same six
   values J_j as in the paper.
3. Hence, as formal power series in 7^(-x), 7^(-w), 7^(-6z),
   F_{eta,u}(x, w, z) = zeta^S(6z) L^S(w, chi_.(u)) / L^S(x, eta conj(chi_.(u))) prod_{p != T} H_p,
   with H_p as in eq. (local-H-definition). For u = 1 this is
   zeta^S(6z) zeta^S(w) / L^S(x, eta) times the correction: **the principal row is
   proportional to 1/L, as in the paper.**
4. For p not dividing u the leading terms of H_p - 1 are Q^(-x-w), Q^(-w-6z), Q^(-x-6z),
   Q^(4-6x-6z) and Q^(1-x-w-6z) (from the closed form; the paper's line 4150 bounds the last
   two). Since F_7[T] has 7^d/d + O(7^(d/2)) monic irreducibles of degree d, the product over
   such p converges absolutely exactly where all five exponents have real part below -1. The
   paper's two regions, eqs. (local-region-one) and (local-region-two), lie inside that
   set. At the principal point (w, z) = (1, 1/6) it is Re x > 2/3, against the Re s > 7/8 the
   paper states and needs (derived; at p = T + 1 and u = 1 the closed form's lowest
   monomials of H_p - 1 are exactly these, with squared moduli 1, 1, 1, 64 = (Q + 1)^2 and
   4233649, about Q^8, as `test_ffprobe.py` pins).

What differs from the number field is only bookkeeping: every angular datum (alpha,
chi_p(4), omega_p) is a character of the degree, because the units of F_7[T] are the
constants. One consequence is new: **a selection rule.** The substitutions m -> lambda m,
for the six lambda in F_7^x, preserve the box and multiply the summand by
eps(chi(lambda))^(xi_j + deg A - deg s). Averaging over them shows that the m-sum equals
itself times (1/6) sum over lambda of that factor, so it vanishes unless
deg s = deg A + xi_j (mod 6). Of the 16 checked triples
the ones off that class are zero in all three representations, as predicted, and the ones on
it are nonzero. At the paper's balanced point D_X = D_s = D_A/2 the rule leaves only
D_A = -2 xi_j (mod 12); with xi = chi_T that is D_A = 10, 22, ..., and with xi = chi_T^5 or
chi_T^4 the balanced probe is nonzero at D_A = 2 or 4 (section 4).

## 4. The loss ledger: what the template charges against the exact sizes

| quantity | template charge | exact in F_7[T] | consequence |
|---|---|---|---|
| Poisson coefficient F(s, A, H) | abs(F) <= q_s q_{b_* A} (line 3840), used only to justify interchanges | abs(F)^2 = 7 q_A for squarefree coprime s, A and H prime to s A (all 417 checked cases, deg s = 1, deg A = 2); the largest ratio abs(F)/(q_s q_{b_* A}) over deg s, deg A <= 2 and deg H <= 1 is 7^(-1/2) = 0.378, at s = A = 1, H = 2, over 63,870 nonzero cases | a square-root overcharge, outside the abscissa |
| theta and twist Gauss sums | abs(gamma_r) = 1 | exact | none |
| correction product H_eta(x) = H_{eta,1}(x, 1, 1/6) | holomorphic on Re s > 7/8 (line 5525), and sup abs(H - 1) <= 1/2 after enlarging S to all primes of norm up to P_0 (lines 5526-5531) | absolutely convergent for Re x > 2/3 (section 3); with S = {T} alone, max abs(H_eta - 1) on Re x = 7/8 is 0.199 (0.210, 0.246 and 0.277 on Re x = 5/6, 3/4 and 17/24; measured, primes to degree 6, 360 points on the circle; by the maximum principle this is the supremum over the half-plane) | no enlargement of S is needed at this target; the region is not where the template binds |
| the target's zeros | none assumed beyond 7/8 | L(u, eta) = 1 + c_1 u with abs(c_1)^2 = 7 exactly, so its only zero is on Re x = 1/2 | RH holds here, as Weil's theorem says |
| the balanced probe, X = Y = Z^(1/2) | abs(I) << Z^(1/4 + eps) (the direct estimate, Part I) | abs(I) = 1.529 at Z = 7^2 (xi = chi_T^5) and 0.609 at Z = 7^4 (xi = chi_T^4), in the paper's normalization, against Z^(1/4) = 2.646 and 7; original and Euler representations agree at both | two points; no exponent can be read off |
| the abscissa | k = 6: 11/12 (balanced probe), 7/8 (Part II corner), 13/15 (perfect row counts) | the truth is 1/2 | the template charges at least 3/8 above the truth here |

The k = 6 walls are hunt #136's order-k template (`PROBE.md` there, section 3, derived
there and unreviewed), recomputed here as exact fractions. Nothing in the local identity is
where the 3/8 is lost: the identity is exact, its regions are generous, and the correction
is small already at S = {T}. The loss sits in the low estimate and the Part II row counts,
which this hunt does not model; the balanced probe vanishes at every degree below D_A = 10
for xi = chi_T, so the low side's exact size at the balanced point is out of this hunt's
computed range for the paper's own choice.

## 5. The doors

**Candidate status.** The F_q[T] transplant reproduces Lemma 7.1 exactly; as a ceiling
statement, the template applied to it would price 7/8 (k = 6), where the truth is 1/2.
Parameter range: q = 7, the probe triples and local ranges of section 2. Information class:
the same data the paper's high side reads. Proof status: exact computation plus the paper's
algebra, unreviewed.

- **Active constraints at the optimum.** In the template the binding inputs are, ranked by
  hunt #136's shadow prices, the pole 1/k (price -3/4 per unit of 1/k at the paper's
  geometry) and the low estimate's exponent 1/4; neither involves the local identity, which
  is exact here and slack in its regions (the principal correction converges from
  Re x = 2/3, not 7/8).
- **Frozen-constant inventory.** The order k = 6 of the twist (fixed by the cubic theta's
  Gauss pairing, as hunt #136 reads it; here the pairing holds verbatim), the auxiliary
  character xi = chi_T^xi_j (here xi_j selects which degree classes the probe sees, a
  genuine trade: it moves the balanced point between D_A = 2, 4, ..., 10 mod 12 at no cost
  to the identity), the target's conductor T^2 (a free choice), and the excluded set
  S = {T} (enlarging it trades a smaller correction for nothing here, since the correction
  is already within 1/2).
- **Information class.** Every door above stays inside the data the probe already reads.
  Reading more means a different theta: `S4.md` shows the biquadratic one cannot be used,
  and that is the only lower-k door this hunt tested.

## 6. Not done

- **A deviation from the task: the reflected representation was not built.** The task asked
  that the probe's reflected and Poisson representations agree. In the paper the reflected
  representation is the low side: the theta row B_{m,sigma}(Z) rewritten by Proposition
  completed-reflection (lines 1676 to 1847) as a dual sum over the theta function's
  coefficients at three cusps, taken from Dunn and Radziwill. Its F_7(T) analogue would need
  the cubic theta function's expansions at the cusps that reflection uses, and both Patterson
  sources compute coefficients at the cusp at infinity only. Building it is a construction of
  its own and was not attempted, so the low estimate is not checked here. What is checked
  instead is that the original representation, the one the reflection acts on, equals the
  Poisson and Euler representations exactly (section 2).
- Only q = 7, one target eta and xi = chi_T for the identities (xi = chi_T^5 and chi_T^4
  only for the two balanced values).
- The general statement of section 3 is derived, not proved here for every p and u: the
  computation covers the stated primes and rows.

## Reproduce

```
.venv/bin/python hunts/ff_probe/ffprobe.py --part step2     # results_step2.json (checkpoints per unit)
.venv/bin/python hunts/ff_probe/ffprobe.py --part ledger    # results_ledger.json
.venv/bin/python -m pytest -q -n0 hunts/ff_probe/test_ffprobe.py
```
