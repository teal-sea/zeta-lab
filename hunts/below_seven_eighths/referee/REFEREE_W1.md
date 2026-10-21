# REFEREE_W1: a code-disjoint check of the scalar Euler identity

**Hunt #136 (`below_seven_eighths`), referee lane `b78-referee`, wave 1, 2026-10-21.**
A second route, sharing no code with the first-wave lanes, for the claim in OpenAI's
quasi-Riemann paper that carries the Euler product: Lemma 7.1 (`lem:local-euler`) and its
Gauss-sum inputs, Lemma 4.2 and Equation (4.7). Nothing here is a result until the case
log in `hunts/README.md` says how this hunt ended.

**Grades.** Every check below is *derived*: an exact equality in a cyclotomic number
field, computed by PARI/GP, at the stated primes and inside the stated truncation boxes.
None is a proof of the lemma for all primes, none is kernel-checked, and nothing here
bears on real part 1/2. Where a statement is a reading of the paper rather than a
computation it is marked *inferred*.

**What is committed and what is only a file.** At the time of writing, the four files of
this directory (`REFEREE_W1.md`, `local_identity_pari.py`, `test_local_identity_pari.py`,
`disagreements.json`) are committed to the local branch `hunt/below-seven-eighths` by this
lane and are not pushed. The first-wave lane files the task names (`euler_step.py`,
`probe_table.py`) were untracked on the branch at every check, so no comparison with them
was made (section 5).

## 0. Source and method

The source is `paper.tex` of `github.com/openai/math` at `adc7f124`, read from the
campaign cache; its SHA-256 is checked against
`42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3` before any line is
quoted, and every cited line number is pinned by `test_cited_lines_say_what_the_report_says`.

Engine: PARI/GP through cypari2 (version 2.17.2 on the campaign box, an environment
fact, not pinned). Residue symbols come from PARI's `nfmodpr`
reduction of `O = Z[omega]` to the residue field followed by the `(Q-1)/6` power there
(quartic symbols in `Z[i]` the same way). Gauss sums, Jacobi sums and every coefficient
are exact PARI polmods modulo `polcyclo(N)`, compared by exact equality; one complex
embedding is used only to choose the positive square root of a norm. The first-wave lane
uses python-flint convolutions; nothing here imports python-flint.

Test primes (pinned by `test_primary_generators_and_symbols`): the primary generators
`1 + 3w` (norm 7), `4 + 3w` (13), `-2 + 3w` (19), `-5` (the inert prime 5, norm 25), and
`1 + 6w` (31, the verifier's prime), with `omega_p = chi_p(-1)` equal to -1, 1, -1, 1, -1.
The primes above 6 lie in S by line 591; there only the claims the paper makes at S are
checked (section 1.6). Lemma and equation numbers are the task's; the tests pin the LaTeX
labels at the cited lines and that `lem:local-euler` is the only numbered environment of
section 7 (so Lemma 7.1 is an *inferred* numbering, as is Lemma 4.2 as the second lemma of
section 4).

## 1. Lemma 7.1 and its Gauss-sum inputs

### 1.1 Lemma 4.2 and the identities of its proof

All 21 identities of `lemma_4_2_checks` hold exactly at norms 7, 13, 19 and 25 (and 31):
`gamma_2^3 = -alpha(p)`, `gamma_1 gamma_2 = conj(H(4)) gamma_3 gamma_2^3`, `|gamma_r| = 1`
for `r = 1..5`, `G_0 = -1`, `tau(A) tau(conj A) = A(-1) P` for the five nontrivial powers,
`J(H, H^3) = H(4) J(H, H)`, `J(H^2, H^2) = -p`, `tau_2^3 = -pP`, and the five facts the
proof of Lemma 7.1 quotes (`G_1 G_{-1} = omega_p Q`, `gamma_3^2 = omega_p`,
`gamma_2 gamma_4 = 1`, `gamma_1 gamma_2 = -alpha(p) conj(chi_p(4)) gamma_3`,
`gamma_4/gamma_1 = -conj(alpha(p))/G(p)`, lines 3886, 4079, 4117-4122). Normalized
statements are cleared of square roots before comparison (for example `gamma_2^3 = -alpha`
is tested as `G_2^3 = -pP`).

### 1.2 Equation (4.7), Lemma 4.3 and Equation (4.6)

Equation (4.7) holds exactly at the squarefree indices `c = 1 + 3w`, `7` (both primes
above 7), `(1 + 3w)(4 + 3w)`, `(4 + 3w)(-5)`, `19` (both primes above 19) and
`(1 + 3w)(-5)`, and in the slow tier at the three-prime index
`(1 + 3w)(4 + 3w)(-2 + 3w)`: `gamma_2(c)^3 = mu(c) alpha(c)`,
`gamma_1 gamma_2 = mu alpha G`, `G = conj(chi_c(4)) gamma_3` (that is, the quadratic
Gauss sum equals `gamma_3`) and `|G| = 1`. At each of these `c` the direct quadratic sum
also equals Lemma 4.3's four-term value. At `c = p^t` the four-term value matches direct
summation for `t <= 3` (norms 7 and 25) and `t <= 2` (13, 19), and Equation (4.6)
(`G(p^3) = gamma_3(p)`, `R(p, p) = gamma_3(p)^2 = chi_p(-1)`) and `G(p^2) = chi_p(4)`
(line 953) hold.

### 1.3 The local scalar C_p

The lift of lines 3877-3883 (`g_{chi^r}(p^t, p^{j'})`) equals direct summation over
`O/p^t` for every `r` and `j' <= t + 1`, for `t <= 3` at norm 7 and `t <= 2` at 13, 19, 25
(slow tier: `t <= 4` at 7, `t <= 3` at 13 and 25). Then `C_p(t, k, j')`, computed from its
definition (`local-scalar-definition`, the sum over `d mod p^k` done term by term with its
congruence), equals the paper's table (`local-scalar-values`) at every key of the boxes
`t <= 13`, `k <= 3`, `j' <= 29` (norm 7, 1680 keys, inner Gauss sums summed directly for
`t <= 2`) and `t <= 13`, `k <= 2`, `j' <= 29` (13, 19, 25, 1260 keys each, direct for
`t <= 1`). Above those depths the inner sums use the lift, which is the one input taken
from the paper beyond the directly summed range.

### 1.4 The closed form

**`(local-P)` equals Lemma 7.1's closed form (`old-eq:5.13a`) as an exact identity of
truncated local series** in `X = Q^{-x}`, `B = Q^{-w}`, `V = Q^{-6z}`, through the box
`t <= 13`, `k <= 2`, `m <= 4`, for all six rows `j = v_p(u)`, all six unit phases `rho`,
at norms 7, 13, 19 and 25 (144 identities). The comparison multiplies the series by
`(1-R)(1-V)(1-W_loc)` and matches the closed form's polynomial numerator, so each of the
four families of the table (`eq:local-family-table`) is tested through `r = 1`, and the
family with `t = 6r + 1` through `r = 2`. It is not
vacuous: at norm 7 the six rows carry 28, 24, 26, 28, 26, 26 nonzero series coefficients
in the box (at `rho = zeta_6^2`) and the numerator of row 0 has 11 monomials. Every
monomial `X^t` carries `eta(p)^t`, so `eta = 1` suffices; `eta = zeta_12^5` and `eta = 2`
were also run and agree.

Two further routes agree with the same summands:

* **The phase bookkeeping (lines 3953-3996).** The raw coefficient at an index supported
  on one prime, `gamma_2(p)^{e0} conj(alpha)^t eta^t conj(G(p^t)) R(p^t, p^k) rho^{k-t}
  C_p`, with `gamma_2` summed directly and `G`, `R` from the four-term value, equals the
  summand of `(local-P)` through `t <= 13`, `k <= 2`, `m <= 3`, at all four primes.
* **The global coefficient.** `K_eta(c, n, s, a; u)` built from
  `local-full-coefficient` itself, with `S = {(2), (lambda)}`, `b_* = 2 lambda`, `xi`
  of order three at 2 and quadratic at `lambda`, `tau`, `Xi`, and `F(s, A, H)` as a sum
  of complete Gauss sums modulo `b_* A` (lines 3742-3745), equals `Q^{e0/2+l}` times the
  summand at single-prime indices (11 cases with `t <= 3`, `k <= 2`, `m <= 1` at norm 7
  for rows 0, 1, 2 and two units; 6 cases at norms 13 and 25 for rows 0 and 1; rows 3 and
  4 at `t = 4` in the slow tier). It **separates into prime factors** (line 3994): the
  coefficient at an index supported on two primes is the product of its two one-prime
  coefficients for the pairs (7, 7bar), (7, 13) and (7, 25), each for `eta = 1` and
  `eta = chi_{-4} o N`, and for `u = 1`, `zeta_6`, `1 + 3w`.

### 1.5 H_p and the analytic statements

The defect formula `local-H-defect` holds exactly in the box at all four primes, rows and
phases, and `H_p - 1` has no `X^1` term: the `-D` entry of `J_0` cancels the Euler factor
`D = eta(p) conj(chi_p(u)) Q^{-x}`, which is what places `1/L^S(x, eta conj(chi_.(u)))` in
`eq:probe-high`.

The convergence statements were read as exponent bookkeeping over the monomials of the
polynomial `(1-D)(1-R)(1-V)(H_p - 1)` (symbolic, in sympy, exact rationals). In region one,
at `eps0 = 1/1000` the largest monomial is `Q^{-1001/1000}` in rows 0 and 1 and
`Q^{-1/1000}` in rows 2 to 5; at `eps0 = 1/10` it is `Q^{-11/10}` in rows 0 and 1 and
`Q^{-3/100}`, `Q^{-1/25}`, `Q^{-1/10}`, `Q^{-3/50}` in rows 2 to 5. At those values and at
`eps0 = 1/50` every row is inside the stated `O(Q^{-1-eps_H})` (row 0, p not dividing u)
and `O(Q^{-eps_H})` (rows 1 to 5, `p | u`), `eps_H = min(eps0, 1/50)`. In region two the
maxima are exactly `-363/200` and `-33/40`, attained by the terms the paper names (`Q^{1-x_r-w_r-6z_r}` and `Q^{1-x_r-w_r}`), and the tail
exponent `1 - 363/200 = -163/200` gives `c_H = 4/5`. This checks the bookkeeping of
lines 4148-4185 given the closed form; it is not a proof of normal convergence.

### 1.6 At the primes above 6

Only what the paper claims there was checked, with `S = {(2), (lambda)}` and with the
inert prime 5 added: the six units are distinct modulo 3 (line 580), `xi` is a character
of `(O/b_*)^x` of order three at 2 and quadratic at `lambda` (lines 3349-3355),
`|tau| = 1` (line 3367), `g_xi(b_*, H) = 0` when `H` meets S (line 3755), and
`g_xi(b_*, h) = conj(xi(h)) g_xi(b_*, 1)` for `h` prime to S. Lemma 4.2 and Lemma 7.1 are
not claimed at S and were not run there.

**Verdict on (1).** No defect was found. At norms 7, 13, 19 and 25, inside the stated
boxes, Lemma 7.1's closed form, its scalar factorization at the level of single-prime and
two-prime coefficients, and its Gauss-sum inputs hold exactly. *Derived*, at those primes
and boxes only.

## 2. Rivals: the identity fails, and where

**Placement.** The identity reads the target only through `eta(A)` in
`local-full-coefficient`, linearly. The paper places a Dirichlet character there as
`a -> chi(N a)` (line 6725). The same rule applied to a rival's Dirichlet coefficients
`a(n)` puts `f(a) = a(N a)` in the eta slot, and the rival's bad primes join S
(`S = {(2), (lambda), (5)}` for both rivals).

* **Davenport-Heilbronn.** `f(a) = c_1 chi(N a) + c_2 conj(chi)(N a)`, `chi` mod 5 with
  `chi(2) = i`, `c_{1,2} = (1 -+ i kappa)/2`: a linear combination of two Hecke
  characters of F. `kappa` is built exactly in `Q(zeta_20)` and agrees with
  `zeta/epstein.py`'s pinned value (0.2840790438404123 to fifteen places). The
  coefficients are 1, `kappa`, `-kappa`, -1, 0 by `n mod 5`.
* **Epstein, D = -15 (hunt #120).** `f(a) = r(N a)/2` for `Q0 = x^2 + xy + 4y^2`, with
  `r = (1 * chi_-15) + (chi_-3 * chi_5)`, hunt #120's identity in the paper's vocabulary;
  the formula matches a direct lattice count at the 17 values of `n` tested.

In the identity's terms at a good prime of norm P: `eta(p) := f(p)` (forced, since the
`t = 1` coefficient is `-eta rho^{-1}`, `eta` or `-eta (Q-1)` in every row),
`a_p = conj(alpha)^3 f(p)^3`, `b_p = conj(alpha)^2 f(p)^2 conj(chi_p(4))`,
`R = a_p^2 Q^{4-6x-6z}`, `D = f(p) conj(chi_p(u)) Q^{-x}`, while the series carries the
rival's own `f(p^t)` where a character has `eta(p)^t`.

**The failing local term.**

1. **Separation (the distinguishing step).** In the `u = 1` row the coefficient at the
   squarefree index `c = 7 = (1 + 3w)(-2 - 3w)`, which the product of local factors
   gives as `D_p D_pbar` (the product of the two `J_0` entries `-eta rho^{-1} Q^{-x}`),
   comes out as `f(7)` times the same Gauss-sum phase. The phase itself separates (the
   trivial character passes). DH: `f(7) = a(49) = -1` against
   `f(p) f(pbar) = kappa^2 = 0.0807009`. Epstein: `1` against `0`. Also failing: DH at
   (7, 13) (`1` against `-kappa^2`) and Epstein at (19, 19bar) (`3` against `4`).
2. **The single-prime closed form.** With `eta(p) = f(p)`, the first monomial where the
   rival's series leaves the closed form is, in the `u = 1` row, the `R(1-Q^{-1})` entry
   (family `(0, 2r+2)`, `r = 0`, the monomial `X^6 V`), where `f(p^6)` replaces
   `f(p)^6`: DH at norms 7 and 13 (`f(p^6) = -1` against `kappa^6`), Epstein at 7, 13
   (`1` against `0`), 19 and 31 (`7` against `64`). In the other rows the first failure is
   `J_2` (row 2, `t = 3`), the first entry of `J_3` (row 3), `J_4` (row 4) and `J_5`
   (row 5) for DH at 7 and 13 and Epstein at 19 and 31; for Epstein at 7 and 13, where
   `f(p^3) = 0 = f(p)^3`, row 2 first fails at `t = 6` and row 3 at the `X^4` entry of
   `J_3`.

**Where a rival passes.** DH at norms 19 and 31, where `chi(P) = -1` or `1`, is
completely multiplicative on powers of `P`, so the single-prime closed form holds for it
there through the whole box, and the cross terms (19, 19bar) and (7, 19) separate. That
single-prime identity is therefore a shared lemma for DH in the sense of `ALIGNMENT.md`
section 5; the step DH cannot pay is the separation across primes with non-real
`chi(P)`. The Epstein coefficient vanishes on both sides at (7, 13) and (7, 19), and its
coefficients are multiplicative at (19, 31) (checked from the coefficients alone).

*Scope.* The placement tests the identity's terms, not the rivals' zeros: the
norm-composed series are not the rivals themselves (for DH it is
`c_1 L(chi) L(chi chi_-3) + c_2 L(chibar) L(chibar chi_-3)`), and no zero of either placed
series is computed here. The kill condition "a claimed arithmetic step also holds for a
function with a zero beyond the claimed abscissa" does not fire on this step.

## 3. The lower-order probes, one prime each

These are the referee's own constructions from the task's one-line descriptions, built
before any lane file was opened (the lane's definitions were never read; section 5).
"Scalar" means in `mu_infinity * alpha(p)^Z`, the values a Hecke character can take at p;
the test is exact (`x^12 alpha^{-a}` a root of unity), and `alpha(p)` is checked not to be
a root of unity.

* **S1, cubic theta with the conjugate cubic twist (k = 3), at norm 7.**
  `gamma_2 gamma_4 = 1` exactly (also at the two-prime indices `7` and
  `(1 + 3w)(4 + 3w)`, so no Moebius sign and no cross phase). With the paper's row
  normalization the `u = 1` coefficient of `X` is `+conj(alpha(p) G(p)) eta rho^{-4}`: the
  angular factor `conj(alpha)` does appear, as the kill says. With a bare row (no angular,
  no `G` and no `R` insertion, all three being there to cancel phases that
  `gamma_1 gamma_2 = mu alpha G` produces and this product does not) it is exactly
  `+eta rho^{-4}`, and the full local factor factors as
  `(1-V)^{-1} (1-W)^{-1} (1 - eta^2 X^2)(1 - eta X)^{-1} H` with no pure `X` or `X^2` left
  in `H - 1` (norms 7 and 13). **The scalar factorization exists, with the target in the
  numerator**: `L(x, eta)/L(2x, eta^2)` at `u = 1`, not `1/L`. The shape a zero detector
  needs is absent, but not for the stated reason (disagreement D1 in
  `disagreements.json`).
* **S2, the quadratic twist (k = 2), at norm 7.** `gamma_2 gamma_3` has alpha-exponent
  `1/3`; with the paper's row normalization the coefficient has exponent `-2/3`, and with
  the conjugate theta `-1/3`. Since `gamma_2^3 = -alpha` and alpha has infinite order, no
  finite-ray phase or integer power of alpha makes it scalar. The attempt to exhibit a
  scalar identity failed. Consistent with the kill.
* **S3, classical theta over Q(i) with the quartic twist, at the prime `-1 + 2i` of norm
  5 (every scalar by direct summation through `t = 4`) and at `3 + 2i` (norm 13).** The
  theta coefficients at `p^t` are 2, 0, 2, 0, 2 for `t = 0..4`, so there is no `X^1` term
  in any row. The non-scalar twist values (quartic Gauss sums, alpha-exponent `1/2` and
  `-1/2`) occur only at odd `t`, exactly where the theta vanishes; every surviving
  coefficient is scalar (the quadratic Gauss sum at `t = 2`, Ramanujan sums at `t = 4`),
  and the `u = 1` row starts at `X^4`. A scalar local factor exists, in `Q^{-2x}` and
  `Q^{-4x}`; the factor `1/L(x, eta)` is absent. Consistent with the kill.

## 4. Planted faults

Both planted faults required by the task turn checks red (tests
`test_planted_fault_wrong_gauss_sum_sign` and `test_planted_fault_wrong_local_factor`):

* **Wrong Gauss-sum sign, `G_1 -> -G_1`.** Six of Lemma 4.2's 21 identities fail, the
  raw-coefficient route fails in every row, and the C_p table comparison fails where the
  inner sums are summed directly. The closed-form identity alone catches it only in rows
  3 and 4: elsewhere `G_1` enters only through the ratio `C_p/gamma_1`, which is
  invariant. A check of the closed form by itself is blind to this sign in rows 0, 1, 2
  and 5 (section 6, note N1).
* **Wrong local factor, `R` built from `a_p` instead of `a_p^2`.** The closed-form
  identity fails in every row, first at `X^6 V` and `X^6 B V`.

Further variants also fire: `J_2` with an extra `rho` (row 2 only), `(1 + Q^{-1})` for
`(1 - Q^{-1})` (every row), and an unconjugated Euler factor `D = eta chi_p(u) Q^{-x}`
(caught by the `-D` cancellation exactly when `rho` is not real, and by the region-one
bookkeeping, whose maximum becomes `-51/100`).

## 5. Comparison with the first-wave lane files

**Not performed.** `euler_step.py` and `probe_table.py` (and their tests and notes) were
untracked on `hunt/below-seven-eighths` at every check, HEAD `9c1f21c52`, and the task
forbids treating uncommitted files as final. They were not opened. The kill statements
compared in section 3 are the task's descriptions of them, not the lane's text.
`disagreements.json` lists the one disagreement with those descriptions and records the
comparison as outstanding.

## 6. Notes for the owner and the verifier

* **N1.** Because the closed form is free of Gauss sums, a route that checks only
  `(local-P) = closed form` cannot see a sign error in `G_1` outside rows 3 and 4. The
  inputs need their own check (here Lemma 4.2 and the raw coefficient).
* **N2.** The worktree's branch was not created from `origin/main` `fb647bfc7`, as the
  task's override states; its base is `d5d1dfc81`. No file outside `referee/` was
  touched.
* **N3.** A process listing taken to find this lane's own background job displayed
  another session's command lines, which named tests and planted-fault strings of the
  uncommitted `euler_step.py` and `test_euler_step.py`. This lane did not open those
  files and shares no code with them; the disclosure is made because the route is meant
  to be independent.
* **Rerun at another prime.** `local_identity_pari.py --norm 31` runs the prime-level
  battery (Lemma 4.2, the lift, the C_p table, the closed form for all rows and phases,
  the raw route, `H_p`) and both planted faults; the slow test tier includes norm 31.
  Default tier: `.venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/referee -m "not slow"`
  (about three minutes on the campaign box, measured once, not pinned).
