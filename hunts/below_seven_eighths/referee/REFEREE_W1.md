# REFEREE_W1: a code-disjoint check of the scalar Euler identity

**Hunt #136 (`below_seven_eighths`), referee lane `b78-referee`, wave 1, 2026-10-21;
repaired the same day after an adversarial review (section 7).**
A second route, sharing no module or function with the first-wave lanes (note N3), for
the claim in OpenAI's
quasi-Riemann paper that carries the Euler product: Lemma 7.1 (`lem:local-euler`) and its
Gauss-sum inputs, Lemma 4.2 and Equation (4.7). Nothing here is a result until the case
log in `hunts/README.md` says how this hunt ended.

**Grades.** Every check below is *derived*: an exact equality in a cyclotomic number
field, computed by PARI/GP, at the stated primes and inside the stated truncation boxes.
None is a proof of the lemma for all primes, none is kernel-checked, and nothing here
bears on real part 1/2. Where a statement is a reading of the paper rather than a
computation it is marked *inferred*.

**What is committed and what is only a file.** The four files of this directory
(`REFEREE_W1.md`, `local_identity_pari.py`, `test_local_identity_pari.py`,
`disagreements.json`) were committed by this lane in `b6c4972a8` on the branch
`hunt/below-seven-eighths`. The branch was later pushed to `origin`: the local reflog
records the push at 2026-10-21 21:23:47 UTC, to `baa41597e`, which contains `b6c4972a8`.
This lane did not push it. The repair after the adversarial review (section 7) is a
further local commit on the same branch, and this lane does not push it either. The
first-wave lane files the task names (`euler_step.py`, `probe_table.py`) were still
untracked on the branch at the repair, so no comparison with them was made (section 5).

## 0. Source and method

The source is `paper.tex` of `github.com/openai/math` at `adc7f124`, read from the
campaign cache; its SHA-256 is checked against
`42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3` before any line is
quoted, and every cited line number is pinned by `test_cited_lines_say_what_the_report_says`.

Engine: PARI/GP through cypari2 (on the campaign box the PARI library is version 2.17.2
and the cypari2 package version 2.2.4; environment facts, not pinned). Residue symbols
come from PARI's `nfmodpr` reduction of `O = Z[omega]` to the residue field followed by
the `(Q-1)/6` power there (quartic symbols in `Z[i]` the same way). Gauss sums, Jacobi sums and every coefficient
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
`gamma_4/gamma_1 = -conj(alpha(p))/G(p)`, lines 3886, 4079, 4117-4121 and 4124; the
first version cited 4117-4122, which stops before line 4124, where `gamma_2 gamma_4 = 1`
is stated). Normalized
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

Two further derivations agree with the same summands. They share this module's Gauss
sums, `C_p` and field arithmetic, so they are distinct derivations, not independent
implementations:

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
`a -> chi(N a)` (line 6725). This lane extends that rule, which the paper states only for
characters, to a rival's Dirichlet coefficients `a(n)`: `f(a) = a(N a)` goes in the eta
slot, and the rival's bad primes join S (`S = {(2), (lambda), (5)}` for both rivals).

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

**The failing local terms.** Both steps of the identity fail for both rivals.

1. **The single-prime closed form.** With `eta(p) = f(p)`, the first monomial where the
   rival's series leaves the closed form is, in the `u = 1` row, the `R(1-Q^{-1})` entry
   (family `(0, 2r+2)`, `r = 0`, the monomial `X^6 V`), where `f(p^6)` replaces
   `f(p)^6`: DH at norms 7 and 13 (`f(p^6) = -1` against `kappa^6`), Epstein at 7, 13
   (`1` against `0`), 19 and 31 (`7` against `64`). In the other rows the first failure is
   `J_2` (row 2, `t = 3`), the first entry of `J_3` (row 3), `J_4` (row 4) and `J_5`
   (row 5) for DH at 7 and 13 and Epstein at 19 and 31; for Epstein at 7 and 13, where
   `f(p^3) = 0 = f(p)^3`, row 2 first fails at `t = 6` and row 3 at the `X^4` entry of
   `J_3`. Below `t = 6` the `u = 1` row has monomials only at `t = 0` and `t = 1`, and
   its `X^6 V` coefficient carries `C_p(6, 0, 6) = Q^6 - Q^5`, which is never zero
   (`test_row_zero_reads_only_t_0_1_below_six`, at norms 7, 13, 19 and 25): that row
   fails at `X^6 V` exactly when `f(p^6) != f(p)^6`.
2. **Separation into prime factors (line 3994).** In the `u = 1` row the coefficient at
   the squarefree index `c = 7 = (1 + 3w)(-2 - 3w)`, which the product of local factors
   gives as `D_p D_pbar` (the product of the two `J_0` entries `-eta rho^{-1} Q^{-x}`),
   comes out as `f(7)` times the same Gauss-sum phase. The phase itself separates (the
   trivial character passes), so at a pair separation holds exactly when
   `f(pq) = f(p) f(q)`. DH: `f(7) = a(49) = -1` against
   `f(p) f(pbar) = kappa^2 = 0.0807009`. Epstein: `1` against `0`. Also failing: DH at
   (7, 13) (`1` against `-kappa^2`) and Epstein at (19, 19bar) (`3` against `4`).

**Which step fails where: both, on the same primes.** No tested index has a rival pass
the single-prime closed form and fail only the separation.

* *DH.* The placed coefficient depends only on `N a mod 5`. Where `chi(N p)` is real
  (`N p = 1` or `4 mod 5`: among the tested primes those of norm 19 and 31, and every
  inert prime, whose norm is a square), `f(p^t) = f(p)^t` for every `t` and `f(pq) = f(p) f(q)` for
  every `q`: DH agrees with the Hecke character `chi o N` on every power of `p`, and
  neither step can fail at `p`. Where `chi(N p)` is not real (`N p = 2` or `3 mod 5`:
  norms 7 and 13), the single-prime closed form fails at `X^6 V`, and separation fails at
  every pair of two such primes (`-1` against `kappa^2`, or `1` against `-kappa^2`) and
  at no other pair. The coefficient statements are exhaustive over the residues mod 5
  (`test_dh_both_steps_fail_on_the_same_primes`); the closed form was computed at norms 7,
  13, 19 and 31, and the global coefficient at (7, 7bar), (7, 13), (19, 19bar) and
  (7, 19). The single-prime identity is therefore a shared lemma for DH only at primes
  where DH is locally a character, and at those primes separation holds as well.
* *Epstein.* The single-prime closed form fails at every tested prime (7, 13, 19, 31).
  At a split prime `p | ell`, `f(p^t) = sum_{i <= t} chi_5(ell)^i`, so `f(p^6)` is `7`
  against `64` when `chi_5(ell) = 1` and `1` against `0` when `chi_5(ell) = -1`; from
  the coefficients this holds at all 21 split `ell` below 200. Separation fails at the
  conjugate pairs `(p, pbar)` over one rational prime (computed at (7, 7bar) and
  (19, 19bar); from the coefficients, `f(ell^2) != f(ell)^2` at all 21) and holds across
  distinct rational primes (computed at (7, 13) and (7, 19), both sides zero; from the
  coefficients, at all 210 pairs of the 21), as
  `test_epstein_single_prime_fails_everywhere_and_separation_only_at_conjugates` pins.
  For Epstein the step that fails at every tested prime is the single-prime closed form,
  and separation is shared at pairs over distinct rational primes.

The first version of this section called the single-prime identity a shared lemma for DH
in the sense of `ALIGNMENT.md` section 5, and the separation the step DH cannot pay. That
reading is withdrawn (section 7); the computed values it rested on are unchanged.

*Scope.* The placement tests the identity's terms, not the rivals' zeros: the
norm-composed series are not the rivals themselves (for DH it is
`c_1 L(chi) L(chi chi_-3) + c_2 L(chibar) L(chibar chi_-3)`), and no zero of either placed
series is computed here. The kill condition "a claimed arithmetic step also holds for a
function with a zero beyond the claimed abscissa" does not fire on this step.

## 3. The lower-order probes, one prime each

These are the referee's own constructions from the task's one-line descriptions, built
before any lane file was opened (this lane has never read the probe lane's definitions;
section 5). The one report about them, from the adversarial review, is attributed as such
in the S1 bullet.
"Scalar" means in `mu_infinity * alpha(p)^Z`, the values a Hecke character can take at p;
the test is exact (`x^12 alpha^{-a}` a root of unity), and `alpha(p)` is checked not to be
a root of unity.

* **S1, cubic theta with the conjugate cubic twist (k = 3), at norm 7.**
  `gamma_2 gamma_4 = 1` exactly, also at the two-prime indices `7`, `(1 + 3w)(4 + 3w)`,
  `(1 + 3w)(-2 + 3w)`, `(4 + 3w)(-2 + 3w)` and `(1 + 3w)(1 + 6w)` and at the products of
  the conjugate primes above 13 and above 19: the product itself carries no Moebius sign
  and no cross phase. This holds at every squarefree `c` prime to 6, by an argument the
  adversarial review supplied: at a prime, `tau(H^2) tau(H^4) = H^2(-1) P = P` (section
  1.1's `tau(A) tau(conj A) = A(-1) P` with `A = H^2`), and for `c = p_1 ... p_r` the CRT
  cross factors of `g_2(c)` and `g_4(c)` multiply to `prod_{i != j} chi_{p_i}(p_j)^6 = 1`
  (*derived*: a two-line argument, checked exactly at the indices just listed).
  * *The paper's row normalization.* At one prime the `u = 1` coefficient of `X` is
    `+conj(alpha(p) G(p)) eta rho^{-4}`: the angular factor `conj(alpha)` does appear, as
    the kill says, together with `conj(G(p))`. Across primes this coefficient separates
    only where the pair phase is trivial. Its squarefree part is `conj(alpha(c) G(c))`,
    and `G(pq) = G(p) G(q) R(p, q)`, so at `pq` it is `conj(R(p, q))` times the product
    of the two one-prime values.
    `R(p, q) = -1` at (7, 13), (7, 19), (13, 19) and (7, 31), and `+1` at the conjugate
    pairs above 7, 13 and 19 (exact, with `Gamma` summed directly and compared with Lemma
    4.3; `test_S1_does_not_separate_in_the_paper_row_normalization`). In the same
    normalization the paper's own probe gives `mu(c)` at every one of these indices and
    separates; dropping the `conj(G)` insertion, a planted lesion, flips both verdicts at
    (7, 13) (`test_S1_pair_phase_lesion_without_the_G_insertion`). So in that
    normalization S1 has no single Euler product
    `L(s, eta conj(alpha))`, in either position. Reading line 3416, which expands
    `conj(G(A))` over the characters of `T-hat`, what remains is a finite combination over
    `T-hat` (*inferred*, not computed here). The first version of this bullet stated the
    paper-normalization coefficient at one prime only.
  * *The bare row.* With no angular, no `G` and no `R` insertion (all three are there to
    cancel phases that `gamma_1 gamma_2 = mu alpha G` produces and this product does not)
    the coefficient of `X` is exactly `+eta rho^{-4}`, and it separates. **At norms 7 and
    13, inside the box `t <= 7`, `k <= 2`, `m <= 3`, the bare-row local factor at `u = 1`
    has the scalar shape** `(1-V)^{-1} (1-W)^{-1} (1 - eta^2 X^2)(1 - eta X)^{-1} H`, with
    no pure `X` or `X^2` left in `H - 1`: the target sits in the numerator,
    `L(x, eta)/L(2x, eta^2)`, not `1/L`. The size exponents of `H - 1` that the tests
    bound are floats measured at those two primes; no convergence of the correction
    product over all primes is shown.
  * *Scope of the construction.* That factor shape is specific to this lane's S1, which
    keeps `H = u a^6` with `V = Q^{-6z}` and twists the s-side character to `chi^{4k}`.
    The adversarial review reports that the probe lane's `PROBE.md` (uncommitted, not
    opened by this lane) defines S1 as "cubic, j = 4", the twist used here, and prices it
    with pole 1/3 (as reported, not checked here). D1 is then not about the twist; what
    remains is normalization and decomposition. The sign in D1 depends only on the
    `(t, k, m) = (1, 0, 0)` coefficient, which reads neither the a-variable nor the s-side
    twist, so it is unaffected.

  The shape a zero detector needs, `1/L(x, eta)`, is absent in both normalizations, but
  not for the stated reason (disagreement D1 in `disagreements.json`).
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
untracked on `hunt/below-seven-eighths` at every check (HEAD `9c1f21c52` in wave 1,
`baa41597e` at the repair), and the task forbids treating uncommitted files as final.
This lane has not opened them. The kill statements compared in section 3 are the task's
descriptions of them, not the lane's text; the one report about `PROBE.md` in section 3
is the adversarial review's, attributed as such. `disagreements.json` lists the one
disagreement with those descriptions and records the comparison as outstanding.

## 6. Notes for the owner and the verifier

* **N1.** Because the closed form is free of Gauss sums, a route that checks only
  `(local-P) = closed form` cannot see a sign error in `G_1` outside rows 3 and 4. The
  inputs need their own check (here Lemma 4.2 and the raw coefficient).
* **N2.** The worktree's branch was not created from `origin/main` `fb647bfc7`, as the
  task's override states (the repair task's override repeats it); its base is
  `d5d1dfc81`. No file outside `referee/` was touched.
* **N3.** A process listing taken to find this lane's own background job displayed
  another session's command lines, which named tests and planted-fault strings of the
  uncommitted `euler_step.py` and `test_euler_step.py`. This lane did not open those
  files and shares no module or function with them; the disclosure is made because the
  route is meant to be independent. The adversarial review compared the two files and
  reports six textually identical lines: the pinned SHA-256 constant, the `from
  __future__` import, three lines of generic `Z[omega]` arithmetic, and the `omega_p`
  exponent line of `(local-P)`, variable name `om_exp` included (as reported; this lane
  still has not opened `euler_step.py`). That exponent line transcribes the exponent
  `tk - e_0 l - l(l-1)/2` of paper line 4002.
* **N4.** The adversarial review reports reproducing the prime-level checks with its own
  code, which uses neither PARI nor python-flint, at further primes, and the global
  coefficient one level deeper than here, row 5 included. That code is outside the
  repository and this lane has not inspected it, so nothing in this report rests on it
  and no grade here is raised by it.
* **Rerun at another prime.** `local_identity_pari.py --norm 31` runs the prime-level
  battery (Lemma 4.2, the lift, the C_p table, the closed form for all rows and phases,
  the raw route, `H_p`) and both planted faults; the slow test tier includes norm 31.
  Default tier: `.venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/referee -m "not slow"`
  (about three minutes on the campaign box, measured once, not pinned).

## 7. Corrections after the adversarial review (2026-10-21)

An independent adversary reviewed wave 1 and returned "holds with fixes": one major issue
and six minor ones. Every experiment of wave 1 is kept; what changed is listed here.

1. **Rival verdict (major), withdrawn and replaced.** Wave 1 called the single-prime
   identity a shared lemma for DH and the separation into prime factors the distinguishing
   step. Its own data contradicted that: DH fails the single-prime closed form at every
   tested prime where `chi(N p)` is not real, and fails separation only at pairs of such
   primes. Section 2 now says that both steps fail, on the same primes, and pins the
   residue structure (DH) and the split-prime structure (Epstein) by two new tests.
2. **D1, three additions (minor).** The review's report that the probe lane's S1 uses the
   same `chi^4` twist; the computation that S1 does not separate in the paper's row
   normalization (pair phase `conj(R(p, q))`, new test); and the scope of this lane's S1
   construction. Section 3 and `disagreements.json`.
3. **Grade wording (minor).** The bold S1 factorization sentence is now scoped to norms 7
   and 13 and the stated box, the size exponents are labeled as floats measured at those
   primes, and the argument for the sign at every squarefree `c` is written out.
4. **Citation (minor).** `gamma_2 gamma_4 = 1` is on paper line 4124, not 4122 (section
   1.1 and the check's label in `lemma_4_2_checks`), pinned by
   `test_gamma_2_gamma_4_is_cited_at_line_4124`; lines 3416 and 4002 are now pinned too.
5. **Versions (minor).** 2.17.2 is the PARI library; the cypari2 package is 2.2.4
   (section 0).
6. **Push status (minor).** The header paragraph now records that the branch was pushed
   after wave 1, not by this lane.
7. **Wording (minor).** The rival placement is stated as this lane's extension of the rule
   on line 6725, and the raw and global routes as distinct derivations sharing one
   module, not independent implementations (sections 1.4 and 2).

## 8. Open issues

* The comparison with `euler_step.py` and `probe_table.py` is outstanding: neither is
  committed on the branch.
* D1 is unresolved and goes to the owner. After the review it is narrowed to
  normalization (whether the probe keeps the `conj(alpha)` and `conj(G)` insertions) and
  decomposition (one Euler product or a finite combination over `T-hat`).
* The `T-hat` reading of line 3416 in section 3 is *inferred*; no finite combination over
  `T-hat` is computed here. The bare-row S1 factor shape is checked at norms 7 and 13 in a
  box, and no convergence of its correction product is shown.
* Lemma 7.1 is checked only at the stated primes and inside finite boxes. The global
  coefficient is compared with the local summand only for `t <= 4` at norm 7 and `t <= 1`
  at norms 13 and 25, and row 5, which needs `t = 6`, is not computed globally here.
* The analytic part is exponent bookkeeping given the closed form, not a proof of normal
  convergence; above the directly summed depths the inner Gauss sums use the paper's
  lift.
* The rivals are placed by this lane's extension of the rule on line 6725; the placed
  series are not the rivals themselves, and no zero of either is computed. Beyond the
  computed pairs, the step-by-step verdict of section 2 rests on the coefficient
  structure together with the reduction of separation to `f(pq) = f(p) f(q)`, which is
  checked at the computed pairs only.
