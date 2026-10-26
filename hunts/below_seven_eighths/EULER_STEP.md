# EULER_STEP: the step where the 7/8 argument uses the Euler product, checked exactly

Hunt #136, lane `eulerstep`, 2026-10-21. Revised twice the same day after two rounds of
an adversarial verifier: the first listed seven issues, all minor; the second listed one
major issue (the lane's report described its files as they stood before the first
repair) and nine minor ones. Each issue is listed with what was done under "Repair
rounds" below. A probe: nothing here is a result until the case log in
`hunts/README.md` says how the hunt ended. Instrument: `euler_step.py`. Every number
below is pinned by `test_euler_step.py` (fast tier, or `slow` for the full ranges), and
the tests read this file: its line numbers, its fractions, its rival table and its
headline counts.

Grades, as in `MISSION.md`: *cited* (a line of paper.tex, quoted); *derived* (algebra
or a finite computation done here in exact integer arithmetic and pinned by the
tests; a finite computation is derived only on the range stated); *inferred* (a
reading that no computation here checks); *measured* (a floating-point route);
*enclosed* (a python-flint ball carries the step). Nothing in this file is
kernel-checked, and nothing here bears on Re s = 1/2.

Source: OpenAI, *The Quasi-Riemann Hypothesis*, paper.tex at the pinned commit,
16,677 lines, SHA-256 `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`,
read as data from `<cache>/openai-math-adc7f124/paper.tex`.
All 202 line citations in `euler_step.CITATIONS` are checked against that file, each on
its own line: every citation moved one line up, or one line down, fails the check. Every
line number below is one of them (`test_every_line_number_in_the_document_is_a_cited_line`
reads this file for that).

## The answer

Lemma 7.1, the scalar Euler identity, and its Gauss-sum inputs (Lemma 4.2, Lemma 4.4
with (4.7), and the 11/12 paper's Appendix A.1 form) agree with exact computation
everywhere they were tested, and no discrepancy with the paper was found. The local
closed form (7.11) follows from the defining series (7.10) as an exact identity of
formal series, with the Gauss sums as symbols tied only by the four relations the
proof names (derived). Those relations hold exactly at every one of the 1234 prime
ideals of norm at most 10^4 outside S, 1222 split and 12 inert, each by summation in
Z[omega][zeta_ell] (derived on the range). (7.10) equals (7.11) again with the true
Gauss sums, and no relation between them assumed, at all 165 prime ideals of norm at
most 1000 (derived on the range). Table (7.16), all ten of its rows, matches the
summands of (7.10) on a window of 7128 cases (derived on the window), and the
evaluation (7.8) matches the definition (7.7) by brute force over O/p^t, up to t = 7
at norm 7 and to smaller t at norms 13, 25 and 121 (derived on the range). At p = 2
and p = 3 the statement is not local and is not made: the sextic symbol does not
exist there (derived), and those primes are in S by hypothesis (cited).

The rivals fail exactly where the Euler product is used. The Davenport-Heilbronn
combination fails multiplicativity at the first coprime pair of good ideals, the
conjugate pair over 7, where a(49) = -1 while a(7)^2 = kappa^2; its first failing pair of
distinct norms is (7, 13); and it fails the prime-power test at t = 6. The Epstein zeta
of discriminant -15 fails on the conjugate pair over 7 and at t = 6 (derived). What the
step's local tests separate is degree one, complete multiplicativity with unit values,
from everything else. They do not single out Hecke characters: a truncated chi_5 that is
no Hecke character passes them all (derived on the range; that it is no Hecke character
is inferred).

A by-product for the campaign: the Euler step does not bind at 7/8. A scan of paper.tex
finds 52 lines outside Section 7.2 that name the lemma, one of its labels, an Euler
region, D_1 or D_2 (Section 1.1). The 26 of them that use the second region ask of the
local factors, at every row u, at most x_r > 2/3 at the residue point and x_r > 401/600
at the region's corner (w_r, z_r) = (19/20, 33/200). Part II's estimate
B_p = -1 + O(Q^(-7/8)) carries the region's own x-floor, through the monomial
D = eta(p) Q^(-x); the multiplier itself needs only x_r > 3/5 at the residue point and
x_r > 301/500 at the corner (derived exponents, inferred completeness; Section 6).

## Repair rounds

### Round 1 (2026-10-21)

| the verifier's issue | what was done |
|---|---|
| Section 6 drew its conclusion from the Part I consumer and missed where Part II consumes the second region and its exponents | Part II's consumers are listed (1.1) and computed (Section 6): the majorant of 8748 to 8749, the lower bound of 9054, and the principal multiplier of 9051 to 9077, whose four exponents (9068) carry the 7/8 that feeds 15613, 15619 and 16304. The conclusion survives with them. |
| "singles out single Hecke characters" overreached | Withdrawn. Section 5 now states what the controls support, with a new control, a truncated chi_5, that passes every local test without being a Hecke character. |
| table (7.16) has ten rows, not twelve | Corrected. The old twelve cases were the ten rows with rows 1 and 6 sampled twice. The check is now complete on a window, with rows 1 and 6 at every j. |
| route (b) said "no relation assumed" but formed gamma_1^(-1) = conj(G_1) Q^(-1/2), which assumes abs(G_1)^2 = Q | Route (b) now multiplies the identity through by G_1 (nonzero, checked), so gamma_1^(-1) is never formed and no relation is assumed. Re-run at all 165 ideals. |
| (4.6) G(p^3) = gamma_3(p) was read off the four-term formula at p^3 and never summed; the entry `G_unit` was hard-coded | Gamma(p^t) is now summed over O/p^t, t up to 3, at 25 prime ideals (14 of them in the fast tier), and (4.6) holds exactly there. `G_unit` is replaced by the exact product behind abs(G(p)) = 1, at all 1234. |
| the lane's report counted 13 planted faults, one of which is a control | Faults and controls are separated: 16 faults (the first round's 12 and one for each new check) and 1 control. |
| the reserved stem appeared in sibling lanes' files | Not this lane's files, so not edited here. This lane's three files contain no form of it; `test_lexical_rules_of_this_lane` reads their bytes. |

### Round 2 (2026-10-21)

| the verifier's issue | what was done |
|---|---|
| major: the lane's report repeated counts from before round 1 and the withdrawn claim that the step singles out Hecke characters | The report is regenerated from the files as they now stand, with a new runmanifest; the counts it quotes are the ones this file states and the tests pin. |
| "fails multiplicativity at the first pair of good ideals, of norms 7 and 13" | Corrected in The answer and Section 5: the first coprime pair of good ideals is the conjugate pair over 7, where the combination already fails (a(49) = -1, a(7)^2 = kappa^2); (7, 13) is the first failing pair of distinct norms. Both are pinned. |
| the rival table counted the prime above 5 for the Davenport-Heilbronn combination but excused it as in S for the controls; its Moebius column was computed over Q without saying so | Each target now has its own S, the primes above 6 and above its conductor (3336 to 3340), and every column counts that target's good norms; the Moebius column is computed over the good ideals of F, and the values over Q move to the prose. `rival_table_rows` generates the table, and a test checks this file against it. |
| the docstring of `chi5_truncated` applied the density argument to the quotient by chi_5 o N | Corrected: it applies to the function itself, which is 1 at every prime ideal over a rational prime above 100 and i at norm 7 (both values pinned). |
| local data (7.6) runs from 3861 to 3867, not 3862 to 3866 | Corrected, with 3861 and 3867 cited. |
| the consumer list was not every occurrence of the lemma's label, and Section 6 called its own coverage principal-row only | Section 1.1 is rebuilt from a scan of paper.tex: every line outside Section 7.2 that names the lemma, a label defined in Section 7.2, an Euler region, D_1 or D_2, 52 lines, each cited and placed in a group; `test_consumer_scan_is_complete` repeats the scan. Section 6 now covers every row u: rho = chi_p(u) is formal at the primes not dividing u, and the factors at p dividing u are computed for j = 1 to 5. The conclusion stands. |
| the line-number test missed a number before a period and the numbers of a hyphenated range | The scanner reads both. The verifier's two planted strings (a line number ending a sentence, and a hyphenated range of two line numbers) now go red. |
| no planted fault exercised the citation checker | Every one of the 202 citations moved one line down, and every one moved one line up, fails; so does one wrong line. A checker weakened to a search of the whole file would let them pass, and `test_citation_checker_is_line_specific` would go red. |
| no test read this file's numbers | `test_doc_sync` pins every fraction in this file (each one computed by the tests or cited from paper.tex), the rival table and the headline counts. A Section 6 floor changed to a nearby fraction, and one count of the rival table changed by one, both go red (planted). |
| the round-1 note on the reserved stem was time-bound and went stale | Reworded to cover only this lane's three files, which a test reads. |

## 1. The statements, with every hypothesis

### 1.1 Lemma 7.1, lines 4010 to 4067 (cited)

Setting. F = Q(sqrt(-3)) (line 568), O = Z[omega], lambda = sqrt(-3) = 1 + 2 omega
(572); alpha(a) = a/|a| (575); e(z) = exp(2 pi i Tr(z/lambda)) (610); ideals coprime to
3 have a unique primary generator, congruent to 1 mod 3 (581). S is a finite set of
primes containing the primes above 6 (591) and, for the probe, the supports of every
fixed character presentation and every prime of norm at most P_0 (3336 to 3340); ideal
sums exclude S and use primary generators (603). For p outside S the residue field
has order q_p = 1 mod 6 (627); chi_p(a) is the sextic symbol, a^((q_p-1)/6) mod p
(631), zero at p | a, extended multiplicatively, with exponent 0 meaning the
coprimality indicator (639); gamma_j(c) = q_c^(-1/2) sum chi_c(v)^j e(v/c) (642);
g_psi(c, k) = sum_{d mod c} psi(d) e(kd/c) (3359).

Hypothesis (4011 to 4012): u a nonzero sixth-power-free element with (u, S) = 1, and p a
prime outside S. Local data (7.6), lines 3861 to 3867: Q = q_p, j = v_p(u) in {0..5},
rho = chi_p(u/p^j), omega_p = chi_p(-1), a_p = conj(alpha(p))^3 eta(p)^3,
b_p = conj(alpha(p))^2 eta(p)^2 conj(chi_p(4)), V = Q^(-6z), R = a_p^2 Q^(4-6x-6z),
W_loc = rho Q^(-w). Gauss sums G_r = g_{chi_p^r}(p, 1), G_0 = -1, gamma_r = Q^(-1/2) G_r
(3874 to 3875). C_p(t, k, j') is defined by the sum (7.7) (line 3892) and evaluated in
(7.8) (line 3900); P_p is the series (7.10) (3997 to 4004), P_p^* its part with t > 0.

Statement. (7.11), lines 4016 to 4031: P_p^* = (1/(1-R)) {[R(1 - Q^(-1)) - eta(p)(Q-1)
Q^(-x-w) V^(1_{j<=1})]/(1-V) + J_j} and P_p = 1/(1-V) + 1_{j=0} W_loc/(1 - W_loc) + P_p^*,
with the six J_j of the table. (7.12), line 4038: H_p = P_p (1-V)(1-W)/(1-D),
W = chi_p(u) Q^(-w), D = eta(p) conj(chi_p(u)) Q^(-x). (7.13): F_{eta,u} =
zeta_F^S(6z) L^S(w, chi(u)) / L^S(x, eta conj(chi(u))) times the product of the H_p.
Normal convergence on the regions (7.14) (4054) and (7.15) (4056); for u = 1 in (7.15),
H = 1 + O(P_0^(-c_H)) with c_H = 4/5 (4064). The proof's table (7.16) (4086 to 4098)
has ten rows; its first holds for every j (4083), and "Every omitted case is zero"
(4084).

Where it is consumed (cited; the grouping is this lane's reading). A scan of paper.tex
finds 52 lines outside Section 7.2 (the subsection "The scalar Euler identity", lines
3847 to 4199) that name the lemma, refer to a label defined in Section 7.2, say "Euler
region", or name D_1 or D_2; `test_consumer_scan_is_complete` repeats the scan. Each
line is cited, was read in context, and is placed in one group:

- Pointers, notation and the regions' definitions, with no requirement (8 lines): 217
  and 3380 (forward pointers); 5467, 8658 and 8662 (notation); 5571 and 5574 (the
  definitions of D_1(eps_0) and D_2); 5578 ("These are the two regions in Lemma 7.1").
- Region one only (12 lines), whose floors 51/100, 17/50, -1/100 and
  x_r + w_r >= 1 + eps_0 do not involve the target: 5842, 5859, 5879, 5933 and 5934
  (D_1(10e) and its stronger estimate); 6418 and 6469 (D_1(3/8)); 8735 and 8737 (the
  majorant (8738) in region one); 8909 and 9046 (the dynamic region x_r = a + 16e,
  w_r = 1 - a - 6e, z_r = 17/50 of line 8856, inside D_1(10e)); 9134 (the first region
  with eps_0 = 3/8).
- Region two at the principal row u = 1 (11 lines): 5525 (Part I: H_eta(s) =
  H_{eta,1}(s, 1, 1/6) (5520) is holomorphic on Re s > 7/8, and P_0 is fixed so that
  sup |H_eta - 1| <= 1/2 (5531), the hypothesis (2.2) of Proposition 2.1 (400, 413));
  6294 (H_eta holomorphic and bounded there); 6784 (the proof of the 11/12 theorem:
  H_eta holomorphic and nonzero on Re s > 11/12); 6232 and 6239 (the principal residue
  paths at Re s = beta_* + e, with w moved to 19/20 and z to 33/200, lie in D_2); 6318
  (the principal rectangle lies in D_2); 9052 and 9062 (the principal local factor and
  the principal factorization: H_p is bounded away from zero (9054); the four error
  exponents are -x_r, -6z_r, 4 - 5x_r - 6z_r and 1 - w_r - 6z_r (9068 to 9069), "Each is
  at most -7/8 in that region" (9071), so B_p = -1 + O(Q^(-7/8)) (9074)); 9084 (the
  principal tuple bound, which reuses the second-region majorant (9081)); 15557 (that
  bound on the whole rectangle); 15594 (B_p = -1 + O(q_p^(-7/8)) applied at w = 1,
  z = 1/6 (15597, 15599)).
- Region two at every row u (15 lines): 5609 (the data must be holomorphic near each
  point of D_2 and of every D_1(eps_0)); 5656 (the lemma gives that holomorphy and the
  all-height majorant for the base probe); 5907 and 5910 (|H_{eta,u}| << q_u^eps in both
  Euler regions); 6479 (the large rows (2, 2, v) lie in D_2); 8690, 8695 and 8696
  (G_p = H_p B_p, and |R|, |V|, |D| < 1 make G_p holomorphic in both regions); 8699 and
  8729 (the selected factorizations); 8748 (the majorant (8738) in the second region
  "uses the respective defect exponents -363/200 and -33/40" (8748 to 8749)); 8757
  (holomorphy of the tuple sum); 8817 and 8826 (the identity (16.8), whose denominators
  1 - R, 1 - V and 1 - D are nonzero in both regions); 15537 (the full correction is
  holomorphic in the two required regions).
- (7.13) used as an identity, with no bound (6 lines): 5468, 5565, 5655, 8714, 8727 and
  8775.

Second-order uses were followed by reading along the chain that carries the 7/8 of
(9074): |rho_i| << P_i^(-7/8) (15613); a pretarget number 0 < kappa_P < (7/8) min_i l_i
(15619), chosen as kappa_P = 7/(96K) with m_P := kappa_P (16304 to 16306); the remainder
Z^(C(beta_*)+e-kappa_P+eps) (15669); e + eps_pr < m_P/4 (16317); and the common saving
m = (1/4) min{m_high, m_w, m_z, m_P} > 0 (16366). The interface lemma asks only for some
mu > 0 chosen independently of eta (6201); it is stated for sigma_0 in [7/8, 1) (6178),
and the shared lemmas take sigma_0 = 7/8 (15532). The other second-order uses (of
(5531), of the majorant (8738) and of the tuple bound) were not traced line by line;
that they ask nothing more of the local factors is inferred.

Local and global (inferred from the text). (7.11) and the exponent bounds are
statements at one prime. (7.13) is global: it rests on the separation of the
coefficient (7.4) into prime factors ("has therefore separated into prime factors",
3995), which uses reciprocity across pairs of primes (3953 to 3992), the unit factor
U_p (7.9) (3930) and the b_* bookkeeping (3941 to 3951). The coefficient (7.4) depends on
the target only through the factor eta(A), A = c n^3 (3820).

### 1.2 The Gauss-sum identity

paper.tex has no appendix: the file contains neither `\appendix` nor an appendix
environment (derived, a scan of the file). The identity hunt #120 quotes from the
11/12 paper's Appendix A.1 (`hunts/qrh_rival_step/RESULTS.md`, section 2.2: "valid for
squarefree primary n away from a fixed set of excluded primes: mu(n) gamma_{-1}(n) =
chi_n(-1) G(n)^{-1} conj(alpha(n)) gamma_2(n)"; cited second hand, the 11/12 source was
not read) has these counterparts in the 7/8 paper (cited):

- Lemma 4.2, lines 766 to 775. For p the primary generator of a prime ideal outside S,
  H = chi_p: gamma_2(p)^3 = -alpha(p); gamma_1(p) gamma_2(p) = conj(H(4)) gamma_3(p)
  gamma_2(p)^3; |gamma_j(p)| = 1 for j not divisible by 6.
- Lemma 4.3, lines 841 to 869. Gamma(c) = |c|^(-1) sum_{x mod c} e(x^2/c) =
  (1 + i^(-b) + i^a + i^(b-a))/2 for odd c = a + b omega (851), with the table on the
  square classes 1, -1, lambda, -lambda and the bicharacter (4.4) (864).
- Lemma 4.4, lines 934 to 972. chi_b(a) = R(a, b) chi_a(b) for coprime primary a, b
  outside S (938); G(c) = conj(chi_c(4)) Gamma(c) (946); (4.5) G(vw) = G(v) G(w) R(v, w)
  (951); (4.6) G(p^3) = gamma_3(p) and R(p, p) = gamma_3(p)^2 = chi_p(-1) (955 to 956);
  and (4.7), for squarefree c: gamma_2(c)^3 = mu(c) alpha(c), gamma_1(c) gamma_2(c) =
  mu(c) alpha(c) G(c), G(c) = conj(chi_c(4)) gamma_3(c), |G(c)| = 1 (966 to 968).

Derived: under the 7/8 definitions, the 11/12 form is equivalent to the second
identity of (4.7), given |gamma_j(c)| = |G(c)| = 1 and gamma_{-1}(c) = chi_c(-1)
conj(gamma_1(c)) (substitute v -> -v in the defining sum). That the 11/12 paper's G is
this G is inferred; the 11/12 form is in any case checked directly below.

## 2. How the checks are made

- **Exact arithmetic.** An element of Z[omega][zeta_N] (N the exponent of O/m, prime to
  3) is a pair of integer coefficient vectors; products are exact cyclic convolutions
  (python-flint `fmpz_poly`, or Python integers once a product would leave 64 bits);
  equality is equality of canonical coordinates in the power basis of each prime-power
  factor, a basis of Q(omega, zeta_N) because 3 does not divide N. Each identity is
  restated without square roots, for example gamma_2(p)^3 = -alpha(p) as G_2^3 = -p Q.
- **The additive character** is e(w/m) = zeta_{N(m)}^d with d the omega-coordinate of
  w conj(m) (derived from line 610: Tr(y/lambda) is the omega-coordinate of y in O). A
  second route, the complex form exp(4 pi i Im z / sqrt 3) of line 613, agrees to 1e-9
  on 400 random pairs (w, m) (measured).
- **The one square root.** Lemma 4.3 asserts the sign of a quadratic Gauss sum. Its
  square is checked exactly; its sign by an acb ball (enclosed). The same holds for
  Gamma(p^t) at odd t; at even t the sum is checked exactly, with no sign to decide.
- **Lemma 7.1, three routes.** (a) Generic: (7.10) and (7.11) as truncated formal series
  in X = Q^(-x), W = Q^(-w), Z = Q^(-z), up to X^25, W^3, Z^30, the Gauss sums symbols tied
  only by gamma_1 gamma_2 = -alpha conj(chi_p(4)) gamma_3 (4118), gamma_2 gamma_4 = 1
  (4124), G_1 G_{-1} = omega_p Q (3886), gamma_3^2 = omega_p (4079), every unit symbol
  (eta(p), alpha(p), chi_p(4), rho, gamma_1, gamma_3) otherwise free. (b) At actual
  primes, with that prime's true G_r, eta and rho kept formal, up to X^13, W^2, Z^18.
  The series is A + gamma_1^(-1) B, A from e_0 = 0 and B from e_0 = 1, and the closed
  form C contains no Gauss sum, so the identity is tested as G_1 (A - C) + Q^(1/2) B = 0.
  That uses only the definition gamma_1 = Q^(-1/2) G_1 (3875) and G_1 nonzero, checked
  exactly: no relation between the Gauss sums is assumed. (c) (7.7) against (7.8) by
  summation over O/p^t and O/p^k.
- **Table (7.16), completely on a window.** Every summand of (7.10) with r <= 10, each of
  the four families of line 4075, k <= 2, j in 0..5 and m <= r + 3, against R^r times the
  sum of the entries of the rows whose conditions hold, and zero where none does.
- **Gamma(p^t) directly**, summed over O/p^t (Q^t residues), t up to 3.
- **Where the step binds.** The exact exponents of the truncated expansions of H_p - 1
  for every j (to X^19 W^3 Z^24; at j = 0 rho = chi_p(u) stays a formal unit, so the
  j = 0 numbers hold for every row u at the primes not dividing u) and of Part II's
  principal multiplier B_p + 1 = (G_p + H_p)/H_p (to X^12 W^2 Z^18), the latter with a
  second, floating-point route (measured).
- **The consumer scan** of Section 1.1: paper.tex searched, outside Section 7.2, for the
  lemma's label, every label defined in Section 7.2, "Euler region", and D_1 or D_2.
- **This file.** The tests read it: every integer of three to five digits must be a
  cited line or a listed count; every fraction must be computed by the tests or cited;
  the rival table must equal the one `rival_table_rows` generates; and the headline
  counts must match the computations.

## 3. Results

| statement | range | grade | outcome |
|---|---|---|---|
| the line citations | all 202, each on its stated line; moved one line up or down, every one fails | derived (a text check) | holds |
| the consumer scan (Section 1.1) | every line of paper.tex outside Section 7.2: 52 lines found, each cited and grouped | derived (a text search); the grouping inferred | as listed |
| Lemma 4.2 (both identities and abs value 1), (4.6) through the four-term formula at p^3, (4.7) at p including abs(G(p)) = 1, Gamma(p) = gamma_3(p), G_1 G_{-1} = omega_p Q, gamma_2 gamma_4 = 1, gamma_3^2 = omega_p | all 1234 prime ideals of norm at most 10^4 outside S: 1222 split (both primes above each of the 611 split rational primes up to 10^4) and 12 inert | derived on the range | holds |
| four-term formula at p (the sign of G_3) | the same 1234 | square derived, sign enclosed | holds |
| (4.6) G(p^3) = gamma_3(p) by summation over O/p^3, and Gamma(p^t) against the four-term formula, t up to 3 | 25 prime ideals: both primes over every split ell up to 100, the inert 5 and 11 (t up to 3) and the inert 17 (t up to 2); 14 of them, the split ell up to 43 and the inert 5 and 11, in the fast tier | derived on the range; the sign at odd t enclosed | holds |
| Jacobi route: J(H^2, H^2) = -p (line 834), J(H, H^3) = H(4) J(H, H) (803) | the same 1234 | derived on the range | holds |
| 11/12 (Appendix A.1) form at p | the same 1234 | derived on the range | holds |
| inert p = -ell: G_r = ell for r not divisible by 6 | all 616 inert ell in [5, 10^4] by the reduction below plus the exact values chi_p(4) = chi_p(-1) = 1; direct sums for all 32 inert ell up to 300 | derived | holds |
| (4.7) and the 11/12 form on squarefree composites | 7 composites, norms 7*13, 7*7 (a conjugate pair), 7*25, 13*19, 7*13*19, 25*121, 7*13*25 | derived; sign enclosed | holds |
| CRT rule gamma_j(ab) (line 1043) and R(a, b) as its cross factor (1048) | 4 pairs | derived | holds |
| sextic reciprocity (938) and the supplement chi_c(4) = (c / -2)_3 (1005 to 1009) | 93 primes of norm at most 500, 8556 ordered pairs, 3600 of them with R = -1 | derived on the range | holds |
| Lemma 4.3 table and bicharacter (4.4); Gamma depends on c mod 4 and Gamma(c v^2) = Gamma(c) | all 12 odd classes mod 4 | derived | holds |
| pair phases of Section 7.2: the identities at 3957, 3979 and 3987 | 300 random valuation tuples over 5 primes | derived on the range | holds |
| (7.10) = (7.11) and P_p^* likewise, every j | generic, to X^25 W^3 Z^30; every monomial carries eta to the power of its X-degree | derived | holds |
| table (7.16), its ten rows | r up to 10, k up to 2, every j, m up to r + 3: 7128 cases, 528 under a row (rows 1 and 6 at every j) and 6600 under none, all of them zero as line 4084 says | derived on the window | holds |
| (7.10) = (7.11) with the true Gauss sums, no relation assumed | all 165 prime ideals of norm at most 1000 (160 split, 5 inert) | derived on the range | holds |
| (7.7) = (7.8) | norm 7, both primes: t <= 7, k <= 1 (104 cases each); t <= 4, k <= 3 (100); norm 13: t <= 4, k <= 2 (75); norm 25: t <= 3, k <= 2 (54); norm 121: t <= 2, k <= 2 (36) | derived on the range | holds |
| the Gauss lift formula (3880 to 3881), every r | norm 7: t <= 7; norm 13: t <= 4; norm 25: t <= 3 | derived on the range | holds |
| (7.17) (4139), and Part II's (16.4) (8718 to 8719), (16.8) and the p dividing u form (8832) | rational-function identities | derived | hold |
| exponent bookkeeping of the proof | region (7.15): the maxima over the expansion are -363/200 at good primes and -33/40 at p dividing u, the numbers of lines 4173 to 4174; region (7.14) at its two minimal vertices: -101/100 and -1/100 at eps_0 = 1/100, -1001/1000 and -1/1000 at eps_0 = 1/1000, -21/20 and -3/100 at eps_0 = 1/20, inside the claimed O(Q^(-1-eps_H)) and O(Q^(-eps_H)) with eps_H = min(eps_0, 1/50) (4166) | derived | as claimed |
| Part II's four error exponents (9068 to 9069) as the leading exponents of B_p + 1 | 54 rational points: x_r from 61/100 to 3/2 at six (w_r, z_r), among them (1, 1/6) and (19/20, 33/200) | derived on the grid; series against direct evaluation measured | as stated |

The inert reduction (derived, and checked against direct sums for every inert ell up to
300): for p = -ell the additive character is e(v/p) = zeta_ell^(-y) at v = x + y omega,
trivial exactly on F_ell; chi_p is trivial on F_ell^* because 6 divides ell + 1; so
G_r = (ell - 1) - c with c = sum_x chi^r(x + omega) = -1. Every relation of Lemma 4.2
then reduces to chi_p(4) = chi_p(-1) = 1, which holds at all 616.

The truncation of route (a) is closed by the period structure the proof states (4076
to 4080): raising r by one, with the first permitted m, multiplies each family's summand
by R. Term by term this is the table check to r = 10. For every r it follows from two
facts, both checked by `test_period_structure_closes_the_truncation` (derived): with the
factor conj(gamma_3)^2 = omega_p, the omega_p exponent changes by 6k - 2e_0 - 2l, which is
even (checked for every l up to 40, and visibly for all l); and the Gauss lift ratio is
Q^6 (checked as an exact identity for every t up to 121 and every r).

Planted faults: nineteen, each confirmed red. Sixteen are in `planted_faults`
(`test_every_planted_fault_goes_red`). The first round's twelve: a sign flip in J_3
(fails at j = 3 only); dropping the -l(l-1)/2 term of the omega_p exponent; G_1 replaced
by G_5 in the fourth case of (7.8); the sign of the relation gamma_1 gamma_2 = -alpha
conj(chi(4)) gamma_3; Gauss sums built on the conjugate character; the conjugate prime in
gamma_2^3 = -alpha; one Gauss-sum coefficient moved by one; the congruence of (7.7)
dropped; the sign of mu in (4.7) on a composite; the two prime-route faults at true
primes; and a near miss, a character except at p^6, which the local test reports at
exactly t = 6. Four came with the round-1 checks: row 6 of (7.16) given the condition
m >= r; G(p^3) compared with gamma_3(p) without its factor Q; the sign of v^(-1) H_p
flipped in the principal multiplier, so that its -1 does not cancel; and G_5 in place of
G_1 as the multiplier of route (b). Three came in round 2, on the instruments that read
the paper and this file: every citation moved one line down, and every one moved one
line up (`test_citation_checker_is_line_specific`); a line number ending a sentence and a
hyphenated range of two line numbers, appended to a copy of this file
(`test_line_number_scanner_catches_planted_numbers`); and a Section 6 floor and a count
of the rival table changed in a copy of this file (`test_doc_sync_catches_planted_changes`).
Beside them one control must stay green, and does
(`test_the_control_beside_the_near_miss_stays_green`): the unmodified character passes
the test the near miss fails. One sensitivity limit is stated rather than hidden: the
omega_p exponent has no effect where omega_p = 1, so the prime-route fault is invisible
at norm 13 and visible at norm 19 (Q = 7 mod 12); route (a) catches it at every j.

## 4. p = 3, p = 2 and the transfer

Lemma 7.1 and Lemma 4.2 are stated only for p outside S, and S contains the primes
above 6 (591; cited). At those primes the statement is not local because its symbol
does not exist (derived): the residue fields have orders 3 (at lambda) and 4 (at 2), so
(Q - 1)/6 is not an integer; the sixth roots of unity collapse, omega = 1 mod lambda and
-1 = 1 mod 2; and no associate of lambda is primary. Their Euler factors are deleted on
both sides of (7.13) (zeta_F^S, L^S).

The transfer of Proposition 11.3 (6705) is the other place a local Euler identity is
used. For every one of the 1229 rational primes up to 10^4 (611 split, 617 inert
including 2, and the ramified prime 3) the splitting found by exhaustive search for an
element of norm p agrees with chi_{-3}(p), and the local factor identity of lines 6733
to 6741 holds as an exact polynomial identity in chi(p) and p^(-s) (derived on the
range). At p = 3 it holds exactly with eta(lambda) := chi(3), since N(lambda) = 3; the
paper instead deletes 3 from both sides.

## 5. The rivals, and exactly where the identity fails for them

Lemma 7.1 consumes three properties of the target on good ideals (inferred from the
proof, and each is visible in it): (M) multiplicativity on completed indices A = c n^3,
which the separation at line 3995 needs because (7.4) carries the target only as
eta(A); (C) eta(p^t) = eta(p)^t at each good prime for every t in the support of
P_p^*, which the closed form (7.11) needs; (U) |eta(p)| = 1 at good primes (3870, and
|D| < 1). Since every monomial of (7.10) and (7.11) carries eta to the power of its
X-degree (derived), putting a(p^t) in place of eta(p)^t changes the coefficient at
(t, k, m) of series minus closed form to (a(p^t) - a(p)^t) times the generic coefficient:
the local identity at p fails exactly at the least t of the support where
a(p^t) differs from a(p)^t. For the principal row j = 0 the support is
t in {1, 6, 7, 12, 13, ...}, and the first monomials carrying eta(p)^6 are X^6 Z^6 and
X^6 W Z^6, that is R(1 - Q^(-1)) = a_p^2 Q^4 (1 - Q^(-1)) Q^(-6x-6z) and its companion
W_loc R (derived).

A rival on Q enters the way Proposition 11.3 enters chi: as a(N ideal) (inferred, the
modelling choice of this lane; the paper has no slot for a combination). Each target's
excluded set S contains the primes above 6 and the primes above its conductor, the
supports of its presentation (3336 to 3340): the prime above 5 for four of the targets,
and the two primes above 19 for the Epstein zeta of discriminant -19. Every column
counts that target's good prime ideals of norm at most 200: 22 norms (21 split and the
inert norm 121; for the discriminant -19 control, 20 split and the inert norms 25 and
121), their 231 pairs of distinct norms, and their conjugate pairs. The values are exact,
kappa in Q(kappa) reduced by its minimal polynomial k^4 + 2k^3 - 6k^2 - 2k + 1, which
agrees with the lab's derived constant 0.2840790438... (derived). The Moebius column
compares the Dirichlet inverse of A -> a(N A) over the good ideals of F, the
coefficients of 1/L^S(s, eta) when a is eta o N, with mu_F(A) a(N A).

| target | S beyond the primes above 6 | (C): norms failing, first t | (M): distinct-norm pairs failing | (M): conjugate pairs failing | (U): norms not unimodular | Moebius form over the good ideals of F |
|---|---|---|---|---|---|---|
| Davenport-Heilbronn, ((1 - i kappa)/2) chi_5 + ((1 + i kappa)/2) conj(chi_5) | the prime above 5 | 12 of 22, exactly the norms 2 or 3 mod 5; first t = 6 | 66 of 231, first (7, 13) | 12 of 21, first over 7 | 12 of 22 | first differs at norm 49 |
| Epstein zeta of x^2 + xy + 4y^2, a = r/2 | the prime above 5 | 21 of 22, exactly the split norms; first t = 6 | 0 of 231 | 21 of 21, first over 7 | 21 of 22 | first differs at norm 49 |
| control: chi_5 composed with the norm, a Hecke character | the prime above 5 | 0 of 22 | 0 of 231 | 0 of 21 | 0 of 22 | agrees up to norm 200 |
| control: Epstein zeta of x^2 + xy + 5y^2, 2 zeta(s) L(s, chi_-19), an Euler product of degree two | the two primes above 19 | 22 of 22, every good norm; first t = 6 | 0 of 231 | 20 of 20, first over 7 | 22 of 22 | first differs at norm 49 |
| limit control: the completely multiplicative function equal to chi_5 at primes up to 100 and to 1 at larger primes, composed with the norm; not a Hecke character | the prime above 5 | 0 of 22 | 0 of 231 | 0 of 21 | 0 of 22 | agrees up to norm 200 |

The Davenport-Heilbronn combination: a(7) = kappa while a(49) = a(4) = -1, so
multiplicativity fails on the conjugate pair over 7 (a(49) against a(7)^2 = kappa^2),
the first coprime pair of good ideals by the product of their norms; across distinct
norms the first failure is (7, 13), where a(91) = 1 and a(7) a(13) = -kappa^2. At the
prime of norm 7, a(7^6) = a(4) = -1, and -1 - kappa^6 is not zero, so the principal
row's local factor already differs from (7.11) at X^6 Z^6; at norm 7 the first failing t
is 6 for j in {0, 1, 5}, 3 for j in {2, 3} and 4 for j = 4. At the norms 1 and 4 mod 5,
chi_5(N p) = +-1 and a(p^t) = chi_5(N p)^t, so (C) holds there; the failure is exactly
where chi_5(N p) = +-i. The Epstein function at norm 7: a(7) = 0 while
a(7^4) = a(7^6) = 1; at norm 19, a(19) = 2. On norms of ideals prime to 3 its two genus
pieces coincide, so a = (1 * chi_{-15}) there (329 norms up to 2000; derived):
multiplicative across distinct norms, which is why (M) fails only at the conjugate
pairs. Over Q instead of over the ideals of F, the Moebius test first fails at n = 4 for
the three failing targets: the inverse there is 1 + kappa^2, -3 and -1 respectively,
against mu(4) a(4) = 0. On Q directly the Epstein function has a(2) = a(3) = 0 while
a(6) = 2, and a(4) = 3.

The kill condition "a claimed arithmetic step also holds for a function with a zero
beyond the claimed abscissa" does not fire. The Epstein zeta for -15 has zeros beyond
7/8: hunt #120 records twelve in its census box up to height 300.5, the largest real
part 1.0267748672 (measured and hardened there, read here from its `results.json`, not
recomputed). Lemma 7.1's arithmetic fails for it, at (M) and (C), as computed above.

What the step separates (the controls derived; the reading inferred). Its local tests
use (M), (C) and (U) only, that is, complete multiplicativity on good ideals with unit
values. The degree-two control, an Euler product that is multiplicative but not
completely so, fails them at every good norm, and so do both rivals. The limit control
passes them all: it agrees with chi_5 o N at every prime of norm at most 100 and differs
from it at 8 good norms up to 200. It is no Hecke character by the standard density
argument, applied to the function itself: a Hecke character equal to 1 at all but
finitely many primes is trivial, and this function is 1 at every prime ideal over a
rational prime above 100 yet equals i at norm 7 (both values derived; the argument
inferred, not computed). So the local step singles out degree-one coefficient functions,
not Hecke characters. Telling a Hecke character from another completely multiplicative
unimodular function is left to the global parts of the argument that use eta as a ray
class character (the ray class of p, 3992), which this lane reads but does not check.
The paper's transfer, Proposition 11.3, is what supplies a Hecke character for every
Dirichlet L-function.

## 6. Where the Euler step binds, requirement by requirement

The exponents come from exact expansions of H_p - 1 for each j in 0..5, truncated at
X^19 W^3 Z^24, and of the principal multiplier B_p + 1 (derived). At j = 0 the instrument
keeps rho = chi_p(u) as a formal sixth root of unity, so the j = 0 numbers hold at every
prime not dividing u, for every row u; at p dividing u (j = 1 to 5) W and D vanish
(8664). Each exponent has the coefficients -deg W and -deg Z in w_r and z_r, so over the
second region the binding point is its corner (w_r, z_r) = (19/20, 33/200) (4056, 5574);
the residue point (w, z) = (1, 1/6) is where the principal factorization is applied
(15599) and where Part I evaluates H_eta (5520). That the monomials beyond the
truncation do not raise any maximum is inferred: they are retained monomials times
powers of R, V, W and D, each of modulus below one on the regions concerned. That
Section 1.1 holds every consumer is inferred: the scan is complete for its search terms,
and a use that names none of them would be missed.

| requirement on the local factors | consumers (Section 1.1) | at the residue point | at the corner |
|---|---|---|---|
| R1: every exponent of H_p - 1 below -1 at p not dividing u (j = 0) | Part I's H_eta (5525, 5531, 6294, 6784); abs(H_{eta,u}) << q_u^eps (5907 to 5910); the majorant's first product (8748 to 8749) and the principal tuple bound that reuses it (9081, 9084, 15557) | x_r > 2/3 | x_r > 401/600 |
| R2: every exponent of H_p - 1 below 0 at p dividing u (j = 1 to 5, each j) | the majorant's divisor product (8747, 8748 to 8749) | x_r > 1/2 | x_r > 301/600 |
| R3: abs(R) < 1, with abs(V) < 1 and abs(D) < 1 | G_p holomorphic (8695, 8696); the identity (16.8) (8817, 8826); holomorphy of the full correction (5609, 5656, 8757, 15537) | x_r > 1/2 | x_r > 301/600 |
| R4: every exponent of H_p - 1 below 0 at j = 0 | H_p bounded away from zero, u = 1 (9054) | x_r > 1/2 | x_r > 301/600 |
| R5: every exponent of B_p + 1 below 0, u = 1 | B_p = -1 + O(Q^(-7/8)) (9074), applied at the residue point (15594 to 15599) | x_r > 3/5 | x_r > 301/500 |

Each entry is exact for the truncated expansions (derived; R3 is the single exponent
4 - 6x_r - 6z_r of R). R1 is the strictest. Its binding monomial is R(1 - Q^(-1)),
exponent 4 - 6x - 6z, from the family (e_0, l) = (0, 2) with m >= 1; above x = 4/5 the
term Q^(1-x-w-6z) leads instead (both are -9/5 at x = 4/5), and at x = 7/8 the maximum is
-15/8 (derived). At p dividing u the factor with j = 1 has the same R1 floors as j = 0,
while for j = 2 to 5 the largest exponent at the corner with x_r = 7/8 is -33/40, the
figure of line 4174, which is above -1: that is why the paper asks only for exponents
below 0 there, where the product is finite in each row and the divisor-product bound
applies (8747).

The principal multiplier. At all 54 points of a grid (x_r from 61/100 to 3/2, at six
pairs (w_r, z_r) among which the residue point and the corner) the largest exponent of
B_p + 1 equals the largest of the four exponents that line 9068 states (derived on the
grid). The series agrees with a direct floating-point evaluation of (7.11), (7.12) and
the formula for G_p (8685 to 8688) to below 1e-9 (measured). At x_r = 7/8 at the corner
the four are -7/8, -99/100, -273/200 and -47/50, and the largest exponent of the whole
expansion is -7/8, attained only by the monomial D = eta(p) Q^(-x) (derived). So the
-7/8 of B_p = -1 + O(Q^(-7/8)) (9074), and with it |rho_i| << P_i^(-7/8) (15613) and
kappa_P < (7/8) min_i l_i (15619), is the x-floor of D_2 entering through D, not a
constraint that the Euler step adds. The principal approximation's own floor is where
4 - 5x_r - 6z_r vanishes: 3/5 at the residue point and 301/500 at the corner (derived).

What Part II does with that margin (cited, then inferred). kappa_P = 7/(96K) is half of
the bound 7/(48K), with l = 1/6 (16304 to 16305), and m_P := kappa_P (16306). The
interface lemma asks only for some mu > 0 chosen independently of eta (6201); the
remainder Z^(C(beta_*)+e-kappa_P+eps) (15669) is a saving once e + eps_pr < m_P/4
(16317); and the common saving is m = (1/4) min{m_high, m_w, m_z, m_P} > 0 (16366). On
this reading kappa_P only has to be positive, so a lower x-floor would change its value
and not the shape of the argument (inferred).

Where the 7/8 of D_2 comes from (cited). D_2's x-floor (5574) is the target
sigma_0 = 7/8 of the shared analytic lemmas (15532), and the interface lemma is stated
for sigma_0 in [7/8, 1) (6178): the principal paths run at Re s = beta_* + e (6232,
6239) and the principal rectangle lies in D_2 (6318) because beta_* > sigma_0; the large
rows sit at (2, 2, v) (6479), far inside. Lowering the target lowers D_2's floor with
it, and the local factors follow it down to the floors of the table above (inferred).

Over every consumer found, the strictest requirement is R1: x_r > 2/3 at the residue
point and x_r > 401/600 at the corner. The slack against 7/8 is 5/24 at the residue
point and 31/150 at the corner. On this reading the 7/8 of Theorem 1.1 is not set by the
Euler step (derived exponents, inferred completeness), which is consistent with hunt
#134 placing the binding inputs in the row counts.

## 7. What this does not show

- That Theorem 1.1 is true or false, or anything about Re s = 1/2.
- The analytic estimates of Lemma 7.1 beyond their exponent bookkeeping (normal
  convergence is inferred from the exponents; the uniformity in imaginary parts is read,
  not checked).
- The global separation in full: the pair phases, the CRT rule and (4.5) to (4.7) are
  checked exactly on the stated sets, but the unit factor U_p (7.9) and the b_*, xi,
  tau, Xi cancellation (3941 to 3951) are read only.
- Primes above 10^4: the local identity there rests on route (a) plus relations not
  computed beyond that norm; the inert case is derived for every ell.
- That Section 1.1 holds every consumer of the lemma: the scan is complete for its
  search terms, but a use that names none of them, and the second-order uses not traced,
  are covered only by reading. That Part II's margin needs only to be positive is a
  reading too.
- That the limit control is no Hecke character: a density argument, not computed.
- Novelty: nothing was searched. These are the paper's own identities, checked.

## The doors

This lane locates the Euler step rather than a ceiling, but its floor is owed.

**Active constraints.** The strictest requirement over the consumers found is R1, the
majorant's: the monomial R(1 - Q^(-1)) of H_p - 1, exponent 4 - 6x_r - 6z_r, must lie
below -1 at every prime not dividing u, which sets x_r > 2/3 at z = 1/6 and
x_r > 401/600 at z_r = 33/200 (derived). Its slope in x_r is -6, so lowering the
region-two x-floor costs nothing in the local product until that line. Next come the
principal approximation (R5, 4 - 5x_r - 6z_r < 0: 3/5 and 301/500) and then R2, R3 and
R4 (1/2 and 301/600). Every row u is covered: at the primes not dividing u the j = 0
floors apply unchanged, and at p dividing u R2 asks only for 1/2 and 301/600. Region
(7.14) does not involve the target (inferred from the proof's text).

**Frozen constants.**

| constant | value | line | what relaxing it trades |
|---|---|---|---|
| region-two x-floor | 7/8 | 4056 | slack: the local product needs only 401/600 at the paper's z, w floors |
| D_2's x-floor | 7/8 | 5574 | it is sigma_0 (15532), and the interface lemma is stated for sigma_0 in [7/8, 1) (6178); it moves with the target, and the local factors follow it down to 401/600 |
| exponent of B_p = -1 + O(Q^(-7/8)) | 7/8 | 9074 | it is D_2's x-floor through D; the multiplier itself decays down to 3/5 at the residue point |
| kappa_P | 7/(96K) | 16304 | half of (7/8) min l_i; only positivity is used (6201, 16366), so it trades nothing locally |
| region-two z-floor | 33/200 | 4056 | below 1/6 for the contour to the residue; raising it toward 1/6 lowers the x-floor toward 2/3 |
| region-two w-floor | 19/20 | 4056 | enters only the subleading term Q^(1-x-w-6z) and the multiplier's 1 - w_r - 6z_r |
| c_H | 4/5 | 4064 | the tail exponent is 163/200 at x_r = 7/8; any c_H below it works |
| P_0 | unspecified | 3340 | trades the size of S against sup abs(H_eta - 1) <= 1/2 |
| region-one floors | 51/100, 17/50, -1/100 | 4054 | set by nonprincipal contours, independent of the target |

**Information class.** Every door above stays inside the data the argument already
reads: the local identity is exact for every Hecke character and every prime outside
S. None of them moves Theorem 1.1's 7/8 by itself; the binding inputs are elsewhere.

## Open issues

- The global separation behind (7.13) is only partly checked: the pair phases, the CRT
  rule and (4.5) to (4.7) are exact on the stated sets, but U_p (7.9) and the b_*, xi,
  tau, Xi cancellation (3941 to 3951) are read, not computed. An exact check of the
  coefficient (7.4) against its local factors on small multi-prime indices would close
  this.
- Route (b) runs to norm 1000. Between 1000 and 10^4 the local identity rests on route
  (a) plus the relations checked exactly there; above 10^4 nothing is computed, apart
  from the inert case, which is derived for every ell.
- Inert primes with 300 < ell <= 10^4 rest on the derived reduction G_r = ell plus exact
  symbol values, not on direct sums over F_{ell^2}.
- The 11/12 paper's source was not in hand: that its G is the 7/8 paper's G is
  inferred, and the A.1 form was checked under the 7/8 definitions.
- The floors of Section 6 use exact exponents, but three things in them are readings: that
  Section 1.1 holds every consumer (the scan is complete only for its search terms, and
  some second-order uses were not traced), that omitted higher monomials do not raise a
  maximum, and that kappa_P needs only to be positive. A reviewer should confirm them
  before any lane builds on the floors.
- Feeding a rival into the argument as a(N ideal), with the primes above its conductor
  in S, is this lane's modelling choice; the paper has no slot for a linear combination.
- The files are written and not committed; no git state was changed, and the
  `hunts/README.md` case-log entry for the hunt was not written by this lane.
