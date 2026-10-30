# SOURCES: the function-field theta coefficients, verified or replaced

**Hunt #148, step 1. Status: the cited formulas are pinned by brute force at q = 7, n = 3,
degree at most 3, with the corrections listed below; files produced on branch
`hunt/ff-probe`, not landed.** Grades as in `MISSION.md`. Every count on this page is read
from `results_step1.json` (or `results_step3.json` for n = 4) and pinned by
`test_ffprobe.py`.

## What was obtained

| source | as cited by the workflow | what was found | local copy, SHA-256 |
|---|---|---|---|
| J. Hoffstein, *Theta functions on the n-fold metaplectic cover of SL(2), the function field case*, Invent. Math. 107 (1992) 61-86 | from memory | bibliographic data confirmed (doi 10.1007/BF01231881; the reference lists of both Patterson papers below); the text was **not obtained**: the publisher requires a login and no open scan was found | none |
| S. J. Patterson, *Note on a paper of J. Hoffstein*, Glasgow Math. J. 49 (2007) 243-255 | from memory | confirmed (doi 10.1017/S0017089507003540); the publisher's PDF was obtained and read through a text extraction that garbles some displayed formulas, so a formula quoted from it below is marked "as extracted" | `<cache>/ffprobe-sources-patterson2007/patterson2007.pdf`, `789082e8b99dbf97612bbc2e494ee37f237cc54a2a5ff70b5084e33f7cb04824` |
| S. J. Patterson, *The Fourier coefficients of metaplectic theta series on GL(2) over rational function fields*, arXiv:1411.7594 (2014) | not cited | added: it restates the 2007 note in cleaner notation and is the source quoted by line below | `<cache>/ffprobe-sources-patterson2014/JHPaper.tex`, `d39e92ef8da150fd063db0fdd01013e62668bc2e37bfe3219fe0f3cf3212403c` (the e-print archive is `90a80fa5f800139d3112d77c5c3630439fb0709f8edd23effcf40b3af1bbf90b`) |

Hoffstein's own statements are therefore used only as Patterson restates them. The
downloads are untrusted data in new directories under `<cache>/`;
nothing in them was executed.

## Conventions fixed by the sources

- R = F_q[x], chi(y) = y^((q-1)/n) on F_q^x, eps an embedding of mu_n(F_q) in C^x; here
  eps sends g^((q-1)/n) to zeta_n for g the least primitive root mod q (2014, lines 78-82).
- The Legendre-Jacobi symbol (f/g)_n = chi(b_0^(-m) R(g, f)) with b_0 the leading
  coefficient of g and m = deg f (2007, page 244). For monic c this is chi(Res(c, a)); the
  hunt also computes it by Frobenius, a^((|P|-1)/n) mod P at each prime factor, and the two
  routes agree on every residue modulo all 399 monic moduli of degree at most 3 over F_7.
- The additive character e(f) = e_o(-Res_infty(f dx)) = e_o(a_-1(f)), the coefficient of
  x^-1 (2014, lines 86-90). This is the hunt's convention throughout.
- g(r, eps, c) = sum over xi mod c of eps((xi/c)_n) e(r xi / c) (2014, lines 91-92), with the
  zero extension at non-units.

## The formulas, and what brute force says

| # | statement | where | check | verdict |
|---|---|---|---|---|
| 1 | Davenport-Hasse: for (r, c) = 1, g(r, eps, c) = mu(c) eps((r/c)^-1 (c'/c)) (-tau(eps chi))^deg c | 2014, lines 97-101 | brute-force Gauss sums: 34,202 at (q, n) = (7, 3), 85,505 at (7, 6), 85,683 at (13, 4); every j, every monic r of degree at most 2 coprime to c | **holds**, no mismatch |
| 2 | Theorem 2.1: the same with ((-r)/c)^-1 | 2007, page 247, as extracted | the same sums | **holds for the 2007 note's own character** e(f) = e_o(Res_infty(f dx)) = e_o(-a_-1(f)), which turns g(r, .) into g(-r, .): no mismatch at any (q, n). With the 2014 character it fails exactly when eps(chi(-1))^j = -1 and deg c is odd: 45,129 of 85,505 at (7, 6) (three odd j times the 15,043 pairs (c, r) with deg c odd), 4,394 of 85,683 at (13, 4) (two odd j times 2,197 pairs), none at (7, 3) |
| 3 | g(r, eps, c) = 0 when c is not squarefree and (r, c) = 1 | 2007, page 247 | brute force, r of degree at most 1: 350 cases at (7, 3), 350 at (7, 6), 169 at (13, 4) | **holds** |
| 4 | twisted multiplicativity and the prime-power reduction behind the structural route | 2007, page 247; standard | structural against brute-force Gauss sums: 319,200 cases, every monic r and c of degree at most 3, j = 1, 2 | **holds** |
| 5 | C(r, eps, i) = sum over r* of g(r, eps, r*) eps(chi(-1))^((i-1) deg r*) C*(r r*^(n-2), eps, i - deg r*) | 2007, eq. (5); 2014, lines 156-161 | against brute force and the structural route, i at most 3: 56 cases | **holds** |
| 6 | Psi(r, eps, i, T) is a polynomial of degree at most R = floor((1 + deg r - i)/n) | 2007, page 246; 2014, lines 121-128 | the T-coefficients above R vanish in all 36 checked cases | **holds** |
| 7 | rho_0(1, eps, 0) = 1, rho_0(1, eps, 1) = q tau(eps chi), rho_0(1, eps, 2) = 0 for n = 3, and the n = 4 values of `S4.md` | 2007, page 252 (with c_o = (q-1)/n, dropped in the 2014 normalization rho_0 = Psi(q^(-n-1)), line 137) | exact | **holds in the 2014 character**; in the 2007 character the n = 4 value at i = 1 carries eps(chi(-1)) = -1, which the note's text drops |
| 8 | the Hecke relations at infinity | 2014, lines 224-231 | exact, 40 checks at (7, 3) | **fails as printed** whenever rho_0 is nonzero (20 of the 40 hold): the printed q-power does not depend on i and deg r, and it must |
| 9 | the same relations | 2007, (9) and (10), page 251, as extracted | exact: 60 checks at (7, 3) in the corrected reading; 30 at (7, 3) and 30 at (7, 6) in each additive character | **holds in the 2007 character** at every checked (q, n), once its last argument is read as the unreduced index 1 + deg r - i with the note's own rule rho(r, eps, i + nN) = q^((n+1)N) rho(r, eps, i): the exponent is 2i + E - 3 - deg r + (n+1)R, E = 2 + floor((2i-2-deg r)/n). As printed (reduced index) it fails whenever R >= 1 (40 of 60 hold). In the 2014 character the sign eps(chi(-1))^(i sigma), sigma = 1 + deg r, becomes eps(chi(-1))^((i+1) sigma) |
| 10 | the finite Hecke relation, with its q-power carries, and rho_0(r_o pi^(n-1), eps, i) = 0 | 2014, lines 235-247 | exact, 72 cases and 36 vanishing cases at (7, 3) | **holds** |
| 11 | rho_0 depends only on r modulo n-th powers | 2014, lines 42-45 | exact, 24 cases | **holds** |
| 12 | Theorem 1 (the PGL_2(F_q) action), affine g | 2014, lines 303-309 | exact, combined with the unit rule rho_0(u r, i) = eps(chi(u))^(-i) rho_0(r, i) | **holds** in all 144 checked cases |
| 13 | the R = 2 evaluation of Psi(q^(-n-1)) | 2014, lines 536-541 | algebra | **typo**: the last term is C(r, eps, i+2n) q^(-2n-2), not q^(-n-2) |
| 14 | for n = 4 and deg r = 3, rho = 0 at i = 0, 3 | 2007, page 252, as extracted | relation (10) and the computation at q = 13 | **misprint or extraction error**: the zeros are at i = 0, 2 (2i = 1 + deg r mod 4) |
| 15 | the four relations among the C(r, eps, i) for n = 4 | 2007, page 252, as extracted | exact, at q = 13 | three **hold** in the 2014 character (not in the 2007 one); the degree-4 relation holds with q in place of q^2 (`S4.md`, section 1) |
| 16 | the functional equations of Psi | 2014, lines 205-221 | none | **not checked**: the two printed forms are not equivalent as written (p for q, x for X); the residue-level relations 8 to 10 are checked instead |

**Why the two additive characters disagree only sometimes.** Changing e to its inverse
turns g(r, eps, c) into g(-r, eps, c), and by the unit rule rho_0(-r, i) =
eps(chi(-1))^(-i) rho_0(r, i). Every discrepancy above is a power of eps(chi(-1)), which is 1
exactly when -1 is an n-th power in F_q, that is when q = 1 mod 2n. That holds at (7, 3) and
fails at (7, 6) and (13, 4), which is why the n = 3 checks pass in both readings and the
others separate them. The 2007 note is consistent with its own character in its main
formulas (2 and 9) and with the 2014 character in some of its worked values (7 and 15).

The rows marked "holds" are checked exactly, as equalities of reduced elements of
Q(zeta_N), at the stated (q, n) and degrees; they are measured facts about those cases, not
proofs of the general statements, which rest on the cited papers. Formula 1 was also
recomputed in PARI/GP (`ffprobe_pari.py`) for the cases in `test_ffprobe.py`.

## What the hunt takes from the sources

- **n = 3 (the control).** Along the component families i(r) = (b - deg r) mod 3, the finite
  Hecke relation reduces a squarefree index to fewer primes, and the computation confirms
  the consequence: for b = 0 and b = 1, rho_0(c, eps^2, i(c)) equals gamma_2(c) times a
  number that depends on deg c only, for every squarefree c of degree at most 3; the family
  b = 2 vanishes identically, by the Hecke relation at infinity. So over F_7(T) the cubic
  theta's squarefree coefficients are the cubic Gauss sums, as in Patterson's number-field
  theorem, and the 7/8 paper's row D(s) built from gamma_2(c) is (up to that degree factor)
  the theta row. That is the input of `LOCAL_IDENTITY.md`.
- **n = 4.** The finite Hecke relation no longer reduces r_o pi to r_o, and the
  coefficients at squarefree indices are Patterson's C-sums: Jacobi-type sums for two
  linear primes, hypergeometric-type sums for three. Their structure is the subject of
  `S4.md`.
