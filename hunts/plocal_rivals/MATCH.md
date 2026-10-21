# MATCH: the combination, its functional equation, and where F_chi agrees with L(s, chi)

Hunt #149, steps 1 to 3 of `MISSION.md`. Instrument: `rivals.py`; every number below is
pinned by `test_rivals.py`. Grades: *measured* (one float route), *hardened* (independent
routes agree), *exact* (integer or rational arithmetic), *ordinary argument* (a derivation
written here, reviewed by nobody outside this hunt). Nothing here is a result
(`hunts/README.md`).

## 1. The combination and its functional equation (step 1)

**Setting.** q = 1 (mod 4) prime, g its least primitive root, chi the character mod q with
chi(g) = i, a in {0, 1} with chi(-1) = (-1)^a, and

    Lambda(s, chi) = (q/pi)^{(s+a)/2} Gamma((s+a)/2) L(s, chi),
    Lambda(s, chi) = eps Lambda(1 - s, chi-bar),   eps = tau(chi) / (i^a sqrt q) = e^{i theta}.

These are the classical facts (Davenport, *Multiplicative Number Theory*, ch. 9) and are
used, not re-derived. They give Lambda(1 - s, chi) = eps Lambda(s, chi-bar) and
Lambda(1 - s, chi-bar) = eps^{-1} Lambda(s, chi), since eps(chi-bar) = conj(eps).

**Derivation (ordinary argument).** Put G = c Lambda(s, chi) + c' Lambda(s, chi-bar). Then
G(1 - s) = c' eps^{-1} Lambda(s, chi) + c eps Lambda(s, chi-bar), and the two completed
L-functions are linearly independent (distinct Dirichlet series), so G(s) = G(1 - s) holds
exactly when c' = c eps. Real Dirichlet coefficients 2 Re(c chi(n)) need c' = conj(c), so
c / conj(c) = e^{-i theta} and c = r e^{-i theta/2} with r real. The normalisation
a(1) = 2 Re c = 1 fixes r = 1/(2 cos(theta/2)), which exists exactly when
cos(theta/2) != 0:

    c = (1 - i k)/2,   k = tan(theta/2),
    F_k = c L(s, chi) + conj(c) L(s, chi-bar) = [eps^{-1/2} L(s, chi) + eps^{1/2} L(s, chi-bar)] / (2 cos(theta/2)).

The Davenport-Heilbronn function is q = 5 (odd, a = 1), with k = kappa.

**The linear solve, as `zeta/epstein.py` derives kappa.** G_k(s) - G_k(1 - s) is linear in k,
so `k_linear_solve` takes one solve at s0 = 3/4 + 3i/2 and then requires the same k to kill
the defect at s1 = 3/10 + 2i. At dps 40 the imaginary residue of k and the cross-point
relative defect are both below 1e-50 for q = 5, 17 and 73.

| q | a | P | first non-square | k (linear solve, 40 digits) | theta | cos(theta/2) | J(chi, chi) |
|---|---|---|---|---|---|---|---|
| 5 | 1 | 1 | 2 | 0.2840790438404122960282918323931261690911 | 0.55357435889704525 | 0.96193835778391744 | -1 - 2i |
| 17 | 0 | 2 | 3 | 0.4879283649264853247148290699651012206776 | 0.90788749496088039 | 0.89872471018733976 | -1 + 4i |
| 73 | 0 | 4 | 5 | 0.3126334205272301997186929661823790657452 | 0.6060128282621622 | 0.95444371692510638 | 3 + 8i |

Three routes give the same k (hardened): the linear solve; tan(theta/2) from this hunt's
Gauss sum (`k_from_gauss`, within 1e-40 at dps 40); and PARI's `lfunrootres` on
`lfuncreate([znstar(q,1), chi])`, a library sharing no code with mpmath (within 1e-38).
At q = 5 the linear solve returns `zeta.epstein.KAPPA_REF` to 1e-39.

**cos(theta/2) != 0 for every order-4 character (ordinary argument from cited facts).**
tau(chi)^2 = J(chi, chi) tau(chi^2) (Ireland and Rosen, ch. 8) and tau(chi^2) = sqrt q for
the quadratic character of a prime q = 1 mod 4, so eps^2 = chi(-1) J(chi, chi)/sqrt q.
J(chi, chi) is a Gaussian integer of norm q (exact: -1 + 4i and 3 + 8i above, norms 17 and
73), and q is not a square, so Im J != 0 and eps^2 is not real. So eps is none of +-1, +-i,
theta is none of 0, +-pi/2, pi, and both cos(theta/2) and k are nonzero. The identity
eps^2 = chi(-1) J/sqrt q is measured to 1e-40.

**The functional-equation defect** |G(s) - G(1-s)| / |G(s)|, maximum over six asymmetric
points (`FE_POINTS`), with k from the linear solve at the same dps (measured):

| dps | q = 17 | q = 73 |
|---|---|---|
| 20 | 3.1e-22 | 3.0e-22 |
| 30 | 1.7e-32 | 1.05e-32 |
| 40 | 1.3e-42 | 2.9e-42 |

The defect falls with precision, as a real quantity should; at dps 60 it is below 1e-60
for q = 17 at three points. **Planted faults fail the test:** adding 1e-10 to b on one
residue class, adding 1e-10 to the single coefficient b(7), or moving k by 1e-12 each
raises the defect above 1e-14.

**A third functional-equation check that shares no code.** PARI's `lfuncheckfeq` on F's
own Dirichlet series (`lfuncreate` with the coefficients b(n), self-dual, gamma factor [0],
conductor q, root number +1), at real precision 40, reports log2 of the defect:

| q | F | b(7) + 1e-10 | k + 1e-12 | root number -1 |
|---|---|---|---|---|
| 17 | -153 | -44 | -42 | 1 |
| 73 | -148 | -37 | -43 | 0 |

The test pins F below -140, the coefficient fault above -50, and the sign fault above -5.

## 2. The P-smooth identities, exactly (step 2)

**Coefficients.** b(n) = 2 Re(c chi(n)) = Re chi(n) + k Im chi(n), periodic mod q.

**The factorisation behind them (ordinary argument, checked exactly).** chi(p)^2 is the
Legendre symbol, so chi(p) = +-1 exactly at the quadratic residues. If chi(m) is real then
b(mn) = chi(m) b(n) for every n. So at every residue prime p,
F_k(s) = (1 - chi(p) p^{-s})^{-1} F_(p)(s) with F_(p) supported on integers prime to p: F_k
carries the exact Euler factor of L(s, chi) at every quadratic-residue prime, which is half
of all primes. Equivalently, since chi-bar(p) = chi(p) there,

    F_k(s) = L_QR(s, chi) [ c L_NR(s, chi) + conj(c) L_NR(s, chi-bar) ],

with L_QR, L_NR the Euler products over residue and non-residue primes. Hence the Dirichlet
coefficients of -F'/F equal Lambda(n) chi(n) at every n except the n > 1, prime to q, whose
prime factors are all non-residues. When every p <= P is a residue, every P-smooth n is in
the agreement set, b(n) = chi(n) there, and a(n) = 2 cos(theta/2) chi(n): the statement of
`MISSION.md`.

**The exact check** (`exact_identity_report`, n <= 10^4). Lambda_F(n) is computed in
Z[k] (x) span{log p} with integer coefficients, k an indeterminate, and compared formally
with Lambda(n) chi(n) as Gaussian integers times log p; every formal disagreement is then
confirmed numerically at the derived k.

| q | P-smooth n <= 10^4 | failures among them | first disagreement | disagreements | disagreement set = non-residue-composed n |
|---|---|---|---|---|---|
| 17 | 14 | 0 | 3 | 2138 | yes, no accidental agreement |
| 73 | 67 | 0 | 5 | 1535 | yes, no accidental agreement |
| 5 (DH) | 1 | 0 | 2 | 3497 | yes, no accidental agreement |

The smallest numerical gap |Lambda_F(n) - Lambda(n) chi(n)| on a disagreement exceeds 1e-6
in all three cases. For q = 17 the first entries are Lambda_F(2) = -log 2 =
Lambda(2) chi(2); Lambda_F(3) = k log 3, against Lambda(3) chi(3) = i log 3;
Lambda_F(6) = 0 on both sides (a mixed n); Lambda_F(9) = -(2 + k^2) log 3, a non-unitary
power sum at the first non-residue. A lesion is caught: flipping chi(2) on the comparison
side fails the identity at n = 2, 8 and 32 and leaves 4, 16 and 64.

*Side observation (ordinary argument, literature unsearched).* At q = 5 the same
factorisation says the Davenport-Heilbronn function carries the exact Euler factor of
L(s, chi_5) at every prime p = +-1 (mod 5). Its failure to be multiplicative
(`zeta.epstein.claim_multiplicativity`) lives entirely on the classes 2 and 3 mod 5.

## 3. The window forms (step 3)

**Assembly.** `galerkin.py` (`hunts/rogue_frontier/weil_trunc/`) assembles the CvS/CCM
truncated Weil form Q = W02 - WR - Wp on the Fourier basis of L^2([0, log c]), band
n in [-N, N]. Its archimedean block depends only on the Gamma shift (1/4 here, both
characters being even) and on the constant log(q/pi) + psi(1/4); its prime block reads
Lambda_f(n) for n <= c, and the term at n = c carries weight 0. Neither F_k nor L(s, chi)
has a pole, so W02 = 0. `rivals.CharacterTruncation` builds a `galerkin.Truncation`
instance with these inputs, so its `entry`, `even_matrix` and `odd_matrix` are galerkin.py's
own code. F_k's coefficients come from `zeta.epstein.log_derivative_coefficients`, a
floating-point recursion that shares no code with the exact check above; L's come from the
von Mangoldt function directly.

**The one new piece (ordinary argument).** L(s, chi) needs complex coefficients once a
non-residue prime enters the window. The explicit formula pairs Lambda(n) chi(n) with the
autocorrelation G(log n) and its conjugate with G(-log n) = conj G(log n), so c_n enters
as 2 Re(c_n G(log n)). With g_nm the correlation of two basis functions, 2 Re g_nm is CCM's
kernel q_nm and -2 Im g_nm = [cos(a_m y) - cos(a_n y)]/(pi (n - m)) (diagonal
-2 (1 - y/L) sin(a_n y)), so the block stays real symmetric but couples galerkin.py's even
and odd sectors. With the opposite pairing the form is that of L(s, chi-bar), the parity
reflection of this one, with the same spectrum; nothing below depends on the choice.

**Calibrations (measured).** At q = 5 the assembly equals galerkin.py's own `"dh"` form
entrywise to below 1e-38 (c = 13.5, N = 6). At q = 1 with Lambda(n), adding galerkin.py's
pole block reproduces its `"zeta"` form to below 1e-38 (c = 11). The new kernel matches
direct quadrature of the correlation integral to below 1e-25 at three (c, n, m, y).

**F_k against L(s, chi), band N = 8** (full (2N + 1)-square matrices, dps 40, measured):

| q | c | max entry difference | max eigenvalue difference | lambda_min(F) |
|---|---|---|---|---|
| 17 | 2.5 | 0 | 0 | 1.360618 |
| 17 | 3 = P + 1 | 2.9e-41 | 4.6e-40 | 1.267932 |
| 17 | 3.001 | 1.9e-4 | 1.1e-3 | 1.267757 |
| 17 | 3.01 | 2.4e-3 | 1.1e-2 | 1.266187 |
| 17 | 3.5 | 0.17 | 0.18 | 1.177847 |
| 73 | 3.5 | 8.6e-42 | 5.5e-40 | 1.963318 |
| 73 | 5 = P + 1 | 2.3e-41 | 4.6e-40 | 1.661545 |
| 73 | 5.001 | 5.7e-5 | 5.2e-4 | 1.661346 |
| 73 | 5.01 | 6.7e-4 | 5.2e-3 | 1.659553 |
| 73 | 5.5 | 8.4e-2 | 9.3e-2 | 1.565040 |

Up to c = P + 1 the two forms agree to working precision, at every N tried (6 and 8 in
the tests). As soon as c passes the first non-square prime they separate, from zero at
c = P + 1, because two things change at once: F's coefficient there is real,
+-k log n(q), against L's +-i log n(q), and L's form acquires the parity-coupling block.
**The comparison has power below P + 1 too:** an L-form built with chi(2) flipped differs
from F's by more than 0.1 already at c = 2.5.

**What this does and does not show.** It shows that the window forms with c <= P + 1
cannot tell F_k from L(s, chi), and that the equality is not an artifact of the assembly,
since the same code separates them immediately past n(q). It says nothing about
positivity at larger c: every lambda_min above is positive, for both functions.
