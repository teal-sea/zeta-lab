# THEOREM: enclosed Li positivity for 1 <= n <= 58

Claim: lambda_1, ..., lambda_58 > 0, each enclosed by an explicit
rational interval with positive lower bound. Artifacts:
enclosure_mid_*.json in this directory (superseded/ holds the
withdrawn n <= 71 claim and its correction note). Grade:
enclosure-carrying (Arb balls); hardened by cross-checks below.
This is a theorem about n <= 58. It is not RH and implies no
uniform statement.

Correction history: first stated to n = 71 with a remainder bound
missing the oscillation terms; re-derivation caught it, the
invalid rows were moved to superseded/ unmodified, and corrected
re-runs establish n <= 58 with n = 59 as the boundary.

## Definitions

Li coefficients: lambda_n = coefficient identity
  lambda_n = n [z^n] log xi(1/(1-z)),  R = contour radius,
  c_n = (1/2pi R^n) ∫_0^{2pi} f(R e^{it}) e^{-int} dt,
  f(z) = log xi(1/(1-z)), xi(s) = s(s-1)/2 pi^{-s/2} Gamma(s/2) zeta(s).
Derived in zeta/li.py (Hadamard product computation); numerically
verified against the literal derivative definition by
li_generating_function_defect (defects ~1e-50 at dps 20).

## Lemmas with explicit dependencies

L1 (unconditional zero-free disk). Every nontrivial zero satisfies
|rho| >= gamma1 > 14 (first ordinate; pinned in this tree against
mpmath zetazero and the PARI oracle). Hence every zero image
z = 1 - 1/rho satisfies |z| >= 1 - 1/|rho| >= 13/14 > 0.92.
So f is analytic on |z| <= 0.88, and the principal log below is
the analytic branch wherever Re(xi) > 0 on the contour.

L2 (branch, computed). On each contour used, interval evaluation
over panels covering the circle gives min Re(xi) lower > 0
(R=0.5: 0.4951; R=0.7: 0.4854; R=0.88 outer: 0.3589; rho=0.85
outer: 0.2927; artifacts branch_R*.json) with max |arg| upper
< 0.12 on working contours.
Hence principal log equals the analytic branch at every sample.

L3 (midpoint remainder, analysis). The quadrature integrates
g(t) = f(R e^{it}) e^{-int}, so |g''| <= G2 with
G2 = F2 + 2n F1 + n^2 M, F1 = R M1, F2 = R M1 + R^2 M2c,
M1 = M/(rho-R), M2c = 2M/(rho-R)^2 by Cauchy's estimate, M a
rigorous max of |f| on |w| = rho from coarse interval panels
(finite and Re(xi) > 0 verified there too). Then
|integral - midpoint sum| <= G2 (2pi)^3/(24 K^2). Used triples
(R,rho,K) = (0.7,0.85,16384) for n <= 16 and (0.8,0.88,65536)
for n = 17..58. (An earlier version used M2c alone and is
withdrawn; see superseded/CORRECTION.md.)

L4 (soundness of balls). Every operation (cos, sin, exp, gamma,
zeta, log) is Arb ball arithmetic (python-flint 0.9.0), hence
inclusion-monotonic; panel t-balls cover [0,2pi] with 1e-15
padding; midpoint balls arb(mid,1e-15) cover true midpoints.
The summed balls therefore contain the true integral, and the
added remainder ball contains the discretization error by L3.

## Proof

For each n, the script enclose_li_mid.py evaluates the enclosure
per L2-L4 and reports [re_lo, re_hi] with re_lo > 0:
n = 1..16 at (0.7,16384), n = 17..58 at (0.8,65536).
Sample widths: n = 16: [5.70, 5.73]; n = 40: [30.19, ~30.7];
n = 58: [11.72, 97.04]. Imaginary enclosures all contain 0,
consistent with real lambda_n. Mechanical check over the
artifact files: full coverage 1..58, every lower bound > 0,
every enclosure contains the independent float Cauchy value.
n = 59 ([-0.06, 111.57]) is the mapped boundary and is excluded.

## Cross-checks (hardening, not part of the proof)

C1. lambda_1 closed form 1 + euler/2 - log(4pi)/2 in Arb:
[0.02309570896612103381 +/- 3.6e-38], inside every quadrature
enclosure of lambda_1.
C2. Float Cauchy values (zeta/li.py, independent DFT code path)
lie inside all 58 enclosures.
C3. Prec 128 vs 192 overlap for n = 1, 2 (widths panel-dominated).
C4. Disproof lanes empty: Li positivity scan n <= 100 and Jensen
scan d <= 16, n <= 25 show no violation (measured grade).

## Formal-statement check

The claim proved is "the Li coefficients 1..58 of xi are
positive", with xi as implemented in zeta/core.py (checked against
mpmath and PARI oracles). Li's criterion (Li 1997, RH iff all
lambda_n >= 0) is used ONLY as motivation. No RH equivalence is
assumed or invoked in L1-L4. The theorem statement matches what
the code computes: coefficients of log xi(1/(1-z)), not a
restatement of RH.

## Doors (what would extend this)

Active constraint: width ~ n M2/(K^2 R^n); n = 72 needs 4x K.
Frozen: contour family (circles), midpoint order (Simpson would
need f'''' bounds, available by the same Cauchy device),
prec 128 (widths are discretization-dominated; more digits help
nothing). Information class: any fixed (K,R,rho) decides only
finitely many n; the uniform tail is outside this family.
