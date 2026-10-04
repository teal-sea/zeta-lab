# Li positivity computation: enclosure claim pending repair

## Current audit status (2026-10-04)

**Verdict: incomplete, with the missing implication being a sound bound
for the midpoint quadrature error.** The saved rows report positive lower
endpoints for n = 1..58; that mechanical observation is not presently an
enclosure proof of those Li coefficients. The historical theorem and
stronger grade below are withdrawn pending repair and a reproducible rerun.
No RH resolution, uniform positivity result, or refutation is claimed.

Audit target: `af74d3edf0e9754855713d01002f3de2f9081db4`,
`enclose_li_mid.py` lines 21..91 and its unchanged JSON artifacts.
The current merge preserves that implementation. All raw results, including
`superseded/`, remain unchanged. This is a documentation correction only.

Outstanding proof obligations:

1. `bound_M`, lines 40..41, takes the maximum of the absolute real and
   imaginary endpoints. This bounds the coordinate norm, not complex
   modulus as required by the Cauchy estimate: for example, 1+i has
   coordinate norm 1 and modulus sqrt(2). A bound for `abs(L)` is needed.
   This identifies a missing justification, not a demonstrated false Li sign.
2. Lines 39..41 and 60..84 convert bounds and radii to binary floats and
   calculate the remainder with ordinary arithmetic. Outward rounding of
   these operations is not established. Arb evaluations of the midpoint
   samples do not enclose this separate error calculation.
3. The angle coverage uses float pi and fixed 1e-15 padding (lines 31..33,
   76..77). Coverage must be proved for the stated grids or constructed
   directly with ball arithmetic. A positive outer-contour bound for
   Re(xi(1/(1-z))) then extends to the disk by the harmonic minimum
   principle, proving zero-freeness and the principal-log branch without
   the first-zero completeness assumption in historical L1.
4. The correction commands in RUNS.md omit `--rho 0.88 --K0 16384` for
   the R=0.8 runs. These parameters are recoverable from RESULTS.md,
   but JSON rows omit rho, K0, and the branch minimum. Record every
   parameter and bound in a future run; existing data are not relabelled.

Bounded checks using `.venv/bin/python`, serially,
with python-flint at 128 bits and no midpoint rerun:

- The three range-stamped midpoint files cover 1..60, and exactly 1..58
  have positive reported lower endpoints. Row 59 starts at -0.06481890146.
- `bound_M("0.85", 2048, 128)` reproduces M=1.196816073730588.
  `bound_M("0.88", 16384, 128)` reproduces M=0.9714775364845991 and
  min Re=0.358857166309262, matching the narrative. At the default
  K0=2048 the latter contour fails its branch check (min Re=-0.04814).
  These reproduce the implementation, not a valid complex modulus bound.
- The independent closed form for lambda_1, evaluated directly in Arb,
  is [0.0230957089661210338143102479064952916 +/- 3.59e-38], positive.

Cheapest next step: correct the norm, outward rounding, angle coverage,
and metadata, then perform a budgeted finite-range rerun. No repaired
range is asserted here. The panel-covering implementation does not use
this derivative remainder, but its branch and angle-coverage obligations
still need review; this audit does not promote its rows to a new theorem.

## Historical argument (2026-10-03; grade withdrawn by the audit above)

### Former claim: enclosed Li positivity for 1 <= n <= 58

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
