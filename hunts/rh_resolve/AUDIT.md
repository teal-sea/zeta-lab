# Li positivity rows: audit of the withdrawn enclosure grade

Formerly `THEOREM.md`. Renamed on 2026-10-10 because the claim that name
announced was withdrawn by the audit below; the file now records the audit
and, under a separate heading, the withdrawn argument.

Grade of every Li row in this hunt: **measured**. The saved positive lower
endpoints for n = 1..58 are numerical evidence, not enclosures. The numbers
quoted from saved artifacts in this file are pinned by
`tests/test_rh_resolve.py`; numbers that exist only in a session's output say
so where they appear.

## Current audit status (2026-10-04)

**Verdict: incomplete, with the missing implication being a sound bound
for the midpoint quadrature error.** The saved rows report positive lower
endpoints for n = 1..58; that mechanical observation is not presently an
enclosure of those Li coefficients. The historical claim and its
enclosure grade below are withdrawn pending repair and a reproducible rerun.
No RH resolution, uniform positivity result, or refutation is claimed.

Audit target: `af74d3edf0e9754855713d01002f3de2f9081db4`,
`enclose_li_mid.py` lines 21..91 and its unchanged JSON artifacts.
The current merge preserves that implementation. All raw results, including
`superseded/`, remain unchanged; the `grade` field inside the JSON files is
the label written at run time and is not relabelled.

Outstanding obligations:

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
   76..77). Coverage must be shown for the stated grids or constructed
   directly with ball arithmetic. A positive outer-contour bound for
   Re(xi(1/(1-z))) would then extend to the disk by the harmonic minimum
   principle, giving zero-freeness and the principal-log branch without
   the first-zero completeness assumption in historical L1.
4. The correction commands in RUNS.md omit `--rho 0.88 --K0 16384` for
   the R=0.8 runs. These parameters are recoverable from RESULTS.md,
   and the saved M2 values match the G2 formula with rho = 0.85
   (R = 0.7) and rho = 0.88 (R = 0.8), but JSON rows omit rho, K0, and the
   branch minimum. Record every parameter and bound in a future run;
   existing data are not relabelled.

Bounded checks using `.venv/bin/python`, serially,
with python-flint at 128 bits and no midpoint rerun:

- The three range-stamped midpoint files cover 1..60, and exactly 1..58
  have positive reported lower endpoints. Row 59 starts at -0.06481890146.
- `bound_M("0.85", 2048, 128)` reproduces M=1.196816073730588, the M saved
  in every R = 0.7 row. `bound_M("0.88", 16384, 128)` reproduces
  M=0.9714775364845991, the M saved in every R = 0.8 row, and
  min Re=0.358857166309262, matching the narrative. At the default
  K0=2048 the latter contour fails its branch check (min Re=-0.04814).
  The two min Re values are audit-session output, not saved in an
  artifact and not pinned by a test.
  These reproduce the implementation, not a valid complex modulus bound.
- The independent closed form for lambda_1, evaluated directly in Arb,
  is [0.0230957089661210338143102479064952916 +/- 3.59e-38], positive.

Cheapest next step: correct the norm, outward rounding, angle coverage,
and metadata, then perform a budgeted finite-range rerun. No repaired
range is asserted here. The panel-covering implementation
(`enclose_li.py`, rows for n = 1..10) does not use this derivative
remainder, but its branch and angle-coverage obligations still need review;
this audit does not promote its rows either, so they are measured too.

## Historical argument (2026-10-03; grade withdrawn by the audit above)

Everything below records what was claimed on 2026-10-03. Where it says
"lemma", "claim" or "enclosure" it describes the argument as then stated,
not a grade it holds now. L3 and L4 are exactly the steps audit items 1..3
found incomplete.

### Former claim: enclosed Li positivity for 1 <= n <= 58

Former claim: lambda_1, ..., lambda_58 > 0, each enclosed by an explicit
rational interval with positive lower bound. Artifacts:
enclosure_mid_*.json in this directory (superseded/ holds the
withdrawn n <= 71 claim and its correction note). Grade as stated
then: enclosure-carrying (Arb balls), hardened by the cross-checks
below, and called a theorem about n <= 58. Grade now: measured.
Either way it is not RH and implies no uniform statement.

Correction history: first stated to n = 71 with a remainder bound
missing the oscillation terms; re-derivation caught it, the
invalid rows were moved to superseded/ unmodified, and corrected
re-runs reported positive lower endpoints for n <= 58, with n = 59 as
the boundary. The audit above then withdrew the enclosure grade of
those corrected rows too.

### Definitions

Li coefficients: lambda_n = coefficient identity
  lambda_n = n [z^n] log xi(1/(1-z)),  R = contour radius,
  c_n = (1/2pi R^n) ∫_0^{2pi} f(R e^{it}) e^{-int} dt,
  f(z) = log xi(1/(1-z)), xi(s) = s(s-1)/2 pi^{-s/2} Gamma(s/2) zeta(s).
Derived in zeta/li.py (Hadamard product computation); numerically
checked against the literal derivative definition by
li_generating_function_defect (defects below 1e-45 at dps 20, pinned
in tests/test_li.py).

### Lemmas as stated then, with explicit dependencies

L1 (zero-free disk). Every nontrivial zero satisfies
|rho| >= gamma1 > 14 (first ordinate; pinned in this tree against
mpmath zetazero and the PARI oracle; the step uses completeness of the
zero count below gamma1). Hence every zero image
z = 1 - 1/rho satisfies |z| >= 1 - 1/|rho| >= 13/14 > 0.92.
So f is analytic on |z| <= 0.88, and the principal log below is
the analytic branch wherever Re(xi) > 0 on the contour.

L2 (branch, computed). On each contour used, interval evaluation
over panels covering the circle gave min Re(xi) lower > 0
(R=0.5: 0.4951 and R=0.7: 0.4854, saved in branch_R*.json; R=0.88
outer: 0.3589 and rho=0.85 outer: 0.2927, session output only), with
max |arg| upper < 0.12 on working contours (session output only).
The angle coverage this relies on is audit item 3.

L3 (midpoint remainder, analysis). The quadrature integrates
g(t) = f(R e^{it}) e^{-int}, so |g''| <= G2 with
G2 = F2 + 2n F1 + n^2 M, F1 = R M1, F2 = R M1 + R^2 M2c,
M1 = M/(rho-R), M2c = 2M/(rho-R)^2 by Cauchy's estimate, M a
max of |f| on |w| = rho from coarse interval panels
(audit item 1: the code bounds the coordinate norm, not |f|).
Then |integral - midpoint sum| <= G2 (2pi)^3/(24 K^2). Used triples
(R,rho,K) = (0.7,0.85,16384) for n <= 16 and (0.8,0.88,65536)
for n = 17..58. (An earlier version used M2c alone and is
withdrawn; see superseded/CORRECTION.md.)

L4 (soundness of balls, as stated then). Every operation (cos, sin,
exp, gamma, zeta, log) is Arb ball arithmetic (python-flint 0.9.0),
hence inclusion-monotonic; panel t-balls cover [0,2pi] with 1e-15
padding; midpoint balls arb(mid,1e-15) cover true midpoints.
The remainder itself is float arithmetic (audit item 2) and the
coverage claim is audit item 3, so L4 does not hold as stated.

### Former argument

For each n, the script enclose_li_mid.py evaluates the window
per L2-L4 and reports [re_lo, re_hi] with re_lo > 0:
n = 1..16 at (0.7,16384), n = 17..58 at (0.8,65536).
Sample windows: n = 16: [5.70, 5.73]; n = 40: [30.19, 30.77];
n = 58: [11.72, 97.04]. Imaginary windows all contain 0,
consistent with real lambda_n. Mechanical check over the
artifact files: full coverage 1..58, every lower endpoint > 0,
every window contains the independent float Cauchy value.
n = 59 ([-0.06, 111.57]) is the mapped boundary and is excluded.

### Cross-checks (agreement, not part of any argument)

C1. lambda_1 closed form 1 + euler/2 - log(4pi)/2 in Arb:
[0.02309570896612103381 +/- 3.6e-38], inside every saved
quadrature window for lambda_1.
C2. Float Cauchy values (zeta/li.py, independent DFT code path)
lie inside all 58 windows.
C3. Prec 128 vs 192 windows overlap for n = 1, 2 (widths panel-dominated).
C4. Disproof lanes empty: Li positivity scan n <= 100 and Jensen
scan d <= 16, n <= 25 show no violation (measured grade).

### Formal-statement check

The former claim was "the Li coefficients 1..58 of xi are
positive", with xi as implemented in zeta/core.py (checked against
mpmath and PARI oracles). Li's criterion (Li 1997, RH iff all
lambda_n >= 0) was used ONLY as motivation. No RH equivalence is
assumed or invoked in L1-L4. The statement matched what the code
computes: coefficients of log xi(1/(1-z)), not a restatement of RH.

The doors for this lane are in RESULTS.md, "The doors".
