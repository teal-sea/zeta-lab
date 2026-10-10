# RESULTS: rh_resolve, direct RH resolution attempt (unresolved)

Grade: measured (float), throughout. No violation found, no support claimed.
Every Li row in this file is graded measured, including the Arb-ball rows
of phases 2 to 4 (AUDIT.md). Numbers quoted from the saved artifacts in this
directory are pinned by `tests/test_rh_resolve.py`; numbers that were only
printed by a session say so where they appear.
Artifacts: probe_phase1.py, results_phase1.json and the files named below.

## Current audit status (2026-10-04)

The n <= 58 enclosure claim below is withdrawn pending a sound complex
modulus bound, outward-rounded remainder arithmetic, angle coverage, and
a reproducible rerun. See AUDIT.md (formerly THEOREM.md) for exact defects
and bounded checks. The saved rows still report positive lower endpoints
for 1..58, but these are numerical evidence, not an established enclosure.
Phases 2 to 4 below were regraded to measured on 2026-10-10 to match the
audit; the wording claimed at the time is in git history and in AUDIT.md's
historical section. Raw artifacts are unchanged.

## What was measured

Route A, Li coefficients (Cauchy, unconditional): lambda_1..20 all
positive at dps=30, min margin lambda_1 = 0.023095708966121033.
Dps 20 vs 30 agree to 3.33e-21 max. Cauchy minus zeros (n<=8,
1000 zeros) is +2.4e-10..+1.5e-08, consistent with the tabulated
truncation residual in zeta/li.py. Asymptotic at n=20 predicts
8.3507 vs measured 8.7693 (5 percent, inside the documented
oscillating remainder, not a constant offset).

Route B, Weil explicit formula: Gaussian a=1 gives
abs_diff 1.63e-21 (zero_side 0.0, arithmetic side 1.63e-21; the
session's tail bound of 1e-21 is not saved); Fejer b=1 gives
abs_diff 1.33e-04. Both are consistency checks of the two sides, not
positivity results.

Route C, heat flow: Phi evenness defect 4.8e-32..3.5e-31 at
u = 0.5, 1.0, 2.0; H_0(z) = (1/8) Xi(z/2) confirmed with max
residual 3.77e-32. Identity machinery healthy, no RH signal.

Controls: rival battery imports and runs (constant-True claim is
shared with all rivals, distinguishes False, as it should);
Jensen scan d<=4, n<=2 all hyperbolic with min gaps 0.20..0.42
(session output, not saved; no violation, never support, docs/08).
Precision response positive (3.3e-21 movement on dps change with
cross-method convergence pattern).

## Route chosen for phase 2

Li Cauchy positivity with ball-arithmetic numerics. Reason:
it is the only lane whose sign carries information (zeros-route
is structurally nonnegative), whose disk is unconditionally
zero-free (RADIUS_MAX in zeta/li.py), and whose enclosure
reduces to bounding one Cauchy integral, which the Arb backend
in zeta/rigor.py can carry. Weil needs a new test-function
construction first; heat needs an upper bound on Lambda, which
no finite computation supplies.

Phase 2 obligation: enclose lambda_1..N on both Arb and mpmath.iv
backends, cross-check, and state the exact N and widths (the mpmath.iv
run was never done). Enclosed positivity to N would be a statement about
1..N only, not about RH. The uniform tail (all n) remains open and is
named as the gap.

## Phase 2: positive lower endpoints for lambda_1..3 (2026-10-03; measured)

Status: measured. On 2026-10-03 this phase was recorded as proved finite
positivity; that grade is withdrawn, because the panel scheme's branch
and angle-coverage obligations are unreviewed (AUDIT.md). Script
enclose_li.py, panel quadrature in Arb balls, R = 1/2, K = 32768,
prec 128 and 192.

Saved windows (real part; imag parts all contain 0):

n   prec 128                    prec 192                    float check
1   [0.018865, 0.027334]       [0.018519, 0.027681]       0.02309570896612103381 (closed form)
2   [0.075364, 0.109330]       [0.074007, 0.110687]       0.09234573522804667039 (Cauchy float)
3   [0.155621, 0.259678]       (not run)                 0.20763892055432480379 (Cauchy float)

Every saved lower endpoint exceeds 0. The closed-form value for
lambda_1 ([0.02309570896612103381 +/- 3.6e-38]) lies inside both
quadrature windows: two independent routes agree, which is a measured
agreement, not an enclosure.

Branch check, same run: min Re(xi) lower over all 32768 panels is
0.4951 > 0 (saved in branch_R0.5_K32768.json) and max |arg| upper is
0.0329 < 1 (session output, not saved). With angle coverage unproved
(AUDIT.md item 3) this does not establish the branch on the whole
circle. Zero-free disk uses only |rho| >= gamma1 > 14: every zero image
satisfies |z| = |1-1/rho| >= 1-1/14 > 0.92 > 1/2.

Explicit dependencies: Arb ball soundness (python-flint 0.9.0);
first-zero bound gamma1 > 14 (pinned in this tree against mpmath
and PARI oracles); the Li generating identity (derived in
zeta/li.py, defect-checked against the literal definition).
Precision control: prec 128 vs 192 windows overlap; widths are
panel-width dominated, as expected.

Scope, plainly: measured positive lower endpoints for n = 1, 2, 3.
It says nothing about RH, which needs all n. The uniform tail is open.

## Phase 3: extension to lambda_1..10 (2026-10-03; measured)

Radius tradeoff: error scales like |f-prime|_R/(K R^n), so R = 0.7
beats R = 0.5 above n = 5 (session comparison; no R = 0.5 rows above
n = 5 are saved) and R = 0.3 loses badly (R^{-n} dominates; the saved
R = 0.3 rows for n = 6..10 all have negative lower endpoints).
At R = 0.7, K = 131072, prec 128:

n   saved window                    float check
6   [0.776440, 0.878693]           0.8275660122823793
7   [1.038326, 1.210599]           1.1244601175709595
8   [1.323520, 1.607997]           1.4657556771470606
9   [1.619875, 2.081962]           1.8509160483825342
10  [1.908723, 2.649964]           2.2793393631931577

Combined with phase 2 (R = 0.5, K = 131072: n = 1..5 widths
0.002..0.18, all lower endpoints > 0), the saved lower endpoints are
positive for n = 1..10 (measured, AUDIT.md). Branch check at R = 0.7
in-run: min Re(xi) lower 0.4869 > 0, max |arg| upper 0.1192 (session
output at K = 131072, not saved; the saved check at K0 = 32768 in
branch_R0.7_K32768.json gives 0.4854).
Artifacts: enclosure_li_R0.7_K131072_p128.json and
 enclosure_li_K131072_p128.json (R = 0.5 rows for n = 1..5).

Ceiling note: width grows like n R^{-n}/K. Extrapolating the saved
n = 10 row at R = 0.7 by that law, deciding n = 20 would need about
three times K = 131072 (an estimate, not run). Finite extension has
diminishing returns and no finite N implies RH. The tail needs
new mathematics, not larger K.

## Phase 4: midpoint scheme, positive lower endpoints to n = 58 (2026-10-03; enclosure grade withdrawn 2026-10-04)

Status: measured. First stated to n = 71, then withdrawn in part:
re-derivation showed the midpoint remainder missed the oscillation
terms. With them the bound G2 = F2 + 2n F1 + n^2 M exceeds the old
M2c from n = 4 at R = 0.7 and from n = 5 at R = 0.8. Invalid rows
were moved unmodified to superseded/ with CORRECTION.md, and the
corrected bound re-ran. Corrected state: saved lower endpoints are
positive for n = 1..58 (1..16 at R = 0.7/K = 16384, 17..58 at
R = 0.8/K = 65536), with n = 59 mapped as the boundary
([-0.06, 111.57]). Mechanical check: coverage 1..58 complete, all
lower endpoints > 0, all windows contain the float Cauchy values.
The audit of 2026-10-04 (AUDIT.md) then withdrew the enclosure grade
of these corrected rows: the complex modulus bound, outward rounding
of the remainder arithmetic, and angle coverage are unproved. The
panel-covering scheme (n <= 10) does not use the derivative remainder
and agrees with these rows, but it is measured too.

Original phase-4 text (n = 71 claim) is preserved in git history
and superseded/CORRECTION.md, not edited away.

Second scheme (enclose_li_mid.py): midpoint rule with near-point
balls plus the remainder G2 (2pi)^3/(24 K^2), G2 from Cauchy's
estimate on a larger circle whose M comes from coarse interval
panels. For lambda_1 at K = 4096, R = 0.5 its saved window is about
9000x narrower than the panel-covering one.

Range with positive saved lower endpoints: every n = 1..58.
Contours: R = 0.7 with rho = 0.85 (n <= 16, K = 16384) and R = 0.8
with rho = 0.88 (n = 17..58, K = 65536, K0 = 16384). Branch checks
on the contours gave Re(xi) lower 0.29..0.49 (partly session output;
see AUDIT.md, L2). Sample windows: n = 16: [5.70, 5.73];
n = 40: [30.19, 30.77]; n = 58: [11.72, 97.04]. Boundary mapped:
n = 59 does not decide at this K ([-0.06, 111.57]). Coverage
1..58 re-verified mechanically, all lower endpoints > 0.

Scope: measured, about n <= 58 only. It is not RH and implies
nothing uniform. The tail remains open and needs new mathematics.
The nominal width grows like n^3 R^{-n}/K^2; the saved width grows
by a factor of about 1.31 from n = 58 to n = 59 at fixed K.

## Rival lane closed (2026-10-03)

Weil zero-side comparison, Gaussian h with a = 0.5, 1, 2:
87 DH on-line ordinates to height 150 (Z_dh sign hunt) plus the
pinned off-line pair, vs 400 zeta ordinates. Both sides positive
at all three widths (artifact rival_weil.json). Expected, and
POWERLESS BY CONSTRUCTION: positive h sums positive over any
zero set, so this comparison cannot distinguish zeta from DH.
The distinguishing content lives in the arithmetic side (prime
coefficients, where the Euler product enters), which no
zero-side scan reads. This matches the outband hunt's ceiling:
Weil positivity is shared structure, not an RH detector. Lane
closed by argument plus this null, not by building DH prime
machinery for a foregone null. The battery (zeta.epstein.battery)
remains the live control for future candidate claims.

## Disproof search (2026-10-03, measured, both lanes empty)

Li lane: positivity scan n = 1..100 (Cauchy, dps 25), zero
violations, min margin lambda_1 = 0.023095708966121033,
lambda_100 = 118.603775376791. Artifact disproof_li100.json.
Jensen lane: hyperbolicity scan d <= 16, n <= 25 (416 rows,
dps 30), zero non-hyperbolic instances, min root gap 0.0432.
Artifact disproof_jensen16x25.json. Honest reading for both:
no violation found in range, never support for RH.

## Gaps

1. The Li rows are measured. The enclosure obligations in AUDIT.md
   (complex modulus bound, outward rounding, angle coverage, run
   metadata) are open, and no repaired rerun exists.
2. No uniform estimate. Finite N, however enclosed, does not
   imply lambda_n >= 0 for all n (Littlewood).
3. Width grows like n^3 R^{-n}/K^2 under the midpoint-Cauchy
   scheme (n^2 from the oscillation term in G2). At K = 65536
   and R = 0.8 the saved rows stop deciding at n = 59. The saved
   width grows about 1.31x from n = 58 to 59, so with the 1/K^2
   law deciding one more n needs roughly 1.13x the panels (an
   estimate from the saved rows, not a rerun). A higher-order rule
   (Simpson via the same Cauchy device) would shift the boundary,
   not remove it.
4. Formal statement check not yet done: any Lean claim must be
   checked against the original RH statement (zeros of zeta,
   real part 1/2), not against the encoded Li equivalence alone.
5. Weil Fejer defect 1.3e-04 is truncation, not a signal; needs
   tail accounting before any positivity reading.

## Logarithmic-derivative equivalence (2026-10-03)

Classical, recorded here; not a resolution of RH and not new. RH is
equivalent to Re(xi'/xi(s)) > 0 for every s with real part greater
than 1/2. Main states it in `hunts/epp_herglotz/RESULTS.md`; see
Lagarias, Acta Arith. 89 (1999), 217-234. EQUIVALENCE.md records an
ordinary derivation of this known result (unreviewed), its
dependencies, and the positive-weight witness. The log-concavity
obstruction remains conditional on an unproved uniform margin. Spot
checks: check_logderiv.py. The open step is the sign of that real part
inside the strip, where the archimedean term and zeta'/zeta
nearly cancel.

## The doors

1. Active constraints: first repair the enclosure soundness gaps in
   AUDIT.md. The historical calculation reports a boundary at n = 59;
   its nominal width grows like
   n^3 R^{-n}/K^2. The n^2 factor comes from the oscillation
   term in G2 (missing it once cost a full correction round).
   Shadow price near the boundary: the saved width grows about
   1.31x per unit of n at fixed R = 0.8, K = 65536, so each further
   n costs roughly 1.13x the panels (estimate from the saved rows).
2. Frozen-constant inventory: contour radii R = 0.7/0.8 with
   outer rho = 0.85/0.88 (raising rho toward the 0.92 zero-free
   edge tightens M2c but risks the branch condition, since
   zero images start at 0.929); midpoint order (Simpson via the
   same Cauchy device would change the width law to 1/K^4 and
   shift the boundary outward at equal cost); prec 128
   (widths are discretization-dominated, more digits buy
   nothing); Gaussian a in {0.5,1,2} and Fejer b = 1 for the
   Weil probes (arbitrary pair choices, relaxing the pair class
   is the Weil door, already priced at zero by the outband
   hunt); heat z in {0,1,2} (illustrative only).
3. Information class: all enclosures stay inside values of xi
   on Re s > 1/2, hence under the Li-configuration ceiling;
   they cannot close the uniform tail. The tail door requires
   reading more: a uniform bound on the zero sum or on the
   Taylor remainder valid for all n at once, which the current
   family does not contain. Finite K decides finitely many n,
   no matter how large, so extension is mileage, not approach.
