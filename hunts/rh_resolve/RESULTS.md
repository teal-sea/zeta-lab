# RESULTS: rh_resolve phase 1, comparative probe

Grade: measured (float). No violation found, no support claimed.
Artifacts: probe_phase1.py, results_phase1.json (this directory).

## What was measured

Route A, Li coefficients (Cauchy, unconditional): lambda_1..20 all
positive at dps=30, min margin lambda_1 = 0.023095708966121033.
Dps 20 vs 30 agree to 3.33e-21 max. Cauchy minus zeros (n<=8,
1000 zeros) is +2.4e-10..+1.5e-08, consistent with the tabulated
truncation residual in zeta/li.py. Asymptotic at n=20 predicts
8.3507 vs measured 8.7693 (5 percent, inside the documented
oscillating remainder, not a constant offset).

Route B, Weil explicit formula: Gaussian a=1 gives
abs_diff 1.63e-21 (zero_side 0.0 with tail bound 1e-21, arithmetic
side 1.63e-21); Fejer b=1 gives abs_diff 1.33e-04. Both are
consistency checks of the two sides, not positivity theorems.

Route C, heat flow: Phi evenness defect 4.8e-32..3.5e-31 at
u = 0.5, 1.0, 2.0; H_0(z) = (1/8) Xi(z/2) confirmed with max
residual 3.77e-32. Identity machinery healthy, no RH signal.

Controls: rival battery imports and runs (constant-True claim is
shared with all rivals, distinguishes False, as it should);
Jensen scan d<=4, n<=2 all hyperbolic with min gaps 0.20..0.42
(no violation, never support, docs/08). Precision response
positive (3.3e-21 movement on dps change with cross-method
convergence pattern).

## Route chosen for phase 2

Li Cauchy positivity with enclosure-carrying numerics. Reason:
it is the only lane whose sign carries information (zeros-route
is structurally nonnegative), whose disk is unconditionally
zero-free (RADIUS_MAX in zeta/li.py), and whose enclosure
reduces to bounding one Cauchy integral, which the Arb backend
in zeta/rigor.py can carry. Weil needs a new test-function
construction first; heat needs an upper bound on Lambda, which
no finite computation supplies.

Phase 2 obligation: enclose lambda_1..N on both Arb and mpmath.iv
backends, cross-check, and state the exact N and widths. Finite
positivity to N is a theorem about 1..N, not about RH. The
uniform tail (all n) remains open and is named as the gap.

## Phase 2: enclosure-carrying positivity for lambda_1..3 (2026-10-03)

Status: proved finite positivity. Script enclose_li.py, panel
quadrature in Arb balls, R = 1/2, K = 32768, prec 128 and 192.

Enclosures (real part; imag parts all contain 0):

n   prec 128                    prec 192                    float check
1   [0.018865, 0.027334]       [0.018519, 0.027681]       0.02309570896612103381 (closed form)
2   [0.075364, 0.109330]       [0.074007, 0.110687]       0.09234573522804667039 (Cauchy float)
3   [0.155621, 0.259678]       (not run)                 0.20763892055432480379 (Cauchy float)

Every lower bound exceeds 0, so lambda_1, lambda_2, lambda_3 > 0
is decided. The closed-form enclosure for lambda_1
([0.02309570896612103381 +/- 3.6e-38]) lies inside both
quadrature enclosures: two independent routes agree.

Branch soundness, proved in the same run: min Re(xi) lower over
all 32768 panels is 0.4951 > 0 and max |arg| upper is 0.0329 < 1,
so the principal log is the analytic branch on the whole circle.
Zero-free disk uses only |rho| >= gamma1 > 14: every zero image
satisfies |z| = |1-1/rho| >= 1-1/14 > 0.92 > 1/2.

Explicit dependencies: Arb ball soundness (python-flint 0.9.0);
first-zero bound gamma1 > 14 (pinned in this tree against mpmath
and PARI oracles); the Li generating identity (derived in
zeta/li.py, defect-checked against the literal definition).
Precision control: prec 128 vs 192 overlap; widths are
panel-width dominated, as expected.

Scope, plainly: this is a theorem about n = 1, 2, 3. It says
nothing about RH, which needs all n. The uniform tail is open.

## Phase 3: extension to lambda_1..10 (2026-10-03)

Radius tradeoff measured: error scales like |f-prime|_R/(K R^n),
so R = 0.7 beats R = 0.5 above n = 5 and R = 0.3 loses badly
(R^{-n} dominates). At R = 0.7, K = 131072, prec 128:

n   enclosure                       float check
6   [0.776440, 0.878693]           0.8275660122823793
7   [1.038326, 1.210599]           1.1244601175709595
8   [1.323520, 1.607997]           1.4657556771470606
9   [1.619875, 2.081962]           1.8509160483825342
10  [1.908723, 2.649964]           2.2793393631931577

Combined with phase 2 (R = 0.5, K = 131072: n = 1..5 widths
0.002..0.18, all lower bounds > 0), positivity is now enclosed
for n = 1..10. Branch soundness at R = 0.7 proved in-run:
min Re(xi) lower 0.4869 > 0, max |arg| upper 0.1192.
Artifacts: enclosure_li_R0.7_K131072_p128.json and
 enclosure_li_K131072_p128.json (R = 0.5 rows for n = 1..5).

Ceiling note: width grows like n R^{-n}/K, so n = 20 needs
K ~ 3M panels with this naive scheme. Finite extension has
diminishing returns and no finite N implies RH. The tail needs
new mathematics, not larger K.

## Phase 4: enclosure-carrying positivity to n = 58, after a correction (2026-10-03)

First stated to n = 71, then WITHDRAWN IN PART: re-derivation
showed the midpoint remainder missed the oscillation terms
(n^2 M dominant for n >= 5). Invalid rows moved unmodified to
superseded/ with CORRECTION.md; corrected bound
G2 = F2 + 2n F1 + n^2 M re-ran. Corrected state: n = 1..58
enclosed (1..16 at R = 0.7/K = 16384, 17..58 at R = 0.8/K =
65536), n = 59 mapped as the boundary ([-0.06, 111.57]).
Mechanical verification: coverage 1..58 complete, all lowers > 0,
all enclose the float Cauchy values. The panel-covering scheme
(n <= 10, pure inclusion) was never affected and agrees.

Original phase-4 text (n = 71 claim) is preserved in git history
and superseded/CORRECTION.md, not edited away.

Second scheme (enclose_li_mid.py): midpoint rule with near-point
balls plus analytic remainder M2 (2pi)^3/(24 K^2), M2 from
Cauchy's estimate on a larger circle whose M comes from coarse
interval panels. 1000x tighter than panel covering at equal K.

Decided range (corrected): lambda_n > 0 enclosed for every
n = 1..58. Contours: R = 0.7 (n <= 16, K = 16384) and R = 0.8
with rho = 0.88 (n = 17..58, K = 65536, K0 = 16384). Branch
proved on every contour (Re(xi) lower 0.29..0.49 > 0). Sample
widths: n = 16: [5.70, 5.73]; n = 40: [30.19, ~30.7];
n = 58: [11.72, 97.04]. Boundary mapped: n = 59 does not
decide at this K ([-0.06, 111.57]). Coverage 1..58
re-verified mechanically, all lower bounds > 0.

This is a theorem about n <= 58. It is not RH and implies
nothing uniform. The tail remains open and needs new
mathematics; width grows like n^3 R^{-n}/K^2, so each unit of
n costs ~1.35x the panels near the boundary.

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

1. No uniform estimate. Finite N, however enclosed, does not
   imply lambda_n >= 0 for all n (Littlewood).
2. Width grows like n^3 R^{-n}/K^2 under the midpoint-Cauchy
   scheme (n^2 from the oscillation term in G2). At K = 65536
   and R = 0.8 the boundary is n = 59; each further unit of n
   costs ~1.35x the panels. A higher-order rule (Simpson via
   the same Cauchy device) would shift the boundary, not remove
   it.
3. Formal statement check not yet done: any Lean claim must be
   checked against the original RH statement (zeros of zeta,
   real part 1/2), not against the encoded Li equivalence alone.
4. Weil Fejer defect 1.3e-04 is truncation, not a signal; needs
   tail accounting before any positivity reading.

## Logarithmic-derivative equivalence (2026-10-03)

Derived, not a resolution. RH is equivalent to Re(xi'/xi(s)) > 0
for every s with real part greater than 1/2. Proof, dependencies,
and the two killed sufficient conditions (positive weight;
log-concavity of Phi) are in EQUIVALENCE.md. Spot checks:
check_logderiv.py. The open step is the sign of that real part
inside the strip, where the archimedean term and zeta'/zeta
nearly cancel.

## The doors

1. Active constraints at the optimum: the enclosed boundary
   n = 59 binds on the enclosure width, which grows like
   n^3 R^{-n}/K^2. The n^2 factor comes from the oscillation
   term in G2 (missing it once cost a full correction round).
   Shadow price near the boundary: each further unit of n
   costs ~1.35x the panels at fixed R = 0.8, K = 65536.
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
