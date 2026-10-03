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
zero-free (RADIUS_MAX in zeta/li.py), and whose certificate
reduces to bounding one Cauchy integral, which the Arb backend
in zeta/rigor.py can carry. Weil needs a new test-function
construction first; heat needs an upper bound on Lambda, which
no finite computation supplies.

Phase 2 obligation: enclose lambda_1..N on both Arb and mpmath.iv
backends, cross-check, and state the exact N and widths. Finite
positivity to N is a theorem about 1..N, not about RH. The
uniform tail (all n) remains open and is named as the gap.

## Gaps

1. No uniform estimate. Finite N, however certified, does not
   imply lambda_n >= 0 for all n (Littlewood).
2. Enclosure code for log xi on the Cauchy circle does not exist
   yet; probe used float mpmath only.
3. Formal statement check not yet done: any Lean claim must be
   checked against the original RH statement (zeros of zeta,
   real part 1/2), not against the encoded Li equivalence alone.
4. Weil Fejer defect 1.3e-04 is truncation, not a signal; needs
   tail accounting before any positivity reading.

## The doors

1. Active constraints at the optimum: none, this phase measured
   consistency, not an optimum. Binding object for phase 2 is the
   enclosure width growth like R^{-n} times the DFT sum width.
2. Frozen-constant inventory: Cauchy radius 0.5 (could raise
   toward 0.929 at the cost of arg-unwrap density and node
   count); dps 30 (trades time for width); N=20 (trades
   coverage for per-n width); Gaussian a=1 and Fejer b=1
   (arbitrary pair choice, relaxing the pair class is the
   Weil door); heat z in {0,1,2} (illustrative only).
3. Information class: phase-2 enclosures stay inside values of
   xi on Re s > 1/2, hence under the Li-configuration ceiling;
   they cannot close the uniform tail. The tail door requires
   reading more: a uniform bound on the zero sum or on the
   Taylor remainder for all n, which the current family does
   not contain.
