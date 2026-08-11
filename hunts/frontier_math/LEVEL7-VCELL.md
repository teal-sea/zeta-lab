# Level 7: the v-cell joint cap, the ladder correction, and the first reading

## Disposition (three results, stated in the order they matter)

1. **The joint cap exists and closes the pinch.**  The named theorem object
   of level 6b — an on-line-configuration-free upper bound on the joint
   profit against a pair cluster — is delivered in the Fourier bridge's one
   variable (`v_certificate.py`).  At the level-6b pinch (nu_p = 1.5,
   y = 0.49, 15 pairs), the cap is 37.36 against a budget of 41.11:
   **margin +3.75**, where the greedy measured adversary of level 6b
   reached 5.00.  The verdict quality is *measured* (double-precision
   quadrature with one-sided grid/Lipschitz structure); the arb pass is
   the named hardening.

2. **The level-6a full-ladder claim is corrected, not extended.**  The
   full-ladder hardened penta scan (`full_ladder_scan.py`) — the compute
   level 6a deferred — FAILS between the probe depths: the measured
   optimal-split eta has a shallow spike (eta(0.02) = 0.4066 against a
   plateau of ~0.30) that the seven-point probe grid could not see, and
   honest cell widths dilate the caps.  theta_full = 0.02 via the
   *per-depth linear assembly* is therefore withdrawn as a full-strip
   statement; what survives is the probe-grid statement plus the *joint*
   accounting, which does not use eta at all.  First failed cell and the
   full scan record are below.

3. **The reconnect's first reading is 0.6725009045 — a candidate, not a
   claim.**  With the retention theta_full = 0.02 fed through the
   one-sided ordered-gap floor (c_u = 5.02e-6 at nu_on = 0.6725007037),
   the candidate arithmetic gives +2.01e-7 over the pinned Theorem D
   constant.  Every named unproven step is listed in `reconnect.py`; per
   the operating rules, **no proportion is claimed to have moved**.

## The two exact laws behind the certificate

**LAW N (windowed spectral floor).**  For n on-line points in an interval
of length S and |v| <= pi/S:

    |F_on(v)| >= n cos(vS/2),

because each phasor's argument about the window midpoint is within vS/2 of
zero.  Integrated against K over the floor region this forces on-line
spectral mass kappa_00 n^2, so the internal mass obeys
R >= kappa_00 n^2 - n: **density is self-defeating pointwise in v** — the
fourth appearance of the self-defeat pattern (depth at level 3, on-line
packing at level 4, pair stacking at level 6b, and now spectral
concentration).  Machine check: worst margin +1.07e-4 over 200 random
windowed configurations (it is a proved inequality; the check is a typo
control).

**The safe cell.**  For on-line and pair ordinates in a common span-S
window and |v| <= pi/(2S), arg(F_on conj(F_p)) lies in [-vS, vS], so the
cross integrand is pointwise >= 0: the band where a dense pair cluster
concentrates its spectral mass cannot be attacked.  This is level 6b's
chi collapse (0.15 -> 0.017) as a pointwise mechanism.

**LAW M under the taper.**  int W_I dg = 2 * 4 pi b/(a^2 L) at every depth
and *every* taper (only v = 0 survives the g-integral): the mean of the
low-pass damage field is not attackable, only its band-limited ripple is.
Measured: 3.6064 for v1 = 0.4 and 0.8 alike (2 x LAW M = 3.6064).

## The cap, term by term

On-line zeros are split by distance from the pair window (near / mid /
far; R >= R_near + R_mid + R_far drops only nonnegative terms), and the
near cross by a smooth taper m_I + m_II = 1 (m_I = 1 on [0, v1/2], 0
beyond v1):

    J_cap = DP_I                        zone I: chain DP on the low-pass
                                        field, charge rho (1-theta) K_delta
          + M_II / ((1-rho)(1-theta))   zone II: per-cell Cauchy-Schwarz,
                                        telescoped to one pair-mass number
          + (1-rho)(1-theta)/(4 kappa_00)   the LAW N leak cap
          + DP_mid + err_far            measured mid field; psi_S tail

minimised over the (G_near, v1, rho) ladder — every choice one-sided, so
the min is.  At the pinch (v1 = 1.4, rho = 0.02, S = 13.33):

    dp_I 0.58 + M_II 25.62 + leak 7.27 + dp_mid 3.22 + far 0.68 = 37.36
    budget = slack 511.26 + T -470.16 = 41.11        margin +3.75

The pinch's spectral anatomy (from `fourier_bridge.pinch_spectrum`): the
pair deficit lives at |v| in [3, 7] (peak -176 per bin), the mean at
v ~ 0 (+59), and the certificate's accounting matches: the dense cluster's
attackable mass M_II is 25.8 of a total pair mass of ~101 — the other ~75
hides in the coherent band where the safe cell and LAW M defend it.

## Controls

| control | requirement | measured |
|---|---|---|
| LAW N typo control | floor holds on random configs | worst +1.07e-4 |
| safe cell | cross >= 0 on the coherent cell | worst +3.22 |
| LAW M taper independence | int W_I dg = 2 x 1.8032 | defect < 2e-5 |
| pinch budget vs level 6b | slack 511.26, T -470.16 | reproduced |
| domination (greedy joint) | greedy <= cap | 5.00 <= 37.36 (extended greedy 5.56) |
| theta = 1 must fail | cap infinite | infinite (charges vanish) |
| single-pair domination (levels 3/4) | measured profit <= cap | 0.14<=6.17, 1.85<=13.82, 6.73<=42.09 |
| sub-critical lattice (naive pointwise form) | defeats fixed d(v) linearly in N | H(4.7) drops -1436 -> -1508 as N 20 -> 80 while `\|F_on(4.7)\|^2` stays O(1) |

## The naive pointwise form is dead, and that record is kept

The directive's literal object — a fixed budget d(v) with
|F_on + F_p|^2 - theta |F_on|^2 >= -d(v) pointwise for every admissible
configuration — is defeated by the **sub-critical on-line lattice**
(spacing tau < 2 pi / L = h, the critical spacing of LAW J): its nonzero
spectral spikes leave the kernel band entirely, so on essentially all of
(0, L] the diagonal-subtracted integrand sits near -(1-theta) N while any
admissible budget is configuration-independent.  The escaping v-band is
*the whole band minus the v ~ 0 spike*, and the deficit grows linearly in
N (`pointwise_form_obstruction`; the aliasing family of level 1, again).
The delivered certificate survives the same family through LAW N: the
concentration that empties the mid-band fills the floor region, and the
n - kappa_00 n^2 credit caps the leak at (1-theta)/(4 kappa_00).  The
lesson is structural: **the v-cell budget must be an integral-per-cell
object with a spectral floor, not a pointwise envelope.**

## The sweep (joint verdicts, on-line-configuration-free)

Budget = sum slack + T_signed (exact); cap = J_cap; margins absolute.
`sep` is the level-6b separable margin (per-slack units) for the same
configuration; a row is covered when either is positive.

| configuration | budget | J_cap | v-margin | sep margin | covered by |
|---|---|---|---|---|---|
| lattice nu=0.75 y=0.45 | 200.09 | 223.23 | -23.15 | +0.73-ish flank | separable |
| lattice nu=1.0 y=0.45 | 370.04 | 393.82 | -23.78 | +0.93 | separable |
| lattice nu=1.0 y=0.49 | 606.98 | 636.69 | -29.71 | +1.10 | separable |
| lattice nu=1.05 y=0.49 | — | — | -24.11 | +0.500 | separable |
| lattice nu=1.1 y=0.49 | — | — | -19.10 | **-0.165** | **NEITHER** |
| lattice nu=1.2 y=0.49 | — | — | -11.70 | -0.573 | **NEITHER** |
| lattice nu=1.25 y=0.49 | 36.57 | 45.63 | -9.06 | -0.590 | **NEITHER** |
| lattice nu=1.3 y=0.49 | 35.11 | 42.07 | -6.97 | -0.600 | **NEITHER** |
| lattice nu=1.35 y=0.49 | — | — | -4.58 | -0.601 | **NEITHER** |
| lattice nu=1.45 y=0.49 | — | — | +0.50 | -0.600 | v-cap |
| lattice nu=1.5 y=0.49 (pinch) | 41.11 | 37.36 | **+3.75** | -0.599 | v-cap |
| lattice nu=1.5 y=0.45 | 33.99 | 28.88 | +5.11 | -0.596 | v-cap |
| lattice nu=2.0 y=0.49 | 84.65 | 44.50 | +40.15 | -0.555 | v-cap |
| lattice nu=3.0 y=0.49 | 237.30 | 71.71 | +165.59 | (breaks) | v-cap |
| alternating nu=1.0 | 139.43 | 157.29 | -17.86 | +0.53 | separable |
| edge cluster nu=1.0 | 606.98 | 636.69 | -29.71 | +1.10 | separable |
| sandwich nu=1.0 | 806.19 | 777.68 | +28.51 | +1.68 | both |
| shallow sandwich nu=1.0 | 800.92 | 772.30 | +28.61 | +1.67 | both |
| alternating nu=1.5 | 120.54 | 116.71 | +3.83 | — | v-cap |
| staggered / sandwich / shallow sandwich nu=1.5 | 207-226 | 39-57 | > +168 | — | v-cap |
| staggered nu=2.0 | 420.21 | 60.37 | +359.83 | — | v-cap |

Reading: the certificate closes nu_p >= 1.45 — including every mixed-depth
battery shape and the shallow sandwich that defeats the eta assembly —
which is exactly where the level-6b separable budget breaks (worst -0.599
at the pinch).  The separable level-6a caps close everything at
nu_p <= 1.05.  **The seam nu_p in [1.1, 1.4] deep is a genuine two-sided
hole** (post-tightening map, y = 0.49):

| nu_p | v-margin | separable | status |
|---|---|---|---|
| 1.05 | -24.11 | +0.500 | separable |
| 1.10 | -19.10 | -0.165 | **HOLE** |
| 1.20 | -11.70 | -0.573 | **HOLE** |
| 1.25 | -9.06 | -0.590 | **HOLE** |
| 1.30 | -6.97 | -0.600 | **HOLE** (also -5.60 at y = 0.45) |
| 1.35 | -4.58 | -0.601 | **HOLE** |
| 1.45 | +0.50 | -0.600 | v-cap |
| 1.50 | +3.75 | -0.599 | v-cap (the pinch) |

The truth sits far inside the budget throughout: the **extended greedy**
(sites to +-8 beyond the window, up to 100 zeros, min spacing 1/16)
extracts 7.23 with 18 zeros at nu = 1.3 against a budget of 35.11, and
5.56 at nu = 1.5 against 41.11 — the hole is bound looseness, not
adversary strength, and that control is now a permanent test.

**The escaping v-band, pinned.**  The seam's excess cap is M_II mass in
v in [5, 7]: the pair lattice's first spectral spike sits at 2 pi nu_p
(8.17 at nu = 1.3, 9.42 at 1.5), and as nu_p drops below ~1.45 its
shoulder re-enters the kernel band top (M_II share of [5, 7]: 17.8 at
nu = 1.3 vs 11.7 at nu = 1.5, against a budget 6.0 smaller).  The
Cauchy-Schwarz grants full anti-alignment against that shoulder; the
g-space truth shields it.  At nu = 1.3 the residual -6.97 decomposes as
M_II-term 30.8 (of which the [5, 7] band carries 17.8) + leak 7.2 +
dp_mid 3.3 + far 0.6 against budget 35.1: reversing it needs the band
grant cut by ~x0.6 — **the next theorem object is the g-localised v-cell
dual** (per-v-cell damage kernels W_c(g, y), band-passed and
taper-smoothed, with honest g-space charges in exactly that band), and
**the next kill control is the seam lattice (nu_p in [1.1, 1.4],
y = 0.49) attacked in v in [5, 7]**.

**The span boundary.**  The leak term is window-fixed, so short clusters
do not amortise it: at the pinch density, span 6 is open (v-margin
-1.09), span 8 closes (+1.24), span 10 closes (+3.75), span 16 with room
(+9.56 pre-tightening).  The certificate's closure at nu_p >= 1.45 is a
span >= 8 statement; shorter deep clusters at seam-adjacent densities
belong to the same named hole.

**Instrument v2.**  After the first audit, the mid-zone cell margins were
made per-cell (the blanket global-slope margin over ~500 cells was most
of dp_mid at seam-scale budgets: 6.5 -> 3.2 at the pinch), moving the
pinch margin from +0.49 to +3.75 and nu = 1.45 from -3.40 to +0.50.  The
sweep table above and the audit log reflect the v2 instrument.

## The full-ladder scan record (level 6a corrected)

220 depth cells (ratio 1.05 shallow, 1.012 from y = 0.09), hardened
`EnclosedPenta` caps at theta = 0.02, eta measured-optimal on a ten-point
grid, bracketed one-sided per cell.  **Verdict: OPEN — 45 cells fail, in
two bands:**

    shallow  y in [0.0095, 0.0501]   margins -0.017 .. -0.056
             (worst -0.0557 at [0.0293, 0.0307]; eta 0.37-0.41 vs 0.30)
    deep     y in [0.4193, 0.4724]   margins -0.002 .. -0.012
             (cap/slack 0.699-0.709 + eta 0.303 at honest 1.2% cells)

Every other cell passes, with margins +0.02 (mid-deep) to +0.36
(y < 0.01, where eta = 0).  The level-6a statement "theta_full = 0.02,
hardened at all seven probe depths" was resolution-fragile in both bands:
the probe grid could not see the shallow eta spike, and the deep probes
(1%-wide cells, margin 9e-4 of slack) do not survive honest cell widths.
theta_full via the per-depth linear assembly is accordingly **reduced to
the passing bands**; the shallow failing band is covered at the joint
level (shallow sandwich rows above), and the deep failing band coincides
with the seam depths, where coverage is the certificate's (nu >= 1.5,
span >= 10) plus the separable regime (nu <= 1.0) — the same named hole.

The eta spike mechanism: a shallow pair (y ~ 0.02) riding a deep lattice
takes its split share of strong T-negativity against a slack of only
8 sigma^2 + 8 sigma^4 ~ 0.012; the optimal reweighting cannot push the
ratio below ~0.41 because the deep partners' own budgets are nearly
saturated.  The joint accounting has no such bookkeeping: the shallow
layer's spectral mass is coherent (cosh(0.02 v) ~ 1) and hides at v ~ 0.
Joint verdict on the failing shape (shallow sandwich, y = 0.02 + 0.49):
margin **+169.85** at nu_p = 1.5 and **+28.61** at nu_p = 1.0 (both close;
at nu_p = 1.0 the separable accounting also holds it at +1.67 per slack).
The eta band is a bookkeeping failure of the linear per-depth assembly,
not a failure of theta_full's joint content on the tested shapes.

## The reconnect: the first reading of the decimal

The 2026 clean kill established that the withdrawn 0.672529 chain needed
exactly one missing input: an unconditional control on the hyperbolic
off-line blocks.  theta_full is that input, within its labels.  The
candidate arithmetic (`reconnect.py`, all floor minima one-sided, ladder
converged at n = 600001 = 2400001):

    c_u (one-sided, nu_on = 0.6725007037) = 0.00000502
    candidate = 0.6725007037 + 2 * 0.02 * 0.00000502 = 0.6725009045
    first reading: +2.01e-7 against the pinned constant

Controls: the hardened floor at CG's inputs is 0.00011287 <= CG's printed
0.00012636 (one-sided as it must be); the lambda_2 -> 2 lambda_1 lesion
kills the floor exactly.

**Named unproven steps, in severity order** (the reading is a candidate
until all close):

1. *The transplant lemma*: the paper's constant is linear in the retained
   on-line cross mass with coefficient 1, including the normalization
   match between the grid kernel omega^2 and the MT kernel g.  This is the
   withdrawn chain's plumbing, audited at every gate except the one
   theta_full now supplies — but it has never been proved, only not
   refuted.
2. *theta_full's own labels*: the v-certificate is quadrature-measured
   (arb pass named); pair-side placement freeness rests on the swept
   families plus the stacking floor; the sparse regime rests on the
   level-6a caps whose full-ladder statement is the corrected one above.
3. *Taper/truncation of the upstream count* restated one-sided at the
   composed value.

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/v_certificate.py      # ~30 min
.venv/bin/python hunts/frontier_math/full_ladder_scan.py   # ~45 min
.venv/bin/python hunts/frontier_math/reconnect.py          # ~2 min
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_v_certificate.py              # ~4 min
```
