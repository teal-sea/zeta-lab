# Level 7: the v-cell joint cap, the ladder correction, and the first reading

## Disposition (three results, stated in the order they matter)

1. **The joint cap exists and closes the entire swept density axis.**  The
   named theorem object of level 6b — an on-line-configuration-free upper
   bound on the joint profit against a pair cluster — is delivered twice
   over in `v_certificate.py`: the v-cell route (the spectral laws below)
   and the **direct route**, the level-4 chain counting dual on the damage
   field summed over pair centres with the positive part taken of the
   JOINT field.  The final cap is the min of the two.  At the level-6b
   pinch (nu_p = 1.5, y = 0.49, 15 pairs) the direct cap is 14.78 against
   a budget of 41.11: **margin +26.33** (v-route: +3.75; greedy adversary:
   5.00).  Every lattice density nu_p in [0.75, 3], every mixed-depth
   battery shape, and every short-span cluster tested now closes — there
   is no uncovered configuration in the sweep.  The verdict quality is
   *measured* (double-precision grids with one-sided structure); the arb
   pass is the named hardening.

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

(the v-route's pinch verdict; the direct route reaches 14.78 there, and
the final cap is the min of the two)

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
| domination (greedy joint) | greedy <= cap | 5.00 <= 14.78 (extended greedy 5.56) |
| joint vs per-pair positive part | per-pair clipping inflates the field ~10x | at nu 1.3, g 4.65: joint 0, clipped > 4 |
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

Budget = sum slack + T_signed (exact); cap = min(direct, v-route); margins
absolute.  **Every configuration closes, all via the direct route.**

| configuration | budget | direct cap | margin |
|---|---|---|---|
| lattice nu=0.75 y=0.3 / 0.45 / 0.49 | 45.9 / 200.1 / 294.4 | 14.2 / 141.0 / 230.7 | +31.7 / +59.1 / +63.7 |
| lattice nu=1.0 y=0.3 / 0.45 / 0.49 | 57.4 / 370.0 / 607.0 | 5.1 / 53.1 / 119.4 | +52.3 / +317.0 / +487.6 |
| lattice nu=1.05..1.45 y=0.49 (the former hole) | 34.7-401.9 | 14.9-47.6 | **+15.7 .. +354.4** |
| lattice nu=1.25 y=0.3 / 0.45 / 0.49 | 9.2 / 25.5 / 36.6 | 2.6 / 13.8 / 20.9 | +6.5 / +11.7 / +15.7 |
| lattice nu=1.5 y=0.3 / 0.45 / 0.49 (pinch) | 22.5 / 34.0 / 41.1 | 1.4 / 9.7 / 14.8 | +21.1 / +24.3 / **+26.3** |
| lattice nu=2.0 y=0.3 / 0.45 / 0.49 | 64.1 / 77.2 / 84.7 | 0.9 / 8.9 / 13.8 | +63.2 / +68.3 / +70.8 |
| lattice nu=3.0 y=0.3 / 0.45 / 0.49 | 201.6 / 224.7 / 237.3 | 0.9 / 11.5 / 19.2 | +200.8 / +213.2 / +218.1 |
| alternating nu=1.0 / 1.5 / 2.0 | 139.4 / 120.5 / 314.8 | 11.9 / 1.5 / 12.7 | +127.6 / +119.0 / +302.1 |
| staggered nu=1.0 / 1.5 / 2.0 | 108.1 / 207.9 / 420.2 | 4.2 / 3.3 / 3.5 | +103.8 / +204.7 / +416.7 |
| sandwich nu=1.0 / 1.5 / 2.0 | 806.2 / 226.2 / 434.3 | 37.3 / 10.6 / 8.1 | +768.9 / +215.6 / +426.2 |
| shallow sandwich (y=0.02+0.49) nu=1.0 / 1.5 / 2.0 | 800.9 / 226.0 / 434.0 | 37.0 / 10.5 / 7.9 | +763.9 / +215.4 / +426.0 |
| edge cluster nu=1.0 / 1.5 / 2.0 | 607.0 / 41.1 / 84.7 | 119.4 / 14.8 / 13.8 | +487.6 / +26.3 / +70.8 |
| short spans: span 6 nu=1.5; span 4 nu=1.3 | 32.4 / 27.8 | 14.6 / 17.5 | +17.8 / +10.4 |

The v-route's own margins (closing nu_p >= 1.45, open below) and the
separable margins (closing nu_p <= 1.05) are retained in the audit log as
the two independent cross-checks; the direct route dominates both
everywhere tested.

Reading: the v-route closes nu_p >= 1.45, the separable accounting closes
nu_p <= 1.05, and the band between them — the seam that was, for one
session, a genuine two-sided hole — **is closed by the direct route with
wide margins** (y = 0.49):

| nu_p | v-margin | separable | direct margin | status |
|---|---|---|---|---|
| 1.05 | -24.11 | +0.500 | +354.36 | closed |
| 1.10 | -19.10 | -0.165 | +153.67 | closed (was the hole) |
| 1.20 | -11.70 | -0.573 | +19.48 | closed (was the hole) |
| 1.25 | -9.06 | -0.590 | +15.72 | closed (was the hole) |
| 1.30 | -6.97 | -0.600 | +16.93 | closed (was the hole) |
| 1.35 | -4.58 | -0.601 | +17.81 | closed (was the hole) |
| 1.45 | +0.50 | -0.600 | +22.90 | closed |
| 1.50 (pinch) | +3.75 | -0.599 | +26.33 | closed |

Short spans close too: span 6 at nu = 1.5 (+17.76 direct vs -1.09
v-route), span 4 at nu = 1.3 (+10.38).  Sparse lattices close directly as
well (nu = 0.75, y = 0.49: +63.68), so the direct route alone covers the
axis; the v-route and the separable caps stand as independent
cross-checks.

**Why the direct route was almost missed, and what the seam taught.**
The direct object — "the level-4 machinery with the damage field summed
over pair centres", named verbatim at level 6b — is tight *only* if the
positive part is taken of the JOINT field: clipping per pair discards the
coincident-pair shielding (a deep pair's own +2E(y)^2 hump protecting its
neighbour's negative band) and inflates the field by an order of
magnitude (at nu = 1.3, g = 4.65: joint field 0, per-pair-clipped field
> 4).  That near-miss is the separable accounting's ghost, and it is now
a permanent control.  The seam diagnosis (the v-route's Cauchy-Schwarz
granting anti-alignment against the band-edge spike shoulder in
v in [5, 7]) stands as the record of why the v-route is loose there —
the mutual exclusion that protects the lattice is g-local shielding,
visible to the direct field and invisible to band-wise moduli.

**The extended greedy** (sites to +-8 beyond the window, up to 100 zeros,
min spacing 1/16) extracts 7.23 at nu = 1.3 against the direct cap 18.18
and budget 35.11: adversary, cap and budget are now in the right order
with honest daylight at every tested density, and the control is a
permanent test.

**Instrument v2.**  After the first audit, the mid-zone cell margins were
made per-cell (the blanket global-slope margin over ~500 cells was most
of dp_mid at seam-scale budgets: 6.5 -> 3.2 at the pinch), and the direct
route was added.  The sweep table above and the audit log reflect the v2
instrument.

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
