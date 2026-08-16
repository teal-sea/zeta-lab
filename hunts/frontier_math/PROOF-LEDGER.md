# Proof ledger: closure audit of the 0.672529 candidate

Audited local state: `add40513fb1919ea4d00f87bdb61b5b433f7801d`.

Pinned upstream state:

- Paper PDF SHA-256:
  `6792988e6cd0e17690621ce898abd5d534f98407741bc7cb14bbe7d07c77d72f`.
- Lean companion: `anthropics/zeta-23-lean`, commit
  `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, tag `v1.0`.
- Upstream Mathlib commit:
  `51e6992efd06126df61a496bebf8f49482a4e129`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Block positivity | FAILED | upstream `Zeta23/Defs.lean:298-305`; `Zeta23/ZeroSide.lean:314-379` | transpose, not conjugate transpose; exact witness `tr(P1 Q') = -2` |
| Truncation | NOT REACHED | Gate 0 is necessary first | endpoint chain loss also found: `j-1` per cell, asymptotically negligible |
| Taper | NOT REACHED | Gate 0 is necessary first | no taper estimate can change the failed algebraic sign |
| Census | MOOT | pinned Theorem D normalization | audit found no fatal conversion error; it cannot repair Gate 0 |
| Bootstrap | MOOT | `gap_lp.py:bootstrap` | first forward step was noncircular; it cannot repair Gate 0 |
| LP / exact object | MOOT | `gap_lp.py`, `_GTable` | current value is a float primal with sampled minima, not an exact lower object |
| Lean integration | OBSTRUCTION ADDED | `lean/ZetaLean/FrontierMathObstruction.lean` | kernel checks the negative cross interaction and `9 < 13` failure |

Disposition: **CLEAN KILL**. The candidate constants `0.6725124`,
`0.672529`, and `0.6725318` are withdrawn. The pinned upstream constant
`0.6725007037...` is unaffected.

## Post-kill interaction-control audit

Audited local state: `21ad0d49720a288b1d428d46664d623a0f6c4282`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Lower bound for `2tr(PQ)` | FAILED | pinned `ZeroSide.lean:470-555` | `Q=-tP` has positive index zero and sends the interaction to negative infinity |
| Positive recovery coefficient | FAILED | pinned rank-trace lemma at `c=2` | Gaussian-integer family forces `theta <= 3/(2m^2+1)` |
| Prime-side moment objection | CLOSED | paper's trace and Frobenius summaries | rational direct-sum family has `tr(A)=N`, approaches the printed second moment, and has normalized slack below the full old floor |
| Surviving rigidity floor | NONE | all rows above | every fixed positive portion is excluded by the family |
| Missing input | IDENTIFIED | comparison of gap data with zero-side interface | signed on/off incidence with horizontal depth, ordinate offset, and overlap consistency |
| Next hierarchy | DESIGNED | `INTERACTION-CONTROL-REPORT.md` | marked incidence cells, marked gap words, projective consistency, then local potentials |

Disposition: **NO CONTROL FROM EXISTING INPUTS**. No new decimal search is
opened. The next admissible task is to find an unconditional signed-incidence
constraint that rejects the exact obstruction family.

## Level-1 constraint delivered (2026-08-11)

Audited local state at the start of this session: `c35dc04`. Full account:
`SIGNED-INCIDENCE-LAW.md`; instrument `incidence_law.py`; controls
`test_incidence_law.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Unconditional signed incidence law | DELIVERED | complex extension of the paper's Lemma 2.2 (no aliasing at critical spacing) | bilinear self-incidence `= aL^2` at every depth and position; defect ladder `1.7e-13 -> 5.4e-19` |
| Rational lower envelope per cell | DELIVERED | alias-free imaginary mass `aL^2 sigma^2(y)` | `2 Re(Bhat^2) >= -2 sigma^2(y)` on every subgrid; worst scan margin `+3.3e-4`, no violation |
| Exclusion of the exact obstruction family | DELIVERED | walls W1-W4 in the report | bad-pair margin exact integer `2m^2+2`; `m_cap(L=8) = 1.315` kills every `m >= 2` at every placement; dilution shares the bad block |
| Aliasing lesion | HELD | grid stretch 65/64 | defect `0.3038` flat across the ladder |
| Rival check | HELD | Davenport-Heilbronn off-line zero, pinned digits | LAW D defect `2.7e-14` at depth `0.30851718...` |
| Epsilon-robust exclusion | NOT ATTEMPTED | level-2 projective consistency | recorded as the open task; exactness of W2/W3 named as the boundary |

Disposition: **LEVEL 1 OPEN FOR LEVEL 2**. The hierarchy's entry condition is
met; the level-2 task (one off-line pair marked against two consecutive
on-line gaps, projective consistency between marginals) may begin. No decimal
search was run and no proportion is claimed.

## Level 2 delivered (2026-08-11)

Full account: `LEVEL2-GAP-CONSISTENCY.md`; instrument `gap_consistency.py`;
controls `test_gap_consistency.py`. Both defects level 1 recorded against
itself are repaired by using LAW D off-diagonal.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Projective consistency (one-gap marginals vs marked two-gap words) | DELIVERED | LAW D off-diagonal: incidence is `omega(g) = Phi2(g)/Phi2(0)` | correlation 0.99 buys gap <= 0.0719; independent outer declaration refuted, residual `0.13228305` |
| Anti-duplication (aggregate caps) | DELIVERED | paper's (2.17) majorant + unconditional `N(t+1)-N(t) <= A_0 log(t+3)` | `kappa(3) = 6.825`, `kappa_cross(3, 0.3) = 31.036`; aggregate flat across `n = 20, 80, 240` |
| Kill control: one pair duplicated in overlapping cells | HELD | n-independence of `kappa_cross` | level-1-legal cheat rejected past the crossover `n = 72`, margin growing linearly |
| Epsilon-robust family exclusion | DELIVERED | `R(P) <= n kappa(nu)` bounds the quantity, not the declaration | family needs `n-1` per label; at `nu = 3` every `m >= 2` excluded, `m = 10` by 29.5x |
| Residue for the recovery coefficient | IMPROVED | density cap replaces depth cap | floor `3/kappa(nu) ~ 1/log T` beats level 1's `~e^{-L/2}` from `L >= 16`, by 544x at `L = 32` |
| Decoy / lesion / rival | HELD | see report's ledger | cap planted 4x small violated 11/12; collapse saturates at exactly `n-1`; DH depth obeys the laws |
| Admissible `theta` for an actual inequality | NOT ATTEMPTED | level 3 telescoping potential | named as the open task; nothing here proposes a strengthened inequality |

Disposition: **LEVEL 2 OPEN FOR LEVEL 3**. The improvement is asymptotic in
`n` (crossover stated, not hidden) and the size bound is a function of `nu`
(tabulated, not averaged away). No decimal search was run and no proportion
is claimed.

## Level 2, marked two-gap coexistence (2026-08-11)

Full account: `LEVEL2-TWO-GAP-MARKED.md`; instrument `two_gap_marked.py`;
controls `test_two_gap_marked.py`. The directive's immediate question is
answered NO, and the outcome is mixed by lane.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Immediate question: joint saturation across two gaps | ANSWERED **NO** | Cauchy-Schwarz equality needs `sin(gu) ~ sinh(yu)`, Taylor forces `g(g^2+y^2)=0` | no cell saturates at any offset; at `g=0`, `W = +2.8046` against floor `-0.8623` |
| Phase 1 exact identities | DELIVERED | parity of `phi^2` in the `C`/`S` split | translation covariance, evenness in `g` and in `y`, shared kernel column; defects `< 1e-12` |
| LAW I: one-cell tightening | DELIVERED (**OUTCOME A**) | sharpened Cauchy-Schwarz against `sin^2` | `W >= -(1+m0) sigma^2`, `m0 = 0.2137172540`; uniform slack `x1.6478` over level 1; holds pointwise on a dense grid |
| LAW J: periodic word identity | DELIVERED | Poisson; the density vanishes at the dual points | `sum_k W = 2b/a^2 = 2.2959062623` exactly, independent of depth and ordinate; defect `< 6e-8` |
| Phase 2/3: two-gap coexistence penalty | **COLLAPSES (OUTCOME B)** | evenness of `W` in `g`; distinctness only | mirror pair at `s = 2g*` gives penalty `< 4e-13`; clusters give penalty/cell `-> 0` (`7e-5` at `n=10`, `delta=1e-3`) |
| Projective-consistency LP | NOT BUILT, deliberately | the value is zero on an explicit family | building it would rediscover the two constructions above at cost |
| Escaping family | **PINNED (OUTCOME C)** | the `+-g*(y)` cluster | a near-multiple zero at the kernel's optimal offset; controlled only by density/multiplicity, never by gap geometry — this is the level-3 kill control |
| Phase 4 lesions | HELD | see report's ledger | independent cells buy `0.3827`; conjugate-transpose geometry destroys every sign; broken spacing defect `3.5e-2`; independent *depths* recorded as a negative lesion |
| Phase 5 epsilon robustness | DELIVERED | LAW I, no coexistence input needed | no cell within `(1-m0) sigma^2(y)` of the level-1 floor; margin linear in `n` |
| Phase 6 decimal gate | **NOT PASSED** | both conditions fail | LAW I tightens the envelope, not a proportion; the coexistence route that could give an additive floor is the one that collapsed |

Disposition: **COEXISTENCE CLOSED, ENVELOPE TIGHTENED**. Level 3 should not
re-derive the coexistence route. It inherits two objects: LAW I's pointwise
gap-dependent form (the shape a telescoping potential consumes) and the
`+-g*` cluster as its mandatory kill control. No decimal search was run and
no proportion is claimed.

## Level 3 delivered: theta > 0 at the single-pair reduction (2026-08-11)

Full account: `LEVEL3-THETA-RECOVERY.md`; instrument `theta_recovery.py`;
controls `test_theta_recovery.py`. The milestone ("theta > 0, or an exact
reason theta must still be zero") is answered in the positive at the
single-pair reduction.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| LAW K: exact pair spectrum | DELIVERED | LAW D forces `u.u = 1` real, hence `x _|_ y` | spectrum `{2(1+s^2), -2s^2}` to 8 digits vs actual grid, `x.y ~ 1e-16`; retained slack exactly `8s^2 + 8s^4` |
| Three-zero lemma | DELIVERED (proved fragment) | LAW I + LAW K slack | margin `8 - 6(1+m0) = 0.7177 > 0`, placement- and depth-free, at theta = 1 |
| Phase 2: worst-case cancellation, one pair | MEASURED SAFE | dense-lattice + greedy families, depths 0.05-0.49 | worst net `+0.046` at every theta through 0.9; binding regime is the shallow limit where net ~ `(8 - D/s2) s2` |
| Scan power (theta = 1 fails) | HELD | dense regime | violated as it must be; damage 24s^2 beats slack 13s^2, internal mass 1274 drowns it below theta ~ 0.99 |
| Phase 3: dual-certificate seed | DELIVERED (shape) | `FT[omega^2] = (phi^2 * phi^2)`-shaped `>= 0` | packing form psd, `Lambda(theta,y)` finite for theta < 1; per-pair net `>= (8 - Lambda) s^2 + 8 s^4` |
| Phase 4: asymptotics | CLASSIFIED | scale-matching of both self-defeats | recovery range nu-free and sigma-free: `theta -> theta_0 > 0` at this reduction |
| Phase 5: extremal battery | HELD | all eight named classes | table in the report; every extremal accounted, none violates |
| Multi-pair slack partition | **NAMED GAP** | dipole worst `-2.84..-16.3` vs slacks | covered by factors 2.8-6.7, stacking positive; the joint partition is the missing estimate |
| Proved bound on `Lambda(theta)` | **NAMED GAP** | band-limited moment problem | measured sup is over two adversary families, not all configurations |
| Phase 6 decimal gate | **NOT ENTERED** | both named gaps open | no proportion computed; 0.672529 not revisited |

Disposition: **OUTCOME A AT THE SINGLE-PAIR REDUCTION, CANDIDATE**. The
adversary that once drove theta to zero is now twice self-defeating (depth
pays quartic slack, density pays quadratic packing), and both self-defeats
are scale-matched, which is the exact reason a positive theta exists here
and could not before levels 1-2. Promotion to the directive's full OUTCOME A
requires the two named gaps, in that order. No decimal search was run and no
proportion is claimed.

## Level 4 delivered: the counting dual, theta gap 1 closed (2026-08-11)

Full account: `LEVEL4-COUNTING-DUAL.md`; instrument `counting_bound.py`;
controls `test_counting_bound.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Configuration-free adversary cap | DELIVERED | chain counting theorem: same-cell pairs pay `K_delta`, adjacent pay `K_{2delta}`, exact tridiagonal DP | dominates every level-3 measured adversary, the level-2 cluster, and the LAW I single cell |
| One-sided continuum cells | DELIVERED | closed-form centres + Cauchy-Schwarz Lipschitz inflation in `g` and `y`; depth-scaled tail `psi_S ~ y` | lesion (inflation dropped) produces sup violations 0.115-0.725 at every probe depth |
| Secured positive theta | DELIVERED (double precision) | slack at the shallow lip vs damage at the deep lip, 60+ geometric depth cells | **theta* = 0.1 secured**; binding cells shallow with ~10% relative margin; theta = 0.2 fails at `y ~ 0.15-0.29` |
| Soundness incident | RECORDED | factor-2 leak in `f = -2W` caught by the projection control before shipping | the hierarchy's own level-4 row, now a permanent test |
| Theta gap to the measured 0.9 | QUANTIFIED | dropped non-adjacent payments + cell sups | cap within 1.4x of measured at `y = 0.1`, 2.7x at `y = 0.45`; the psd moment problem is the named sharpening |
| Gap 2 partition frame | MEASURED | halved slack per pair, shared terms split evenly | all measured worst dipoles fit; stacking positive; pair-pair cell bound at combined depths is the named remaining layer |
| Arb-enclosure pass | **NAMED GAP** | same finitely many cells, interval evaluation | binding margins ~10% relative, far above float noise, but graduation requires the enclosure pass |
| Phase 6 decimal gate | **NOT ENTERED** | multi-pair closure open | no proportion computed |

Disposition: **THETA POSITIVE, CONFIGURATION-FREE, AT THE SINGLE-PAIR
REDUCTION**. The first level-3 gap is closed modulo the enclosure pass; the
promotion order is now (i) enclosure hardening, (ii) the psd moment problem
for the theta gap, (iii) the multi-pair layer. No decimal search was run
and no proportion is claimed.

## Level 5 delivered: enclosure pass and the multi-pair energy (2026-08-11)

Full account: `LEVEL5-ENCLOSURE-AND-PAIRS.md`; instruments
`enclosure_pass.py` (gate 1) and `pair_energy.py` (gate 2); controls
`test_level5.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Gate 1: ball-arithmetic hardening | DELIVERED | acb/arb closed forms, exact rational `aL`, geometric series tails, directed endpoints, DP total inflated `1+1e-9` | full ladder at original resolution: hardened theta* = 0.1, worst margin +1.1e-5 at the shallow binding cells (~10% relative); probe cells +0.27 to +2.03 |
| The resolution scare | RECORDED | Lipschitz inflation scales with the sup-grid step | a 2x-coarser hardened grid FAILS by up to −3.0; original resolution passes — the economy was the failure, not the balls; kept as a negative control |
| LAW L: pair-pair cross via the single-pair kernel | DELIVERED (exact) | `u_r.u_s` and `u_r.conj(u_s)` are LAW D instances | `T(dt,y,y') = W(dt,y−y') + W(dt,y+y')`; defect 8.9e-16; difference layer nonnegative (min +6e-10) |
| Phase 2 energy algebra | DELIVERED | LAW K self terms + LAW L cross | decomposition matches brute force < 1e-9; sign-indefinite terms exactly identified |
| Phase 3 partition | MEASURED | proportional depth split from the sinh addition bound | eta(0.5) = 0.594, eta(1) = 0.487 < 1; shallow pairs charged asymptotically nothing |
| Phase 4 collective modes | HELD | six named configurations, both densities | all survive; worst cross/slack −0.876 > −1 |
| Dense pair lattice | **PROMOTED TO LEVEL-6 KILL CONTROL** | eta = 7.7 at nu_p = 2 while collective energy survives | pairwise charging is the weak link, exactly as per-cell reasoning was at level 4 |
| Phase 6: theta_full | **OUTCOME B — NOT CLAIMED** | combined budget cap/slack + eta > 1 at every depth | overdraw 0.151–0.387 quantified per depth; reversing estimates named: level-4 cap looseness (1.4–2.7x) or pair-split looseness (~2x); either suffices |
| Phase 7 decimal gate | **NOT ENTERED** | theta_full unproved | no proportion computed |

Disposition: **GATE 1 CLOSED, GATE 2 QUANTIFIED (OUTCOME B)**. The next
admissible tasks, in order: sharpen the level-4 shallow-cell caps (recover
half the dropped non-adjacent payments) or the pair split; then the
level-6 counting dual on the T kernel at mixed depths, against the dense
pair lattice kill control. No decimal search was run and no proportion is
claimed.

## Level 6a delivered: theta_full = 0.02, the overdraw closed (2026-08-11)

Full account: `LEVEL6A-THETA-FULL.md`; instrument `penta_bound.py`
(including the ball-hardened `EnclosedPenta`); controls
`test_penta_bound.py`. Both level-5 reversing estimates landed.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Lever 1: pentadiagonal counting dual | DELIVERED | three one-sided charge ranges inside omega's first positive stretch; exact (n_{j-1}, n_j)-state DP | reduces to the level-4 chain at K3 = 0 (< 1e-6); dominates every level-3/4/5 measured adversary; x1.26 gain at the deficit's home depth |
| Lever 2: optimal charge split | DELIVERED | min-max over free split weights, single-worst-depth adversary | eta drops 0.487 -> 0.303 max; eta(0.01) = 0.000 exactly (depth grading) |
| The optimiser bug | RECORDED | a sum over neighbour depths is a density-6nu_p adversary | the density budget makes the worst mix a single depth: max, not sum; the buggy version RAISED eta to 0.78 and was caught by comparison with the proportional split |
| theta_full | **DELIVERED: 0.02 > 0** | combined budget cap/slack + eta <= 1 per depth | float scan closes at 0.02 (worst 0.9991 at y = 0.45), opens at 0.03; hardened at all seven probe depths |
| Hardened caps | DELIVERED (probe grid) | EnclosedPenta: ball kernels + penta DP + 1e-9 inflation | cap fractions 0.571-0.696; binding margin 9e-4 of slack at y = 0.45, stated not rounded |
| Configuration-free pair layer | **NAMED (level 6b)** | counting dual on T at mixed depths | eta is measured on its adversary family; the dense pair lattice remains the kill control |
| Full-ladder hardened penta scan | NAMED (compute) | same machinery, longer run | probe grid spans the strip; shallow cells close at 0.571 with charge 0 |
| Phase 7 decimal gate | **NOT ENTERED** | 6b outstanding | no proportion computed |

Disposition: **THETA_FULL POSITIVE AT UNIT PAIR DENSITY — the milestone
equation holds within its stated labels.** Not optimised further, per the
operating rule; the value is that it is positive. Next, in order: the
level-6b T-kernel dual (configuration-free eta), the full-ladder hardened
scan, then Phase 7's reconnect — the gap floor against the error budget.
No decimal search was run and no proportion is claimed.

## Level 6b: the density question answered by mutual exclusion (2026-08-11)

Full account: `LEVEL6B-DENSITY.md`; instrument `pair_density.py`; controls
`test_pair_density.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Separable global budget | **BREAKS, recorded** | summed per-pair hardened caps are valid but simultaneous-worst-case | 24/68 configurations fail; worst −0.599 at nu_p = 1.5 deep — the level-5 lesson one level up |
| Compensation factor | MEASURED | greedy joint on-line adversary vs whole lattices | chi = 0.14–0.17 at nu 1, **0.016–0.018 at nu 2** — dense pair clusters are nearly immune to on-line attack |
| Joint budget across the density sweep | **HOLDS** | joint on-line profit + T-deficit vs total slack | worst margin **+0.0704** at the pinch (nu 1.25–1.5, deep); both flanks grow; theta_full = 0.02 corroborated at the joint level |
| Stacking floor | DELIVERED (one-sided) | grid + Lipschitz margin on T at |dt| <= delta_p | +2.78 at delta_p = 0.2 across all depth pairs; dies by 0.3 at the strip edge — the third self-defeat (depth, on-line density, pair density) |
| The mutual-exclusion structure | IDENTIFIED | band-overlap geometry: one pair's g* is a neighbour's positive region | the two adversaries cannot both show up; the trade-off curve is measured with its pinch |
| Joint cap dual | **NAMED THEOREM GAP** | level-4 machinery with the damage field summed over pair centres | would upper-bound the joint profit and make this verdict configuration-free; the greedy is a lower bound on the sup |
| Phase 7 decimal gate | **NOT ENTERED** | joint cap + full-ladder hardened scan outstanding | no proportion computed |

Disposition: **THE DENSITY LOOPHOLE CLOSES BY MUTUAL EXCLUSION, MEASURED.**
The chain now reads: theta = 0.1 hardened single-pair; theta_full = 0.02 at
the assembly; joint verdict positive across all tested densities with the
pinch mapped at +0.07. The remaining theorem objects before Phase 7, in
order: the joint cap dual, mixed-depth joint sweeps, the full-ladder
hardened scan. No decimal search was run and no proportion is claimed.

## Level 6c: LAW M and the Fourier bridge (2026-08-11)

Full account: docstring of `fourier_bridge.py` (instrument); controls
`test_fourier_bridge.py`. The joint cap dual's room is built.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| LAW M: mean positivity, depth-blind | DELIVERED (exact) | Parseval on the bilinear square: only v = 0 survives | `int W(., y) dg = 4 pi b/(a^2 L) = 1.8032005631` at every depth, defects at the quadrature floor; reproduces LAW J's constant to ten digits as its periodization |
| The Fourier bridge | DELIVERED (exact) | conjugate closure makes `sum e^{i z_j v}` square to a real modulus | `E_total = (1/(aL)^2) int_{-L}^{L} K(v) |F(v)|^2 dv`, `K = phi^2 * phi^2 >= 0`; worst relative defect 4e-12 over mixed configurations; the entire law hierarchy (D, K, L, R(P), W, T, census) is the term dictionary of this one identity |
| The joint problem restated | DELIVERED | `F = F_on + F_p`; pair slack = the `4 cosh^2(y v)` diagonal | the assembly is equivalent to a pointwise-in-v budget over one nonnegative kernel: on-line placement and pair density are two exponential sums against the same K |
| The pinch, spectrally | MEASURED | K-weighted pair fluctuation by frequency bin | the deficit lives at `|v| in [3, 7]` (peak -176), the LAW M mean at `v ~ 0` (+59), the cosh^2 diagonal at the band edge — the certificate's job is now a concrete 1-D spreading problem |
| The pointwise-in-v certificate | **THE NAMED OBJECT** | finitely many one-sided v-cells, same shape as every hardened object in the chain | delivering it makes the level-6b joint verdict configuration-free and reopens the road to Phase 7 |

Disposition: **THE JOINT CAP DUAL IS NOW A ONE-DIMENSIONAL PROBLEM.** The
mutual exclusion of level 6b is pointwise structure here: the cross term
that damages and the pair mass that pays live at the same frequency. Next:
the v-cell certificate; then mixed-depth sweeps and the full-ladder scan;
then Phase 7. No decimal search was run and no proportion is claimed.

## Level 7: the v-cell joint cap, the ladder correction, the first reading (2026-08-11)

Full account: `LEVEL7-VCELL.md`; instruments `v_certificate.py`,
`full_ladder_scan.py`, `reconnect.py`; controls `test_v_certificate.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| LAW N: windowed spectral floor | DELIVERED (exact) | phasor arguments within vS/2 of the window midpoint | `\|F_on(v)\| >= n cos(vS/2)` on `\|v\| <= pi/S`; forces `R >= kappa_00 n^2 - n` — the fourth self-defeat (spectral concentration) |
| The safe cell | DELIVERED (exact) | common-window phase coherence | cross integrand >= 0 on `\|v\| <= pi/(2S)`: the chi collapse of 6b, pointwise |
| Naive pointwise-in-v budget | **DEAD, recorded** | sub-critical lattice (spacing < 2 pi/L) empties the band | diagonal-subtracted integrand ~ -(1-theta) N mid-band, linear in N; the aliasing family again; the certificate survives it only through LAW N |
| The joint cap (on-line configuration-free) | DELIVERED, two routes; **ARB-HARDENED at the binding configurations** | direct: chain DP on the joint field at full charge (mean-value ball cells — the naive interval route amplifies radii ~1.8e5 and is recorded); v-route: three-zone split + taper + LAW M mean + LAW N leak cap + cell C-S | every swept configuration closes via the direct route (float: +6.5..+769); hardened (`hardened_direct.py`, budget directed down, cap directed up): former hole +17.33..+159.05, pinch +25.45, sparse +115.48, shallow sandwich +213.33 — worst hardened margin **+17.33** at nu 1.3; greedy 5.00, extended greedy 5.56; theta = 1 cap infinite |
| Mixed-depth joint sweeps (phase 2a) | DELIVERED | same instrument, battery shapes + shallow sandwich | all nu >= 1.5 shapes close (shallow sandwich +166.6); nu = 1.0 shapes covered separably (+0.53..+1.68) |
| **The seam** nu_p in [1.1, 1.4] deep | **CLOSED (direct route)** | the level-4 chain DP on the JOINT damage field `(-(sum_r 2W))_+` at full charge — 6b's original named object, tight only with the positive part of the joint sum | direct margins +15.7..+153.7 across the former hole; short spans close (span 4 at nu 1.3: +10.4); per-pair clipping (the separable ghost, field inflated ~10x) recorded as a permanent control; the v-route's [5, 7]-band looseness diagnosis kept as the record of why the spectral route needed the g-local shielding |
| Full-ladder hardened penta scan (phase 2b) | **RUN — 6a CORRECTED** | honest cell widths (1.05/1.012 ratios, 220 cells) + ten-point eta grid | 45 cells FAIL in two bands: shallow y in [0.010, 0.050] (worst −0.056; the eta(0.02) = 0.4066 spike the probe grid missed) and deep y in [0.419, 0.472] (worst −0.012; the 9e-4 probe margin does not survive honest widths); theta_full via the per-depth assembly is reduced to the passing bands; the shallow band closes at the joint level (shallow sandwich +166.6 / +22.9), the deep band coincides with the seam |
| The reconnect (phase 3) | **CANDIDATE ARITHMETIC RECORDED, GATE CLOSED** | one-sided ordered-gap floor x theta_full through the withdrawn chain's plumbing | c_u = 5.02e-6 one-sided (ladder-stable, CG calibration <= printed, lesion dies); candidate = 0.6725007037 + 2(0.02)(5.02e-6) = **0.6725009045** (+2.01e-7); named unproven steps: the transplant lemma, the arb pass, the seam, taper/truncation |
| Phase 7 decimal gate | **NOT ENTERED** | the seam + the assembly correction + measured-grade caps | no proportion is claimed to have moved |

Disposition: **THE JOINT VERDICT IS ON-LINE-CONFIGURATION-FREE ACROSS THE
ENTIRE SWEPT AXIS (measured grade), WITH TWO INDEPENDENT ROUTES AND THE
SEPARABLE CAPS AS CROSS-CHECKS.** The seam that stood open for one session
closed the moment the 6b-named direct object was built correctly (joint
positive part); the near-miss that had hidden it is a permanent control.
Level 6a's full-ladder extrapolation is corrected, not extended — the
probe grid missed both failing bands (the shallow eta spike and the deep
cells whose 9e-4 probe margins vanish at honest widths); that lesson
(resolution fragility, third occurrence) is now a permanent scan.  The
first reading of the decimal exists as candidate arithmetic only; with
the binding configurations now arb-hardened, the road to it runs through
pair-side placement freeness and the transplant lemma (plus the
mechanical full-sweep hardening), in that order. No proportion is
claimed.


## The transplant lemma dissected (2026-08-12, branch claude/transplant-lemma)

Full account: `TRANSPLANT-LEMMA.md`; instrument `transplant_lemma.py`;
controls `test_transplant_lemma.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Direct floor at the hunt kernel | **DEAD, measured** | omega(L=8) zeros arithmetic to 1e-4 — the floor's own lesion condition | bucket LP floor = 0.00e+00 exactly; ratios 1 : 2.0001 : 3.0003 |
| Direct floor at the Hann grid kernel | **DEAD EXACTLY** | 2 lambda_1 = lambda_4 (zeros 6pi, 8pi, 10pi, 12pi) | 2 lambda_1 - lambda_4 = -5e-13; LAW D there is alias-free (defect 3.7e-8) |
| The MT kernel identified | DELIVERED (exact) | g_MT = normalised (FT of cos(sqrt2 t) width-1 box)^2 | identity defect 2.5e-16; the sqrt2 modulation is the unique non-degeneracy of the three |
| The lemma decomposed | DELIVERED | no kernel comparison needed — the chain moves to the floor's own kernel | T1 chain re-run at the MT window (alias defect 0.53% to carry one-sidedly), T2 census (measured consistent: damage band at 1.10-1.12 mean gaps ~ lambda_1), T3 plumbing (calibrated), T4 taper/truncation, T5 the upstream Lean window pin (external) |
| MT-window entry card | MEASURED | Phi2_mt closed form | minW/sigma^2 = -0.40..-0.43 vs the hunt's -(1+m0) = -1.21: 3x friendlier; sigma^2(0.49) = 0.0175 |
| Candidate status | UNCHANGED | all of the above | the reading 0.6725009045 stays a candidate; the "incomparable kernels" failure mode is eliminated, the "floor dies at the paper's kernel" risk is now a measured fact with the MT modulation as the unique escape |

Disposition: **THE TRANSPLANT LEMMA IS NOT AN INEQUALITY — IT IS A
RE-RUN.** The critical path to the decimal is now: T1 (the retention
chain at the MT window, compute with existing machinery), then T5 (pin
the upstream zero-side window in the external Lean file). No proportion
is claimed.


## T1 first session: the MT-window re-run (2026-08-12, branch claude/transplant-lemma)

Full account: `TRANSPLANT-LEMMA.md` (T1 section); instrument
`mt_chain.py`; controls in `test_transplant_lemma.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| LAW D at MT | **EXACT — alias claim corrected** | width-1 support cannot reach the +-2pi combs (Poisson) | truncation control: defect scales 1/K (3.8e-3 -> 6.0e-5 over K 80 -> 5120) |
| LAW K at MT | HOLDS | same algebra, LAW D exact | grid pair-block spectrum matches {2(1+s2), -2s2} at y = 0.45 |
| LAW-I-style envelope | DELIVERED (one-sided) | fine grid + Lipschitz + Im-majorant tail | W >= -0.54 sigma^2 (y = 0.49), -0.70 (y = 0.3); hunt window: -1.21 |
| Single-pair trade at MT | **MEASURED HEALTHY** | explicit band-riding adversary | D = 0.030 vs slack 0.142 at y = 0.49, 4.7x inside at FULL charge (c = 1, theta = 0); only the +-1.10-mean-gap band pair is ever profitable. (A first write-up said "even at theta = 1" — false: at theta = 1 the charge vanishes and stacking is unbounded. Caught by the adversary hunt; kept in the record.) |
| Level-4 chain DP at MT | **DOES NOT TRANSPLANT, pinned** | damage bands at kernel zeros persist ~1/g^2; interval charge floors straddle the same zeros | min omega^2 over [d, 3d] = 0.182/0.023/0.000; true point repulsion at band separations 0.017/0.011/0.001 — the DP grants the far bands free |
| The named T1 theorem object | NAMED | band-lattice counting dual with point-separation charges | charge the k-th band pair its actual omega^2 at the near-arithmetic separation, not an interval minimum |
| Candidate reading | RE-FOUNDED, value unchanged | hunt-kernel floor = 0 (finding 1) removes the old support | now rests on MT retention (measured) + one-sided g-floor + calibrated plumbing + census + T5; no proportion claimed |

Disposition: **THE LAWS TRANSPLANT; THE COUNTING DUAL DOES NOT — AND THE
REASON IS THE SAME ARITHMETIC THAT MAKES THE FLOOR LIVE.** The sqrt2
modulation that gives the CG mechanism its non-arithmetic zeros also
parks the damage bands on the repulsion nulls, so interval-charge
counting is structurally blind here. The trade itself is healthy by 4.7x
at the explicit adversary; making that configuration-free needs the
band-lattice dual. No proportion is claimed.


## T1 second session: the band-lattice dual (2026-08-12, branch claude/transplant-lemma)

Full account: `TRANSPLANT-LEMMA.md` (T1 second session); instruments
`band_dual.py`, `mt_pairs.py`, `mt_adversary.py`; controls in
`test_transplant_lemma.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| The first session's named obstruction | **WITHDRAWN** | omega^2 is a square, so cross-band charges drop one-sidedly | the band/kernel-zero coincidence was never load-bearing; the 0.44 cap was mostly a blanket-margin artifact (~800 uniform cells x 1.7e-3), the third occurrence of that failure mode in this hunt |
| The band partition is complete | DELIVERED (one-sided) | a band is exactly where q = Re^2 - Im^2 < 0; an unresolved dip needs an interior minimum | q / ((1/8)\|q''\| step^2) >= 326 (y = 0.02) to 7347 (y = 0.49) off the widened bands, so the off-band allowance is exactly 0 |
| Band structure | MEASURED | closed-form Phi2, Phi2', Phi2'' | 63 bands in (0, 400]; width 0.970 grid units; first at 1.106 mean gaps; maxima decay 4.93/2.33/1.80/1.57 vs the 1/g^2 law |
| The free-band ratio | **MEASURED 0.34-0.36, depth-flat** | band sum + closed-form tail | granting every band maximum at zero internal cost takes only ~a third of the slack, at every depth from 0.02 to 0.49 |
| Secured single-pair theta at MT | **DELIVERED: theta* = 0.995** | band dual, one-sided | hunt window secured 0.1; the binding constraint is same-band multiplicity alone, not damage |
| Projection + kill controls | HELD | measured band-riding adversary; theta = 1 | 0.0102 <= 0.0179 (y = 0.3), 0.0298 <= 0.0493 (y = 0.49); cap(theta = 1) infinite |
| Pair layer at MT | MEASURED, friendlier | LAW L (defect pure 1/K truncation, 3 lesions reject) | stacking floor 0.979 mean gaps (vs 0.255); worst dipole cover 8.84-9.91 (vs 2.8-6.7); **no dense-deep pinch**; single soft window nu_p ~ 0.97, T/slack -0.381 |
| The joint cap at MT | **NOT RUN** | the level-7 direct dual rebuilt on the band partition | named; until it runs, theta_full^MT is unknown and no new reading is computed |
| Candidate reading | UNCHANGED | the joint layer is what the composition needs | 0.6725009045 stands; conditional arithmetic at theta_full^MT = 0.2 / 0.995 would give +2.0e-6 / +1.0e-5, explicitly not readings |

Disposition: **THE RETENTION COEFFICIENT AT THE FLOOR'S OWN KERNEL IS
FIFTY TIMES THE HUNT WINDOW'S, AT THE SINGLE-PAIR REDUCTION.** The
window that makes the Cheer-Goldston mechanism live also makes the
retention trade easy: its damage is confined to narrow bands carrying a
third of the slack in total, and its pair layer's stacking floor nearly
fills the mean gap. The next object is the joint cap on the band
partition. No proportion is claimed to have moved.


## T1 third session: the joint cap and the coherent composition (2026-08-12)

Full account: `TRANSPLANT-LEMMA.md` (T1 third session); instruments
`mt_joint.py`, `mt_adversary.py`; controls in `test_transplant_lemma.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Joint cap at MT (theta_full's object) | **DELIVERED** | level-7 direct route on the band partition; joint positive part; cross-cell charges dropped; partition completeness Q-test | closes every swept configuration at theta = 0.995; worst case is the ISOLATED pair (budget 0.1423, cap 0.0653, margin +0.0771) |
| Density at MT | **DEFENCE, not danger** | LAW M's positive mean summed over pairs | at nu_p >= ~1 the joint field has NO positive region: max over a 200-unit halo is -7.5e-4 vs a single pair's +1.5e-2; cap is exactly 0 for every nu_p >= 1.25 row |
| theta_full at MT | **= theta* = 0.995** | the joint layer imposes no loss | inverted ordering vs the hunt window, where the joint layer cost 5x (0.1 -> 0.02) and needed a mutual-exclusion argument for a dense-deep pinch |
| Independent adversary hunt | HELD | exhaustive n <= 6 with gradients, band lattices, multiplicity, phase/depth/theta sweeps | no configuration beats the two-zero band pair; charge-free envelope 0.325-0.335 of slack (independent of the dual's one-sided 0.34-0.36); measured largest safe theta 0.9990 at y = 0.49 |
| **theta\* sandwiched** | MEASURED | one-sided dual vs measured adversary | **0.995 <= theta\* <= 0.999**: the configuration-free bound is within 0.4% of the measured truth |
| Convention error | **CORRECTED, recorded** | at theta = 1 the charge vanishes and stacking is unbounded | an earlier line claimed the trade held "even at theta = 1"; false as written - the figure was the full-charge case (c = 1, theta = 0). Both duals correctly report cap(theta = 1) = infinity |
| Window coherence of the composition | **REPAIRED** | g_MT is exactly the MT window's kernel (defect 2.5e-16) | floor and retention now live on ONE kernel; the previous pairing drew retention from a window whose own floor is 0 (it sits on the floor's lesion) |
| Candidate reading | **RECOMPUTED, still a candidate** | window-coherent composition | 0.6725007037 + 2(0.995)(5.0212e-6) = **0.6725106958**, i.e. +9.99e-6 vs the hunt-window composition's +2.01e-7 |
| The five open steps | UNCHANGED | plumbing linearity, census conversion, taper/truncation one-sided, the arb pass, T5 (external Lean window pin) | any one alone withholds the word improvement; no proportion is claimed |

Disposition: **THE JOINT LAYER IS FREE AT THE FLOOR'S OWN KERNEL, AND THE
COMPOSITION IS COHERENT FOR THE FIRST TIME.** The window that makes the
Cheer-Goldston mechanism live also makes density a defence rather than a
danger: dense pair sets leave the on-line adversary no positive field to
stand on. The candidate reading is recomputed at 0.6725106958 and remains
a candidate behind five named steps, one of them external. No proportion
is claimed to have moved.


## T1 fourth session: arb pass + the kernel-pairing error (2026-08-12)

Instruments: `hardened_band.py`, `kernel_pairing.py`; controls in
`test_transplant_lemma.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Arb pass over the single-pair band dual | **DELIVERED** | interval-argument acb enclosures; no Lipschitz margin granted anywhere | amplification 1.06 -> 0.0024 over g = 1.1 -> 300 (hunt window: ~1.8e5), so the MT form is interval-friendly; hardened margins +1.53e-4 (y=0.02) to +9.32e-2 (y=0.49) at theta = 0.99 |
| Hardened vs float | **TIGHTER, not looser** | the cover removes the float pass's blanket slope margins | hardened cap below float cap at every depth; largest surviving theta 0.9988 with an identical float boundary (clears .9988, fails .9989) |
| No-missed-band under hardening | **STRONGER FORM** | continuum cover, not grid inference | every unflagged cell has f <= 0 throughout the cell; the curvature test reproduced with directed endpoints clears at 8.1-118.9 |
| **Kernel-pairing error in our own composition** | **FOUND AND CORRECTED** | theta_full retains sum omega^2 (omega = FT(phi^2) normalised); c_u is computed in g = (FT phi)^2 | (FT phi^2) != (FT phi)^2: ratio 1.02/1.12/1.70/0.66 at u = 0.3/0.6/0.9/1.5, zeros differ 6% (1.1208 vs 1.0573). The product mixed two kernels, undeclared |
| Own-kernel floor | DELIVERED (one-sided, ladder-stable) | omega^2 zeros non-arithmetic (1, 1.839, 2.713) so the floor is live | c_u(omega^2) = 4.021769e-06 vs c_u(g) = 5.021179e-06, ratio 0.801; both stable across n = 600k/1.2M/2.4M; lambda_2 lesion dies on both |
| Reading of record | **REVISED DOWNWARD** | conservative pairing | **0.6725087070** (+8.00e-6), replacing 0.6725106958 |
| Residual T3 | SHARPENED | which pairing the upstream count requires | now a precise question about the paper's Theorem D derivation - is its discarded mass an omega^2 sum or a g sum? - not a vague plumbing worry |

Disposition: **THE HARDENING COSTS NOTHING AND THE COMPOSITION COST A
KERNEL.** The arb pass moves theta by less than a scan step (0.9988), but
auditing what the symbols denote found the reading pairing two different
kernels; the conservative repairing lowers it to 0.6725087070. Still a
candidate: T3 (now sharp), the census conversion, taper/truncation, and
T5 (external) remain. No proportion is claimed to have moved.


## Confidence audit (2026-08-12)

| Claim | Grade | What it rests on |
|---|---|---|
| MT-window retention: theta* in [0.995, 0.999], arb-hardened 0.9988 | **strong** | one-sided dual + independent adversary hunt + ball arithmetic, three routes agreeing |
| LAW D / LAW K / band structure at MT | **strong** | exact identities, truncation-scaling controls, independent grid routes |
| Joint layer free at MT | **good** | configuration-free on the on-line side; pair side is families + stacking floor |
| omega^2 != g, floors differ by 0.801 | **strong** | direct computation, ladder-stable, lesions die |
| The paper's window is MT | **one number** | the pinned constant IS the MT constant to 2e-11 (rounding) — real evidence, and the only evidence |
| **theta enters `H + 2 theta c_u` multiplicatively** | **NOT ESTABLISHED** | the formula's coefficient and linearity are calibrated against CG (conditional, Montgomery framework); the multiplicative entry of a Frobenius-framework retention is derived nowhere. **If false, the reading is vacuous** |
| T5 (upstream Lean window pin) | **open, external** | outside this session |

Defects of our own found and corrected in this session: the
blanket-margin artifact (x3, three guises), a theta = 1 convention
mislabel, the kernel-pairing mix, a propagated stale comment. All found
by controls or independent routes, none by inspection.


## T3/T5 paper session (2026-08-12)

Instrument: `paper_pin.py`; the paper itself, SHA-256
6792988e6cd0e17690621ce898abd5d534f98407741bc7cb14bbe7d07c77d72f,
section 7.1 + Theorem D proof (pp. 20-21) and the (Z)(P)(L) skeleton
(pp. 4-5).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| T5: upstream window pin | **ANSWERED FROM SOURCE** | "Writing phi^2(u) = v(u/L)"; Theorem D takes phi = cos(sqrt2 u/l)^(1/2) box, ramp-mollified, rho = 1 | functional (7.3) implemented once reproduces MT constant at v* (defect 6.8e-9, ladder-shrinking), Montgomery's 2/3 at v = 1 |
| T3 kernel half | **ANSWERED FROM SOURCE** | K = |vhat|^2 in (7.3); LAW D weight = FT(phi^2)^2; for the paper's window FT(phi^2) = v*-transform | omega^2 = g to 2.5e-16 under the paper's window; gap >= 7% under the T1 window — the ambiguity belonged to the wrong window |
| T1 window class membership | **STRICTLY WEAKER** | v-profile cos^2 vs cos | H(cos^2) = 0.6673241, 5.2e-3 below the optimum; every T1 field was built at this member |
| Burden (a): chain re-run at Phi2 = FT(cos box) | NAMED, OPEN | one kernel swap in mt_chain/band_dual/mt_joint | theta* = 0.995 is currently a measurement about a neighbouring window |
| Burden (b): ramp mollification | NAMED, OPEN | paper's window is ramped; theta* was at the pure box | paper states O(log l / l) window-constant corrections |
| Burden (c): multiplicative theta | UNCHANGED, LOAD-BEARING | "(2 tr P - r) + (4 tr Q - 4b) plays the role that sum (2m-1) plays" — (L) consumes the Frobenius mass whole | derived nowhere; if false the reading is vacuous |
| Reading of record | UNCHANGED | conservative pairing until burden (a) lands | **0.6725087070**, a candidate; correctly-paired figure 0.6725106958 waits on (a) |
| Stale comment digits in cg_transplant.py | CORRECTED (again, this copy) | comments printed 1.3274992766 / 0.6725007233 | now 1.3274992963 / 0.6725007036; value itself was always right and is pinned by test |

Disposition: **BOTH QUESTIONS THE AUDIT LEFT OPEN ARE ANSWERED, AND THE
ANSWER INDICTS OUR OWN WINDOW.** The paper's window puts the cos profile
on phi squared; ours put it on phi. That dissolves the kernel ambiguity
(in favour of g) and simultaneously reveals the T1 field was built at a
strictly weaker class member. Next build: the kernel swap (burden (a)).
No proportion is claimed to have moved.


## Burden (a): chain re-run at the paper field (2026-08-12)

Instruments: `paper_chain.py`, `test_paper_chain.py` (11 tests).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Field swap Phi2 -> FT(cos box) | **DELIVERED** | closed-form s, s', s'' with series joins (mismatch <= 5e-9); kernel identity (phihat/A)^2 = g to 2.5e-16 | band lattice = MT-kernel zeros, 63 bands in (0, 400], non-arithmetic |
| theta* at the paper field | **0.995** | one-sided band dual, no blanket margins (off-band allowance exactly 0) | caps 0.000111/0.002636/0.023905/0.091090 vs slacks 0.000248/0.006208/0.056436/0.153435 at y = 0.02/0.1/0.3/0.49; 0.999 fails at y = 0.49 |
| Completeness | CLEAR | q vs curvature, local closed-form d2 | ratios 328/1618/4670/7154 |
| Convention control | PASS | cap(theta = 1) must diverge | inf, as required |
| Dual dominates primal | PASS | greedy adversary at theta* | 0.02102 <= 0.02391 (y=0.3), 0.05960 <= 0.09109 (y=0.49) |
| Distinctness | PASS | paper field != T1 field at first band centre by > 1e-3 | not a re-run of the same numbers |
| Prompt-series defect | CAUGHT BY CONTROL | s' cubic coefficient: prompt said u^3/1920, sympy pins u^3/960 | derivative pins 4.8e-10 / 6.2e-8 after fix |
| Reading of record | **MOVES to 0.6725106958** | pairing settled (g) + theta at the correct field | still a candidate: ramp (b) and multiplicative theta (c) remain |

Disposition: **THE RETENTION SURVIVES THE WINDOW CORRECTION.** Same
theta* grid point, larger margins. Burdens (b) and (c) unchanged; (c)
is still the load-bearing unknown. No proportion is claimed to have
moved.


## Burden (c) first half + burden (a) hardening (2026-08-12)

Instruments: `t3_composition_skeleton.lean` (Aristotle service, project
2e5d794d; sorry-free, standard axioms only), `hardened_paper.py`,
`test_hardened_paper.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Composition skeleton s >= 2N - \|\|P+Q\|\|_F^2 + D | **KERNEL-CHECKED** (service-side) | exact identities \|\|P\|\|_F^2 = sum m_i^2 + R, 2m - m^2 <= 1 for positive integers | Lean 4 + Mathlib, no sorry, axioms propext/Classical.choice/Quot.sound; artifact in-tree with #print axioms |
| Conditional composition s >= (2-C)N + theta*R0 | **KERNEL-CHECKED** (service-side) | \|\|P+Q\|\|_F^2 <= C*N and D >= theta*R0 | result2_conditional, same file |
| Unit-conversion seam (i) | NAMED, OPEN | paper's (4.4) units vs chain's LAW D normalisation | carries half the remaining weight |
| Identification seam (ii): the dual's cap IS D >= theta*R0 | NAMED, OPEN | 2 tr(PQ) with transpose pair blocks = the W-field | test_mt_W_normalisation pins a piece at the T1 field; paper-field version open |
| Ball-arithmetic pass at the paper field | **DELIVERED** | interval-argument acb, both sides enclosed, no blanket margins | theta = 0.995 survives; 0.9988 fails at y=0.49 (multiplicity threshold 0.989249); hardened tighter than float everywhere (0.94-0.996) |
| Singular-branch series | PINNED | explicit remainder bounds; mpmath oracle at dps 40 + 45 guard digits | 27 checks, reference inside every ball; the oracle trap (24-digit cancellation in s'' near u=1e-8) recorded |
| Cross-backend spot check | PASS | flint midpoints vs mpmath | defects 1.5e-39..1.9e-39, all inside radii |
| Inherited-prose defect (T1 multiplicity print) | FOUND, RECORDED | direction of the profitable side | T1 files untouched; correct direction stated in hardened_paper.py |

Disposition: **THE FORMULA IS NOW THEOREM-SHAPED AND THE FIELD IS
BALL-AGREED.** What remains of burden (c) is two named seams, not an
analogy. Joint layer at the paper field still running; ramp (b) still
open. No proportion is claimed to have moved.


## Joint layer at the paper field (2026-08-12)

Instruments: `paper_joint.py`, `test_paper_joint.py` (10 tests).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| theta_full at the paper field | **0.995** | joint band dual over configuration families; positive part of the JOINT field only | 0.999 fails at lattice nu=0.5 y=0.49 (-1.29 rel); binding config at 0.995 is the same lattice (+0.33 rel) |
| Soft window re-derived | DELIVERED | this field's own band geometry, not the T1 copy | nu_p = 0.9576 (first band centre 1.0443 mean gaps); at it only 4 residual band cells survive shielding |
| Dense-lattice shielding | PASS | joint clipping order | nu >= 1.25 caps exactly 0 with positive budget; per-pair clipping strictly larger (the control has power) |
| Completeness on the joint field | CLEAR | local curvature, no blankets | ratios 166-3673, off-band allowance exactly 0; the non-clear branch exercised at a coarse step reports a positive allowance |
| No band merging | PASS | widest joint band 0.968 grid units | vs first kernel zero 6.643 |
| Cap divergence at theta = 1 | PASS | convention control | inf on isolated and dipole |
| Greedy dominated | PASS | dual dominates primal at 0.995 | 0.0476<=0.0947, 0.1077<=0.1901, 0.0587<=0.1344 |
| Distinctness vs T1 joint | PASS | matched config, theta 0.9 | caps 26% apart, budgets 7.5% apart |

Disposition: **THE JOINT LAYER HOLDS AT THE PAPER WINDOW.** theta_full
= 0.995 across all swept families, float grade, single-pair skeleton
ball-agreed. Open: ramp (b), the two (c) seams, optional joint
hardening. No proportion is claimed to have moved.


## Burden (b): ramp mollification (2026-08-12)

Instruments: `ramped_field.py`, `test_ramped_field.py` (14 tests).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| theta* under the paper's ramp | **0.995 AT EVERY eps** (1/8, 1/16, 1/32) | C^3 degree-7 smoothstep taper squared on phi^2; band lattice from each field's own zeros | caps/slacks converge monotonically to box values; 0.999 fails at every eps at y=0.49 |
| Field construction | PINNED | mpmath quadrature, no global state leak | ladder worst 2.9e-14, dps-30 oracle worst 8.9e-16; one-sided pins added to every margin |
| eps -> 0 convergence | MEASURED O(eps) | taper differs from 1 on a 2*eps fraction | constant 0.877 (ratio 0.9997 across eps = 1e-3 -> 1e-4) vs derived bound 1.226 |
| Completeness at every (eps, y) | CLEAR | local curvature, zero off-band allowance | ratios 324-7495 |
| Convention + domination controls | PASS | cap(theta=1) = inf at every eps; paper_chain greedy reused unchanged | adversary inside cap at all spot depths |
| Psi shape dependence | MEASURED (one point) | degree-9 vs degree-7 smoothstep | binding cap moves 1.6%, verdicts unchanged; caveat recorded, not a supremum |
| Thinnest margin | NOTED | y=0.02 at eps=1/8 | +1.05e-4 (~57% of the box margin) |

Disposition: **THE RAMP COSTS MARGIN, NOT THE VERDICT.** Burdens (a)
and (b) are discharged; the candidate 0.6725106958 rests on the two
burden-(c) seams alone (units / identification). No proportion is
claimed to have moved.


## Seam (i) core: LAW D kernel-checked (2026-08-12)

Instrument: `law_d_incidence.lean` (Aristotle service, project
c6519a2a; sorry-free, standard axioms only).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Grid incidence = 2 pi FT(phi^2) | **KERNEL-CHECKED** (service-side) | phi measurable, bounded, supp in [-1/2,1/2], EVEN | tsum_phihat_mul_phihat_even; summability included (hasSum form) |
| Our three windows admissible | **KERNEL-CHECKED** (service-side) | edge jumps allowed; continuity NOT assumed | tsum_phihat_windowA / windowB / of_continuous (ramps covered, boundedness derived) |
| Our submission's phi^2 form without evenness | **FALSE — CAUGHT BY THE PROVER** | indicator of (0, 1/2]: grid sum 0 vs pi | grid_incidence_needs_even, in the same file |
| Hypothesis-free form | KERNEL-CHECKED | autocorrelation RHS 2 pi int phi(u) phi(-u) e^{i(x-y)u} | hasSum_phihat_mul_phihat |
| Method | Parseval on R/2piZ, not Poisson | support width 1 < 2 pi; polarised Parseval built from fourierBasis | bounded measurable suffices; no BV/decay needed |
| Remaining of seam (i) | BOOKKEEPING | aL^2 units of (4.4) vs 2 pi Phi2(0); finite-truncation accounting (measured ~1/K) | named, open |
| Seam (ii) | UNCHANGED | dual's cap as D >= theta*R0 | next piece of work |

Disposition: **THE UNITS SEAM'S ANALYTIC CORE IS CLOSED, AND THE PROVER
CAUGHT A MISSING HYPOTHESIS IN OUR SUBMISSION.** The evenness
counterexample joins the session's defect list. Seam (ii) remains. No
proportion is claimed to have moved.


## Seam (ii): the identification (2026-08-12)

Instrument: `identification_seam.py`; 4 controls in
`test_transplant_lemma.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Gram = omega under LAW D normalisation | MEASURED | unit norms 2 pi A; truncation ~1/K | defect 4.4e-4 at K=1200, ladder decreasing |
| u^T Q_p u = W (the dual bounds -2 tr PQ) | MEASURED | transpose pair convention | worst defect 5.4e-5 |
| Pair surplus = slack(y) | MEASURED | tr Q_p = 2, b_p = 1 measured | defects 2e-6..6e-4 across depths |
| Pair-pair cross terms | **NEGATIVE, COVERED** | 4-per-pair cushion (4 tr Q_p - 4 b_p) | cross -0.066..-0.342 vs cushion 4p; recorded |
| End-to-end gross: D >= theta*R | HOLDS (all 11 configs) | direct matrix assembly | including field-derived adversarial placements |
| End-to-end sharp: damage <= (1-theta)R + slack | HOLDS (all 11) | the dual's statement on explicit matrices | worst adversarial damage +0.0796 < hardened cap 0.0907 < budget 0.1534 |
| First-run quadrature defect | CAUGHT, KEPT AS CONTROL | fixed GL order fails beyond \|x\| ~ 150 | ladder ran backwards; sized rule restores 1/K |
| Remaining | BOOKKEEPING-GRADE | R >= R0 census (nu at the paper window), (P)-side o(N) units, T4 | named, open |

Disposition: **THE DICTIONARY IS MEASURED AND THE LAST HOLE-CANDIDATE
(NEGATIVE CROSS TERMS) IS FOUND AND COVERED.** The dual's verdict now
IS the corollary's hypothesis over the swept scope. Candidate
unchanged at 0.6725106958. No proportion is claimed to have moved.


## Closing bookkeeping (2026-08-12)

Instrument: `closing_bookkeeping.py`; 4 controls in
`test_transplant_lemma.py`.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Census: floor monotone in nu | MEASURED | LP at fixed edges | 0 -> 1.26e-4 over nu = 0.5 -> 0.83625; under-reporting nu is safe |
| Census: nu input | CITED (Theorem B) + one-sided | H_pinned lower-bounds the distinct density | monotonicity makes the citation's direction safe |
| Grade note | RECORDED | hardened vs discovery table | reading's 5.02e-6 < discovery ~8e-6: conservative side |
| Units: R/N -> lattice reference | MEASURED | reference 0.00612719 | defects 4e-4/1.5e-5/2.7e-4 at N=9/17/33; damage N-stable |
| T4: beyond-window tail | COVERED | real (G,2G] bands vs closed-form allowance | 5.0e-5 vs 6.6e-4 (y=0.3); 1.3e-4 vs 1.8e-3 (y=0.49) |
| T4: assembly truncation direction | **FIRST-DRAFT CLAIM REFUTED BY OWN CONTROL** | truncated norms inflate R; assembly is not a one-sided device | R(K) decreasing 0.0279/0.0258/0.0249; reading unaffected (exact-kernel floor) |
| Boundary of remit | STATED | (P)-side, Theorem B, D0 edges are the paper's theorems | cited, never re-measured |

Disposition: **THE BOOKKEEPING IS CLOSED AND THE BOUNDARY IS DRAWN.**
Candidate 0.6725106958 with every in-remit step measured, hardened, or
kernel-checked; session defect count nine, all caught by controls or
independent routes. No proportion is claimed to have moved; the ledger
is the deliverable.


## Formal chain, track 1: the LP floor as a rational certificate (2026-08-12)

Instrument: `lp_certificate.py` (agent build, coordinator-reviewed and
re-run).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Rational dual certificate for the census LP | **EXACT IN Q** | dual feasibility checked in fractions arithmetic, no floats | F_rat = 5.021172019e-6, gap to the float floor -7e-12; all 8 dual inequalities exact; strong-duality control 1.9e-20 |
| One-sided direction | STATED AND SAFE | cost lower bounds can only lower a minimization | the four kernel values enter as LOWER bounds r_a, r_b, r_h, r_j |
| The four trig leaves | NUMERIC (dps 40 + slope margin), STATED AS THE LEAN LEMMAS | margins 9.4e-8 / 1.05e-11 / 4.1e-6 / 4.5e-6 | r_b is the tight one; the Aristotle submission carries them as Theorems B1-B4 |
| Candidate under the rational floor | UNCHANGED at printed precision | H + 2*0.995*F_rat | 0.6725106958 (down 1.4e-11) |

Disposition: **THE FLOOR IS NOW ARITHMETIC PLUS FOUR ONE-VARIABLE TRIG
LEMMAS.** Submitted to the theorem-proving service. No proportion is
claimed to have moved.


## Formal chain, track 2: the retention as a rational certificate (2026-08-12)

Instruments: `band_certificate.py`, `data_band_certificate.json` (agent
build, coordinator re-checked in a fresh process).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| theta = 995/1000 in pure rational arithmetic | **CLOSES, all four depths** | checker imports fractions + math.isqrt only ("numerical modules imported by this path: none"); sin/cos by Taylor with Lagrange remainders, sqrt2 by isqrt, pi by Machin enclosure | margins +1.28e-4 / +3.16e-3 / +2.77e-2 / +4.49e-2, exact fractions recorded |
| Cover completeness as a cover property | STRUCTURAL | 15 band intervals + negativity cells tile (0, 98] exactly in Q | tiling checked in Q; ~840-1273 cells per depth |
| One-sided directions | STATED PER FIELD | F up, K down, slack down, tail up, cap up | square completion monotone-safe in one-sided F/K |
| Where it stops | HONEST BOUNDARY | closes at 995, 996, 997; fails at 998/1000 | worst -2.58e-2 at y = 49/100 (multiplicity branch), consistent with the hardened scan's 0.9988 failure |
| Cross-checks | PASS | dps-40 midpoints inside every sampled enclosure; rational cells intersect the acb balls; planted corruptions rejected | near-arb tightness (widths 1.6e-4 vs 1.2e-4 at band 1) |
| Lean readiness | DRAFTED | LawN256 pattern, leaves L1-L6 | submission prepared |

Disposition: **THE RETENTION IS NOW ~1000 RATIONAL INEQUALITIES PER
DEPTH PLUS TAYLOR-ENCLOSURE TRIG LEAVES.** Together with track 1 the
two measured pillars of the candidate are certificate-shaped. No
proportion is claimed to have moved.


## Audit follow-through: the co-optimizing adversary and two instrument repairs (2026-08-12)

Instruments: `coopt_adversary.py` (new), `test_coopt_adversary.py` (8
tests), repairs in `paper_chain.py` and `identification_seam.py`.
Executes the trajectory set by `EXTERNAL-AUDIT-2026-08-12.md`: attack
the untested corner before building the depth cover.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Co-optimized attack: pairs AND zeros chosen together | **NO VIOLATION, 57 restarts** | closed-form (*) objective (W, T, omega2, slack), Nelder-Mead over positions, depths, multiplicities 1-3; every search path point evaluated | 0 of 57 reach V > 0; top-3 verified on explicit K=1200 matrices, defect 7.5e-7 |
| The trivial supremum is decoupling | RECORDED | sup V = 0 approached by walking zeros away and shrinking depth | the difference objective says nothing about engaged attacks; hence the ratio hunt |
| Engaged worst case under co-design | **0.5754 of budget** | ratio objective (damage - cross)/((1-theta)R + slack) on structured seeds | worse than every swept family (joint sweeps ~0.49) -- the audit's untested corner was real -- and 1.7x short of violation (> 1) |
| Self-stacking charge | MODELED AND PINNED | band dual charges m(m-1)K, so R includes m_i(m_i-1) omega^2(0); GridAssembly verification expands multiplicities into coincident points | test pins the +2 for an m=2 point, closed form and matrix |
| Dictionary control | PASS | budget_terms vs GridAssembly on the battery ADV rows | worst defect 1.2e-4 (truncation grade) |
| Lesion: slack deleted from budget | FIRES | battery worst row must violate a slackless budget | V = +0.0598 > 0 |
| Convention: theta = 1 | PASS | uncharged stacking profit must grow linearly in m and end positive | -0.133 / -0.074 / +0.166 at m = 1/4/16 |
| Shallow-depth false negative (audit finding B) | **REPAIRED** | `PaperBandDual.for_depth` ties step to y/40; `cap()` returns undecided (inf), never 0, when bands are empty but `no_missed_band` is not clear | at y = 5e-4 the ratio moves 1.436 -> 0.5088; at y = 1e-4 the old silent false PASS now reports undecided, and for_depth resolves 15 bands with ratio 0.5088 |
| Battery omission (audit finding A) | **REPAIRED** | cross term on the LEFT of the sharp row; three new rows with zeros at JOINT minima of multi-pair fields | all 14 rows hold; worst joint-minima row at (damage - cross)/budget ~ 0.62, coherent with the co-opt hunt's 0.5754 |

Disposition: **THE CO-DESIGNED CORNER IS MEASURED AND IT HOLDS, WITH A
THINNER MARGIN THAN ANY SWEPT FAMILY -- WHICH IS WHY IT NEEDED
MEASURING.** This is a search, not a proof: the open obligation named
by the audit (retention uniform in depth and over arbitrary pair sets)
is unchanged, and the engaged ratio 0.5754 is the number a uniformity
proof now has to beat. Candidate unchanged at 0.6725106958. No
proportion is claimed to have moved.
## Formal chain, track 1 closed: the floor is kernel-checked (2026-08-12)

Instrument: `zeta23ext/Zeta23Ext/FloorCert.lean` (theorem-proving
service, project 029bed09, 2h27m; 968 lines).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| LP bound by rational weak duality | **KERNEL-CHECKED** | six column inequalities, two sign conditions, the exact value identity, all in Q | `MTKernel.theoremA`, stated for ANY cost vector dominating the four rational bounds |
| The four kernel bounds B1-B4 | **KERNEL-CHECKED** | the genuine MT kernel: `Real.sin`, `Real.sqrt 2`, `pi` - not a rational surrogate | from-scratch Taylor machinery with explicit truncation error 2\|r\|^2N/(2N)!, pi from Mathlib's 20-digit bounds, sqrt2 by 23-digit enclosure; B3/B4 by 4 resp. 6 sub-interval covers refined at the tight endpoint |
| Combined floor | **KERNEL-CHECKED** | h*, j* as genuine infima (`sInf` of the image), bounded below via B3/B4 | `MTKernel.corollary`: every admissible configuration pays >= F = 5.021172019e-6 |
| Method purity | NO ESCAPE HATCHES | no `sorry`, no `admit`, no `native_decide`, no floats | axioms: propext, Classical.choice, Quot.sound |
| Constant fidelity | **CROSS-CHECKED IN Q** | Lean constants vs `lp_certificate.py` | F_RAT identical as a Fraction; edges, duals, r_* all match |
| Independent consistency | NOTED | the formal B2 margin reproduces the measured one | relative slack 4.19e-8 against the measured 1.049e-11 absolute margin |
| Edit to the artifact | DISCLOSED | one comment in the service output used the reserved word of `zeta/rigor.py`; reworded to "enclosure-carrying" for the hunts/ lexical rules | no proof content altered; sorry count 0 before and after. NOTE: this row itself first quoted the reserved word literally and tripped `test_no_hunt_claims_the_reserved_word` - session defect #10, caught by the gate, fixed here |

Disposition: **THE CENSUS FLOOR IS NO LONGER A MEASUREMENT.** c_u >=
5.021172019e-6 is a theorem about the Montgomery-Taylor kernel, checked
by the Lean kernel, with the LP half stated generally enough to survive
any future re-derivation of the kernel bounds. The candidate's floor
pillar is at rung 3. No proportion is claimed to have moved.


## Formal chain, track 2: the retention certificate's arithmetic is kernel-checked (2026-08-12)

Instrument: `zeta23ext/Zeta23Ext/BandCert/` (theorem-proving service,
project 7fb5612e; 8 modules, 2280 lines, sorry-free import chain).

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Certificate arithmetic closes at the four depths | **KERNEL-CHECKED, UNCONDITIONAL** | kernel `decide`; `cap` built from the TRUE band sup/inf, recorded numbers only as one-sided bounds | `cap_le_slack`, `cap_le_slack_at_depths`; margins +1.26e-4 / +3.12e-3 / +2.66e-2 / +2.95e-2 |
| No band missed | **KERNEL-CHECKED** | property of the recorded cover, not an assumption | `f_nonpos_off_bands` over (0, 98] |
| Analytic leaves L1-L6 | **KERNEL-CHECKED** | Taylor enclosures via `Complex.exp_bound`, rational 2pi enclosure, sqrt2 integer bounds, s(u) series branch | proved from Mathlib, quantified over the data |
| **The dual layer H3** | **NOT FORMALISED — NAMED HYPOTHESIS** | "the cap bounds D - (1-theta) R for every configuration" is the modelling step; it is ours, on paper | `band_dual_verdict` takes it as a hypothesis rather than burying it |
| Independent regeneration | **BONUS CROSS-CHECK** | the JSON was not shipped; the service rebuilt the certificate from PROBLEM.md via its own mirror | closed with different margins (+2.95e-2 vs our +4.49e-2 at y=49/100), both positive |
| Toolchain divergence | NOTED, PORT REQUIRED | this package Mathlib v4.28.0 vs upstream Zeta23 v4.33.0-rc2 | integration blocker, mechanical |
| Edit to the artifact | DISCLOSED | one comment reworded in `Iv.lean` for the hunts/ lexical rules | no proof content altered; sorry count 0 before and after |

Disposition: **THE RETENTION'S ARITHMETIC IS A THEOREM; ITS MODELLING
STEP IS NOT.** What the kernel now guarantees is that the recorded
certificate really does close - with the cap defined by genuine suprema,
so the guarantee is not about our bookkeeping but about the field. What
remains is the reduction of the retention to that certificate (H3), and
that reduction is also where blocker 1 (depth-uniformity: four recorded
depths, not all y) lives. No proportion is claimed to have moved.


## Blocker 1 closed (single-pair layer): depth-uniform retention (2026-08-12)

Instruments: `depth_uniform.py`, `test_depth_uniform.py` (27 tests);
coordinator re-ran both.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| **theta over ALL y in (0, 1/2], not sampled depths** | **CLOSED at 0.995** | 18 cells tiling (0,1/2] exactly; endpoints shared as objects so adjacency is exact, not a tolerance | closes at 0.995 and 0.996; fails at 0.997 (-0.078), always on the deepest cell; binding cells are the three deepest, where the square completion turns on |
| The shallow end (no smallest point) | **CLOSED BY HOMOGENEITY, NOT CELLS** | f+(g,y) <= y^2 Fhat(g); B convex through the origin so B(lambda F) <= lambda B(F); slack(y)/y^2 >= 8 L2/A = 0.6199944 (the y->0+ limit, sinh t >= t) | one finite inequality covers an interval with no smallest point; a geometric ladder cannot reach 0 and would have left (0, 0.002) open - the same missing quantifier one decade lower |
| Derivative constants | DERIVED TWO WAYS, NOT COPIED | Cauchy-Riemann gives dC/dy = dS/dg and dS/dy = -dC/dg, so two magnitudes bound four; Cauchy-Schwarz vs direct majorant, module takes the min | direct majorants beat Cauchy-Schwarz throughout (0.055476 vs 0.064328; 0.226506 vs 0.463826 at y=1/2); numeric/bound worst ratios 0.65-0.74 with margin; attainment 0.85 on a dense scan, so near-sharp |
| Worst-corner choice | MEASURED, NOT ASSUMED | sigma^2, E, c_im increase in y (damage at the deep lip); slack/y^2 increases in y (budget at the shallow lip) | direction control passes on every cell used |
| **Consistency vs the point results** | **PARTIAL DEVIATION, REPORTED NOT TUNED** | strict domination of `paper_chain`'s inflated number fails at all four sampled depths (ratios 0.9413/0.9881/0.9963/0.9971) | traced: paper_chain inflates a whole band by a global constant, this module inflates each bin by its own centre gradient plus curvature. The meaningful check - domination of the TRUE field - holds: worst (true - F_up) = 0, worst relative -5.4e-5 (-1.4e-3 shallow); both caps under slack at all four depths; measured adversary dominated |
| Convention + lesion | PASS | cap diverges at theta=1 including on the shallow cell where the y^2 scaling could have hidden it; lesion (drop inflation) fires at 7.08e-3 | |
| Precision response | SETTLES | cap falls monotonically 1.0543e-1 -> 9.996e-2 over step 0.01->0.00125, slices 2->8, G 120->200 | <0.7% total drift |
| **Incidental defect found in an existing module** | RECORDED | `PaperChain.sigma2`'s difference form (Phi2(2iy)-A)/(2A) loses ~4 digits by y~1e-4, worthless by y~1e-6 | a second reason the shallow end cannot be reached by evaluating the point bound at ever smaller depths; the shallow cell uses closed forms only |
| Named open, NOT closed here | STATED | (i) single-pair layer only - `paper_joint.py`'s multi-pair depth quantifier remains open (blocker 2); (ii) double precision - the arb and rational covers exist for four sampled depths, re-running either over these 18 cells is the named next hardening; (iii) band period beyond G measured on the resolved region and assumed to persist, inherited from `paper_chain.tail_sum` | |

Disposition: **THE DEPTH QUANTIFIER IS CLOSED FOR THE SINGLE-PAIR LAYER
AT theta = 0.995, AND COSTS NOTHING.** Depth-uniformity costs one grid
step at the far end (0.997 vs the rational cover's 0.997 at sampled
depths) and nothing at the retention of record. Grade: hardened
(double precision), not kernel-checked. No proportion is claimed to have
moved.


## Blocker 3 resolved: the asymptotic transfer, and the effectiveness verdict (2026-08-12)

Instruments: `asymptotic_transfer.py`, `test_asymptotic_transfer.py`
(18 tests); draft section for the preprint.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Unit dictionary into the source's hat units | **DERIVED, FACTOR 1** | one change of variable x = tau*L and one Poisson lemma read at two step sizes: h=1 gives 2piA (LAW D), h=2pi gives A; undoing the scaling gives aL^2 with a = A | the normalised Gram is grid-step INDEPENDENT (the 2pi/h cancels between inner product and normalisation) - measured at steps 1, pi, 2pi with defects halving as 1/span |
| a vs A | **EXACT** | a*(lambda) = sin(theta)/theta, theta = lambda/sqrt2; A = a*(1) | bit-identical (defect 0.0); their consistency law cRatio(lambda; a*,b*,J*) = c*_lambda reproduces to 1.1e-16 |
| The transfer in their objects | **CLEANEST FORM FOUND** | \|\|P\|\|^2_F = sum m^2 + R exactly, so D = \|\|Ahat\|\|^2_F - sum_{S1 u S2} m^2 | the hypothesis becomes (T): \|\|Ahat\|\|^2_F >= sum m^2 + 2 theta c_u N(I'), stated purely in upstream objects; residual < 8e-15 |
| **Dominant error term** | **NOT calE - the coordinator's guess was wrong** | window-moment drift, constant DERIVED from parts not fitted: 4/(l1 a^2) + 16 l1/a^2 + 8 cinv/a + \|d cinv/d l1\|(2log2 - 1) = 35.519106 | measured drift x L/w = 35.5443 / 35.5216 / 35.5194 at l = 1e4/1e5/1e6; the partial d cinv/d l1 = -0.684755 = -HD'(1) as it must be |
| **Does the improvement drown?** | **NO** | 2 theta c_u is a fixed constant; every error term is o(1) | the composed statement is the same logical type as the source's own epsilon-form, with H raised from 2 - 1/c*_1 to 2 - 1/c*_1 + 2 theta c_u |
| **Is it numerically effective?** | **NO, AND THIS IS THE HEADLINE CAVEAT** | crossover l0 = 3.8621e6, T0 ~ 10^(1.6773e6) | nothing below that height clears the budget. The shape is T0 ~ exp(38.5/improvement) - an eps-improvement costs height exponential in 1/eps - and that shape comes from the SOURCE's own o(1) coefficients, not from the transplant |
| Sensitivity to existential constants | MILD | C = 1 / 10 / 100 gives l0 = 3.86e6 / 5.22e6 / 1.73e7 | because the dominant term is C-free |
| The lambda < 1 requirement | **COSTS THE CENSUS NOTHING** | their `thmD_abstract` needs lambda strictly < 1; the census kernel generalises to g_{lambda,lambda1} | equals `cg_transplant.g_kernel` at lambda = lambda1 = 1 to 3.3e-16 (a strong check on the scaling: a wrong one would move the kernel zeros); re-running the LP on the deformed kernel reproduces c_u to 1 ulp, and dc_u/dlambda ~ -5.3e-4 means the floor RISES as lambda falls - safe direction |
| Lesion + admissibility controls | PASS | carrying our 2piA onto their grid gives unit norm 1/2pi exactly; lambda=1, w=0.5, 8w>L each rejected | |
| Residual, named | STATED | (i) T0 is a reference not an effective bound - four existential EvBound constants would make it effective and nothing else in the budget would; (ii) prime-side and Theorem B cited; (iii) **theta = 0.995 is measured at lambda = 1 only**, its lambda-sensitivity unmeasured (the deformation at 1 - lambda1 ~ 5e-7 is far below that measurement's resolution, but this is named, not closed); (iv) grid instruments truncated ~1/span | |

Disposition: **THE TRANSFER GOES THROUGH AND THE IMPROVEMENT IS REAL AS
A LIMINF STATEMENT - AND IT IS NOT EFFECTIVE AT ANY REACHABLE HEIGHT.**
Both halves are the result. The source's theorem is itself a
non-effective liminf with existential constants, so the composed
statement is the same logical type, not a weaker one; but anyone reading
"improvement" as "better at computable heights" would be wrong, and the
preprint must say so. No proportion is claimed to have moved.


## Blocker 2 NOT closed: the per-pair route is refuted (2026-08-12)

Instruments: `joint_universal.py`, `test_joint_universal.py` (24 tests);
coordinator re-ran the suite.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| **Rung 1: subadditivity at the cap level** | **FALSE** | the field-level intuition is right - `max(0, sum) <= sum max(0,.)` holds with worst violation exactly 0.0 - but it does NOT survive the square completion | joint cap / sum of single caps reaches 1.4475 (k=2) to 3.3796 (k=6) for coincident stacks at theta = 0.995; exact closed-form excess `[2 sum_{i<j} F_i F_j - (k-1)(cK)^2]/(4cK)`, defect 2.8e-17. The adversary collects k times the damage from one stack and pays the internal charge once |
| Which half moves | **THE SQUARE COMPLETION, NOT THE BANDS** | for a coincident triple the joint band SET is identical to one pair's (shielded fraction 0.000) while m* jumps 3 -> 7 | the band set can only shrink; the occupancy grows |
| **The decisive finding: the route could not have worked** | **PER-PAIR ARGUMENTS ARE DEAD, EITHER DIRECTION** | on a nu=1 lattice `sum cap_single` exceeds the budget from k = 3 at FLOAT grade (-0.00595) and from k = 4 at HARDENED grade (-0.03953; k = 3 fits at +0.00614) while the joint verdict closes with +40% relative margin; worst-lattice erosion 0.129/pair vs hardened surplus 0.063, so the accounting goes negative regardless of grade | no argument bounding the joint cap by a sum of single-pair caps can establish universality at theta* = 0.995, because its conclusion is false from k = 4 on at every grade. **The joint field's shielding is load-bearing.** CORRECTION (session defect #12): the original row said "from three pairs on" unconditionally - a float-grade artifact on a 2% margin, caught by re-checking at the hardened cap when asked "are you sure" |
| Slack additivity (the coordinator assumed it) | **FALSE, AND SIGNED** | `budget(P) = sum_i slack(y_i) + sum_{i != j} T(t_i - t_j, y_i, y_j)`, reproducing PaperJoint.budget to <1e-9 | the pair term runs +8.31 (coincident) to -0.756 (nu=1 lattice, k=8); worst infinite-lattice erosion -0.1288 = 84% of one pair's slack against a single-pair surplus of only 0.0587, so even a separated-configurations version dies |
| Rung-2 repair A: even-split lemma | **PROVEN AND USELESS** | `B(sum F_p, K) <= sum_p B(F_p, K/k)`, i.e. cap_joint <= sum cap_single at theta_k = 1 - (1-theta)/k | exact per cell, equality for equal F_p; but theta_2 = 0.9975 and the single-pair dual already fails at 0.999 |
| Rung-2 repair B: union refinement | **ONE-SIDED THE WRONG WAY** | band maxima do not increase under refinement, but the CAP does - each sub-cell inherits the parent maximum while the cell count grows | ladder 0.08745 (62 cells) -> 0.17050 (124) -> 0.33890 (248) |
| Rung 3: randomised adversarial search | **EVIDENCE ONLY, LABELLED** | 320 configurations, k in 2..12, jittered lattices, near-coincident clusters, mixed depths, 12-rung depth ladder, conservative instance | **0 opened the verdict**; worst relative margin +0.2749 at full resolution, and it is a two-pair configuration at 2.05 mean gaps - the sparse-lattice family that binds `paper_joint`'s own sweep, rediscovered blind. 37/320 broke rung-1 domination (worst 1.41) |
| Planted-violation lesion | FIRES | x1 closes, x2/x4/x8 open | budget provably untouched by the lesion |
| **The obligation, reshaped** | **ONE INEQUALITY** | with `c2 = phi^2 * phi^2` (closed form, supported [-1,1], positive inside, `int c2 = A^2` to 0.0), `E[G] = (1/A^2) int c2 \|G\|^2`, `F_on = sum_x e^{ixw}`, `F_p = sum_i 2 cosh(y_i w) e^{it_i w}` | universality <=> `E[F_on + F_p] >= theta E[F_on] + (1-theta) n + 4k` for all finite X and P. Restates the whole verdict in one variable, defect ~1e-11 on mixed configurations |

Disposition: **THE COORDINATOR'S PROPOSED ROUTE IS REFUTED, AND THE
REFUTATION IS THE RESULT.** Session defect #11: the per-pair domination
plan was stated in the brief as the likely route and is false twice over
- the cap is superadditive above the multiplicity threshold, and even
where it is not, the per-pair sum exceeds the budget from three pairs
on. Blocker 2 remains OPEN. What replaces it is better posed than what
it replaces: a single bandlimited nonnegative-kernel inequality in two
exponential sums, which is a target both an attack and a formalisation
can aim at. Multi-pair universality is still a statement about a tested
set - now 320 configurations wider, with the binding family rediscovered
blind. No proportion is claimed to have moved.


## Blocker 2, second campaign: the cluster decomposition (2026-08-12)

Instruments: `cluster_universal.py`, `test_cluster_universal.py`
(20 tests); coordinator re-ran the suite.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| Separation lemma constant | **DERIVED** | two integrations by parts; c2 has a CORNER at w=0 (autocorrelation of a jump window, one-sided slopes -(1+cos sqrt2)/2 closed-form) | C_T = 27.4970 with every factor closed-form except one quadrature; measured worst \|T\| dt^2 / C_T = 0.618 - holds with 38% headroom; eps_T(Delta) = 2 C_T/(2 pi Delta)^2 |
| **The periodic family: CLOSED** | sup rho(s,y) = **0.9286 < 1** | budget by Poisson/Dirac comb in closed form; for s <= 1 mean gap the per-pair budget is DEPTH-FREE with floor +0.024509 at s = 1 and diverges as s -> 0 (the coincident limit: budget wins, cap 0 by shielding - the multiplicity branch never gets to fight) | 636-point map, 511/636 fully shielded (cap exactly 0); nonzero caps only in narrow resonance windows at near-integer s, decaying 0.852/0.775/0.714/0.668/0.651 toward the isolated-pair 0.594; worst member (s, y) = (2.002 gaps, 0.4999); refinement moves the sup DOWN (0.955/0.929/0.915) so the record is the conservative end; >= 7.1% uniform relative margin |
| Jitter direction | SUPPORTED | coherent = worst: margin rises monotonically with jitter at every seed | mean +0.103 -> +0.888 over amplitudes 0 -> 1.2 grid units |
| **Lattice extremality** | **CONJECTURE, LABELLED** | the lattice is NOT a stationary point in position space (max gradient 0.186, compression -0.222); the extremum lives in the spacing parameter | stated as EXTREMALITY_CONJECTURE in the artifact, test-pinned as a conjecture, not claimed |
| **Finite-m bridge** | **OPEN - THE BROKEN RUNG, REPORTED WITH ITS NUMBERS** | per-pair margins approach the m->infinity limit from BELOW at resonance spacings (s=2.0: +0.0240 -> +0.0056 with limit +0.0135; s=1.0 similar) and from above elsewhere | every finite rung closes, but the infinite-lattice verdict does not one-sidedly dominate finite clusters; no bridge in either direction |
| Cap cross term | MEASURED ONLY | the joint instrument optimises one cell width per configuration; the mismatch does not decay in Delta | never decisive on 40/40 separation configs (worst +3.9e-2); named, not papered over |
| Assembly campaign | 40/40 | margin(whole) >= sum margin(clusters) - derived budget eps alone | worst one-sided slack +0.13 |
| Coordinator's pre-refutation | REPRODUCED | k=8 cluster in a legal-density window: deficit 0.448 vs pair-free credit 1.28e-3 | short by a factor ~350; the density rescue stays dead |

Disposition: **THE ADVERSARY'S CONTINUUM IS PINNED TO A ONE-PARAMETER
RESONANCE FAMILY WHOSE WORST MEMBER IS COMPUTED, AND TWO NAMED BRIDGES
REMAIN.** The periodic family - which contains every binding
configuration every search has found - closes uniformly with 7.1%
margin, dense clusters are budget-positive with a depth-free closed-form
floor, and separation carries a derived constant. Open: the finite-m
bridge (margins approach the limit from below at resonances) and the cap
cross-term grade. Blocker 2 remains open, but it is now two specific
bridges, not a continuum. No proportion is claimed to have moved.


## Research-grade prover results: one theorem, one named obstruction (2026-08-12)

Instruments: `zeta23ext/Zeta23Ext/PairEnergy.lean` (project 481e49bf),
`zeta23ext/Zeta23Ext/EForm/` (project 00643d5e). Unlike the four earlier
Lean artifacts, these were OPEN statements: we had numerics and no proof.

| Obligation | Status | Exact dependency | Evidence |
|---|---|---|---|
| **Pair-energy positivity E[F_p] >= 4k** | **PROVED, SHARP, HYPOTHESES DROPPED** | Gram matrix of u -> e^{zeta_a u} against the nonnegative weight g is PSD with a fixed-point-free involution; trace Cauchy-Schwarz plus regularisation, no spectral theory | `pair_energy_ge` / `four_k_le_energy` / `four_n_le_sum_sq`; 785 lines, 36 theorems, all reporting only the three standard axioms; attained at k=1, y=t=0 so 4k cannot be improved; the k>=1 and y in [0,1/2] hypotheses we asked for were shown unnecessary |
| Consequence for blocker 2 | **THE PAIR HALF OF THE E-FORM IS CLOSED** | the obligation splits as pair energy + cross term | one of the two summands in `E[F_on + F_p] >= theta E[F_on] + (1-theta) n + 4k` is now a theorem |
| Single-pair retention at exact constants, n <= 3 | **PROVED** | uniform in shift and depth; from `Icross >= -Shq(y)(A + 1/4)/2`, the exact slack identity, and Phi2 >= -1/4 | `retention_le_three`; `retention_le_two` for n <= 2 |
| Exact reduction | **PROVED** | valid for every n, configuration, shift, depth | `retention_gap` - the gap equals an explicit sum, so the problem is now algebraic |
| Damage localisation | **PROVED** | a single on-line point does no damage outside an explicit region | `Icross_localized`, `Icross_nonneg_of_Wcos_large` |
| Arbitrary n with few damaging offsets | **PROVED** | at most three offsets damaging | `retention_of_few_near`, strictly stronger than the n <= 3 result |
| **The unrestricted single-pair statement** | **NOT OBTAINED, NO COUNTEREXAMPLE** | "looks robustly true" | **the obstruction is named exactly**: any bound `-Icross <= kappa Shq(y)` with kappa uniform in the offset caps at n <= 2A/kappa - here kappa = (A+1/4)/2 gives n <= 3, and even the numerically optimal uniform kappa would give only n <= 7. Closing it needs the 1/s^2 far-field decay plus band/cluster repulsion with near-sharp constants |
| Reading of that obstruction | **A FINDING IN ITS OWN RIGHT** | the capped route is exactly the naive one | it shows our band-dual structure is NECESSARY rather than merely convenient - a uniform-constant argument provably cannot reach large n |
| Edit to the artifacts | DISCLOSED | one comment reworded in `PairEnergy.lean` for the hunts/ lexical rules | no proof content altered; sorry count 0 before and after |

Disposition (CORRECTED, see the row below): **THE PAIR-ENERGY RESULT IS
NOT NEW, AND THE COORDINATOR OVERCLAIMED IT.** It is a corollary of two
classical lemmas that the source paper already states, proves and
formalises, and its exact numerical specialisation is printed in that
paper's own text. The formalisation remains useful to our chain; the
novelty framing was wrong and is retracted here. The second problem's
outcome stands: the uniform-constant obstruction is named and real. No
proportion is claimed to have moved.

## CORRECTION, same day: the pair-energy result is prior art

A novelty check was run before any public claim - and refuted the
framing.

| Finding | Detail |
|---|---|
| **Verdict** | **(b) FOLLOWS EASILY from known results. Do NOT claim novelty.** |
| The reduction | sum Q(a,b)^2 = tr((QS)^2) with tr(QS) = 2n; writing Q = B*B, C = BSB*, the claim is exactly tr(C^2) >= (tr C)^2/n |
| Ingredient (a) | sigma fixed-point-free on 2n points => S has signature (n,n) => n_+(C) <= n. **Sylvester's law of inertia in pull-back form** - the source paper's Lemma 3.1, formalised there as `RHLinalg.posIndex_conj_le` (`Zeta23/LinAlg/Inertia.lean`) |
| Ingredient (b) | (tr C)^2 <= n_+(C) tr(C^2): Cauchy-Schwarz on positive eigenvalues, the Hermitian case of \|\|X\|\|_*^2 <= rank \|\|X\|\|_F^2. **The source paper's Lemma 3.3 at theta = 0**, formalised as `RHLinalg.cauchySchwarz_count` (`Zeta23/LinAlg/Weyl.lean`); also falls out of their `rank_trace_ineq` at P=0, r=0, b=n, c=2 |
| **The killer citation** | the paper's own **section 7.5(a)**: "In the extreme hypothetical configuration in which all zeros in [T,2T] are off-line pairs, Proposition 4.1 gives rank P = 0, n_+(Q) <= N/2, while Lemma 3.2 would then force \|\|Ahat\|\|_F^2 >= 2N." With N = 2n that is >= 4n - our inequality, our constant, in print |
| The structure was theirs too | their Prop 4.1(ii) gives each off-line pair a 2x2 hyperbolic block; our `Fin n x Bool` involution IS that pairing, and 2cosh(yw)e^{itw} is literally the sum of exponentials for rho and 1 - conj rho - their Gram matrix, not an analogy |
| Cosmetic defect in our statement | the `Re` is unnecessary: under hypothesis (ii) the sum is provably real. Stating it as a real part makes the result look more delicate than it is, and a referee would notice |
| The proof route | the spectral-theorem-free regularised-projection argument is a re-derivation of (a)+(b) - proof engineering for formalisation, not new mathematics |
| Independent numerics | 2000 random feasible complex instances, n in {1,2,3,5,8}: imaginary part vanished every time, n_+ <= n every time, min ratio 1.0251, equality at n=1 |
| Naming | moot. If a local Lean label is wanted, "involution-normalised inertia bound" is accurate and collision-free; "rank-trace inequality" and "thresholded Cauchy-Schwarz count" are taken by the very source that pre-empts this |

Session defect #13, the coordinator's: after the prover returned the
result, the ledger, the package README and the operator were all told
this was "a theorem we did not know" and "research-grade". True only in
the sense that WE did not know it; false in the sense that matters. The
check that caught it was run before any public claim, which is the
system working - but the overclaim was written down first and had to be
retracted, which is the system working late. What survives, and is worth
keeping: the Lean file is a correct formalisation of a step our chain
uses, obtained in 104 minutes, and it now carries the citation it
should have carried from the start.


## Sphere-Packing-Lean audit: a dependency avoided, and the bridge located (2026-08-12)

Instrument: `SPL-AUDIT.md` (agent build; repo cloned read-only at HEAD
bad3de9, 2026-08-05, 77 files, 18194 lines).

| Finding | Detail |
|---|---|
| **The repo is NOT sorry-free** | 61 real (non-comment) sorrys across 19 files - **including the headline `SpherePacking.MainTheorem`, whose entire proof is `sorry`**. The "formally complete Feb 2026" report the tool survey relayed is not borne out by the tree |
| **The exact scaffolding we wanted is a sorry** | `SchwartzMap.PoissonSummation_Lattices` is `sorry`, lives in a file whose own header says it "SHOULD EVENTUALLY BE REMOVED", and its hypothesis predicate `PSF_Conditions` contains a `sorry` **in its definition** |
| **Trap avoided** | requiring the library would have imported those sorrys; `PoissonSummation_Lattices` would typecheck downstream and be an axiom-tainted lie. Pin conflict too (their Mathlib v4.32.0 vs our v4.33.0-rc2) |
| **Mathlib already has better** | `Real.tsum_eq_tsum_fourier_of_rpow_decay`: continuity plus polynomial decay, **no smoothness at all**. Our c2's corner never enters because c2 appears only as the TRANSFORM; both hypotheses hold at b = 2 with f = c2hat = \|ghat\|^2. Only real work is rescaling Z -> sZ |
| **The bridge is absent by design** | Cohn-Elkies routes finite -> periodic -> infinite and never truncates; no truncation lemma, tail bound or remainder anywhere in the repo |
| **STOP LOOKING FOR A ONE-SIDED LEMMA** | our own data (m=4: +0.0240, m=32: +0.0056, limit +0.0135) says the finite-m value CROSSES the limit, so no one-sided lemma exists to borrow |
| **The tractable statement, located** | a TWO-SIDED estimate \|b_m - b_inf\| <= E(m, s, y), elementary precisely because c2 is compactly supported: the dual sum is ALREADY FINITE (\|2 pi k/s\| < 1), so the discrepancy is a boundary term over O(1) pairs at the cluster ends, not a divergent tail. Self-contained against Mathlib alone |
| No positivity scaffolding either | no Beurling, Selberg, bandlimit, Paley-Wiener; the magic function's two Cohn-Elkies conditions are not formalised at all, so there is no worked example of establishing a Fourier transform nonnegative |
| Verdict | **(iv) not usable as a dependency**, shading into (iii) proof-pattern reference |

Disposition: **THE SURVEY'S RECOMMENDATION #4 IS REFUTED BY ITS OWN
AUDIT, AND THE AUDIT FOUND THE ROUTE ANYWAY.** A vendor-adjacent
"formally complete" claim did not survive a grep; the scaffolding we
were told to build on is a sorry inside a file marked for deletion. What
replaces it is better: Mathlib's own Poisson result needs strictly
weaker hypotheses than the sorried one, and the bridge is a two-sided
boundary estimate over O(1) cluster-end pairs. No proportion is claimed
to have moved.


## The SOS/Gram route is CLOSED, with an exact witness (2026-08-12)

Instruments: `sos_certificate.py`, `test_sos_certificate.py` (23 tests).

| Obligation | Status | Evidence |
|---|---|---|
| Matrix form of the full obligation | **EXACT** | `Xi(Q) = sum c(a,b) Q(a,b)^2 - 4k` with c = 1 except (1-theta) on the on-line off-diagonal and 0 on its diagonal; validated against the Fourier evaluator to 2.55e-11, and the residual is the REFERENCE's quadrature error (falls as h^2) - the matrix side is closed-form |
| Degree-2 SDP relaxation | **LOOSE** | cannot even reproduce the kernel-checked `E[F_p] >= 4k` for k >= 2: that is an INERTIA fact (how many positive eigenvalues perm(sigma) has), invisible to a degree-2 lift on entries of Q |
| **The Gram cone itself is insufficient** | **PROVED INSUFFICIENT, EXACT RATIONAL WITNESS** | `cone_violator`: on-line block all-ones, cross entries +/- i t, pair diagonal 1 + 2t^2, satisfying PSD (two-line identity), the involution relations, diag >= 1 and Cauchy-Schwarz - with Xi = (1-theta)n(n-1) + 2(1+2t^2)^2 - 2 - 4n t^2 -> **-infinity**. Re-checked exactly in fractions with rational LDL^T: Xi = -47/100 (n=3), -36/25 (n=4), -157/20 (n=6) |
| Why it does not refute the target | the witness is NOT REALIZABLE as a configuration | relative fit residual 0.135 - it is not a Gram matrix of exponentials |
| Derived window ranges added | **SHRINK 50x, DO NOT CLOSE** | psi(1) = 1.039221, psi(1/2) = 1.009717 (sharper than Cauchy-Schwarz by log-convexity of Psi), min Phi2/A = -0.180414; deficits -0.045 (3,1) to -0.245 (4,2), still growing in n and k |
| The lesson | **a pointwise entry bound cannot close a joint obligation** | what is missing is the R-vs-D trade: the on-line atoms cannot all sit at the damage minimum at once |
| Size-independent multiplier | **EXISTS AND IS PROVABLY INSUFFICIENT** | the generalised inertia bound `sum Q^2 >= (n+2k)^2/(n+k)` (recovering PairEnergy exactly at n=0) has a fixed kernel multiplier h(a,b) = 2[b = sigma a], and the (0,1) SDP dual is proportional to I - perm(sigma), the same kernel - but it falls short by exactly `nk/(n+k) + theta R` |

Disposition: **THE ROUTE THROUGH GRAM POSITIVITY ALONE IS CLOSED.** Any
proof must use analytic properties of Psi beyond g >= 0, supplying a
JOINT constraint coupling the on-line block to the cross block - not
entrywise bounds - and must supply `nk/(n+k) + theta R` over the inertia
bound. The degree-2 moment hierarchy is the wrong instrument because it
cannot see inertia. No proportion is claimed to have moved.


## The truncation bridge: derived, and it does NOT close the family (2026-08-12)

Instruments: `truncation_bridge.py`, `test_truncation_bridge.py` (19
tests). **Contains a finding that must be chased before anything else -
see the flagged row.**

| Obligation | Status | Evidence |
|---|---|---|
| Convergence rate | **DERIVED, AND NOT 1/m** | it is (a + b log m)/m: the corner of c2 at w = 0 leaves a NON-oscillating 1/d piece whose partial sums are log m. Fitted exponents 0.72-0.86; the derived log-coefficient matches the fit to within 0.3% at every probe |
| Why no one-sided lemma exists | **MECHANISM FOUND** | the coefficient bracket FLIPS SIGN at commensurate spacings: at s in 2 pi Z it is + kappa(cosh^2 y - 1) > 0 (finite above the limit), off resonance it is c2'(0+) < 0 (below). Pinned as a test |
| The two-sided estimate E | **DERIVED** | E_crude = (2 C_T/s^2)(H_{m-1}/m + 1/(m - 1/2)), depth-free, C_T reused from `cluster_universal`; the tail bound is closed-form by telescoping, no zeta(2) needed; an elementary majorisation gives C <= 77 |
| E validated | **HOLDS EVERYWHERE** | 504 grid points; worst measured/E = 0.3544 (crude, headroom x2.82), 0.8166 (hybrid, x1.22); planted inflation breaks it in both directions |
| **m0, the payoff** | **NOT SMALL - THE FAMILY DOES NOT CLOSE** | m0 is 2-4 over most of the range but blows up in two thin regions: the resonance s ~ 2 gaps (little room, rho = 0.89) and the budget floor at s = 1 gap (b_inf = 0.0245 is tiny), where m0 reaches 6157-8454 |
| **FLAGGED: negative finite margin at the rho-map argmax** | **MUST BE CHASED** | at (s, y) = (2.002 gaps, 0.4999) the finite ladder margin goes NEGATIVE from m = 24: +0.02890 / +0.00760 / +0.00037 / **-0.00264** / **-0.00685** at m = 2/8/16/24/64. The budget side behaves exactly as the derived estimate predicts; **the cap side is the cause** |
| Is it real or an instrument artifact? | **UNRESOLVED - the reason it must be chased** | the cap is step-dependent and moves DOWN with refinement (rho = 0.9685/0.9547/0.9286 at step 0.005/0.004/0.002), so coarse-step finite caps may be overestimates. But finite per-pair caps also RISE with m past cap_inf (0.1127/0.1156/0.1184/0.1205 at m = 4/8/16/32), which is the wrong direction |
| Named gaps | G1 cap side not derived and measured wrong-way; G2 m < m0 checked on a ladder, not exhaustively; G3 cap step-dependence | recorded in the module, pinned as tests that assert the FAILURES rather than hopes |

Disposition: **THE BRIDGE IS DERIVED AND THE FAMILY STILL DOES NOT
CLOSE, AND THERE IS A POSSIBLE COUNTEREXAMPLE ON THE TABLE.** The
budget side is now understood exactly, including why no one-sided lemma
could ever have existed. But m0 blows up in two thin regions, and at the
worst point of the rho map the finite margin goes negative from m = 24.
Until that is resolved as real or as a coarse-instrument artifact, the
multi-pair verdict at theta = 0.995 is IN DOUBT, not merely unproved.
No proportion is claimed, and the candidate reading is not defended.


## The truncation bridge is kernel-checked (2026-08-12)

Instrument: `zeta23ext/Zeta23Ext/TruncEst/` (theorem-proving service,
project 9b5d5969, 1h26m; 6 modules, 1383 lines, 91 declarations, every
one reporting only propext / Classical.choice / Quot.sound; no sorry,
no admit, no native_decide).

| Obligation | Status | Evidence |
|---|---|---|
| Lemma 1: far-field decay | **KERNEL-CHECKED** | `abs_T_le : \|T dt y\| <= Cdec/dt^2` for dt != 0, y in [0,1/2], with **Cdec = 200** - a single primitive delivering both integrations by parts on [0,1] plus uniform hyperbolic bounds (the chain gives 180, rounded to 200). Deliberately loose, as the submission permitted |
| Lemma 2: Poisson step | **KERNEL-CHECKED** | `poisson_T` via Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay` on the rescaled kernel - **exactly the route the Sphere-Packing-Lean audit identified**, needing continuity plus polynomial decay and no smoothness; `poisson_rhs_finite` establishes the dual sum has finite support, `bInf_eq_poisson` gives the equivalent closed form |
| Main: the two-sided estimate | **KERNEL-CHECKED** | `abs_bM_sub_bInf_le`: for m >= 1, s > 0, y in [0,1/2], \|b_m - b_inf\| <= (2 Cdec/s^2)(H_{m-1}/m + 1/(m - 1/2)) - our derived shape, proved by the difference identity, head bound and the telescoping tail |
| **Fidelity to our own definitions** | **KERNEL-CHECKED, UNPROMPTED** | `c2_eq_autocorrelation : c2 w = integral g u * g(u - w) du` and `integral_g : integral g = A`. The closed form we hand-derived IS the autocorrelation, proved rather than assumed - a defect class this session hit twice by other routes |
| Constant gap, recorded | the proved Cdec = 200 vs our measured C_T = 27.4970 | ~7x looser. Immaterial to the verdict: the bridge already failed to close the periodic family at the sharper constant, so the formal constant changes nothing about m0 except making it worse. The sharper value stays available for planning, the proved one for the formal statement |
| Edit to the artifact | DISCLOSED | one docstring word reworded in `Sums.lean` for the hunts/ lexical rules; no proof content altered, sorry count 0 before and after |
| **Session defect #14, the coordinator's** | CAUGHT BY THE PARALLEL SESSION'S TEST, AFTER I PUSHED IT | I landed the six modules with their original `import RequestProject.X` lines instead of the package namespace, so the package would have failed to assemble at the first import. `tests/test_zeta23ext_imports.py` - written by the other session - caught it. Worse: my gate command piped pytest into `tail`, which masked the non-zero exit code, so the `&&` chain pushed to main anyway. Imports rewritten, gates re-run WITHOUT the pipe (18 passed, exit 0). The lesson is mechanical and worth keeping: **never pipe a gate command whose exit status the next step depends on** |

Disposition: **THE BRIDGE ITSELF IS NOW A THEOREM, AND IT STILL DOES NOT
CLOSE THE FAMILY.** Both halves stand: the finite-to-infinite comparison
is kernel-checked with an explicit constant, and m0 remains too large at
the resonance and at the budget floor. What the formal artifact adds is
that the estimate can now be cited rather than measured, and that the
Poisson route the audit recommended over a sorried dependency worked
exactly as predicted. No proportion is claimed to have moved.


## E-form retry: the first all-n result, and why it does not yet apply (2026-08-12)

Instrument: `zeta23ext/Zeta23Ext/EForm2/` (theorem-proving service,
project 8f2e43b0, 1h43m; 7 modules, 1570 lines, sorry-free, no
native_decide, standard axioms only). The submission quoted the earlier
attempt's own stated obstruction back to it and supplied the two
ingredients it named as missing.

| Obligation | Status | Evidence |
|---|---|---|
| Exact reduction | **KERNEL-CHECKED** | `retention_gap`: an exact identity for the gap, for every n, configuration, shift and depth |
| Clean sufficient condition | **KERNEL-CHECKED** | `retention_of_damage`: the inequality holds once the total damage sum_j Qim(y, x_j - t)^2 is at most 2 A Shq(y) |
| n <= 3, improved | **KERNEL-CHECKED** | `retention_le_three` now needs **no** hypothesis on the configuration and **no** restriction on y - the earlier attempt's y <= 1/2 turned out unnecessary |
| **All n under separation** | **KERNEL-CHECKED** | `retention_separated`: the inequality for EVERY n, every t, every y in (0, 1/2], provided the on-line points satisfy x_i + delta <= x_{i+1} with **delta >= 26**. This is the first all-n result of the chain |
| The far-field ingredient, as formalised | DELIVERED | `Qim_far`: \|Qim y s\| <= (14/5) y/\|s\| by one integration by parts; with Shq y >= y^2/16 this gives Qim^2 <= (3136/25) Shq(y)/s^2. **Measuring the damage against the slack rather than an absolute C/s^2 is what makes the summation close** - a better idea than the one we supplied |
| The repulsion ingredient, as formalised | DELIVERED | `Counting.lean`: a weight bounded by K and by C/s_i^2 over delta-separated offsets sums to at most 2K + (10/3) C/delta^2, using sum 1/k^2 <= 5/3 and that at most two offsets sit nearest the origin |
| **THE CAVEAT THAT MATTERS** | **delta >= 26 grid units = 4.14 MEAN GAPS** | real on-line zeros have mean spacing of exactly one mean gap by construction, so the hypothesis wants configurations **4.1x sparser than actual zeros**. `retention_separated` is a genuine all-n theorem about a class our application does not live in |
| Why it stops there, in its own words | STATED | with the uniform damage constant kappa = (A + 27/100)/2 ~ 0.594 the uniform argument stops at n <= 2A/kappa ~ 3.09; the far-field bound only beats the uniform bound for \|s\| >~ 17 (= 2.71 mean gaps); and the repulsion term of the exact reduction is not large enough at these constants to pay for a fourth point |
| Refutation | NONE CLAIMED | |

Disposition: **A REAL ADVANCE IN FORM, NOT YET IN REACH.** The chain now
has an all-n theorem and a clean sufficient condition, and the far-field
idea it invented - measuring damage against the slack rather than an
absolute constant - is better than the one supplied to it. But the
separation constant is 4.14 mean gaps against real spacing of one, so
the theorem does not yet cover the configurations the application needs.
The quantitative gap is now explicit and small in shape: bring delta
from 26 down toward 6.28, or handle the near-field cluster separately.
No proportion is claimed to have moved.


## Cross-arm transfer proposal: answered, and it does not survive (2026-08-12)

The higher-xi arm proposed that this arm's multi-pair universality step
might be finite rather than infinite-dimensional: if the binding case is
k = 2, the open step becomes a compact 3-parameter problem in
(d, y1, y2). It supplied its own kill-switch - a four-order discrepancy
between its shallow 2-pair budget (9.42e-05) and this arm's recorded
worst (0.2907) - and asked that it be resolved first.

| Question | Answer |
|---|---|
| The discrepancy | **RESOLVED, both numbers correct.** Their budget reproduces here to six figures (9.417199e-05). The two are not comparable because **at shallow depth the cap is exactly zero** - relative margin 1.0000 at y = 0.01 and 0.05 - so a tiny budget costs nothing. This arm's 0.2907 is a deep budget where the cap bites. Their number measures budget erosion; the verdict consumes budget minus cap |
| Their k-monotonicity at their spacing | **REPRODUCES, and is stronger than claimed**: at d = 6.640 grid = 1.0568 mean gaps, relative margin rises 0.3825 / 0.5031 / 0.6538 / 0.7809 / 0.9062 for k = 1..6, so k = **1** binds there, not k = 2 |
| **Does it generalise** | **NO. The k-dependence CHANGES SIGN with spacing.** Below ~1.2 mean gaps it rises; at and beyond 2 mean gaps it falls monotonically: at d = 2.002 mean gaps, k = 1..6 gives 0.3825 / 0.3649 / 0.3408 / 0.3213 / 0.2935, still decreasing |
| Why their data could not show it | their scan was d in [5.5, 7.5] grid = **[0.875, 1.194] mean gaps**; the binding family sits at 2.002 mean gaps = **12.579 grid units**, a factor ~1.7 outside the top of their window. Dense grid, wrong interval |
| Corroboration | that address is where this arm's own instruments independently landed: `cluster_universal`'s rho argmax (2.002 gaps, y -> 1/2) and `truncation_bridge`'s degrading finite-size ladder. Three instruments, one address |
| What survives from their work | their shallow ratio sum_slack/\|pair_term\| = 4.16, flat in y, agrees with this arm's independently derived limit slack/y^2 -> 8 L2/A = 0.6199944; their observation that only the nearest-neighbour gap contributes negatively is correct and explains the monotone budget rise; and the three-arm convergence on a fixed nonnegative autocorrelation kernel holds |
| Reciprocal correction sent | this arm's `PairEnergy.lean` is prior art (source paper Lemma 3.1 + 3.3, specialisation printed in its 7.5(a)); flagged in case the higher-xi arm leans on a similar Gram bound |

Disposition: **THE TRANSFER IS ANSWERED NO, BY A MEASUREMENT ITS OWN
INSTRUCTION ASKED FOR.** The configuration space cannot be truncated at
two pairs. Reply written to `CROSS-ARM-REPLY.md` with the full tables
and a suggested next probe their machinery is better placed to run than
ours: whether the falling branch beyond 2 mean gaps has a positive limit
in k or crosses zero. No proportion is claimed to have moved.


## Two coordinator defects on the eform3 submission (2026-08-13)

The prover reported both back before finishing. Both are mine.

| Defect | Detail |
|---|---|
| **#15, mathematical: the prescribed route cannot work** | The brief asked for `\|Qim(y,s)\| <= C2 y/s^2` by two integrations by parts, reasoning from `TruncEst.Decay`'s 1/dt^2 bound. **Qim decays exactly like 1/\|s\| and no better.** Measured: `\|Qim\| * s` stays in 0.13-0.30 across s = 20..1600 while `\|Qim\| * s^2` grows 5 -> 220. The cause is one number: the integrand's boundary value `cos(sqrt2/2) sinh(y/2) = 0.153 != 0`, so `g(u) sinh(y u)` JUMPS at +/- 1/2, and a jump gives 1/s |
| Why the coordinator got it wrong | `TruncEst`'s 1/dt^2 is about a quantity built from **c2 = g * g**, which is CONTINUOUS - an autocorrelation vanishes at the edge of its support. Qim is built from **g times sinh directly**, which does not. **This is the same class of error as the omega^2-vs-g kernel-pairing defect earlier in this hunt**: a function and its autocorrelation were treated as interchangeable. Twice now |
| **#16, process: the project was shipped empty** | The brief said "reuse all of it" and listed six prior results by name - and the submission directory contained only `PROBLEM.md`. None of EForm2's 1570 lines were shipped. The prover is rebuilding the window, the autocorrelation, the energy functional, the Fubini identity, the gap identity and the transform bounds from nothing |
| Why the coordinator got it wrong, again | **the identical failure as the band-certificate submission**, where the certificate JSON was not shipped and the service regenerated it. That one was recorded as a lucky cross-check and the lesson was not turned into a rule. It is one now: **a submission's project directory must contain every artifact its brief tells the prover to reuse; naming a file is not shipping it** |
| What the prover proposes instead | its own route: a sharp far-field bound at the true 1/\|s\| rate combined with **a near-field cancellation the earlier run discarded**, which its arithmetic puts at the target separation 2 pi with about 1.5x margin, with a stated fallback to the smallest explicit separation its constants support |
| Disposition | **let it run.** Its plan is better than the one it was given, it is a fifth of the way in, and its independent rebuild of machinery we already hold is an unplanned cross-check on that machinery. The waste is real and is the coordinator's to own; interrupting a working run to fix the coordinator's packaging would compound it |

No proportion is claimed to have moved.


## Note for the meta arm: the prover's effect on the result (2026-08-13)

`PROVER-CONTRIBUTION.md` records, from the job history rather than from
impression, which properties of this result would differ had the
theorem-proving service not been in the loop. Nine submissions, free
tier, no payment method attached. Summary of the finding, with the
caveat that it was written by a party to the comparison:

- **Corrections to the coordinator's mathematics: two.** A false
  statement of the grid-incidence law, shipped back with an explicit
  counterexample establishing the missing hypothesis is necessary; and a
  prescribed far-field route that cannot hold, refused rather than
  attempted, and afterwards substantiated numerically here.
- **Better methods than specified: three.** Polarised Parseval in place
  of Poisson summation (which is why the theorem covers this hunt's
  jump-discontinuous windows at all); damage measured against the slack
  rather than an absolute constant; a near-field cancellation an earlier
  run had discarded.
- **Hypotheses dropped that the coordinator assumed necessary: two.**
- **An obstruction named as arithmetic** (uniform damage bounds cap at
  n <= 2A/kappa), which is what made the following submission's first
  all-n theorem possible. The diagnosis was worth more than the theorem
  it arrived with.
- **An unrequested fidelity check** establishing that this hunt's
  hand-derived kernel closed form really is the autocorrelation it was
  meant to be - closing a defect class that had already bitten twice.
- **What it did not do**: notice prior art (submission 5 is a corollary
  of the source paper's own lemmas; the prover said nothing about
  novelty because it was not asked, and the resulting overclaim was
  entirely the coordinator's), choose targets, or judge significance.
- **What it cost**: two full rebuilds, both caused by the coordinator
  shipping project directories without the artifacts their briefs told
  the prover to reuse.

The load-bearing observation for `meta/`: across nine submissions the
prover's highest-value outputs were the three occasions it contradicted
its instructions, not the theorems it produced on request. n = 9, one
hunt, self-reported.


## The negative-margin question, closed: instrument artifact (2026-08-13)

Instruments: `negative_margin_probe.py`, `adversary_evolution.py`, and
their tests (78 tests, 39 min, all passing). Both modules survived a
container restart that killed their agents; they were run directly.

| Obligation | Status | Evidence |
|---|---|---|
| **Is the crossing at m = 24 real?** | **NO - INSTRUMENT ARTIFACT, MECHANISM NAMED** | it is a property of the settings, not the configuration. **The dominant channel is the per-pair tail allowance at G = 60: 0.027096, i.e. 20.9% of b_inf, which the periodic instrument it is compared against does not pay at all.** An apples-to-oranges comparison |
| Which refinement clears it | **THE WINDOW, NOT THE GRID** | refining the grid step alone moves the crossing out (m* = 24 / 48 / 64 / beyond) but leaves the m -> infinity margin negative at G = 60 at every step measured. Refining the window clears it: no negative m at G >= 120, and the limit margin is positive there at both readings |
| Attribution, quantified | RECORDED | at m = 24 the cap runs 0.134657 -> 0.128546 (step) -> 0.115805 (window) -> 0.109741 (both); step channel +0.006110, window channel +0.018852 - the window is 3.1x the grid |
| Ball-arithmetic decision | **DECIDED POSITIVE** | 128-bit enclosures, one-sided: m=24 G=60 margin_lo +0.003822; m=24 G=200 +0.022650; the worst pinned case (m=64, G=60) flips -0.000211 -> +0.000345 on a single fine-step refinement, i.e. it sat inside the instrument's own noise |
| Largest theta that closes | **0.995** | 0.999 opens (-0.293); theta = 1 diverges in both float and ball arithmetic |
| **Independent second opinion** | **AGREES** | `adversary_evolution`: **20421 scored configurations, none reached a nonpositive margin**, worst promoted relative margin +0.154966. Planted-inflation control has power (inflate 4.0 finds 33 negatives) |
| Its own honest scoping | RECORDED VERBATIM | "This bounds the adversary from below and the quantifier not at all" |

Disposition: **THE RETENTION SURVIVED ITS FIRST SERIOUS ATTEMPT AT
REFUTATION.** Three routes - window/grid refinement with the channel
attributed, ball arithmetic at 128 bits, and a 20421-configuration
adversarial search with demonstrated detector power - agree that
theta = 0.995 holds and that the crossing was the instrument. The
quantifier over all configurations remains open and is unaffected by
this; what closed is the suspicion, not the obligation. No proportion is
claimed to have moved.


## Blocker 2, the retention at realistic separation: DELIVERED at delta = 4 (2026-08-13)

Instrument: `zeta23ext/Zeta23Ext/EForm3/` (theorem-proving service,
project fbb89dd4, 2h42m; 12 modules, 2571 lines, sorry-free, no
native_decide, every theorem on propext / Classical.choice / Quot.sound).

| Obligation | Status | Evidence |
|---|---|---|
| **Retention for ALL n under separation** | **DELIVERED AT delta = 4**, better than the delta = 2 pi requested | `retention_separated_of_le`; `retention_separated` at 2 pi is a corollary; `retention_le_three` still needs no separation at all |
| **In mean gaps** | **0.6366 mean gaps** | the hypothesis went 4.1380 -> 0.6366 mean gaps across two iterations, i.e. from four times the mean spacing of on-line zeros to about two thirds of it |
| **Task (1) of the brief is FALSE, and is now a Lean theorem** | **KERNEL-CHECKED REFUTATION OF THE COORDINATOR'S INSTRUCTION** | `no_second_order_far_field : not exists C, forall y s, ... \|Qim y s\| <= C y/s^2`, with the matching lower bound `Qim_lower_at_even_multiple` giving `\|Qim\| >= 0.7 y/s` along s in 4 pi Z, which beats any C y/s^2 for s > (10/7) C. Structural cause: the window jumps at +/- 1/2 since cos(1/sqrt2) ~ 0.76 != 0, so the second integration by parts leaves a non-vanishing boundary term |
| **What actually bought the improvement** | **NOT the exponent - the interference** | keeping the sqrt2-interference in the numerator instead of taking absolute values: the two shifted poles partially cancel and the majorant near the near/far threshold drops by a factor ~2.6 |
| The far-field majorant | PROVED | `Qim_far_sq`: `Qim^2 <= y^2 Wt(s^2 - 2)` for s >= 28/5, `Wt w = (5/8)/w + (611/50)/w^2 + (6711/100)/w^3 + (2583/25)/w^4`; `Qim_far_first_order`: `\|Qim\| <= (6/5) y/\|s\|`, the true order |
| The near field | PROVED DAMAGE-FREE | `uniform_damage`: `Qim^2 - Qre^2 <= 0.0383 y^2` for every s; the split uses a damage-free near field \|s\| <= 28/5 and two far-field wings compared through a rank function against the progression 28/5 + 4m, with the majorant sum <= 0.0614 as nine explicit terms plus a telescoping tail |
| Budget | **5.7% margin** | gain `Shq y/2 >= 0.129861 y^2` against damage `<= 0.1228 y^2` |
| Its own stated limit | RECORDED | the first far-field offset alone costs 0.0383 y^2 per wing, so this route cannot go much below delta ~ 3.5 without also moving the near-field threshold |
| **The empty-directory cost, restated by the prover** | CONFIRMED | none of EForm2's results were present; definitions, integrability, the master identity, closed forms, Taylor and numeric bounds, near and far field estimates, counting and the retention theorems were all rebuilt from the brief. Coordinator defect #16, now measured: ~2571 lines rebuilt |

Disposition: **A REAL IMPROVEMENT, AND THE SEPARATION ROUTE CANNOT CLOSE
BLOCKER 2 AT ANY delta.** Two iterations moved the hypothesis from 4.14
mean gaps to 0.64, and the coordinator's erroneous instruction is now a
kernel-checked falsity in the tree - the most direct form this ledger's
defect record has taken. But see the correction below before reading the
delta as small enough. No proportion is claimed to have moved.

### CORRECTION, same session: "weaker than the typical spacing" was wrong

Coordinator defect #17, caught by the operator asking "are you sure".

The hypothesis is `x_i + delta <= x_{i+1}` for **every** consecutive
pair. The coordinator reported delta = 4 = 0.6366 mean gaps as "now
weaker than the typical spacing of on-line zeros, rather than four times
stronger". That is true of the **mean** and false of the **requirement**.

Zero gaps follow GUE statistics (Montgomery). Under the Wigner surmise
for beta = 2 (normalisation checked, int p = 1.000000):

| normalised gap x | P(gap < x) |
|---|---|
| 0.2000 | 0.0084 |
| 0.4000 | 0.0613 |
| **0.6366 (= delta 4)** | **0.2065** |
| 1.0000 | 0.5331 |

So roughly **21% of consecutive gaps fall below the hypothesis** - about
207 violations in a run of 1000 on-line zeros. A generic real
configuration does not satisfy it, and never will:

**The structural consequence.** Real zero gaps have no positive lower
bound, so a separation hypothesis of ANY positive delta fails on a
positive fraction of configurations. **The separation route cannot close
blocker 2 unconditionally at any constant, however small.** Driving
delta from 26 to 4 to 3.5 buys plausibility, not closure.

What closure would need instead: the near-coincident case handled by the
**repulsion** rather than excluded by hypothesis - clustered on-line
points inflate R, which is the term that pays for the damage, so the
configurations the separation hypothesis excludes are exactly the ones
where the budget is largest. That trade is visible in the exact gap
identity and is not being used. It is the natural next target, and it is
a different lemma from the one just proved.


## The spectral form of the gap, and a coordinator claim refuted by its own module (2026-08-13)

Instrument: `spectral_gap.py` (coordinator-built while four agents worked
the near-coincident case).

| Finding | Status | Evidence |
|---|---|---|
| **The gap is ONE convex functional of the on-line sum** | **EXACT, checked to 6.7e-16** | `gap A^2 = (1/200)[int c2 \|F\|^2 - n A^2] + 4 int c2(w) e^{-yw} Re[e^{-itw} F(w)] dw + 8 A Shq + 8 Shq^2` on five configurations including a tight cluster and a unit lattice |
| Step 1 | exact, 2.2e-17 | `ghat(s + iy) = Pre(y,s) + i Qim(y,s)` - the two transform components are one complex transform |
| Step 2 | exact, 1.1e-16 | `Pre^2 - Qim^2 = Re[c2hat(s + iy)]` - **the damage profile is the c2-transform at a complex argument**, which is what collapses two kernels into one |
| Step 3 | exact, 8.9e-16 | `sum_{j,k} phiR(x_j-x_k)^2 = int c2 \|F\|^2` since `c2hat = \|ghat\|^2 = phiR^2` (Bochner; c2 >= 0) |
| Why it matters | STRUCTURAL | the repulsion and the damage were being handled by separate machinery - band covers for one, near/far splits for the other. They are the quadratic and linear parts of a single functional against a single positive measure |
| **COORDINATOR DEFECT #18** | **CLAIM REFUTED BY THE MODULE'S OWN AUDIT, WITHIN A MINUTE** | the docstring asserted that since the quadratic coefficient is positive, clustering raises the gap, so "the separation hypothesis was excluding the safe cases". The audit printed the opposite in the same run |
| The confound | FOUND | the first experiment varied cluster spacing without holding the centre, so the cluster drifted off the damage peak. It was measuring escape, not clustering |
| **The trade, measured properly** | **NON-MONOTONE** | centre fixed at the damage peak (offset 6.517, y = 0.49), gap by cluster size at spacing 0.01: m = 1..6, 8, 12, 16 gives 0.1335 / **0.1235** / 0.1236 / 0.1337 / 0.1538 / 0.1840 / 0.2747 / 0.5776 / 1.043 |
| Direction, corrected | **SEPARATION EXCLUDED THE DANGEROUS CASES** | a tight PAIR on the damage peak is the worst configuration in this family; separation is exactly what forbids it. The coordinator had told the operator the opposite |
| The good news that survives | **THE WORST IS +0.1235, POSITIVE WITH ROOM** | and the minimum over cluster size is at m = 2, not at either extreme: the m^2 repulsion overtakes the m damage from m = 4 on. Away from the damage peak clustering helps at every m (4.245 -> 12.408) |
| What this buys | A BETTER-SHAPED SEARCH | the adversary's best play in this family is a PAIR at the peak, and it does not win. That is a two-parameter question, not a search over all configurations |

Disposition: **THE REFORMULATION IS REAL AND THE INTERPRETATION WAS
WRONG.** The identity is exact and collapses the problem to one convex
functional; the coordinator's reading of what its positive quadratic
coefficient implied was refuted by the module's own measurement inside a
minute, and the operator was told the wrong thing in between. What
stands: the worst configuration in the clustered family is a pair on the
damage peak at +0.1235, and the repulsion does win from m = 4 upward. No
proportion is claimed to have moved.


## The SINGLE-PAIR retention closed at hardened grade: the repulsion pays for the damage (2026-08-13)

**HEADING CORRECTED — coordinator defect #19.** This entry was first
written, committed and pushed under the heading "BLOCKER 2 CLOSED".
That was an overclaim by one quantifier; it is corrected here rather
than rewritten away. What closes below is the `k = 1` layer: retention
for **one** pair block, every `n`, every `t`, every `y in [0,1/2]`, with
no separation hypothesis. Blocker 2 as originally posed (2026-08-12,
"the per-pair route is refuted") is the **multi-pair** quantifier
`E[F_on + F_p] >= theta E[F_on] + (1-theta) n + 4k` with `F_p` carrying
`k` blocks at different depths and centres. That is **still open**, and
`cluster_sdp.py` now names why this accounting does not extend to it —
see the `k >= 2` row at the end. Recent entries had drifted into using
"blocker 2" for the single-pair retention quantifier; the two are not
the same statement, and the drift is what let the overclaim through.

Instruments: `near_coincident.py` (40 tests), `repulsion_trade.py` (55),
`exact_gap_attack.py` (32) — three agents, three independent routes, run
without sight of each other. Plus an independent coordinator
reproduction written from `EForm3/Defs.lean` alone
(`scratchpad/verify_lemma_c.py`, imports nothing from this directory).

### The reduction (algebra, on two kernel-checked theorems)

`retention_gap` and `energy_F` are already sorry-free in the tree.
Substituting both into the obligation and cancelling gives, with
`D(y,s) = Qim^2 - Qre^2` the damage of one offset and
`phi_r = Qre 0` the window transform:

    margin  =  E[F+P] - (199/200) E[F] - n/200 - 4  =  (4/A^2) * slack,
    slack   =  Shq(y)/2 - sum_j D(y, x_j - t) + (1/400) sum_{j<k} phi_r(x_j - x_k)^2.

The third term is exactly what `retention_of_damage` discards when it
uses `energy_F_ge` (`E[F] >= n`) instead of the identity. It is the
**repulsion**: two offsets a distance v apart relax the damage budget by
`phi_r(v)^2/400`. Coordinator re-derived this by hand and checked it
against the definition route (Gauss-Legendre on `Eng`) at dps=40 on six
configurations: worst residual **3.95e-17**.

### Why the repulsion is not optional

| Finding | Status | Evidence |
|---|---|---|
| `retention_of_damage`'s hypothesis is **false from n = 8** | MEASURED, two agents independently | 8 offsets on the peak: `8 x 4.396424e-03 = 3.5171e-02 > Shq/2 = 3.3754e-02`; seven fit, eight do not |
| Consequence | **NO sharpening of the damage constants can close blocker 2** | the route that drops the repulsion term is arithmetically dead, not merely lossy |
| Consequence for defect #17 | its verdict stands and is now moot | separation cannot close blocker 2 at any positive constant; it does not have to |

### The closure (window decomposition)

`D(y, .)` is positive only on windows around the zeros of `phi_r`.
Measured at `y = 1/2`, reproduced by the coordinator independently:

| structural fact | agent value | coordinator value |
|---|---|---|
| innermost window edge (no damage inside) | 6.0653188 | **6.06531877311** |
| max window width `w_max` | 0.9860008 | **0.9860007073** |
| min gap between windows | 5.18297 | **5.182969399** |
| `gamma = phi_r(w_max)`, `phi_r` nonincreasing on `[0, w_max]` | 0.88452 | **0.8845197389**, nonincreasing: yes |
| top peak `D_1` and its position | 4.396424e-03 at 6.517 | **4.396424118e-03 at 6.516999776** |

Two offsets in one window are at most `w_max` apart, so each such pair
relieves at least `gamma^2/400`; offsets outside every window do no
damage; cross-window relief is discarded. The problem decouples window
by window and the per-window maximum is over an **integer**
multiplicity — which is the whole point, since the real relaxation is
unbounded below (see below):

    sum_j D_j - (1/400) sum_{j<k} phi_r^2  <=  sum_k max_{m in Z>=0} [ m D_k - (gamma^2/800) m(m-1) ]

| quantity | near_coincident | repulsion_trade | exact_gap_attack | coordinator |
|---|---|---|---|---|
| bound on net damage, `y=1/2` | 1.95721e-02 | 1.9617e-02 | — | **1.9447e-02** (60 windows) |
| `Shq/2` | 3.37542e-02 | 3.3754e-02 | — | **3.375420393e-02** |
| safety factor | 1.7246x | 1.72x | 1.724x | **1.7357x** |
| margin lower bound | 6.72091e-02 | — | +0.06718 | **6.780e-02** |

Maximising multiplicity: **3 on the innermost window of each side, 1 on
every other** — all four instruments agree. `y = 1/2` is the binding
depth (the relief carries no `y^2` while damage and budget both do):
coordinator's net/budget ratio runs 0.3915 / 0.3925 / 0.3942 / 0.4658 /
**0.5725** at `y = 0.1 ... 0.5`.

### The majorant is conservative where it counts

Coordinator evaluated the **exact** slack at the majorant's own
extremal profile and around it:

| test | result |
|---|---|
| exact net damage at the extremal profile | 0.017960 <= majorant 0.019278 |
| spreading the clusters (0 -> 0.986) | net damage falls 0.01796 -> **-0.05349**; coincidence is the dangerous end |
| multiplicity on the top window, m = 1..12 | worst at **m = 3** (0.017960), then falls; m = 6 already negative net damage |
| uniform multiplicity m on all 25 windows | m=1 net 0.013092, m=2 **-0.079993**, monotone down to m=8 |

So the `m^2` repulsion overtakes the `m` damage exactly where the
majorant says it does, and no configuration in any of the four searches
(three agents' ~70k configurations, free-position annealing to n=64, plus
the coordinator's own) produced negative slack.

### Why a convex relaxation cannot do this (agent 3's negative result)

Over nonnegative **measures** the infimum is `-1/200` per unit mass and
crosses zero at n = 23 (`y=1/2`); it falls without bound. Mass can leave
as dust: spread thin it pays no self-energy and collects no damage. The
minimiser is fractional (2.078 at the first window) and unrealisable.
`-n A^2` is the self-energy of `n` **unit atoms** and only integrality
pays it back — so **no convex relaxation of the atom constraint can
close this**, and the SOS/Gram route closed earlier (`sos_certificate.py`)
was closed for the same underlying reason.

### The exact-rational certificate

`exact_gap_attack.rational_certificate` re-runs the bound in
`fractions.Fraction` on the tree's own kernel-checked constants —
`Wt` (`FarField.Qim_far_sq`) and `Shq_half_lower` — plus a 9-window
table with rational endpoints, `K >= 39/50` on `|u| <= 1` and
`K >= 1/125` on `|u| <= 6`:

    deficit 7.9451178e-02   budget 1.2986e-01   surplus 5.0408822e-02 > 0
    margin 1.6345x, gap >= 0.0597, as a statement about rationals.

Coordinator re-checked the one undocumented constant in it (`637/1000`,
the far-tail coefficient): it is a sound rational majorant of
`s^2 Wt(s^2-2)`, which is 0.62508 at s=400 and decreasing to 5/8. The
code does not say where it came from — a documentation defect, logged,
not an arithmetic one.

### Grade, stated exactly

| layer | grade |
|---|---|
| `margin = (4/A^2) slack` | algebra from two **kernel-checked** theorems; the Lean proof is `linarith` from `retention_gap` + `energy_F` and is not yet written |
| the integer square completion per window | elementary, not yet written |
| `K >= 39/50` on `\|u\| <= 1`, `K >= 1/125` on `\|u\| <= 6` | one-variable bounds on an explicit elementary function, not yet written |
| **the 9-window table** (endpoints and damage caps on `[28/5, 60] x [0, 1/2]`) | **the real remaining cost**: a two-variable interval-arithmetic statement, the analogue of the `BandCert` leaf tables already in this package |
| the whole chain | **HARDENED**, not kernel-checked |

### The fourth route, and the quantifier it does NOT reach

`cluster_sdp.py` (86 tests) came in last, from the SDP/moment side, and
lands on the same accounting from a different direction — a fourth
independent agreement.

| Finding | Status | Evidence |
|---|---|---|
| Window occupancy bound, single pair | **+0.000932 (y=0.05) … +0.0672 (y=0.5)** | positive at every depth, 42–60% of budget surviving; `+0.0672` against `exact_gap_attack`'s `+0.06718` and the coordinator's `+0.0678` |
| Its moment-program form picks the true minimiser blind | STRUCTURAL | 2.63 atoms at `±6.5`, one each at `±12.5`, `±19` — the `3,1,1,…` schedule all four instruments found |
| **A closed form for the far-field peak envelope** | **DERIVED, rel. err 3.0e-4** | `D_j s_j^2 -> 2 cos^2(1/sqrt2)(cosh y - 1)`; coordinator measured `0.1475305` against the closed form `0.1475273` at `s` up to 502 |
| Consequence | **it replaces the certificate's one measured constant** | the `637/1000` far-tail coefficient above was standing in for exactly this; the closed form makes the tail derivable rather than read off a scan |
| Normalisation trap, noted | `psi = ghat/A`, so `cluster_sdp`'s `-4 Re psi^2` is `4/A^2` times the damage used elsewhere in this hunt | the raw numbers differ by 1.185 and look like a discrepancy until converted — the fourth such normalisation collision in this hunt |
| `cone_violator` excluded, and by which constraint | MACHINE-CHECKED | the depth cap kills it at the published `t=1/2`; at the largest depth-admissible `t=0.1400` it still violates and **(T3)** kills it — cross entries purely imaginary give `Re(C^2) = -0.0196` where (T3) allows only `-0.0052`, short by 3.76x. Pinning its moments returns `infeasible` at every `t`, `n = 3,4,6`; lesion control drops below the witness with (T2)/(T3)/(T4) deleted |
| **`k >= 2`: NOT reached, reason named** | **OPEN, on the BUDGET side** | the same accounting needs `budget(P) >= 0.5799 sum_p slack(y_p)`; `joint_universal` measures the floor at `0.2918 sum_p slack(y_p)` (500 restarts, binding shape a lattice at 1.005 mean gaps). **Short by a factor 1.99.** Not the damage side |
| Why it does not extend for free | an on-line atom can sit in one damage window **of each pair at once**, so the damage side scales with `k` while the budget does not — slack additivity is false and signed (ledger 2026-08-12: the pair term runs `+8.31` to `-0.756`) | |
| Entry-level SDP, size independence | **PROVABLY INSUFFICIENT past n = 7.68** | a dual with no size in it gives `Xi >= (d^2-1)(2 - 4 n C_D)`; counting how many atoms fit in a damage window is degree >= 3 in the entries, so no degree-2 cut on pairs of entries can supply it. Same shape of finding as `inertia_multiplier` |

### Grade and quantifier, stated exactly

**What is closed**: the `k = 1` retention inequality — one pair block,
**every** `n`, every `t`, every `y in [0,1/2]`, with **no separation
hypothesis** — at **hardened** grade, by four instruments that agree to
three digits plus one exact rational certificate and one independent
coordinator reproduction. That is strictly stronger than what the tree
carries (`d >= 4`, or `n <= 3`), and it retires the separation route
rather than improving it.

**What is not closed**, both named:

1. **Formalisation.** None of it is in Lean. The remaining cost is the
   9-window interval table above; the other three obligations are
   hours, not research.
2. **The multi-pair quantifier — blocker 2 proper.** `k >= 2` is open
   and the obstruction is arithmetic, not presentational: budget floor
   `0.2918` against a requirement of `0.5799`, a factor **1.99** on the
   **budget** side. Closing `k = 1` does not close it, and no argument
   that charges damage per pair can — that is the same superadditivity
   that refuted the per-pair route on 2026-08-12.

No proportion has moved and nothing here is evidence about RH.


## The k-pair identity, and coordinator defect #20 (the over-correction) (2026-08-13)

Instrument: `kpair_identity.py`, `test_kpair_identity.py` (19 tests).
Prompted by the operator asking "are you sure?" about the entry above.

**COORDINATOR DEFECT #20, the mirror of #19.** Having caught himself
overclaiming the `k = 1` closure as blocker 2 (#19), the coordinator
then reported `cluster_sdp`'s factor 1.99 to the operator as though it
were an obstruction to the `k >= 2` **statement**. It is an obstruction
to that **accounting**. Both defects have the same cause: taking a
report's framing instead of deriving the object. So the object was
derived.

### The identity nobody in this hunt had written down

Expanding `|F + P|^2` with `P w = sum_p 2 cosh(y_p w) e^{i t_p w}` and
integrating each piece against `c2`:

    margin_k = E[F+P] - (199/200) E[F] - n/200 - 4k = (4/A^2) * slack_k

    slack_k = sum_p Shq(y_p)/2
            - sum_p sum_a D(y_p, x_a - t_p)                   (damage)
            + (1/400) sum_{a<b} phi_r(x_a - x_b)^2            (repulsion)
            - (1/2) sum_{p!=q} [D(y_p+y_q, tau) + D(y_p-y_q, tau)]

Checked against the definition route (quadrature on `Eng`, sharing no
code) for `k = 1..4`, mixed depths and shifts: worst residual
**4.21e-17**. At `k = 1` the last sum is empty and this is exactly the
single-pair slack the entry above closes.

### What it settles

The worry that motivated the pessimism is real and visible in the
identity: **the repulsion term carries no `p` index**. It is paid once
however many pairs there are, while the damage is summed over them, so
relief per pair goes like `1/k`. That reading is still wrong, and the
identity says why — the adversary has exactly two routes and both pay:

| route | what it costs the adversary | measured |
|---|---|---|
| **spread the centres** so each pair sees the atoms at a damage peak | only **two** positions carry the top peak (`+/- 6.517`); the rest decay like `1/s^2`, so `damage/gain` falls | 1.0420 at `k = 1` and `k = 2`, 0.6365 at `k = 4`, 0.4578 at `k = 6`, **0.2483 at `k = 12`** |
| **stack the centres**, keeping `damage/k` maximal | coincident centres contribute `D(2y,0) + D(0,0) = -(ghat(2y)^2 + A^2)`, which enters `slack_k` with a minus sign — a **gain** of `1.7556` per ordered pair | slack `+1.81` at `k=2`, `+49.4` at `k=8` |

Neither route is visible to an argument that charges damage per pair,
which is exactly what `multi_pair_requirement` does. Its 1.99 compares a
per-pair damage charge against a joint budget floor; the identity shows
the two are **maximised by different configurations**, so the factor
does not bound the truth.

### The joint search, and its power

Minimising the **relative** margin `slack_k / sum_p Shq(y_p)/2` over
atoms, centres and depths jointly (annealing, `n <= 24`, 60 restarts per
`k`). The relative form matters: the coordinator's first search minimised
the absolute slack and collapsed into the degenerate `y -> 0` corner
where gain, damage and repulsion all vanish together — and the planted
fault correctly refused to fire at `x1.5` and `x2.0`, which is what
exposed the bad objective.

| k | 1 | 2 | 3 | 4 | 6 |
|---|---|---|---|---|---|
| worst relative margin | +0.4915 | +0.3719 | +0.3908 | **+0.3430** | +0.3618 |

No downward trend in `k`; the worst is `+0.343`, not near zero.
**Consistency check that the instrument is honest**: a worst relative
margin of 0.343 predicts the first violation once the damage is inflated
by `1/(1-0.343) = 1.522`, and the planted-fault ladder first returns
negatives at `damage_scale = 1.5` (clean at 1.0, `-0.171` at 1.5,
`-0.918` at 2.0, `-2.908` at 3.0). Prediction and detector agree.

### Disposition

**THE CORRECTION WAS RIGHT AND ITS CONSEQUENCE WAS OVERSTATED.** Blocker
2 is the multi-pair quantifier and the entry above closes only `k = 1`
— that stands (#19). But `k >= 2` is **not** short by 1.99x as a
statement: at hardened grade its relative margin is `+0.343` at the
worst `k` searched, with the mechanism named (peak decay on one side,
coincident-centre shielding on the other) and an exact identity to state
it in. What `cluster_sdp` measured is that **one particular accounting**
does not extend, which is a fact about the accounting.

`k >= 2` remains open as a theorem: this is an identity plus a search
over `k <= 6`, `n <= 24`, and named gaps N1–N5 in the module say so. No
proportion has moved and nothing here is evidence about RH.


## The two arms compute one function: ghat(z) = Phi2(-i z) (2026-08-13)

Instrument: `arm_identification.py`, `test_arm_identification.py`
(39 tests). Found while scoping the k=1 formalisation, by reading
`BandCert/Phi.lean` to copy its table pattern.

This hunt grew two independent certification efforts and neither knew
about the other:

* **BandCert** (2283 lines, sorry-free) encloses the paper field
  `Phi2(z) = s(z+sqrt2) + s(z-sqrt2)`, `s(u) = sin(u/2)/u`, on
  fixed-point interval arithmetic at `2^-64`.
* **EForm3** works the retention inequality through `Qre`, `Qim` and
  `D(y,s) = Qim^2 - Qre^2`, built from
  `ghat(z) = int cos(sqrt2 u) cosh(z u) du`.

They are the same function:

    ghat(z) = Phi2(-i z)      for every complex z.

One line: `ghat` has the closed form `sinh((z +/- i sqrt2)/2)/(z +/- i sqrt2)`
summed over signs, and `sinh(i w/2)/(i w) = sin(w/2)/w = s(w)`, so
substituting `z = -i w` turns each `ghat` branch into an `s` branch of
`Phi2`. Measured residual over 27 curated points and a 1600-point grid
over the strip: **exactly 0.0** — not small, bit-identical, because after
the rotation the two closed forms are the same expression. `A = Phi2(0)`
to the last bit, and `phi_r(v) = Phi2(v)` on the real axis, which is
`BandCert.Phi.phiR`.

| consequence | detail |
|---|---|
| **The k=1 table is not the ANALOGUE of the BandCert leaves, it is an INSTANCE** | the entry of 2026-08-13 called it "the analogue of the `BandCert` leaf tables"; that understated the reuse |
| `Phi2` at a **complex** point is already kernel-checked | `BandCert.Phi.phiC` / `phiC_mem`, with `y != 0` |
| the complex interval layer assumed missing already exists | `CIv` with `add/sub/mul/div/mulR/ofR` soundness lemmas |
| the damage enclosure is three composition steps | `D(y,s) = -Re[Phi2(s - i y)^2]`: `phiC` at `(s, -y)`, square by `CIv.mul_mem`, negate the real part |
| obligation count | **7 of 12 already kernel-checked in BandCert**; of the 5 new, four are small (the `linarith` reduction, the wiring lemma, the integer square completion, two one-variable bounds on `phiR`) and **one** is the real cost: the cap table itself |

Two damage routes cross-checked over the obligation box
`y in {0.05 .. 0.5} x s in {6.0653 .. 59.9}`: residual **0.0**.

Disposition: **THE LARGEST REUSE FINDING IN THIS HUNT, AND IT WAS FREE.**
It cost one reading of a file the hunt already owned. What it buys is
that the single substantial obligation left on the `k = 1` chain runs on
machinery that already compiles with zero sorrys, rather than on
machinery that has to be built. Named gaps R1-R5 in the module: the
wiring lemma is derived on paper and checked numerically but is **not
written in Lean**, `phiC_mem`'s `y != 0` still needs its own `y = 0`
line, the table is **not built**, and none of this touches the `k >= 2`
quantifier, which stays open. No proportion has moved and nothing here
is evidence about RH.


## Both roads opened: the table is 196 cells, and the damage integral is negative (2026-08-13)

Instruments: `window_table.py` + `test_window_table.py` (Road A, 12
tests), `mean_damage.py` + `test_mean_damage.py` (Road B, 15 tests).
`ROADMAP-OPTIONS.md` priced both roads; this closes the first task on
each.

### ROAD A — the table is sized: 196 cells

The `k = 1` chain's one substantial formalisation obligation. Two sizing
attempts failed first and the failures were the method:

| attempt | outcome | why |
|---|---|---|
| cap each window, require `D <= 0` elsewhere | 6.36e6 cells, **99.995% undecided** | asking for `D <= 0` on a cell straddling a window edge is **unprovable by enclosure** — `D` is exactly `0` there |
| enlarge to fixed brackets, one wide ball per cap | still diverges; cap sum `3.54e-02` **exceeds** the budget `3.375e-02` | dependency blow-up: a half-width-`0.6` ball gives `2.73e-02` against a true peak of `4.40e-03`, **6x** |
| **locate true edges, pad outward, cap by subdivision INSIDE** | **196 cells, 0 undecided** | brackets sit strictly outside the windows so `D < 0` with margin off-bracket; caps are tight because the cells prove them |

At `y = 1/2`, `s in [5.6, 60]`, Arb at 128 bits: **9 windows** (widths
`0.960975 .. 0.986001`, first at `6.065319`, min gap `5.182969`), **9
brackets** padded by `0.25` and rounded outward to `1e-3` (min gap
`4.682`), **143 in-bracket cells** carrying caps `4.483880e-03` down to
`4.715629e-05`, **53 off-bracket cells** over 10 segments. Cap sum
`1.319090e-02` both sides against `Shq/2 = 3.375420e-02` — ratio
**0.3908**.

`196` sits inside `BandCert`'s existing `62 .. 248`. **The remaining
obligation is an ordinary instance of a pattern this package already
carries.** The depth reduction keeps it one-dimensional: `D(y,s)/y^2 <=
4 D(1/2,s)` shows 0 violations over 400 `s`-points x 6 depths, and closes
with margin `2.39x` because the budget coefficient `Shq(y)/2 / y^2`
*increases* in `y`, so its floor is `0.13087` at `y -> 0` against a
requirement of `5.487e-02`.

**Coordinator slip, caught by the module's own report**: the count was
written as `197` from a scratch run that rounded brackets to nearest;
rounding them outward (which is what soundness requires) gives `196`.
`test_stated_constants_match_the_generated_table` now pins all four
counts so the prose cannot drift from the computation again.

### ROAD B — the damage functional has negative total integral

The missing step was a quantitative form of "only two positions carry the
top peak". There is a sharper and entirely elementary statement.
`-D(y,s)` is the Fourier cosine transform of `w -> c2(w) cosh(y w)`,
continuous and supported on `[-1,1]`, so Fourier inversion **at the single
point `w = 0`** gives

    int_{-inf}^{inf} D(y,s) ds = -2 pi c2(0),     INDEPENDENT OF y,
    c2(0) = 1/2 + sin(sqrt2)/(2 sqrt2) = 0.84922799931830418,
    int D ds = -5.3358568877622847.

| check | result |
|---|---|
| `c2(0)` closed form vs quadrature | `\|diff\| = 0.0` |
| truncated integral at 5 depths | spread across `y in [0.05, 0.5]` is `1.2e-05` — flat, as the identity says |
| tail behaviour | residual shrinks with `S`, consistent with the `O(1/S)` truncation of a `1/s^2` tail |
| mean collectable damage `int C(t) dt / 2L` vs `n int D / 2L` | four digits, for coincident **and** spread atom sets |

**What it buys.** For a fixed on-line multiset, the damage a pair centred
at `t` collects has *negative mean over placements*, at a rate that does
not weaken with depth. A pair placed at random collects negative damage;
positive collection requires landing in one of the narrow windows — and
the windows are exactly what the `k = 1` accounting already controls.
This is the right shape for `k >= 2`, where the difficulty was that
damage sums over pairs while the repulsion is paid once.

**What it does not buy**, stated in `NAMED_GAPS` M1-M5: it bounds the
*mean*, and the adversary chooses placements rather than drawing them.
Converting it into a bound on `sum_p C(t_p)` needs a count of how many
`t` can have `C(t)` large, which is **not** supplied. This is step 1 of
Road B, not Road B.

Disposition: **BOTH ROADS ARE OPEN AND NEITHER IS BLOCKED.** Road A's
cost is now known and small; Road B has an exact, depth-free, elementary
identity where it previously had a measured mechanism. `k >= 2` remains
open, nothing is kernel-checked yet, no proportion has moved, and nothing
here is evidence about RH.


## ROAD B, step 2: the slack is three terms and two of them are free (2026-08-13)

Instrument: `gram_form.py`, `test_gram_form.py` (20 tests).

The `k >= 2` difficulty was stated for two days as "the repulsion is paid
once while the damage sums over pairs". Rewriting the slack against the
measure `c2 dw` shows the difficulty is somewhere else, and isolates it.

### The kernel is positive definite

`-D(y,s) = int c2(w) cosh(y w) cos(s w) dw` is the Fourier transform of
`c2(w) cosh(y w) dw`, a **positive** measure on `[-1,1]` — `c2 = g * g`
is the autocorrelation of a nonnegative window and `cosh > 0`. By Bochner
`K_y := -D(y,.)` is positive definite. Measured min eigenvalue
**`1.03e-08`** over 200 random Gram matrices, **`-6.06e-16`** (numerical
zero) over the binding structured sets.

### The three-term form

    slack_k  =  B(T,y)  +  Cross(X,T,y)  +  R(X)/400
    B(T,y)   = int c2(w) [ cosh^2(y w) |That(w)|^2 - k ] dw
    Cross    = - sum_{a,p} D(y, x_a - t_p)
    R(X)     = sum_{a<b} phi_r(x_a - x_b)^2

Against `kpair_identity`'s direct evaluation: worst residual over 40 random
instances **`< 1e-12`**. `B` against its Gram form
`(1/2)[G_T(2y) + G_T(0)] - k A^2`: **`1e-25`**.

| term | status | why |
|---|---|---|
| `B >= 0` | **FREE, from a kernel-checked theorem** | `int c2 \|That\|^2 >= k A^2` is `Retention.energy_F_ge` applied to the pair centres; `cosh^2 >= 1`; `c2 >= 0`. The three compose in one line. Measured min over 400 random pair sets: `2.06e-05 > 0` |
| `R >= 0` | **FREE, trivially** | `K_0(v) = phi_r(v)^2`, so `R` is a sum of squares |
| `Cross` | **the whole difficulty** | the only term that can be negative |

So `slack_k >= Cross`, and `k >= 2` reduces to the single statement
`B + R/400 >= sum_{a,p} D(y, x_a - t_p)`.

### B is the correct budget, and `k Shq/2` never was

| configuration | `B` | `k Shq(y)/2` |
|---|---|---|
| `k = 1` | 0.033754204 | 0.033754204 |
| 10 pairs on window positions | **0.151405927** | 0.337542039 |
| 6 coincident pairs | **26.536840499** | 0.202525224 |
| 8 on a `2 pi` lattice | **0.102187070** | 0.270033631 |

At `k = 1` they agree exactly (diff `< 1e-13`). Beyond that they are not
close in either direction. **This is what the 2026-08-12 finding that
slack additivity is "false and signed" actually was**: the additive
budget was an artifact of the decomposition, and `B` has no additivity to
fail. A per-pair accounting was bounding a non-additive quantity by an
additive one — which is why `cluster_sdp`'s factor 1.99 could never have
closed, independently of how loose either side was.

Note the sixth row: coincident pair centres give `B` a factor **175x**
larger than ten spread ones. The measured "coincident-centre shield" of
`1.7556` per ordered pair is this, seen from the other side.

### The route that did not work, recorded so nobody re-derives it

Positive definiteness also gives Cauchy-Schwarz directly,
`sum_{a,p} D <= sqrt(S_X S_T)`. Measured against the budget it is **18x
to 111x too weak**, because it bounds `|sum K|` and discards the fact that
`D` is negative almost everywhere. Recorded as insufficient, with a test
pinning it so.

Disposition: **THE FRAME IS RIGHT AND TWO OF ITS THREE TERMS ARE FREE.**
`k >= 2` is now one inequality, `B + R/400 >= sum D`, with the budget in
its correct non-additive form and its nonnegativity resting on a theorem
already kernel-checked in this tree. It is **not proved** — named gaps
G1-G5 say which parts are paper-and-numerics rather than Lean. `k >= 2`
remains open, no proportion has moved, and nothing here is evidence about
RH.


## ROAD B, step 3: the counting lemma is "at most one pair per window" (2026-08-13)

Instrument: `counting_lemma.py`, `test_counting_lemma.py` (17 tests).
`gram_form` reduced `k >= 2` to `B + R/400 >= sum_{a,p} D` and named the
missing piece as a **count**. Two measurements supply it.

### 1. The counting lemma

Put `m` atoms and `j` pair centres in one damage window (width
`<= w_max = 0.9860008`). A **two-species** square completion closes iff
`D_1^2 <= 4 (gamma^2/800) kappa(w_max)`, and it does:

| quantity | value |
|---|---|
| damage per (atom, pair) | `D_1 = 4.396424e-03` |
| atom-atom relief per within-window pair | `gamma^2/800 = 9.779689e-04` |
| **pair-pair relief per within-window pair** | **`kappa(w_max) = 1.620239e+00`** |
| AM-GM condition | `1.932855e-05 <= 6.338174e-03` — **margin 327.9x** |

`kappa(w_max)` is **1657x** the per-pair atom relief. That asymmetry is
the whole content: the pair species cannot crowd. Maximising
`f(m,j) = m j D_1 - m(m-1) gamma^2/800 - j(j-1) kappa(w_max)` over
integers:

    j = 1:  +7.321459e-03  at m = 3   <- exactly the k=1 optimum, recovered
    j = 2:  -3.216073e+00
    j = 3:  -9.670185e+00

**A second pair in the same window is never profitable.** That is the
count `gram_form` said was missing, and it recovers the `k = 1` answer as
its `j = 1` slice, which is the consistency check that matters.

### 2. The budget floor: `B/k` does not decay

`B` is not additive, so a "budget per pair" could in principle vanish as
`k` grows. Minimising over lattice spacings at `k = 64` puts the worst
case at `L = 6.30` — just past `2 pi`, the window period, which is where
`kappa` is most negative (`-1.82e-02`). Along that worst family:

| k | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 |
|---|---|---|---|---|---|---|---|---|
| `B/k` | 2.459e-2 | 1.749e-2 | 1.260e-2 | 9.492e-3 | 7.653e-3 | 6.680e-3 | **6.325e-3** | 6.392e-3 |

It **bottoms out near `6.3e-03` and turns back up**. Every pair carries a
budget bounded away from zero, uniformly in `k`.

### What this settles and what it does not

Together the two kill the configuration the `k = 1` analysis feared —
many pairs sharing one atom cluster's windows. It is **not** closure:
a single pair facing atoms at every one of its window peaks already
collects `1.372e-02`, against a floor of `6.3e-03`, so `R/400` stays
load-bearing and the shared-`R`-across-pairs question is untouched. What
is gone is the *unbounded* form of the worry.

**Test-caught coordinator slip.** `test_one_pair_at_every_window_peak`
first asserted the full-tail figure `1.372e-02` against a nine-window sum,
which is `1.2888e-02` — two different truncations quoted for each other.
The claim was unaffected (both beat the floor) but the test was wrong, and
it now pins both numbers and the inequality between them. Same family as
the `197`/`196` slip: a number carried across contexts without
re-deriving it.

Disposition: **THE COUNT EXISTS AND IT IS SHARP.** `k >= 2` remains open,
named gaps C1-C5 say which parts are measured rather than proved, no
proportion has moved, and nothing here is evidence about RH.

### CORRECTION, same day: coordinator defect #21 — two errors in the site model

Caught by the operator's "if you say so", which prompted checking the
site model against the exact slack instead of restating it. Both errors
were in the entry above; both are corrected in place.

**Error 1 — a factor of 2.** `site_value` used `j(j-1) kappa(w_max)` for
the pair relief. The `k`-pair identity sums over **unordered** pairs, so
the correct term is `j(j-1) kappa(w_max)/2`. Measured against the exact
slack: two coincident pairs relieve `1.75562102`, and the model claimed
`3.24047835`. Every derived constant was inflated with it:

| quantity | as first published | correct |
|---|---|---|
| AM-GM right-hand side | 6.338174e-03 | **3.169087e-03** |
| AM-GM margin | 327.9x | **164.0x** |
| `kappa` vs per-pair atom relief | 1657x | **828x** |
| `j = 2` site value | -3.216073 | **-1.595834** (at m = 5) |
| `j = 3` site value | -9.670185 | **-4.809467** (at m = 7) |

**Error 2 — the logic ran the wrong way, which is the worse one.** The
entry said "maximising `f(m,j)` over integers ... a second pair in the
same window is never profitable", as though `f` bounded what the
adversary gains. It does not. `f` uses the conservative constants, so
`f >= B - slack`, i.e. **`slack >= B - f`**: `f` *understates* the slack
because it discards the budget entirely. Measured — the exact slack
exceeds `f` at every occupancy tested, by `+0.025` at `(m,j) = (1,1)`,
`+5.05` at `(1,2)`, `+15.06` at `(1,3)`.

**What the corrected statement is.** `slack >= B - f`, so a site is safe
as soon as `B >= f`. At `j = 1`, `max_m f = 7.321459e-03` against
`Shq(y)/2 = 3.375420e-02` — a factor `4.61`. At `j >= 2`, `f < 0`, so
`slack >= B - f > B >= 0` outright. The conclusion — a second pair at the
same site is never the adversary's play — **survives both corrections**,
but it holds for a different reason than the entry gave, and with
constants half the size.

**A third thing the check surfaced.** "Put `m` atoms and `j` pairs in one
damage window" is not a coherent picture: damage needs
`|x_a - t_p| >= 6.0653`, so anything inside one window of width `0.986`
does *no* damage. A site is an atom cluster of diameter `<= w_max` and a
pair cluster of diameter `<= w_max` separated by about the peak distance
`6.517`. The arithmetic was right; the description was not.

Two regression tests now pin the factor against the exact pair relief and
pin `slack > f` at every occupancy, so neither error can return silently.

Disposition: **THE COUNT SURVIVES AT HALF THE CONSTANTS AND WITH ITS
LOGIC REVERSED.** Defect #21 joins #19 and #20 as the third correction
this session caught by an operator asking, in substance, "are you sure" —
and the third whose root cause was a quantity used without being derived
in the form it was being used. `k >= 2` remains open, no proportion has
moved, and nothing here is evidence about RH.

### CORRECTION TO THE CORRECTION: coordinator defect #22 (2026-08-13)

The operator asked "are you sure" a fourth time. The #21 correction above
introduced a new error, and this one was in the sentence that was supposed
to be the fix.

**The error.** #21's correction stated `slack >= B - f`. That is **false**.
`B` already absorbs `sum_{p<q} kappa`, and `f` subtracts `j(j-1)kappa/2`
again, so `B - f` charges the pair relief twice. Measured on the nine site
configurations `(m, j) in {1,3,5} x {1,2,3}`:

| pairing | violations |
|---|---|
| `slack >= B - f` (as published in #21) | **6 of 9** — every one with `j >= 2` |
| `slack >= k Shq(y)/2 - f` | **0 of 9** |

At `(m,j) = (3,2)`: exact slack `1.803081`, `B - f = 3.422858` — short by
a factor `1.9`.

**The correct statement.** `f` pairs with `k Shq(y)/2`, not with `B`,
because the identity it comes from is
`slack = k Shq/2 - sum D + R/400 + sum_{p<q} kappa`. Its three steps are
`sum D <= m j D_1`, `R/400 >= m(m-1) g^2/800`, and
`sum_{p<q} kappa >= j(j-1) kappa(W)/2` — the last requiring `kappa`
nonincreasing on `[0, w_max]`, now measured: `1.75562102` falling to
`1.62023918` with no interior minimum.

Every numeric conclusion of #21 survives unchanged; only the budget the
bound is compared against was mislabelled. `j = 1` still needs
`3.375420e-02 >= 7.321459e-03` (factor `4.61`) — that comparison was
always against `Shq/2`, which is why it read correctly.

Three regression tests now pin it: the wrong pairing must fail exactly 6
of 9, the right one must hold 9 of 9, and `kappa`'s monotonicity is
checked on a 200-point grid.

**The pattern, stated plainly.** #19, #20, #21 and #22 are four
corrections in one session, each caught by the operator expressing doubt
rather than by any check in this tree. Every one of them was a *framing*
error — a mislabelled quantifier, a bound relayed as a statement, a
double-counted term — while the underlying numbers survived each time.
The `meta/` entry filed earlier today names the missing capability as a
gate on relayed numbers; that is the wrong shape. The measured failure
mode is not bad arithmetic, it is **prose asserting a relation between
quantities that were never evaluated together**. The gate that would have
caught all four is cheaper: whenever a claim has the form `X >= Y`,
evaluate both sides on the configurations already at hand before writing
the sentence. Each of the four took under two minutes to refute that way.

`k >= 2` remains open, no proportion has moved, and nothing here is
evidence about RH.


## What survives 2026-08-13, measured rather than recalled

Instrument: `salvage_audit.py` — seven checks re-derived from
`EForm3/Defs.lean` alone, importing nothing from this directory.
**7 of 7 PASS.** The ten modules landed today also pass **340 tests**.

| claim | independent residual | status |
|---|---|---|
| `margin_k = (4/A^2) slack_k` (k = 1, 2, 3, by quadrature on `Eng`) | **4.21e-17** | STANDS |
| `ghat(z) = Phi2(-i z)` — BandCert and EForm3 are one function | **0.0** over 24 points | STANDS |
| `int D(y,s) ds = -2 pi c2(0) = -5.33585688776`, depth-free | spread across `y` **4.88e-05**; `c2(0)` closed form exact | STANDS |
| Bochner: `-D(y,.)` positive definite | min eigenvalue **-6.745e-16** over 63 Gram matrices | STANDS |
| **k=1 window bound, no separation hypothesis** | net `1.9447e-02` vs `Shq/2 = 3.3754e-02`, **safety 1.736x** | STANDS |
| window constants (first edge `6.06531877311`, `w_max 0.9860007073`) | to `1e-6` | STANDS |
| three-term Gram form `slack = B + Cross + R/400`, `B >= 0` | **7.89e-31**; min `B` positive | STANDS |

**Every one of the four defects (#19-#22) was in prose, not arithmetic.**
#19 mislabelled a quantifier, #20 relayed an accounting bound as a
statement bound, #21 doubled a term and inverted an implication, #22
double-counted the pair relief inside a fix. Not one touched a
computation, and the audit above separates the two cleanly: the modules
the defective sentences were describing all reproduce from scratch.

What is therefore **rescued and load-bearing**:

1. The `k = 1` retention inequality for every `n`, every shift, every
   depth in `[0,1/2]`, **with no separation hypothesis** — hardened
   grade, four independent instruments, an exact rational certificate,
   and now an eighth from-definitions reproduction.
2. `ghat = Phi2(-i .)`, which collapses two certification efforts into
   one and puts **7 of 12** Road A obligations on machinery that already
   compiles sorry-free.
3. The **196-cell** table spec, sized, all cells decided.
4. The `k`-pair identity and its three-term Gram form, with two of three
   terms free.
5. `int D ds = -2 pi c2(0)`, exact and depth-free.
6. Bochner positive definiteness.

What is **not** rescued: `k >= 2` is open; the Cauchy-Schwarz route is
recorded dead (18x-111x too weak); the site model's role is now only what
`slack >= k Shq/2 - f` says, which is weaker than the counting-lemma
framing first claimed. No proportion has moved and nothing here is
evidence about RH.


## ROAD B, step 4: the shared-R worry does not materialise (2026-08-13)

Instrument: `shared_repulsion.py`, `test_shared_repulsion.py` (15 tests).
The last open piece of `k >= 2` was that the atom repulsion `R` is paid
**once** while the damage sums over pairs. Every earlier search reached
only `n <= 24`, `k <= 6`; this goes to `n = 400`, `k = 60`.

| family (worst over sizes to `(400,60)`, incl. `n/k = 100`) | worst relative margin |
|---|---|
| atoms on a `2 pi` lattice, pairs on a `6.30` lattice | **+24.51** |
| atoms clustered, pairs on the window positions | +38.30 |
| atoms and pairs on one lattice, offset by the peak | +24.76 |
| atoms in many small clusters, pairs free | +14.17 |
| both free random | **+4.83** |

**No degradation with `n/k`**: along the first family the margin runs
`24.51, 24.72, 24.91, 25.06` as `(n,k)` goes `(50,2) -> (400,16)` — flat,
not falling. The worry predicts the opposite.

**The adversary's preference is the reverse of the worry.** Annealing
over both populations reaches its worst at **`n = 5`, `k = 23`** —
*few* atoms, *many* pairs, margin `+0.2716`. It starves the repulsion of
atoms rather than overwhelming it. The many-atom family becomes the best
play only at damage scales where the inequality has *already* broken
(`n = 87` at `x2.5`, `n = 94` at `x3.0`).

### The control, and the two negative results that make it honest

| damage scale | worst | n, k | |
|---|---|---|---|
| x1.0 | +0.2716 | 5, 23 | clean |
| x1.5 | +0.1309 | 19, 21 | clean |
| x2.0 | **-0.0895** | 25, 21 | **FIRES** |
| x2.5 | -1.2505 | 87, 9 | FIRES |
| x3.0 | -2.7047 | 94, 8 | FIRES |

**Negative result 1 — power is effort-dependent, and below the floor
this scan is worthless.** The `x2.0` rung does *not* fire at 20 restarts
x 5000 iterations (`+0.2651`), nor at 20 x 12000 on a single seed
(`+0.0023`). It fires only at 20 x 12000, best of 3 seeds. `EFFORT_FLOOR`
records the ladder and a test pins it, because the first version of this
scan reported "no violation" at an effort with no power — a verdict worth
nothing.

**Negative result 2 — a near-miss caught before landing.** An earlier
draft recorded `-0.5954` at `x2.0`. That number came from the
**scratchpad** implementation, not from the module being landed; the two
consume the RNG in a different order and the landed module does not
reproduce it. The module was held uncommitted until every recorded
number came from the code that ships. This is the same failure family as
defects #19-#22 — a quantity carried across contexts — caught this time
before publication rather than after.

Disposition: **THE SPECIFIC MECHANISM THE WORRY NAMED IS REMOVED, AND
THE RESULT IS EVIDENCE, NOT CLOSURE.** Named gaps S1-S6: the measured
worst is an **upper bound** that drifts down with effort (`0.343` ->
`0.3393` -> `0.2716`) and nothing says it stops above zero; the families
are lattices, clusters and randoms, so an adversary with unseen structure
is not excluded; `y` is fixed at the binding depth `1/2`. `k >= 2`
remains open, no proportion has moved, and nothing here is evidence
about RH.


## Two sessions measured O9 independently; the results reconcile (2026-08-13)

`claude/lab-rejection-philosophy` cherry-picked in (`ebf649c`, `b575100`):
`o9_scoping.py`, `test_o9_scoping.py` (18 tests, all pass here),
`O9-SCOPING.md`, `O9-BRIEF.md`. Their headline is **"the blocker is zero
margin, not table size"**, which is a claim about the same object
`window_table.py` sizes, so it needs reconciling rather than filing.

**Their finding, and it is correct.** The caps `c_k` as recorded in
`RETENTION-PROBLEM.md` §4 are defined as the *supremum* of `Dam/y^2` over
each window box, rounded up. They recomputed all nine and found the
supremum **attained at an interior point of every window**, always at
`y = 1/2`, ratio `1.0000` to four figures. An inequality that is an
equality somewhere has no margin, and no enclosure can discharge it: any
ball containing the argmax has an upper bound strictly above the sup. So
O9 *as §4 states it* cannot be held by interval arithmetic at any table
size.

**It does not apply to `window_table.py`, by construction.** That module
computes caps by adaptive subdivision with `tol_rel = 0.02`, so every cap
sits above its bracket's true supremum:

| k | true sup on bracket | `window_table` cap | ratio |
|---|---|---|---|
| 0 | 4.396423772e-03 | 4.483880e-03 | **1.0199** |
| 1 | 9.750553153e-04 | 9.944775e-04 | 1.0199 |
| … | … | … | ≥ **1.0195** |
| 8 | 4.623464811e-05 | 4.715629e-05 | 1.0199 |

Minimum ratio across the nine brackets `1.0195`; **0 undecided cells** in
the table is the empirical form of the same fact. What was recorded as a
caveat (named gap T4, "the caps are deliberately loose") is, in the light
of their finding, the load-bearing design choice.

**The two size estimates are consistent because they size different
objects.** `window_table` is **196 cells**, one-dimensional at `y = 1/2`,
which is legitimate only because of the depth reduction
`D(y,s)/y^2 <= 4 D(1/2,s)`. Theirs is the full two-dimensional object
over `[28/5,60] x [0,1/2]`. Both are a fraction of `BandCert/Data.lean`.
Neither says size is the obstacle, and they agree on that independently.

**CORRECTED, see coordinator defect #23 below.** This paragraph first
quoted theirs as "264 leaves at depth 12 at `1.20x` inflation plus `0.02`
widening". That is their **first draft's** operating point, which their
own second commit retracted: `0.02` widening **breaks O3**, whose ceiling
is `0.00695`. Their recommended point is `1.20x` inflation with `1/200`
widening — **110 window + 279 complement = 389 leaves, max depth 16**.

**Their §7 ceiling clears ours.** They measure the budget as absorbing
cap inflation up to **`1.3945x`**. `window_table` runs at `1.02x` with a
cap sum of `1.319090e-02` against `Shq/2 = 3.375420e-02` — headroom
`2.5589x` — and inflating its caps all the way to `1.3945x` gives
`1.839470e-02`, still under budget.

Disposition: **THE TWO SCOPINGS AGREE, AND THEIRS SUPPLIES THE REASON
OURS WORKS.** The zero-margin obstruction is real for the §4 statement
and is the thing to fix in `RETENTION-PROBLEM.md`; the table this session
built already avoids it, and now has a named reason rather than a lucky
tolerance. No proportion has moved and nothing here is evidence about RH.


## O9 built as a leaf file, and the 196-cell estimate corrected to 344 (2026-08-13)

Instrument: `o9_leaf.py`, `test_o9_leaf.py` (20 tests), and the generated
`zeta23ext/Zeta23Ext/EForm3/{O9Data,O9Check,O9Damage}.lean`.

**What was actually blocking O9 was nothing.** It was recorded as needing
a prover; it does not. A leaf table is generated data plus a decision
procedure — the pattern `BandCert` already uses — so the work is code
generation, and it can be done and validated without a Lean toolchain.

**The arithmetic is mirrored, not approximated.** `o9_leaf` reimplements
`Iv.lean` (`flo`, `fhi`, `add`, `sub`, `neg`, `mul`, `sqr`, `mulInt`,
`divInt`, `widen`, `ofQ`, `ofInt`, `div`) and `Phi.lean`'s `CIv` layer
**operation for operation in integers at scale `2^64`**, then builds
`phiC` by the same composition. Lean's `Int` `/` is `ediv`, which for
`SO > 0` is floor, so Python's `//` matches. Soundness spot-checked: every
fixed-point damage enclosure contains the Arb reference at six offsets
spanning `[5.7, 59.9]`.

### The size was wrong, and low

| estimate | arithmetic | cells |
|---|---|---|
| `window_table.py` (2026-08-13, earlier) | Arb balls, 128 bits | 196 |
| **`o9_leaf.py`, the kernel's own** | fixed point, `2^-64` | **344** |

Arb at 128 bits is *tighter* than fixed point at `2^-64`, so cells Arb
decides need splitting again in the arithmetic that will actually run.
**196 was an underestimate of the real Lean cost by 43%.** Max depth 20,
**0 undecided**, smallest margin `3.63e9` ulp (`1.97e-10` absolute) — far
above the few-ulp band where the leaf caveat would bite, so the prediction
is safe. 344 sits above `BandCert`'s existing `62..248` but on the same
order.

### The termination detail that decides it

The walk must cut `[28/5, 60]` at **every window endpoint** before
subdividing. Bisection alone never lands on one — the endpoints are
rationals with denominator `10^4`, the midpoints are dyadic — so a cell
straddling a boundary shrinks forever: **768 cells, 18 undecided at depth
40**. With the cuts: 344, none undecided. This is the third appearance of
the same trap in this hunt (it also killed two earlier sizing attempts),
and it now has a test.

### One deliberate refusal

`O9Damage.lean` defines `damageIv` and states its soundness lemma
`damageIv_mem` **in prose, not as a `sorry`**. A placeholder there would
have been the first `sorry` in `zeta23ext`, which has been sorry-free
throughout, and that is the package's whole claim; it is not worth
spending for one lemma whose proof is `phiC_mem` then `CIv.mul_mem` then
`EIv.neg_mem`. A test now enforces the package-wide invariant.

Disposition: **THE TABLE EXISTS, VALIDATED IN THE ARITHMETIC THAT WILL
CHECK IT.** Named gaps L1-L5: nothing is kernel-checked (no toolchain
here); the leaves are Arb rather than `Leaves.lean`'s Taylor series, so
this predicts the kernel's verdict rather than reproducing it; the
soundness lemma is unwritten; the table is one-dimensional at `y = 1/2`
and rests on the unproved depth reduction. `k >= 2` is untouched, no
proportion has moved, and nothing here is evidence about RH.

### CORRECTION: coordinator defect #23 — a superseded number, cherry-picked past its own retraction

The operator asked for the tree to be tied off and warned against
assuming another session's work is wrong without digging. Digging found
the error was mine.

**What happened.** Both `lab-rejection-philosophy` commits were
cherry-picked: `9a99fc9` ("O9 scoped") and `0278f4a` ("O9 work order, **and
the widening ceiling the first draft missed**"). The reconciliation entry
above then quoted their operating point as *"264 leaves at depth 12 at
`1.20x` inflation plus `0.02` widening"* — which is the **first draft's**
figure, retracted by the second commit that was applied in the same
breath. Their §2 establishes a hard ceiling: the widening may not exceed
`(1 - 0.9861)/2 = 0.00695`, because O3 supplies `Kpair >= 39/50` only on
`|u| <= 1` and `Kpair(1.01) = 0.77943 < 39/50`. Their own table marks
`0.02` as **"closes, but breaks O3"**.

| | first draft (quoted in error) | their recommendation |
|---|---|---|
| inflation | 1.20x | 1.20x |
| widening | **0.02 — breaks O3** | **1/200 = 0.005** |
| leaves | 264 | **110 window + 279 complement = 389** |
| max depth | 12 | **16** |

Their `ACTIVE-CLAIMS` row already carried the corrected numbers, and the
conflict resolution took that side correctly; only the prose entry here
was stale. Corrected in place above.

### What the dig also found: this session's table has an unstated dependency

Their §1 records that "no damage outside the windows" is an **equality at
every window endpoint**, so with `I_k` taken as the exact damage support
the complement does not close — 404 leaves and a depth wall. `o9_leaf`
closes anyway, and **not** because fixed point beats Arb. It closes
because §4's recorded `I_k` are decimal-rounded **outward** past the true
support:

| k | §4 `I_k` | true support | slack |
|---|---|---|---|
| 0 | `[6.0653, 7.0514]` | `[6.065319, 7.051319]` | 1.9e-05 / 8.1e-05 |
| 1 | `[12.2342, 13.1999]` | `[12.234289, 13.199859]` | 8.9e-05 / 4.1e-05 |
| 2 | `[18.4704, 19.4332]` | `[18.470414, 19.433183]` | 1.4e-05 / 1.7e-05 |
| 3 | `[24.7289, 25.6909]` | `[24.728967, 25.690832]` | 6.7e-05 / 6.8e-05 |

That rounding is an implicit widening of about `2e-05` and it is
load-bearing: re-deriving §4's endpoints to more decimals would tighten
them onto the support and **this table would stop closing**. Now stated
in the module (`L4b`) and pinned by a test.

### And theirs is the better artifact

`o9_leaf` sizes the **one-dimensional** table at `y = 1/2`: 344 cells at
`1.05x`, no explicit widening. `o9_scoping` sizes the **two-dimensional**
table over the whole box: 389 leaves at `1.20x`/`0.005`. Being 2-D,
**theirs needs no depth-reduction lemma** — this session's 1-D table rests
on `D(y,s)/y^2 <= 4 D(1/2,s)`, which is measured and unproved. Trading an
unproved lemma for 45 leaves is a bad trade, and whoever writes the Lean
file should take the 2-D route. Recorded in `o9_leaf`'s docstring rather
than left for someone to rediscover.

### Two other loose ends closed

* `window_table.py` asserted "**It is 196 cells**" with no pointer to the
  344. It now says plainly that 196 is an Arb-grade sizing which
  understates the Lean obligation by 43%, and `N_CELLS` carries the same
  note. A test pins the two counts against each other.
* The generated `O9{Data,Check,Damage}.lean` are **staged but deliberately
  not imported** by `Zeta23Ext.lean`. They are uncompiled here — there is
  no toolchain — and wiring unverified modules into the package root would
  risk the other session's build. A test pins that they exist and that the
  root does not import them.

Disposition: **THE ERROR WAS MINE, THE OTHER SESSION'S WORK WAS RIGHT AND
ALREADY SELF-CORRECTED.** Defect #23 is the fifth of the session and the
first involving another session's material; its cause is the same as the
other four — a quantity carried across contexts without being re-derived
in the context it was being used. `k >= 2` remains open, no proportion has
moved, and nothing here is evidence about RH.

---

## 2026-08-15: blocker 2's first multi-pair case — `k = 2`, equal depths, measured

**Claimed:** the two-species restatement (`two_species.py`: `D(0,tau) =
-Kpair(tau)`, so the `k`-pair slack is per-centre budgets + centre-centre
`Kpair` repulsion at rate 2 + atom repulsion at rate 1/200 − atom damage at
depth `y` − centre-centre damage at depth `2y`; identity vs `slack_direct`
1.1e-14, general depths vs `kpair_identity.slack_k` 3.6e-15), and on it the
`k = 2, y_1 = y_2` case of the blocker-2 inequality, all `y in (0,1/2]`,
all `n`, all `tau`, at MEASURED grade: a 6601-cell tau-table on [0, 132]
with 0 nonpositive cells in two independently conservative cap modes
(worst margins +0.0529 signed-field / +0.0033 unsigned, the latter stable
under 2x grid refinement), closed form beyond `tau = 114.2` (windows end
at 57.07), depth uniformity by the same v-convexity as the k=1 proof
(`k2_closure.py`, `K2-TWO-SPECIES.md`).

**Controls:** the module re-derives the k=1 §7 window total to all printed
digits (8.1383160e-2); the accounting dominates the greedy adversary
pointwise in `tau`; the adversary-side damage ladder first fires between
1.5x and 1.7x, consistent with the measured worst relative margin; the
machine's own caps kill the resonance cell at 1.02x inflation, consistent
with its worst margin.  Depth-1 landscape corrections recorded on the way:
the no-damage radius at depth 1 is **5.3984 < 28/5**, and the far constant
at depth 1 is **0.6636 > 637/1000** — neither proved bound survives at the
centre-centre depth, and any depth-1 argument must re-derive them.

**Quantifier discipline (defect #19 applies):** this is the FIRST
multi-pair case, not blocker 2.  Open and named: `k >= 3` (the centre-gas
split T1/T2 of `K2-TWO-SPECIES.md` §5 is a direction with measurements —
the gas eats 87.8% of the per-centre budget on the worst uniform lattice
and the signed field poisons atoms there — not a schedule); unequal depths
(grid-measured `>= 0`, the convex-majorant route's gap named); hardening
(interval pass over the same cells, O9-table technology).  `k >= 2` in
full remains OPEN, no proportion has moved, and nothing here is evidence
about RH.
