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

Disposition: **THE BRIDGE ITSELF IS NOW A THEOREM, AND IT STILL DOES NOT
CLOSE THE FAMILY.** Both halves stand: the finite-to-infinite comparison
is kernel-checked with an explicit constant, and m0 remains too large at
the resonance and at the budget floor. What the formal artifact adds is
that the estimate can now be cited rather than measured, and that the
Poisson route the audit recommended over a sorried dependency worked
exactly as predicted. No proportion is claimed to have moved.
