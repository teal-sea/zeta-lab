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
