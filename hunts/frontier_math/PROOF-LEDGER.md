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
