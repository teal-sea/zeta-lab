# Level 3: theta > 0 at the single-pair reduction, and why

## The milestone, answered

> THETA > 0, OR AN EXACT REASON THETA MUST STILL BE ZERO.

**Theta is positive at the single-pair reduction, by a wide measured margin
(the scan stays safe through theta = 0.9), and the mechanism is exact.**
Before levels 1–2 the adversary had two unbounded resources: per-pair
incidence magnitude (the scalar family's `m -> infinity`) and free reuse of
one pair across many cells. Laws D–H priced both, and level 3 can now name
the two structural facts that make a positive trade possible where the
interaction-control audit found none:

- **deep pairs are self-defeating** — damage is linear in `sigma^2` while
  the pair's own retained Frobenius slack grows like `8 sigma^4` (LAW K);
- **dense packing is self-defeating** — multiplying damage `nu`-fold
  manufactures internal `R(P)` mass quadratically (LAW G), of which the
  adversary must leave `(1-theta)` on the table.

Both self-defeats are scale-matched (damage² ~ σ⁴ against slack ~ σ⁴;
damage ~ ν against packing ~ ν²), which is why the measured recovery range
is `nu`-free and `sigma`-free — the Phase-4 classification is
`theta -> theta_0 > 0` at this reduction, not a decaying coefficient.

## LAW K — the exact pair spectrum (new, and the level's engine)

For a pair `u = x + iy` at depth `y`, LAW D pins the bilinear square
`u.u = 1` — *real* — which forces `x . y = 0` exactly; the Hermitian
identity gives `|x|^2 + |y|^2 = 1 + 2 sigma^2(y)`. Together:

```text
|x|^2 = 1 + sigma^2,   |y|^2 = sigma^2,   x  |  y,
spec( 2(xx^T - yy^T) ) = { 2(1 + sigma^2(y)),  -2 sigma^2(y) }   exactly.
```

The paper knew the signature (1,1); the eigenvalues pinned by depth are new.
Checked against the actual grid to machine precision (`x.y ~ 1e-16`,
eigenvalues to 8 digits at three depths). Two consequences:

1. **The pair's negative eigenvalue *is* the depth envelope** `-2 sigma^2` —
   LAW E's per-cell floor reappears as spectral data.
2. **Against the baseline's flat charge 4** (Lemma 3.2 at `c = 2`,
   eigenvalue-wise), the pair retains slack **exactly `8 sigma^2 + 8
   sigma^4`**. This is the security level 3 spends; the baseline never
   touches it.

## The three-zero lemma (proved, unconditional, theta = 1)

From LAW I alone (`2W >= -2(1+m0) sigma^2` per cell) and LAW K's slack:

```text
a pair with at most three on-line zeros in its negative cells has
net >= (8 - 6(1+m0)) sigma^2 = 0.7177 sigma^2 > 0,
```

placement-free, depth-free, retaining **all** of `R(P)`. The adversary is
forced to field at least four zeros per pair — i.e. into the density regime
where the quadratic packing costs live. This small statement is the level's
proved fragment and would be the natural first Lean target.

## The worst-case cancellation problem (Phase 2), solved at one pair

Objective, per pair, in normalised units:

```text
net(theta) = (1-theta) R_int(X) + 8 sigma^2 + 8 sigma^4 - D(X),
D(X) = -2 sum_{x in X} W(x, y),    R_int(X) = 2 sum_{x != x'} omega(x-x')^2,
```

minimised over on-line configurations `X` (any size, any placement,
respecting the density cap) and over the depth. Two adversary families
bracket the landscape:

- **dense lattices** (spacing ladder 2.0 down to 1/16, keeping only
  negative cells — the continuum of the level-2 escaping family);
- **greedy sparse placements** (marginal-gain, min-spacing `1/nu`).

Measured worst net over both families and depths `y in [0.05, 0.49]`:

| theta | worst net |
|---|---|
| 0.0 | +0.0465 |
| 0.5 | +0.0460 |
| 0.8 | +0.0457 |
| 0.9 | +0.0456 |

The bottoming configuration is the *shallow-depth* limit, where slack and
damage scale to zero together and the ratio stays safe (`net ~ (8 - D/s2)
s2` with `D/s2` well below 8). The dense attack is genuinely dangerous —
at `y = 0.35`, spacing 1/16, damage `24 sigma^2` beats the bare slack
`13 sigma^2` — but its internal mass is 1274 in the same units: even
retaining 90% of `R(P)`, the remaining 10% drowns the surplus. Theta = 1
fails in exactly this regime (`test_theta_equal_one_fails_in_the_dense_
regime`), which is the scan's power control: the instrument can see the
failure it is claiming to exclude.

## The dual-certificate seed (Phase 3)

The internal form's kernel is `omega(r)^2`, whose Fourier transform is
`(phi^2 * phi^2)`-shaped: **nonnegative, supported in the band** (measured:
positive at every in-band frequency, zero beyond). So the packing quadratic
form is positive semidefinite, the adversary's value

```text
Lambda(theta, y) := sup_X [ D(X) - (1-theta) R_int(X) ] / sigma^2(y)
```

is finite for every `theta < 1`, and the per-pair inequality has the closed
shape

```text
net >= (8 - Lambda(theta)) sigma^2 + 8 sigma^4.
```

The proof object level 3 leaves for the graduation step: an upper bound on
`Lambda` via this positive-definiteness (a band-limited moment problem),
replacing the measured sup over adversary families. The measured content:
`Lambda` stays below 8 through `theta = 0.9`; the dense lattice breaks even
against `(1-theta) R_int` only near `theta ~ 0.99`.

## Pair–pair terms: measured, partially covered, and the named gap

The full Phase-2 problem couples pairs. Measured here:

- **stacked pairs** (same ordinate) interact *positively* (`T = +8.94` at
  `y = 0.3` twice; `+25.6` deep) — stacking is self-defeating outright;
- **dipoles**: the worst interaction over ordinate offsets is negative
  (`-2.84` at `dt = 0.68`, `y = (0.3, 0.3)`) but covered by the two pairs'
  own slacks with factor **2.8–6.7**, uniformly over the tested depths.

Not delivered: the joint inequality with a slack partition proving that one
pair's security is never spent twice (once against on-line damage, once
against each neighbour pair). The dipole cover factors say the budget
exists; the partition is bookkeeping plus a pair-density argument (pairs
also obey LAW H), and it is **the named missing estimate** of this level.

## Phase 5 — the extremal battery

| extremal | fate |
|---|---|
| scalar obstruction family | unrealisable below level 3 (laws D–F); never reaches this level |
| moment-matched dilution | same bad block, same fate |
| level-1 near-obstructions (cells near the old floor) | LAW I band: excluded before entry |
| independent-duplication decoy | LAW H (level 2); also `theta_star` treats one pair exactly |
| off-line mass at maximal depth | quartic slack dominates: `8 sigma^4 > 4` worst zeros at `y = 0.49` |
| density-saturating configurations | the dense-lattice family; self-defeating, measured |
| periodic marked gap words | LAW J: total is `+2b/a^2 > 0` — no damage at all |
| near-coincident on-line collapse | the `+-g*` cluster = the lattice fine-spacing limit; covered |

## Classification, per the directive

**OUTCOME A at the single-pair reduction — candidate, not yet promoted.**
A positive recovery coefficient exists after worst-case single-pair
cancellation, with no error term in the reduction, a proved fragment (the
three-zero lemma), a proved finiteness certificate shape, and the failure
mode at `theta = 1` exhibited. Two steps separate this from the directive's
full OUTCOME A, and both are named rather than blurred:

1. a proved upper bound on `Lambda(theta)` (the measured sup is over two
   adversary families, not all configurations);
2. the multi-pair slack partition (dipole factors measured 2.8+, partition
   not written).

**The Phase-6 gate stays closed**: no proportion is computed, nothing is fed
back into the gap machinery, and the withdrawn 0.672529 is not revisited.
Per the operating rule, the reward claimed is the first kind only: a
strictly positive, twice-self-defeating cancellation bound at one pair,
with the exact reason it could not have existed before levels 1–2.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| LAW K spectrum vs actual grid | `law_k_check` | eigenvalues to 8 digits, `x.y ~ 1e-16`, three depths |
| slack formula | `test_law_k_slack_formula` | `8 s^2 + 8 s^4` exact from the eigenvalues |
| three-zero margin | `three_zero_margin` | `0.7177 > 0` |
| theta scan power (theta = 1 fails) | `test_theta_equal_one_...` | dense regime violates, as it must |
| dense attack realism | `test_dense_attack_is_real...` | damage beats bare slack; internal mass 10x damage |
| shallow-depth scaling | `test_shallow_depth_scaling...` | net > 0 and `O(sigma^2)` at `y = 0.02, 0.05` |
| certificate seed | `internal_kernel_is_positive_definite` | `FT[omega^2] >= 0`, vanishing off the band |
| dipole coverage | `dipole_worst` | factors 2.8–6.7 over tested depths |
| stacking sign | `pair_pair(0, ...)` | positive, both tested depth pairs |
| battery | table above | every named extremal accounted |

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/theta_recovery.py
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_theta_recovery.py
```

About 26 s and 23 s. Adversary optimisations are deterministic (lattice
phase scans and marginal-gain greedy); no random search enters any number.
