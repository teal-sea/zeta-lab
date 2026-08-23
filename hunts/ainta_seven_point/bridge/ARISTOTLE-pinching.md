# ARISTOTLE-pinching: the S14 (block pinching) agent's submission ledger

Agent: `bridge/pinching` (branch `bridge/pinching`, forked from `bridge/skeleton`).
Cap: 3 submissions. Used: **0 of 3**.

## Submissions

None. No project was opened and no `ARISTOTLE_API_KEY` call was made.

Reason: both S14 obligations (`Zeta23Ext.Bridge.pinching_partition`,
`Zeta23Ext.Bridge.pinching_submatrix`) closed locally with zero `sorry` on the first
direct pass, before any residual existed. Per the precedent set in
`hunts/ainta_seven_point/ARISTOTLE-PROBE.md` §7 and `bridge/ARISTOTLE-skeleton.md`,
sending a closed target buys a comparison, not a result, and that allocation call
belongs to the owner.

## What was proved instead

New module `hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/Helpers_pinching.lean`
(imports `Zeta23Ext.StableRankTrace` only; builds standalone in under 2 s against the
prebuilt store), consumed by the rewritten
`hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/S14.lean`:

- `Psi_convexOn` — Ainta's profile is convex on all of `ℝ`, by affine minorants
  (the device of upstream's `affine_le_gc`).
- `eigenvalues_submatrix_eq_mix` — the mechanism: for Hermitian `M` and injective
  `g : κ → ι`, the eigenvalues of `M.submatrix g g` are a row-stochastic mixture
  `μ_j = Σ_i S_{ji} λ_i(M)` with column sums `compressWeight hM g i ∈ [0, 1]`.
- `sum_eigenvalues_pinching_le` — partition pinching for **every convex `f : ℝ → ℝ`**,
  no sign condition (block weights sum to exactly 1 per eigen-direction).
- `sum_eigenvalues_submatrix_le_of_nonneg` — one-block pinching for convex `f ≥ 0`.
- `rtrace_specMap_pinching_le`, `rtrace_specMap_submatrix_le` — the same two in
  `[L23]`'s `specMap` trace vocabulary; S14's two lemmas are these at `f = Psi`.

Verification: `lake build Zeta23Ext.Bridge.S14` and `lake build Zeta23Ext.Bridge.Main`
from this branch (store populated the way `assemble.sh` does, `Zeta23` at the pinned rev
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, toolchain `leanprover/lean4:v4.33.0-rc2`):
build completed successfully; `#print axioms` for all seven helper theorems and both S14
theorems report `[propext, Classical.choice, Quot.sound]`. No `native_decide`. The
`sorryAx` remaining in `Bridge.Main` comes only from the other groups' step lemmas
(S6, S8, S9, S11, S12, S13, S15), unchanged here.

## Residual goals

None for S14.
