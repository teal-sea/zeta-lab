# ARISTOTLE-finite: the bridge/finite agent's submission ledger

Agent: `bridge/finite` (branch `bridge/finite`, from `bridge/skeleton`). Cap: 3 submissions.
Used: **0 of 3**.

## Submissions

None. No project was opened and no `ARISTOTLE_API_KEY` call was made.

Reason: all six obligations of this group (S6, S7, S11, S12, S13, S15) closed by direct proof
under the pinned toolchain, so no bounded variant was ever worth the owner's money. Every step
lemma of the group now reports `[propext, Classical.choice, Quot.sound]`; none reports `sorryAx`.

## Obligations

| step | lemma | file | status | residual |
| --- | --- | --- | --- | --- |
| S6 | `regroup_posIndex` | `Zeta23Ext/Bridge/S6.lean` | PROVED | none |
| S7 | `count_defect` | `Zeta23Ext/Bridge/S7.lean` | PROVED (skeleton proof; its only `sorry` dependency was S6, now closed) | none |
| S11 | `block_energy` | `Zeta23Ext/Bridge/S11.lean` | PROVED | none |
| S12 | `block_defect` | `Zeta23Ext/Bridge/S12.lean` | PROVED (and the stronger `block_defect_of_isHermitian`: positivity of `G` is not used) | none |
| S13 | `block_bound` | `Zeta23Ext/Bridge/S13.lean` | PROVED | none |
| S15 | `offset_average`, `span_retained_le` | `Zeta23Ext/Bridge/S15.lean` | PROVED (both) | none |

New helper module beside the step files: `Zeta23Ext/Bridge/Helpers_finite.lean` (kernel is even,
`w ≥ 0`, `|k| ≤ 1` from `cos(√2 t) ≥ 0` on `[−1/2, 1/2]`, sorted ordinates, seven-point windows,
the shift identity). `Defs.lean`, `Main.lean` and the other groups' files were not touched.

## Build

Standalone, against the prebuilt store the way `ARISTOTLE-PROBE.md` §1b built `StableRankTrace`
(`.lake/packages/{mathlib,…}` symlinked from the laboratory's `lean/.lake/packages`, `Zeta23`
symlinked to the primary checkout's built copy of rev `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`),
toolchain `leanprover/lean4:v4.33.0-rc2`:

```
cd hunts/frontier_math/zeta23ext && lake build Zeta23Ext.Bridge.Main
Build completed successfully (8851 jobs).   (61 s wall, Bridge modules only)
```

`#print axioms` in the tree after this branch: the ten `sorryAx` lines left are exactly
`S8.tail_passage`, `S9.kernel_limit`, `S9.deleted_strips`, `S14.pinching_partition`,
`S14.pinching_submatrix` and the five `Main` declarations downstream of them. No `native_decide`.

## Static scans

`grep -i certified` over the group's files: no hit. Machine paths: none. `sorry`: none in
S6, S7, S11, S12, S13, S15, Helpers_finite.

## What the formal state showed that the paper hides

See the group report; summarized: S12 never uses `G ⪰ 0`; S11's "a pair spanning `r` gaps occurs
at most `7 − r` times" is a fibre-count over triples `(window, a, b) ↦ (window+a, window+b)` and the
`6/p` pressure term is a telescoping identity, not a counting bound; S13 needs `|k| ≤ 1`, which the
paper never states and which comes from `cos(√2 t) ≥ 0` on the integration interval (i.e. from
`√2/2 < π/2`); S15's "average over the `m` offsets" is replaced by a sum over all `n − m + 1`
block starts with one pinching partition per residue class, which avoids the floor-function count
`Σ_j ⌊(n − j)/m⌋` entirely; and `span_retained_le` needs `L ≤ ℓ₁`, i.e. `2 log 2 − 1 ≥ 0`, and
`log T = o(T)`, neither of which is mentioned in [A] §5.
