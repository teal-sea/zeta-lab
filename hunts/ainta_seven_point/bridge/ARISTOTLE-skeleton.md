# ARISTOTLE-skeleton: the bridge skeleton agent's submission ledger

Agent: `bridge/skeleton` (branch `bridge/skeleton`). Cap: 3 submissions. Used: **0 of 3**.

## Submissions

None. No project was opened and no `ARISTOTLE_API_KEY` call was made.

Reason: the task was to make the whole bridge typecheck end to end with the residuals as named
`sorry` lemmas, not to close any of them. The only two steps that were proved outright (S7,
S16) closed locally in one pass (S7 is a corollary of the kernel-checked S2
`stable_rank_trace` plus S6; S16 is `field_simp`), so there was no residual worth a project.
Every remaining `sorry` is an attacker's target and is listed below so that whoever opens a
project against one of them does not have to rediscover the statement.

## The skeleton, for attackers branching from `bridge/skeleton`

Modules (all new, beside the existing `Zeta23Ext/Bridge.lean`, which was not touched):
`hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/{Defs,S6,S7,S8,S9,S11,S12,S13,S14,S15,S16,Main}.lean`.

Build, standalone against the prebuilt store (the package does not assemble on `main`, #101,
so the root target is not the verdict; the Bridge modules are built by name, the way
`ARISTOTLE-PROBE.md` §1b built `StableRankTrace`):

1. populate `hunts/frontier_math/zeta23ext/.lake/packages/` the way `assemble.sh` does
   (symlinks to the laboratory's `lean/.lake/packages/{mathlib,batteries,aesop,Qq,proofwidgets,
   plausible,importGraph,LeanSearchClient,Cli}`), plus `Zeta23` pointing at a checkout of the
   pinned upstream rev `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` that already has its oleans
   (the primary checkout's own `.lake/packages/Zeta23` is one; from a git worktree, symlink it);
2. `cd hunts/frontier_math/zeta23ext && lake build Zeta23Ext.Bridge.Main`.

Result on 2026-08-23, toolchain `leanprover/lean4:v4.33.0-rc2`, from deleted Bridge oleans:
`Build completed successfully (8850 jobs)`; the eleven Bridge modules compile in one parallel
batch of 105 s wall, `Main` in 5.5 s. Every `#print axioms` line in the tree reports either
`[propext, Classical.choice, Quot.sound]` or the same plus `sorryAx`, and the `sorryAx` ones are
exactly the declarations downstream of the eleven lemmas below. No `native_decide`.

Named `sorry` lemmas (11), each with its residual goal in its docstring:

| file | lemma | step | grade |
| --- | --- | --- | --- |
| `S6.lean` | `regroup_posIndex` | S6 `n₊(Q') ≤ s₂ + p` | small–medium |
| `S8.lean` | `tail_passage` | S8 tail passage to `N₀ˢ ≥ H N + D(M°) − o(N)` | LARGE |
| `S9.lean` | `kernel_limit` | S9 uniform kernel limit | LARGE |
| `S9.lean` | `deleted_strips` | S9 strips hold `o(N)` zeros | small |
| `S11.lean` | `block_energy` | S11 | small |
| `S12.lean` | `block_defect` | S12 | small |
| `S13.lean` | `block_bound` | S13, deterministic at one height | medium |
| `S14.lean` | `pinching_partition` | S14 | medium (pinching absent from Mathlib) |
| `S14.lean` | `pinching_submatrix` | S14, two-block corollary | small given the partition form |
| `S15.lean` | `offset_average` | S15 combinatorial core | small–medium |
| `S15.lean` | `span_retained_le` | S15 RvM input | small |

Proved, sorry-free: `S7.count_defect` (from S2 + S6), everything in `S16.lean`
(`solve_linear`, `Phi_paper`), `Main.eventually_h7`, `Main.block_bound_eventually`,
`Main.pre_solve`, `Main.seven_point_bound`, `Main.seven_point_bound_paper`. Their `#print axioms`
report `sorryAx` only through the eleven lemmas above.

Suggested first projects, if someone spends the cap: `S12.block_defect` (two cases, all tools
upstream; `Psi = gc 2 + 1`), `S14.pinching_partition` (the one genuinely missing library fact),
`S15.offset_average` (pure finite combinatorics, no analysis). Not S8 or S9.

## Known test interaction

`tests/test_zeta23ext_imports.py::test_no_module_is_orphaned_from_the_root` fails on this branch
by construction: the new modules are not imported from `Zeta23Ext.lean`, and editing that
existing file was out of scope for this agent. The fix is one line for the integrator,
`import Zeta23Ext.Bridge.Main` in `Zeta23Ext.lean`. The other eleven tests in that file and in
`test_hunt_probe_discipline.py` pass.
