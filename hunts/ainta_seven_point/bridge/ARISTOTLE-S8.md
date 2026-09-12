# ARISTOTLE-S8: the tail-passage agent's submission ledger

Agent: `bridge/S8` (branch `bridge/S8`, from `bridge/skeleton`). Cap: 3 submissions. Used: **0 of 3**.

## Submissions

None. No project was opened and no `ARISTOTLE_API_KEY` call was made.

Reason: the single obligation, `Zeta23Ext.Bridge.tail_passage`
(`hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/S8.lean`), closed in the local pass with no
residual left to send. There was nothing to bound into a variant.

## Obligation

| lemma | step | trust-map grade | status |
| --- | --- | --- | --- |
| `Zeta23Ext.Bridge.tail_passage` | S8, `N₀ˢ(T,2T) ≥ H N(T,2T) + D(M°) − o(N)` | HANDWRITTEN, LARGE | **PROVED**, zero `sorry` |

`#print axioms tail_passage` reports `[propext, Classical.choice, Quot.sound]`. No
`native_decide`, no `sorryAx`, no new axiom.

## What was done

Two new theorems in `hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/Helpers_S8.lean` (new file,
beside the skeleton's; no existing file outside `S8.lean` was edited):

| theorem | what it is | axioms |
| --- | --- | --- |
| `seamA_mult2_defect` | `[L23]` `Zeta23.Assembly.seamA_mult2` with its zero-side core `hatAz_mult2` replaced by the hypothesis `4 tr Â − ‖Â‖² − 2N(I′) + D ≤ s₁` and `+ D` carried to the conclusion | standard three |
| `endgame_defect` | `[L23]` `Zeta23.ThmD.thmD_mult2_abstract` with `hlam : P.lam < 1` and `hBlock` dropped, the seam core taken as a hypothesis with `+ D T`, conclusion `(2 − 1/c − ε) N + D T ≤ N₀ˢ` eventually | standard three |

`S8.lean` then instantiates `endgame_defect` at `P = paramsOf stdProfile 1` with exactly the inputs
`[L23]`'s `thmD_mult_lam_abstract` feeds `thmD_mult2_abstract` (`tracesBoundsD_concrete`,
`tendsto_cRatio_concrete`, `concreteFactsD.ab_range`, `eventually_tailPackageD`,
`Tail.eventually_NII_le`, `eventually_GzGpD`, `Params.atD_*`, `calE_tendsto_zero`), and
`HD 1 = 2 − 1/cStar 1` by `two_sub_inv_cStar`.

Build (standalone, the way `ARISTOTLE-PROBE.md` §1b built `StableRankTrace`; the package does not
assemble on `main`, issue #101), toolchain `leanprover/lean4:v4.33.0-rc2`, 2026-08-23:

```
lake build Zeta23Ext.Bridge.Helpers_S8   Built (4.9s)   Build completed successfully (8840 jobs)
lake build Zeta23Ext.Bridge.S8           Built (2.9s)   Build completed successfully (8841 jobs)
lake build Zeta23Ext.Bridge.Main                        Build completed successfully (8851 jobs)
```

`Main`'s `#print axioms` lines are unchanged in shape: `seven_point_bound` still reports `sorryAx`,
now only through S6, S9, S11–S15. Static scan of the two files I wrote: no `sorry`, no
`native_decide`, no `axiom`, no reserved word, no machine path.

One pre-existing test failure, not introduced here and not mine to fix:
`tests/test_zeta23ext_imports.py::test_no_module_is_orphaned_from_the_root` fails on
`bridge/skeleton` already (every `Zeta23Ext/Bridge/*.lean` module is unreachable from
`Zeta23Ext.lean`, which the skeleton did not edit). `Helpers_S8` joins that list until the
integrator wires `Zeta23Ext.Bridge.Main` into the root.

## What the formal state showed that the paper and the trust map hide

The trust map grades S8 LARGE and the skeleton's residual note located the difficulty in the
`λ → 1⁻` passage: `[L23]` proves Theorem D at each fixed `λ < 1` and reaches `HD 1` through
`eps_form_HD`, a limit over *different windows*, while the defect `D(M°)` is a function of the
single window at `λ = 1` and cannot ride through such a limit. The note also stated that
`[L23]`'s `calE` "does not tend to `0`" at `λ = 1`.

Neither holds in the tree:

1. `Zeta23.Assembly.calE_tendsto_zero` is stated for `0 < P.lam ≤ 1` (the paper's own
   `𝓔_T ≪ w/L + log l / l` at `λ = 1`), so the trace asymptotics are available at `λ = 1`.
2. Every other analytic input of the endgame (`tracesBoundsD_concrete`,
   `tendsto_cRatio_concrete`, `eventually_tailPackageD`, `isLittleO_sqrtX_Tl`,
   `tendsto_theta_over_L`, `localHypsCoreD_eventually`) takes `P.Valid`, which is
   `0 < λ ≤ 1`, and `Params.Valid` at `paramsOf stdProfile 1` is already proved by the skeleton
   (`P₀_valid`).
3. `thmD_mult2_abstract`'s hypothesis `hlam : P.lam < 1` is consumed exactly once, as `hlam.le`.

So the `λ → 1⁻` passage in `[L23]` is a choice of presentation, not a mathematical necessity,
and the defect term goes through the endgame at `λ = 1` by transcription: `D` enters the fixed-`T`
inequality once (as `N₀ˢ − D` in the role of `N₀*` in `N0star_lower_c`) and the `o(N)` bookkeeping
is verbatim `[L23]`. The step the trust map graded LARGE is a 20-line instantiation plus a
260-line transcription with four marked edits. What the paper hides is the opposite of what was
feared: not a hard limit argument, but the fact that its "Theorem D gives `tr Ĝ = N(1+o(1))`,
`‖Ĝ‖² = (1/c₁* + o(1)) N`" is *already formalised at `λ = 1`* by `[L23]`, two layers below the
theorem statement that `[L23]` chose to export.

Correction owed to `TRUST-MAP.md` S8 and to the skeleton's `S8.lean` docstring (the latter is
replaced on this branch; the former is the integrator's): the `calE` claim and the LARGE grade.
