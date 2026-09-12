# ARISTOTLE-S9: the S9 agent's submission ledger

Agent: `bridge/S9` (branch `bridge/S9`, from `bridge/skeleton`). Cap: 3 submissions.
Used: **0 of 3**.

## Submissions

None. No project was opened and no `ARISTOTLE_API_KEY` call was made.

Reason: both S9 obligations closed locally with zero `sorry` before any residual existed,
so there was nothing left to send. The rule for this group was "the obligation alone; the
obligation with the hardest sub-lemma as a hypothesis; the sub-lemma alone", and all three
variants collapsed to the same closed target.

## Obligations

| lemma | file | status | axioms |
| --- | --- | --- | --- |
| `Zeta23Ext.Bridge.kernel_limit` | `hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/S9.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `Zeta23Ext.Bridge.deleted_strips` | `hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/S9.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |

Helper module (new, beside the skeleton files, nothing pre-existing edited):
`hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/Helpers_S9.lean` (808 lines, 8 sections).

Neither statement in `Defs.lean` or `Main.lean` needed changing. The two hypotheses of
`kernel_limit` that the proof does not use, `H : PaperInputs Z` and `|x_ρ − x_ρ′| ≤ R₀`, are
left in the signature exactly as the skeleton wrote them, because `Main.block_bound_eventually`
consumes the lemma positionally.

## Build

Standalone, the way `ARISTOTLE-PROBE.md` section 1b built `StableRankTrace`: prebuilt store
symlinked into `.lake/packages`, `Zeta23` symlinked to the primary checkout's built copy of
rev `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, toolchain `leanprover/lean4:v4.33.0-rc2`.

- `lake build Zeta23Ext.Bridge.Helpers_S9`: builds, 46 s cold.
- `lake build Zeta23Ext.Bridge.S9`: builds, 18 s cold, **no `sorry` warning in the file**.
- `lake build Zeta23Ext.Bridge.Main`: builds (8851 jobs). `seven_point_bound` still reports
  `sorryAx`, inherited now only from S6, S8, S11, S12, S13, S14, S15.

Static scan of the two files: the reserved word does not occur; no machine paths.

## What the formal state showed that the paper hides

1. **`R₀` is not a hypothesis of eq:kernel-limit.** The paper states the limit "uniformly for
   retained simple zeros with `|x_ρ − x_ρ′| ≤ R₀`" and justifies the tail by decay "uniformly
   when `|x_ρ − x_ρ′|` is bounded". In the formal proof the bound at height `T` is
   `10 (c_DT/w)²/L⁴ + 12w/L` for every pair of retained zeros at every separation: the tail
   goes through `|K_∞ − K| ≤ (ρ(γ) + ρ(γ′))/2` (weighted AM–GM, `[L23]`
   `PrimeSide.abs_Kinf_sub_Kfun_le`), which is a sum of two one-point quantities, and the limit
   `Φ_D(hx)/(aL) → k(x)` is an `L¹` statement about the window, in which `x` only enters through
   `|e^{ihxu}| = 1`. Nothing is uniform-on-compacts; everything is uniform, full stop.
2. **`[L23]` already has the uniform-in-`T` Poisson identity for the Montgomery–Taylor window.**
   The trust map cites `Zeta23/Poisson.lean`'s `hasSum_phiHatR_mul`, which needs a `TaperProfile`
   and so does not apply to `P.atD T` (its profile is `T`-dependent and not monotone). The
   identity that does apply is `AdmWindow.hasSum_vHatR_mul` in `ThmD/WindowCore.lean`, reached
   through `ThmD.admWindow_params`. Same for the decay `|φ̂(r)| r² ≤ c_DT/w`: the constant is
   `cDT ϱ λ`, independent of `T`, which is the whole uniformity.
3. **The `r⁻²` decay of [C26] §5.3 is already a named `[L23]` lemma**, `PrimeSide.rho_le_majorant`
   (`ρ(τ) ≤ W(τ−T) + W(2T−τ) + ψ(τ_d−τ)²`), with `∫_{(Δ,∞)} ψ² ≤ (c/w)²/(3Δ³)`. The strips of
   normalised width `L²` are exactly what puts all three arguments at `≥ 2πL`, where
   `W = O(L⁻²)`; the normalised tail is then `O(L⁻⁴)`, not the `O(L⁻²)` the paper states
   (the paper's `O(L⁻²)` is correct and weaker).
4. **The limit (iii) needs no new analysis.** The paper's "`φ(Lt)² → cos(√2 t) 1_{[−1/2,1/2]}`
   in `L¹`" is `ThmD.integral_abs_phiDsq_sub_sharp` (`≤ 2w`, unrescaled), and the normalising
   `aL → L K(0)` is `ThmD.aD_close`. The only computation done here is the cosine transform of
   the sharp window, `∫ 1_{[−L/2,L/2]} cos(√2u/L) cos(2πxu/L) du = L K(x)`, one substitution.
5. **The strip count is the only place the zeros enter.** `deleted_strips` is the only S9 fact
   that uses `H : PaperInputs Z` (the local count and Riemann–von Mangoldt); `kernel_limit`
   is a statement about the window and the grid, with the zeros present only through the strip
   condition `L² ≤ x_ρ ≤ d − L²`. Window additivity and monotonicity of the abstract `Z.N` had
   to be written (`N_add`, `N_mono`, `ncard_window_le_N`); `[L23]` has them only for the concrete
   `Zeta23.Ncount` (`RvM/NcountWindow.lean`).

## Not done

- Nothing is claimed about S8, S13 or any other step. `Main.block_bound_eventually` now
  inherits `sorryAx` only through `block_bound` (S13).
- The explicit constants (`1600 A₀ L²` for the strips, `12w/L` for the limit) are not
  sharp and were not tuned; every step of the bridge consumes S9 only as `∀ᶠ T`.
