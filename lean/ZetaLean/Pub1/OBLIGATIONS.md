# Pub 1 strong closure — what is proved and what is not

Formalization of `hunts/wide_search/RESULTS-xiprime-admissible-closure.md`
(Zeta Lab PR #45).  Toolchain `leanprover/lean4:v4.33.0-rc2`, Mathlib
`v4.33.0-rc2` (`51e6992efd06126df61a496bebf8f49482a4e129`).

`lake build` succeeds; the tree contains no `sorry`, no `admit`, no `axiom`
declaration and no `native_decide`; every audited theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` (see `PrintPub1Axioms.lean`).

The principal theorem is **conditional**, and this file says exactly on what.
Nothing is weakened: the open facts are the true statements from the evidence
document, carried as explicit named hypotheses rather than assumed as axioms.

## The principal theorem

`ZetaLean.Pub1.pub1_strong_closure`

```
IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w)
```

with `quot v = ⟨1,v⟩² / ⟨Av,v⟩` and `cStar w = ⟨1,w⟩`, together with the
reciprocal orientation

`ZetaLean.Pub1.pub1_strong_closure_reciprocal`

```
IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹
```

`orientation_not_symmetric` records that the two quotients are genuinely
different quantities, so the orientation cannot be silently swapped.

## Discharged unconditionally

| fact | theorem |
| --- | --- |
| exact rational concavity margin `2c₁ + 0.006060899845 < -0.59326318` | `concavity_margin` |
| the same margin fails under the ×101 residual lesion | `concavity_margin_lesioned` |
| `2c₁ = -410178/684401 < -0.5993240804` | `uSecondDerivBound_lt` |
| certificate ⟹ `w'' < -0.59326318 < 0` | `secondDeriv_lt_of_certificate` |
| evenness ⟹ `w'(0) = 0` | `deriv_eq_zero_of_even` |
| strict concavity ⟹ strict radial decrease of `w` | `strictAntiOn_w`, `radial_antitone` |
| `η'(x) = 140x³(1-x)³`, `0 ≤ η ≤ 1`, monotone, `supp` exact | `ZetaLean.Pub1.Ramp` |
| `η ∈ C³` | `eta_contDiff` |
| `∫₀¹ η'² = 700/429`, `‖η''‖₁ = 35/8` | `AristotleD.*` |
| `‖(η²)''‖₁ ≤ 20615/1716` | `ramp_sq_second_deriv_bound` |
| `F₁ ≥ 0`, `F₁` even, `F₁` continuous, `∫₀¹F₁ ≤ 4/9` | `ZetaLean.Pub1.Setting` |
| row bound `∫_I F₁(s-t)dt ≤ 4/9` | `F1_row_bound` |
| Schur bound `\|⟨Tv,v⟩\| ≤ (4/9)‖v‖₂²` | `kerForm_abs_le` |
| coercivity `⟨Av,v⟩ ≥ (5/9)‖v‖₂²` | `energyA_coercive` |
| existence of `w = A⁻¹1` (Banach fixed point) | `exists_profile` |
| `1/5 ≤ w ≤ 1` | `profile_bounds` |
| `w` even | `profile_even` |
| `⟨Aw,w⟩ = ⟨1,w⟩`, i.e. `c*` is the energy of `w` | `energyA_eq_massI_of_profile` |
| **ambient upper bound** `⟨1,v⟩² ≤ c*⟨Av,v⟩` for every `v` | `massI_sq_le_of_profile` |
| `c* > 0` | `cStar_pos_of_profile` |
| taper is `C²` given `w ∈ C²` near `I` | `taper_contDiff` |
| taper: evenness, `0 ≤ φ ≤ 1`, exact support, radial monotonicity | `ZetaLean.Pub1.Window` |
| `v_L(s) = φ_L(Ls)²` | `profile_eq_taper_sq` |
| **`‖v_L - w‖₂² ≤ 2/L`** | `sq_L2_dist_le` |
| `L²` convergence `v_L → w` | `tendsto_L2_zero`, `vseq_tendsto_L2` |
| mass and energy converge along the sequence | `massI_tendsto`, `energyA_tendsto` |
| **the quotient converges to `c*`** | `quot_tendsto_cStar` |
| every admissible profile has positive energy | `energyA_pos_of_admissible` |
| everything above assembles | `strongClosureData_of_member` |

`strongClosureData_of_member` is the sharp statement: **every** input of the
principal theorem is discharged except membership of the constructed sequence in
the source-admissible class.  `sourceWindow_taper` reduces that to the four
facts below and no others.

## Remaining formal obligations

1. **`w ∈ C²` on an open neighbourhood of `I`.**
   `ContDiffOn ℝ 2 w (Ioo (-(3/5)) (3/5))`.
   This is the load-bearing distributional identity `F₁'' = 2δ₀ + q` with
   `q(x) = -8 + Σ d_k|x|^(2k-1)`, `d_k = a_k(2k)(2k+1)`, and the resulting
   pointwise formula `w'' = -2w - q*w` on `I`.  The delta mass must not be
   dropped.  Mathlib has no distributional-derivative API for this kernel, so
   the identity would be formalized directly as a second-derivative computation
   for the convolution against `F₁`.  *Not formalized.*

2. **`0 < w` on that neighbourhood.**
   Immediate from `1/5 ≤ w` on `I` (proved) plus continuity, once (1) fixes the
   extension.  *Not formalized*, only because it is stated on the larger
   interval.

3. **The residual-derived `C²` certificate `‖w'' - u''‖_∞ < 0.006060899845`.**
   This is the one genuinely large piece.  It needs, in exact rational
   arithmetic: the `M = 20` kernel truncation `A₀`; `A₀u` and `r₀ = 1 - A₀u`
   reconstructed as exact rational polynomials; the coefficient absolute-sum
   bounds `‖r₀‖₂ < 7.8749770e-10`, `‖r₀‖_∞ < 2.1710808e-5`,
   `‖r₀''‖_∞ < 0.005982627`, `‖u‖₂ < 0.887972`; the tail bound
   `ρ = ‖E‖_{2→2} ≤ 45088768/2828846926917599723269509375 < 1.6e-20`; the
   coefficient-ratio identity `d_{k+1}/d_k = 2(2k+3)/(2k+1)²` and the sums
   `Σ_{k>20} d_k < 2.90e-17`, `8 + Σ_{k≥1} d_k < 80.963`.
   Everything *downstream* of this certificate is proved: given it,
   `secondDeriv_lt_of_certificate` gives `w'' < -0.59326318` and
   `radial_antitone` gives strict radial decrease.  *Not formalized.*

4. **Uniform `L¹` bounds on the taper.**
   `‖φ_L''‖₁ ≤ (‖p''‖_∞ + 4‖p'‖_∞)/L + 35/4` and
   `‖(φ_L²)''‖₁ ≤ (‖w''‖_∞ + 4‖w'‖_∞)/L + 20615/858`, with `p = √w`,
   uniform for `L ≥ 8`.  The `η`-side constants (`35/8`, `700/429`,
   `20615/1716`) are proved; the product-rule assembly and the `‖w'‖_∞`,
   `‖w''‖_∞` inputs are not.  Depends on (1) and (3).  *Not formalized.*

Obligations 2, 3 and 4 all reduce to obligations 1 and 3; obligation 3 is the
critical path.

## The lesion test

`Pub1LesionTest.lean.expected-fail` **must not compile.**  It replays
`secondDeriv_lt_of_certificate` with the residual bound inflated by the factor
101 from the evidence document's lesion record.  Run:

```bash
cd lean && lake env lean Pub1LesionTest.lean.expected-fail
```

Observed: `error: unsolved goals … ⊢ False` — with the lesioned constant the
arithmetic step is false, so the target proof becomes unusable.  The positive
counterpart, `concavity_margin_lesioned`, is a kernel-checked theorem stating
that the lesioned margin does *not* close.

The file is deliberately not a `.lean` module, so `lake build` never sees it.

## Provenance

Files under `ZetaLean/Pub1/Aristotle/` came from Harmonic's Aristotle (project
ids in `lean/ARISTOTLE-RUNS.md`).  Per `lean/proof_adapter.py`, the service's own
verification claim is input, not evidence: each file passed the static refusal
scan and `lake build` on this repository's toolchain before being used.

All twelve were produced against Lean v4.28.0.  Seven ported unchanged
(`A`, `B`, `F`, `H`, `H2`, `K`, `M`); five needed local repair to build against
the `v4.33.0-rc2` pin and record it in their headers:

| file | repair |
| --- | --- |
| `C` | `simpa [Function.uncurry]` left a `Pi.mul` normal form; replaced by an explicit `rfl` rewrite |
| `D` | both endings used `norm_num` with the interval-integral simp set, which makes no progress here; rewritten with explicit antiderivatives |
| `E1` | same, in `hUp_integral` |
| `E2` | `convert … using 1` did not fix the function, only the derivative; replaced by `HasDerivAt.congr_deriv` |
| `J` | `simpa [contDiff_zero]` normalized to `Pi.mul`; replaced by `contDiff_zero.mpr` |

`H` is superseded by `H2` (the same facts for a two-variable kernel, which is
what the clamped kernel needs) and is retained only as the difference-kernel
form of the row-bound argument.
