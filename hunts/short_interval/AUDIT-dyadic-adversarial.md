# Adversarial re-audit of AUDIT-dyadic.md

Recorded 2026-09-12. A second delegated session, given the gating audit and
told to break it, working independently against the same commit of
`anthropics/formal-math` (`fbdc36bb`) and Wang arXiv:2609.07918v1. Kept
verbatim as evidence; the only edit is em dashes replaced by commas per
house style. Its verdict is folded into `MISSION.md` §6.2 and its eight
corrections to the proof outline were forwarded to the session writing
`PROOF-DRAFT.md` before that draft was finished.

# Adversarial review of `hunts/short_interval/AUDIT-dyadic.md`

Read-only. Sources: `anthropics/formal-math` sparse clone of `zeta23/` at `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (reachable, no fallback); Wang arXiv:2609.07918v1 HTML with the LaTeX `alttext` extracted (the `<` characters the audit lost are present there); `MISSION.md` §2, §4, §6. Nothing under `/home/user/zeta-lab` was edited. All `file:line` are relative to `zeta23/`. "Kernel-checked" means Lean 4 + Mathlib.

## A. Citation check

Every `file:line` in tables 1.1, 1.2, 1.3 was opened (60 citations, dumped to `scratchpad/readit/cites_dump.txt`) plus every citation in §1.4, §3, §4, §5, §6 (18 more). **All exist at the stated lines and say what the audit says; the verbatim Lean text in the tables matches the source.**

Mismatches, none load-bearing:

| Audit says | Clone at fbdc36b |
|---|---|
| `XiPrime/` "111 files, 29,749 lines" | 108 `.lean` files, 31,705 lines |
| "`2 \* T` occurs in 26 files under `XiPrime/`" | 22 files; the "51 elsewhere" and "0 in `WeilEF/`" are exact |
| `xiDeriv_fixedLamBounds`, `Final.lean:216` | line 219 (the admitted numbering artifact) |

**The inventory is incomplete.** Import graph built from `import` lines: 254 of 316 modules reach `Zeta23/XiPrime/Final.lean`. Reachable files with `2 * T` / `Icc T (2 * T)` hits that appear in no audit table and not in the §6 footprint:

| File | Range's role | Class |
|---|---|---|
| `ThmE/PPChi.lean` (imported by `XiPrime/PrimeSide/PP.lean:10`) | `Aminus Φ T y y'`, `Cm/Sm/Cp/Sp Φ T y`, `MV_four`, `Mform_cos_cos_ph`, `diag_estimate_chi:520-525` (`T / π * Σ … g(log n)`, `T` = range length), `O1_bound_chi:615-640` (`sin ((2 * T) * (log n − log m))`, endpoint only) | (a) identity / (b) c = λ, same mechanism as P20/P21 |
| `ThmE/PrimeSideChi.lean` (imported by `PrimeSide/Trace.lean:21`) | `Aphi_mul_norm_tauKernel_le`, `abs_sin_mul_norm_geom_le`, consumer of `riemann_sum_monotone` at `:913` | (a) |
| `PrimeSideA/Basic.lean` | `abs_Mform_le:236-244`: `\|𝓜[u,v]\| ≤ Bu·Bv·(T·∫Φ²)`; `riemann_sum_monotone:879-882` (B.1) | (a)/(b) |
| `PrimeSideA/CrossMuPCore.lean` | `abs_Mform_cos_phase_le:130-134`: `≤ (4B + D·T)·∫Φ²/\|y\|` with `hvol : volume.real (Icc T (2T)) = T` at `:151`; `D·T = ∫_I\|μ'\| = O(1)` | (a) |
| `PrimeSideB/PPOffDiag.lean` | `MV_real hMV X (2 * T)` at endpoints | (a) |
| `Defs/LeafIntegrals.lean:25,51,77` | `∫_T^{2T}(1+(τ−T))^{-2} ≤ 1`, `≤ 2` (the `lem:ends` weight) | (a), range-free bound |
| `Tail/Basic.lean:18,36`, `PrimeSideA/EndsWeighted.lean:218-229`, `PrimeSideA/MuMu.lean:71`, `XiPrime/Transfer/W.lean:306,333,337`, `XiPrime/PrimeSide/Moments.lean:81-109`, `XiPrime/Hardy/ZFunction.lean:339-366` | cosmetic / Hardy copies of P17-P18 | (a)/(b) |

None is class (c). The audit never mentions `ThmE/*`, though two of its files sit on the ξ' prime side's import path and carry the range inside the MV identity.

## B. Findings

### B.1 Condition 4 and the P11 classification are false as stated: `d` is consumed two-sidedly

Audit: condition 4, "every downstream use is an upper bound"; class (a): "P11 … every use is an **upper** bound and holds a fortiori"; class (c) rejection: "the span bound `d h ≤ T` (P11) is consumed only as an upper bound on `δ_kl`".

Lean, `Zeta23/PrimeSideA/Basic.lean:876-882, 890`:
```
/-- ... `d = ⌊T/h⌋` (§5.2: `h Σ_{k=0}^{d−1} μ(τ_k) = ∫_T^{2T} μ + O(h μ(2T))`,
`recall T < T + dh ≤ 2T < T + (d+1)h`). -/
lemma riemann_sum_monotone {μ : ℝ → ℝ} {T h : ℝ} (hh : 0 < h) (hhT : h ≤ T)
    (hmono : MonotoneOn μ (Set.Ici (T - h))) (hnonneg : ∀ x, T - h ≤ x → 0 ≤ μ x) :
    |h * ∑ k ∈ Finset.range ⌊T / h⌋₊, μ (T + k * h) - ∫ x in T..(2 * T), μ x|
      ≤ 2 * h * μ (2 * T) := by
  ...
    have := Nat.lt_floor_add_one (T / h); rw [← hd] at this
```
and `:962` `hlen : 2 * T - (T + h * d') ≤ 2 * h`. Consumed by `PrimeSideA.lean:140` (`prop_trace_mu`) → `prop_trace:300-304` → `XiPrime/PrimeSide/Trace.lean:184-192` (`prop_trace_W`): **this is the main term of `tr G̃`**, and it needs the grid to *fill* the window to within one spacing, i.e. the floor's lower inequality.

Second instance, `Zeta23/PrimeSideA/EndsE1.lean:262-266`:
```
/-- `τ_d = T + d h > 2T − h` (since `d = ⌊T/h⌋`). -/
theorem tau_d_gt (hL : 0 < p.L) (_hT : 0 < p.T) : 2 * p.T - p.h < p.tau p.d := by
  ...
  have hlt : p.T / p.h < (p.d : ℝ) + 1 := by rw [hd]; exact Nat.lt_floor_add_one _
```
used for the majorant of the missing lattice mass `ρ` on `I` in `lem:ends` (`𝓔₁`).

My claim: both localize with `d_H := ⌊H/h⌋` (same two floor inequalities, proofs verbatim with `2T ↦ T+H`), so this is not class (c) and the verdict does not fall. But a formalization following the audit literally (weaken `d ≤ LT/2π` to `d_H ≤ LH/2π`, everything else "a fortiori") will not compile. The audit answered the class (c) question for P11 from `Transfer.lean` alone; the two-sided uses live in `PrimeSideA/`, which it read at docstring level.

### B.2 Class (b) exponents: all re-derived, all confirmed

| Row | Error from the Lean | Against | c | Check |
|---|---|---|---|---|
| P4/P6 | `Tail.lean:676-679` `NII ≤ 6A₀√T·l` | `Hl` | 1/2 | correct; `theta0`'s `/T` at `Tail.lean:57` is `D0² = T` hard-coded |
| P3/P5 | `θ₀ ≤ C l T^{λ/2−1}` | 1 | height | correct, `count_certificate` needs only `hBto` |
| P13 | `:362-378` `(aL²)⁻¹·d·C T^{−δ}·2` | `N` | −δ | with `d_H`: `C T^{−δ}H/(πa₀L)` vs `Hl/4π`; correct |
| P14 | `:380-425` `2C²T^{−2δ}(8d(1+L/2π)+d²/T²)/(a₀L²)²` | `N` | −δ | `O(T^{−2δ}H/L²)` vs `Hl`; the `d_H²/T²` piece only shrinks |
| P15/16/18 i2/19 | `K₀ = A L³ l⁴(1+X)` → `l⁴X/L` | `Hl` | λ | correct; `PPUpper`'s last three terms are range-free, first is `p.T·p.L·Σ‖e‖²/N` with `eT : ((Pf T).toSetting T).T = T` in `reexpansionGeom_of` (see D.5) |
| P17 | `:721-736` `(a₀L²)⁻¹(2/log 2)L²σρ = κtr√X`, `σ = A√X·l`, `ρ = ρ₀/l` | `Hl` | λ/2 | correct; bound is **independent of `d`** (`Aphi_mul_norm_tauKernel_le'` "for every K"), Abel cap `W = max δ_kk ≤ H/2T` shrinks |
| P18 i1 | `2Aρ₀²/a₀²·T ≤ η²/(8π)·Tl` | proportional | none | `K₁ = A L⁴ H l²`, same |
| P22 | `Ends.lean:114-118` `C·L·l·log l·B²`, `B = l + S₁/π` | `HLl²` | λ | correct; `LeafIntegrals` gives `∫_I g ≤ 2` range-free |
| P24 | `Traces.lean:134-139` `l²X/T ≤ T^{(λ−1)/2}` | `H` | λ | correct; `cross_muP` is `(4B + D·T)∫Φ²/\|y\|` with `D·T = O(1)`, in `I_H` it is `D·H ≤ D·T`; `cross_PPi` is `abs_Mform_le` `Bu·Bv·H·∫Φ²` with `Bv` = `PiX_abs_le` (`PiFacts.lean:29`) `O(√X/T)` |
| P21 | `O1_bound_chi` `16C·∫Φ²·ΣΛ(n)²` | `HLl²` | λ | correct and **endpoint-only** |
| P35/S9/P2 | `log T` | `HL` | 0 | correct |

No dropped log matters: every exponent is a strict power inequality. Consumers of P1/P2 (P4, P13, P14, P17, P18, P35, `tendsto_N_atTop`, `kappa_nonneg_of_coeffMoments`) all need `N_H ≥ Hl/4π`, which comes from the §5 count, whose proof uses none of P1/P2. **No circularity.**

### B.3 The (H3) claim: confirmed, T-dependence enumerated

`Coeff/` (19 files) imports among itself plus `XiPrime.Defs`, `Chebyshev`, `Transfer/Inputs`, Mathlib. Every `T` token in the tree is (i) `l T`, (ii) `LT T = l/2 + iπ/4` (`Defs.lean:85`) or generic `Λf T`/`Lb T`, or (iii) a threshold, e.g. `H3.lean:72` `⟨2 * Real.pi * Real.exp l₀, …⟩`. **Zero** `Real.log T`, `2 * T`, `T ^`, `√T`, or any `x ≤ T` constraint. Ranges `2 ≤ x ≤ exp (l T)`, `0 ≤ y ≤ l T` (`Statement.lean:158-166`, `Inputs.lean:58-71`) contain `X = e^{λl}` for every `λ < θ < 1`. Audit §4 stands.

### B.4 Entry dependence: nothing needs `δ_kl` bounded below or a full span

`Transfer.lean:640-660`: the only lower-side facts are `hδnn : 0 ≤ deltaKL` (from `τ_k ≥ T`) and `hδv_mono` (`deltaKL_diag_monotone`), both true on any sub-grid from `T`. The expansion is applied at `δm := min δ (1/2)`; `deltaKL_mem` (`:472-490`) only shows `δm = δ`; on `I_H` the cap is never active. `dependence_frob` needs `0 ≤ δm ≤ 1/2` for `geom_partial_le` (`Dependence.lean:372`). Audit's "easier" is right.

### B.5 The local count: chain confirmed, one statement-shape correction

`GoodHeight T := ∀ ρ, IsXiDerivZero ρ → ρ.im ≠ T` (`Contour.lean:31`); `exists_goodHeight` in every `Icc a (a+1)` (`:34-43`); `halfContour_Yfn_bound` for all `T₀ ≤ T₁ ≤ T₂` (`ZeroCount.lean:111-114`); `gamma_side` exact (`GammaSide.lean:121`); `halfContour_xiDeriv_split` at any two good heights (`:43-46`). Two good heights are two independent applications; nothing couples them. So `N_ξ'(T,T+H) = ∫_T^{T+H} μ + O(log T)`, and the μ-integral is `(H/2π)l(T) + H²/(4πT)(1+o(1)) + O(1/T)`. The `H²/T = T^{2θ−1}` term is a genuine power of `T` (larger than `log T` for `θ > 1/2`), `O(H)` only because `H/T → 0`. The audit says this. Correct.

The correction: the tree's interface does not consume Wang's (1.2). `prop_trace` (`PrimeSideA.lean:300-304`) and `prop_trace_W` (`Trace.lean:184-188`) take
```
∀ N : ℝ, |N - p.T * p.ell1 / (2 * π)| ≤ A * p.l →
  |trGtW cPi c p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X + p.L * S1 c p.X)
```
i.e. count within `O(log T)` of the μ-main term (supplied by `rvm_evBound`, `Moments.lean:110`). Condition 3's form `N_H = HL/2π + O(H + log T)` does **not** satisfy that hypothesis shape (`O(H) ≫ O(l)`). Either state the sharper form (the contour argument gives it), or relax the hypothesis to `≤ A·H` with remainder `C(L√X + L·S₁ + L·H)`, still `o(aLN_H)`. Mathematically harmless (conclusions are `~[atTop]`), but the audit's outline names the weaker statement.

### B.6 Wang's conditions and the ξ' power saving

Alttext: Notation `0<\lambda<\theta<1, H=T^{\theta}, L=\log T, I=(T,T+H]`; Theorem 2.2 `0<\lambda<\theta<1`, `\operatorname{supp}g\subset[-\lambda,\lambda]`, (2.5) error `O_{g}(H+T^{\lambda}L^{2})`. Strict, as the audit says. Mechanism (Lemma 2.4 `O(xL³)` from `xL² log(2+H)` at the ends; Prop 2.6 MV `x log²(2x)`; the `H` from `M₀` and `HΣa_n²`) is what the audit maps to `lem:ends`/`PPUpper`.

The ξ'-specific saving: `XiEF` error `C T^{−δ}(1/max 1 Δ² + 1/T)`, `δ = (1−3λ/4)/2` (`Statement.lean:196-208`, `FamilyFacts.lean:91-98`), a **height** bound (`cauchyK_far` with `T ≤ a = τ_k`), uniform over the grid, positive for `λ < 4/3`. Summed over `d_H ≍ HL` entries against `N_H ≍ Hl`: `T^{−δ}L/l → 0` (trace), `T^{−2δ}H/L² ≪ Hl` (Frobenius). It never competes with `H`. **No additional constraint.**

### B.7 Other candidates examined and rejected

`PoissonSq` (`ZeroSide.lean:804-805`, full lattice, truncation is a sub-sum of non-negatives); prop:block (`ZeroSide.lean:786-830`, pure linear algebra of the finite multiset); Lemma R (`SeamMult.lean:46-53`); `ell1`/`lam1` (cancels in `cRatio`, becomes `L/l = λ`; a definitional change, cosmetic); the fold (functional equation); P34 (not part of a short-interval statement); `WindowZeroSide` (`XiPrime/Assembly.lean:277-283`, height only).

## C. Verdict

**The PASS WITH CONDITIONS verdict stands.** No step uses the dyadic structure to produce a main term; every dyadic use reachable from `xiDeriv_simple_on_line` is cosmetic or an absorption whose exponent I re-derived; the two named exponent conditions are the only ones; the `D₁` corrections are range-free; entry dependence is easier; the local count is a corollary.

Two conditions need rewording, not strengthening:
- **Condition 4** must read: `d_H := ⌊LH/2π⌋` as a floor with **both** floor inequalities re-proved, because `riemann_sum_monotone` (`PrimeSideA/Basic.lean:890`) and `tau_d_gt` (`PrimeSideA/EndsE1.lean:266`) consume the lower one. "Every downstream use is an upper bound" is false.
- **Condition 3** should name the statement the interface consumes: `N_ξ'(T,T+H) = ∫_T^{T+H}μ + O(log T)`, from which Wang's (1.2) follows.

Checked: all 78 citations; import reachability (254 modules) and whole-tree grep for `2 * T`, `2*T`, `Ioc/Icc T (2`, `ell1`, `lam1`, `T / (2 * Real.pi)` restricted to the reachable set, every un-inventoried hit opened; every `T` token under `Coeff/` and its imports; `Transfer/Inputs.lean` in full, `Dependence.lean` §A-C, `Transfer.lean` §3-4 (`hatNegligible_of_geom`, `reexpansionGeom_of`); `ZeroCount/Contour.lean`, `ZeroCount.lean`, `GenericRvM.lean`, `GammaSide.lean`, `IntMu.lean`, `Hypotheses.lean` (Stirling, `int_mu(_sq)`, `MVHilbert`); `PPUpper.lean`, XiPrime `PP.lean` identity and MV region, `ThmE/PPChi.lean` diag/O1/O2; `PrimeSideA/Basic.lean`, `CrossMuPCore.lean`, `EndsE1.lean`, `Ends.lean`; `Traces.lean` remainders and `tendsto_l_sq_mul_X_div`; `Concrete.lean` `concreteData` and `pp`/`cmuP`/`cmuPi`; `Tail.lean` `theta0`, `eventually_theta0_le`, `eventually_NII_le`, `Tail/Count`, `Tail/Grid`; `ZeroSide.lean` block structure; `SeamMult.lean`, `Certificate.lean`; `Window.lean` and `eps_form_of_continuousOn`; `Statement.lean` §3-5; `Final.lean` headline/fixed-λ/limit/Hardy regions; `XiPrime/Assembly.lean` `gzMoments_of_transfer`, `WindowZeroSide`, `fixedLam_family`; `PiFacts.lean`; Wang §1-3 with the proof of Theorem 2.2 and Lemmas 2.3-2.6. Not checked: proofs of the `XiEFAssembly`/`TestWeight` leaf lemmas beyond P27-P30; the Hardy arm beyond statements; `lake build` (not run).

## D. Corrections to the audit's proof outline

1. **Step 2**: state and prove `|N_ξ'(T,T+H) − ∫_T^{T+H}μ| ≤ C log T` first; that plus the μ-integral is what `rvm_evBound`/`prop_trace_W` consume. Wang's (1.2) form is a corollary, not the input.
2. **Step 6a** localizes `PrimeSideA/Basic.lean:879 riemann_sum_monotone` and `PrimeSideA.lean:140 prop_trace_mu`, not only `IntMu.lean`, and needs the floor lower bound on `d_H`.
3. **Step 6b** localizes `EndsE1.lean:263 tau_d_gt` (lower bound on `d_H`) and `Defs/LeafIntegrals.lean:25,51,77`.
4. **Step 6d** localizes `ThmE/PPChi.lean` (`Aminus`, `Cm/Sm/Cp/Sp`, `MV_four`, `Mform_cos_cos_ph`, `diag_estimate_chi`, `O1_bound_chi`), `PrimeSideB/PPKernel.lean` (`Ix`, `T − |x|`), `PPOffDiag.lean`, `MuMu.lean:71`. The "Untouched" list is right; the "To touch" list omits `ThmE/PPChi.lean`, `ThmE/PrimeSideChi.lean`, `PrimeSideA/Basic.lean`, `PrimeSideA/CrossMuPCore.lean`, `PrimeSideB/PPOffDiag.lean`, `PrimeSideA/MuMu.lean`, `Defs/LeafIntegrals.lean`, `Tail/Basic.lean`, `XiPrime/Transfer/W.lean`, `XiPrime/PrimeSide/{Moments,Concrete}.lean`.
5. **Step 5b/6d (`p.T ↦ H`)**: the range enters `PPUpper` through `Zeta23.PrimeSide.Setting.T` (`PrimeSideA/Defs.lean:65-87`: `T`, `d := ⌊LT/2π⌋`, `tau`, `I` are all `Setting` fields/defs; `eT : ((Pf T).toSetting T).T = T` in `reexpansionGeom_of`). The `(T, U)` parameterization must be threaded through `Setting`, not only `Params`; otherwise `p.T` is at once the height (`NuBound`'s `log⁺(|τ|/4T)`, `PiX`, thresholds) and the range length (MV diagonal).
6. **Step 7 (`λ → θ⁻`)**: `eps_form_of_continuousOn` (`Window.lean:364-373`), `exists_lt_one_pos` (`:345`) and `ThmD.eps_form_of_approx` (`ThmD/Limit.lean:73-78`) are hard-wired to `Icc (1/2) 1` and endpoint `1`. A version with endpoint `θ` (or a rescaling) is a new lemma, trivial but not verbatim. `continuousOn_kappaXi_vFlat` on `Ioc 0 1` (`:391`) does supply the continuity.
7. **Step 6f (`lam1 = λ`)** requires redefining `Params.lam1` (`Defs.lean:209-210`, `L/ell1`) or restating `TracesBoundsXi.ratio`/`frhat` (`Traces.lean:60-64`) with `L/l`; `momentsW_of_family`'s `hc` (`Moments.lean:105-108`) is stated in `P.lam1 T`.
8. **Ordering**: the short-window count (step 2) must precede step 5, because P13/P14/P17/P18 close with `gcongr` against `T l/4π ≤ N` (`Transfer.lean:378, 425, 736, 784`); the step list has this right, the §2 table lists P1 last.

Scratch artifacts (clone, citation dumps, reachability list, Wang text) are under `/tmp/claude-0/-home-user/d7bb5a84-33b0-5d58-8124-1025c221a1d8/scratchpad/readit/`; the harness refused `REPORT.md`, so this message is the report.
