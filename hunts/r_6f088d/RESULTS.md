# Hunt R-6F088D Results: zeta23ext root load and arm collision analysis

Run `bc87fba6-95d1-4ce0-a9ef-c7e364c95bcb`, 2026-08-18. Hunt #49.

**Status: settled.** The failure mechanism, scoping history, and remaining symbol duplication across the five arms of `zeta23ext` are mapped, measured, and verified with exact compiler reproductions.

Nothing here is evidence for or against RH (`docs/08`).

## 1. The Core Mechanism

The root assembly module `Zeta23Ext.lean` could not load when importing multiple arms simultaneously because three distinct arms (`EForm`, `EForm2`, `EForm3`) all declare definitions under the identical namespace `Retention`.

In Lean 4, when two imported modules define declarations with identical fully-qualified names (for instance `Retention.Aconst`), Lean immediately halts elaboration of the importing module:

```
error: import Zeta23Ext.EForm2.Main failed, environment already contains 'Retention.Aconst' from Zeta23Ext.EForm.Main
```

This error is demonstrated on a minimal two-file reproduction compiled under Lean 4 (`v4.33.0-rc2`):
- `ModA.lean`: `namespace Retention def Aconst : Nat := 42 end Retention`
- `ModB.lean`: `namespace Retention def Aconst : Nat := 42 end Retention`
- `Root.lean`: `import ModA import ModB` -> `error: import ModB failed, environment already contains 'Retention.Aconst' from ModA`

## 2. Census of Arms and Definitions

The package `hunts/frontier_math/zeta23ext/` contains 64 Lean source files across five separate development iterations (arms):

| Arm | Primary Entry File | Namespace | Normalizing Constant $A$ | Autocorrelation $c_2(w)$ | Window Kernel $g(u)$ | Energy Functional |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Arm 0** (`PairEnergy`) | `PairEnergy.lean` | `_root_` (global) | `_root_.Aconst` | `_root_.c2` | `_root_.gker` | Inline in theorem |
| **Arm 1** (`EForm`) | `EForm/Basic.lean` | `Retention` | `Retention.Aconst` | `Retention.c2` | `Retention.gker` | `Retention.En` |
| **Arm 2** (`EForm2`) | `EForm2/Defs.lean` | `Retention` | `Retention.Aconst` | `Retention.c2` | `Retention.gwin` | `Retention.Ener` |
| **Arm 3** (`EForm3`) | `EForm3/Defs.lean` | `Retention` | `Retention.Aconst` | `Retention.c2` | `Retention.g` | `Retention.Eng` |
| **Arm 4** (`TruncEst`) | `TruncEst/Kernel.lean` | `TruncEst` | `TruncEst.A` | `TruncEst.c2` | `TruncEst.g` | (Not defined) |

### Mathematical Equivalence of Duplicated Definitions

1. **The Normalizing Constant $A$**:
   - In Arm 0, 1, 2, 3: `noncomputable def Aconst : ℝ := Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)`
   - In Arm 4: `def A : ℝ := Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)`
   - Exact numeric value: $A = \sqrt{2}\sin(1/\sqrt{2}) pprox 0.9189037...$

2. **The Window Kernel $g(u)$**:
   - In Arm 0: `gker (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * u) else 0`
   - In Arm 1: `gker (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * u) else 0`
   - In Arm 2: `gwin (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * u) else 0`
   - In Arm 3: `g (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * u) else 0`
   - In Arm 4: `g (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * u) else 0`
   - All five definitions are mathematically and definitionally identical.

3. **The Autocorrelation $c_2(w)$**:
   - In Arm 0, 1: `∫ u, gker u * gker (u - w)`
   - In Arm 2, 3: `∫ u, g u * g (u + w)` (equivalent by evenness of $g$)
   - In Arm 4: Closed-form piecewise algebraic formula `if |w| ≤ 1 then c2core |w| else 0`, proved equivalent to the integral in `TruncEst/Autocorrelation.lean` (`c2_eq_autocorrelation`).

## 3. Full List of Detected Symbol Collisions

A full scan of the 64 modules in `zeta23ext` identifies **17 colliding fully-qualified declaration names** across distinct files:

| Fully-Qualified Symbol Name | Distinct Files | Occurrences |
| :--- | :--- | :--- |
| `Retention.Aconst` | 3 | `EForm/Basic.lean:17`, `EForm2/Defs.lean:23`, `EForm3/Defs.lean:19` |
| `Retention.Aconst_ge` | 2 | `EForm/Sharp.lean:329`, `EForm2/Estimates.lean:100` |
| `Retention.Aconst_pos` | 3 | `EForm/Energy.lean:87`, `EForm2/Bridge.lean:178`, `EForm3/ClosedForm.lean:189` |
| `Retention.c2` | 3 | `EForm/Basic.lean:14`, `EForm2/Defs.lean:20`, `EForm3/Defs.lean:22` |
| `Retention.c2_le_one` | 2 | `EForm/Basic.lean:120`, `EForm3/Gap.lean:46` |
| `Retention.c2_nonneg` | 2 | `EForm/Basic.lean:57`, `EForm3/Integrability.lean:75` |
| `Retention.Fsum` | 3 | `EForm/Decomposition.lean:10`, `EForm2/Defs.lean:49`, `EForm3/Defs.lean:38` |
| `Retention.master` | 3 | `EForm/Energy.lean:53`, `EForm2/Fourier.lean:138`, `EForm3/Master.lean:95` |
| `Retention.Phi2_shift` | 2 | `EForm2/Bridge.lean:58`, `EForm2/Expand.lean:127` |
| `Retention.Qim` | 2 | `EForm2/Defs.lean:41`, `EForm3/Defs.lean:32` |
| `Retention.retention_gap` | 3 | `EForm/Main.lean:53`, `EForm2/Expand.lean:283`, `EForm3/Main.lean:60` |
| `Retention.retention_le_three` | 3 | `EForm/Main.lean:150`, `EForm2/Main.lean:59`, `EForm3/Main.lean:114` |
| `Retention.retention_of_damage` | 2 | `EForm2/Main.lean:24`, `EForm3/Main.lean:70` |
| `Retention.retention_separated` | 2 | `EForm2/Main.lean:76`, `EForm3/Main.lean:105` |
| `Retention.sep_mono` | 2 | `EForm2/Counting.lean:81`, `EForm3/Counting.lean:44` |
| `Retention.Shq` | 3 | `EForm/Sharp.lean:141`, `EForm2/Defs.lean:45`, `EForm3/Defs.lean:35` |
| `Retention.Shq_nonneg` | 2 | `EForm/Sharp.lean:152`, `EForm2/Estimates.lean:247` |

## 4. Scoping vs. Duplication

The historical development progressed through successive iterations:
- **EForm (Arm 1)**: Initial formulation of retention gap and proof for $n \le 3$.
- **EForm2 (Arm 2)**: Reformulation extending retention to separated configurations with gap $\delta \ge 26$.
- **EForm3 (Arm 3)**: Sharpened iteration lowering separation to $\delta \ge 4$, integrating the O9 two-dimensional checker, and correcting numerator/denominator leaf representations.

Because each iteration was developed as an autonomous proof artifact, each arm redefined the problem from scratch in `namespace Retention`.

When `Zeta23Ext.lean` was updated to import `EForm.Main`, `EForm2.Main`, and `EForm3.Main` simultaneously, Lean rejected the combination due to the 17 identical declaration names.

### Resolution Options:
1. **Scoping (Sub-namespacing)**: Place Arm 1 in `Retention.EForm1`, Arm 2 in `Retention.EForm2`, and Arm 3 in `Retention.EForm3`. This eliminates collision while retaining all historic proofs.
2. **Pruning (Supercession)**: In `Zeta23Ext.lean`, import only the active, strictly stronger arm (`EForm3.Main`) along with `TruncEst` and `BandCert`, leaving earlier arms in the directory tree but un-imported from the root assembly.
3. **Common Core Extraction**: Extract `Aconst`, `c2`, `g`, and `Shq` into a shared `Zeta23Ext.Retention.Core` module and have all arms import that core.

## ## Loose threads

1. **Common Core Refactoring in Zeta23Ext**:
   - What it is: Extracting `Aconst`, `c2`, `g`, and their basic positivity/integral lemmas into a single shared module `Zeta23Ext/RetentionCore.lean`.
   - Why it might matter: Allows all historic arms to be imported into a single root module without renaming or qualifying their local theorems.
   - Concrete first step: Create `Zeta23Ext/RetentionCore.lean` with `Aconst`, `c2`, and `gker`, and rewrite `EForm/Basic.lean`, `EForm2/Defs.lean`, and `EForm3/Defs.lean` to import it.

2. **Integration of PairEnergy with RetentionWired**:
   - What it is: `PairEnergy.lean` defines `_root_.Aconst` and `_root_.c2` globally, while `RetentionWired.lean` references `RetentionAlgebra.margin_eq`.
   - Why it might matter: Moving `PairEnergy` into `namespace Zeta23Ext.PairEnergy` prevents potential global namespace pollution with upstream `Zeta23` formalizations.
   - Concrete first step: Add `namespace PairEnergy` to `PairEnergy.lean` and update calling sites in `Zeta23Ext.lean`.
