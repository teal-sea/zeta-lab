module

/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
public import ZetaLean.Pub1.Numeric
public import ZetaLean.Pub1.Closure
public import ZetaLean.Pub1.Ramp
public import ZetaLean.Pub1.Concavity
public import ZetaLean.Pub1.Window
public import ZetaLean.Pub1.Setting
public import ZetaLean.Pub1.Profile
public import ZetaLean.Pub1.QDiff
public import ZetaLean.Pub1.ZBounds
public import ZetaLean.Pub1.UppFormula
public import ZetaLean.Pub1.ZppBound
public import ZetaLean.Pub1.UpolyD2
public import ZetaLean.Pub1.Concave
public import ZetaLean.Pub1.Unconditional
public import ZetaLean.Pub1.Aristotle.Y
public import ZetaLean.Pub1.Main
public import ZetaLean.Pub1.Convergence
public import ZetaLean.Pub1.Assembly
public import ZetaLean.Pub1.Aristotle.D
public import ZetaLean.Pub1.Aristotle.F
public import ZetaLean.Pub1.Aristotle.H
public import ZetaLean.Pub1.Aristotle.N
public import ZetaLean.Pub1.Aristotle.R
public import ZetaLean.Pub1.CertDefs
public import ZetaLean.Pub1.CertAtoms
public import ZetaLean.Pub1.Certificate
public import ZetaLean.Pub1.CertL2
public import ZetaLean.Pub1.CertArith
public import ZetaLean.Pub1.TruncKernel
public import ZetaLean.Pub1.QBound
public import ZetaLean.Pub1.WRegularity
public import ZetaLean.Pub1.Aristotle.V
public import ZetaLean.Pub1.Aristotle.W
public import ZetaLean.Pub1.Aristotle.TU2
public import ZetaLean.Pub1.Aristotle.J2
public import ZetaLean.Pub1.TaperAdmissible
public import ZetaLean.Pub1.ZResolvent
public import ZetaLean.Pub1.TailBound
public import ZetaLean.Pub1.EuBound
public import ZetaLean.Pub1.CertBounds
public import ZetaLean.Pub1.Regularity
public import ZetaLean.Pub1.Aristotle.S
public import ZetaLean.Pub1.Aristotle.T
public import ZetaLean.Pub1.Aristotle.U

@[expose] public section

/-!
# Pub 1 source-admissible strong closure

Formalization of the theorem of
`hunts/wide_search/RESULTS-xiprime-admissible-closure.md` (Zeta Lab PR #45):

```
      sup_{v ∈ 𝒜_source}  ⟨1,v⟩² / ⟨Av,v⟩  =  ⟨1, A⁻¹1⟩  =  c*,
      inf_{v ∈ 𝒜_source}  ⟨Av,v⟩ / ⟨1,v⟩²  =  1/c*.
```

## Module map

| module | content |
| --- | --- |
| `Numeric` | the exact rational comparisons, incl. the concavity margin and its lesion |
| `Closure` | the variational engine over an abstract real inner product space |
| `Ramp` | the `C³` endpoint ramp `η` |
| `Concavity` | strict concavity ⟹ `w'(0)=0` ⟹ strict radial decrease |
| `Window` | the source-admissible class, the taper `φ_L`, `‖v_L-w‖₂² ≤ 2/L` |
| `Setting` | `F₁`, the clamped kernel, the coercive form, existence of `w` |
| `Profile` | the ambient upper bound `⟨1,v⟩² ≤ c*⟨Av,v⟩` |
| `Main` | the variational engine's `StrongClosureData` interface |
| `WRegularity` | interior `C²` of `w`, with `‖w'‖_∞` and `‖w''‖_∞` |
| `Cert*` | the exact-rational certificate: `A₀u + r₀ = 1`, `∫r₀²`, the arithmetic |
| `QBound`, `QDiff`, `TailBound` | `‖q‖_∞`, `‖q - q_M‖_∞`, and the kernel tail |
| `ZBounds`, `ZppBound` | `‖z‖_∞`, `‖z‖₂`, and `‖w'' - u''‖_∞ < 0.006060899845` |
| `Concave` | strict concavity ⟹ radial monotonicity of `w` |
| `TaperAdmissible` | the taper is `C_c²` with uniform `L¹` derivative bounds |
| `Unconditional` | **the principal theorems, with no hypothesis left** |
| `Aristotle/*` | externally generated lemmas, each kernel-checked here |

Everything under `Aristotle/` arrived from an external prover and counts for
nothing until it passes the static refusal scan and `lake build` on this
repository's own toolchain, the rule of `lean/proof_adapter.py`.  Several
needed local repair to build against the `v4.33.0-rc2` pin; each such file says
so in its header.

The development is complete: `Unconditional.pub1_strong_closure` and
`Unconditional.pub1_strong_closure_reciprocal` carry no analytic or membership
hypothesis, and `pub1_strong_closure_exists` carries none at all.
`ZetaLean/Pub1/OBLIGATIONS.md` is the closure record: it says how each of the
four analytic obligations was discharged, and is no longer a list of open work.
-/
