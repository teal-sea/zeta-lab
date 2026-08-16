/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import ZetaLean.Pub1.Numeric
import ZetaLean.Pub1.Closure
import ZetaLean.Pub1.Ramp
import ZetaLean.Pub1.Concavity
import ZetaLean.Pub1.Window
import ZetaLean.Pub1.Setting
import ZetaLean.Pub1.Profile
import ZetaLean.Pub1.Main
import ZetaLean.Pub1.Convergence
import ZetaLean.Pub1.Assembly
import ZetaLean.Pub1.Aristotle.D
import ZetaLean.Pub1.Aristotle.F
import ZetaLean.Pub1.Aristotle.H
import ZetaLean.Pub1.Aristotle.N
import ZetaLean.Pub1.Aristotle.R
import ZetaLean.Pub1.CertDefs
import ZetaLean.Pub1.CertAtoms
import ZetaLean.Pub1.Certificate

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
| `Main` | the principal theorem, in both orientations |
| `Aristotle/*` | externally generated lemmas, each kernel-checked here |

Everything under `Aristotle/` arrived from an external prover and counts for
nothing until it passes the static refusal scan and `lake build` on this
repository's own toolchain — the rule of `lean/proof_adapter.py`.  Several
needed local repair to build against the `v4.33.0-rc2` pin; each such file says
so in its header.

The still-open analytic inputs are listed in `ZetaLean/Pub1/OBLIGATIONS.md`.
-/
