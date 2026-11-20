# Atlas of the Alpoge Lean archive (hunt #160, day one, 2026-11-20)

This is a text-level reading. Every statement below was read off the text of
the unpacked archive with `rg`, `sed` and standard-library Python. No Lean was
run, nothing from the archive was executed, and no kernel has checked the
archive. A separate session owns the kernel replay (`hunts/alpoge_replay/`, on
another branch): it is pending, and this atlas states no verdict on it.

## 0. Scope and grade

**What the object is.** On 2026-11-20 Levent Alpoge posted a note claiming a
Lean 4 proof of the Riemann hypothesis and of the generalized Riemann
hypothesis for Dirichlet L-functions, with a 14-part tarball. Joined, the
tarball has sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
It unpacks to 175,187 `.lean` files under `lean/src`, pinned to Lean
`v4.33.1` and Mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474` (tag
`v4.33.1`).

**What this atlas is.** The map a reader wants before opening a file: what is
stated at the top, the chain of named terms from `Main.lean` down to the last
step that mentions zeros, the one analytic interface, where arithmetic enters,
how the author's 20 timeline items sit against the tree, how large the tree
is, which directory names mislead, what else is stated along the way, and
where an auditor should look first.

**Grades.** Two only, and neither is a rung above *measured* on the lab's
ladder.

- *Text-level reading, quotes replayable.* A claim of the form "the archive
  states X at `path:line`". Each one rests on a citation recorded in
  `quotes.json` with the sha256 of the cited lines; `verify_quotes.py` replays
  all of them against any unpacked copy. Plain-mathematics readings next to a
  quote are this lab's reading of the quoted text and are marked as readings.
- *Measured count.* A number produced by `recount.py` from file text (lines,
  import lines, line-start keywords). Declaration counts are regex counts and
  approximate.

**Wording.** "The archive states" means a line of text says so. It never
means the statement is proved: that is the kernel replay's question. Names in
the archive are machine-generated and several are shown below to be
misleading, so no reading here rests on a name.

**Provenance.** Nine readers worked the archive this morning. Their notes
were the starting point; every claim kept here was opened again in the archive
and re-read by the builder. Several reader statements were corrected or
sharpened in the process, and three questions the readers left open were
closed at text level; each is flagged where it occurs (sections 5, 6, 7, 9
and 10). This atlas is original to the lab. It
makes no novelty claim.

**Citations.** A citation is `path.lean:first-last`, relative to the
directory that holds `Main.lean`. Long directory names are abbreviated:

| abbr. | directory |
|---|---|
| `CB` | `Development/AutomorphicArithmetic/CharacterBoxes` |
| `TGC` | `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses` |
| `DL` | `Development/AutomorphicArithmetic/DedekindLFunctions` |
| `LT` | `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems` |
| `PC` | `Development/AutomorphicArithmetic/PrimitiveCosets` |
| `TPS` | `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries` |
| `FND` | `Development/AutomorphicArithmetic/Foundations` |
| `AV` | `Development/AutomorphicArithmetic/AutomorphicVarieties` |
| `AVT` | `Development/AbelianVarietyTheory` |
| `SWB` | `Formalism/SizeWindowBrackets` |

A path beginning `Mathlib/` is in the Mathlib checkout at the pinned tag.

## 1. The statements

The archive's last file states five theorems.

`Main.lean:4-12`
```lean
theorem riemannHypothesis : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

Four of the five types are defined in a file that imports only Mathlib.

`Statements.lean:3-8`
```lean
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

`Statements.lean:10-16`
```lean
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

The fifth is Mathlib's own, at the pinned tag.

`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185-186`
```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

Readings.

1. These are statements in Mathlib's vocabulary: `riemannZeta`,
   `DirichletCharacter.LFunction`, `RiemannHypothesis`. A scan of all 175,187
   files finds no declaration in the archive named `riemannZeta`,
   `RiemannHypothesis`, `completedRiemannZeta` or `vonMangoldt`. Two
   declarations named `LFunction` exist in archive namespaces
   (`GroundTheory/AutomorphicForms/GL2/GJLocalZeta.lean:431` and
   `GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean:363`); the
   statements above write `DirichletCharacter.LFunction` in full, so they do
   not refer to those.
2. `riemannZeta_eq_zero_re` and `riemannHypothesis` are given the same term,
   `rhOfAll`. That can only typecheck if the archive's
   `RiemannZetaZerosOnLine` unfolds to Mathlib's `RiemannHypothesis`. On the
   text the two differ only in notation: the binder style, and where the cast
   of `n` is written.
3. The half-plane statement carries the side condition `(χ ≠ 1 ∨ s ≠ 1)`: the
   point `s = 1` is excluded for the trivial character of every modulus, where
   the L-function has its pole and Mathlib's function takes a conventional
   value.
4. `DirichletLZerosOnLine` is stated for every character, primitive or not.
   That is consistent: an imprimitive L-function differs from the primitive
   one by finitely many Euler factors whose zeros lie on `Re s = 0`.
5. `riemannZeta₁`, which the analytic files use, is Mathlib's
   (`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:536`), not an archive name.

## 2. The spine: from Main.lean to the last step that mentions zeros

Each node is one named term. "Uses" means the term appears in the proof text
at the cited lines; whether a kernel accepts the application is not decided
here.

**S1. The four top-level terms.**

`Supplements/Kernels/MainTheorems.lean:7-16`
```lean
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi

theorem critAll (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  Formalism.VW.critLine allChi N χ hχ s h0 h1 hz

theorem claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta :=
  ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩
```

Reading: everything in `Main.lean` is obtained from one term, `allChi`, of
one type, `UpperTheory.EveryCharacter`.

**S2. The single Prop.**

`CB/EveryCharacter.lean:13-14`
```lean
def UpperTheory.EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

Reading: `L(s, χ) ≠ 0` for `Re s > 1/2`, for every modulus and every
Dirichlet character, the point `(χ = 1, s = 1)` excepted. It is the same text
as `DirichletLNonvanishingRightOfHalf` and as `Claim.HalfPlane`
(`CB/HalfPlane.lean:3-4`).

**S3. The term for it, and the one Prop it is derived from.**

`CB/MainConclusion.lean:7-11`
```lean
theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)

theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
```

Reading: the half-plane statement is stated to follow from one Prop,
`Row0b` at the reciprocity notion `IsRecT`, used three times: twice as a field
of a three-field structure and once to produce `VWin`. That Prop is quoted in
section 10.3: it reads as existence of l-adic Galois representations, with
local-global compatibility, for polarized regular algebraic cuspidal
representations of `GL_a` over CM fields. It is given the term
`galoisLocalGlobalStrong_recParameter` (`FND/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`).

**S4. The literature ledger.**

`TPS/EveryCharacterOfLiteratureOfVWin.lean:215-218`
```lean
structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where
  caraianiLocalGlobalDual : _root_.UpperTheory.One.M.Row
  localLanglandsExists : _root_.UpperTheory.Zero.LLC.RecTExists
  galoisRepOfPolarizedPairLit : _root_.UpperTheory.One.M.Row
```

This file has 814 lines, 208 imports and 195 theorems, every one of which
takes `O : OpenLiteratureStatements` as an argument; 177 have
`_of_literature` in their name. The theorem consumed by S3 is at
`TPS/EveryCharacterOfLiteratureOfVWin.lean:810`. A field of `O` is written at
four places only (lines 284, 286, 460, 618). Every other theorem in the file
ignores `O` and names an in-archive term, for example

`TPS/EveryCharacterOfLiteratureOfVWin.lean:219-220`
```lean
theorem UpperTheory.LiteratureTheorems.logDerivOne (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Mem.An.LogDerOne :=
  GlobalTheory.LogDerOneProof.logDerOne_holds
```

Reading: the file is a ledger that re-exports about 190 results under names
of published theorems (Linnik, Deligne-Ribet, Casselman-Wallach, Howe
duality, Siegel-Weil, Kawamata-Viehweg, Bhatt-Scholze and so on). Whether each
Prop states the theorem its name suggests was checked for none of them here.
Three structures with hypothesis-style names are built in the same file from
those theorems: `UnitaryGroupThirdPlaceHypotheses`
(`TPS/EveryCharacterOfLiteratureOfVWin.lean:666`), `ThetaLocalInputs`
(`TPS/EveryCharacterOfLiteratureOfVWin.lean:727`) and
`PublishedHodgeBundleTheorems` (`TPS/EveryCharacterOfLiteratureOfVWin.lean:781`).

**S5. From the ledger to the top plug.**

`TPS/SiegelEisensteinSecondTermHypotheses.lean:69-71`
```lean
theorem every_character_of_theta_integrals_local_matching (P : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses) (F : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hX : _root_.GlobalTheory.CovTop.CovolumeBoundOfX) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hV : VWin) :
    UpperTheory.EveryCharacter :=
```

The proof term (`TPS/SiegelEisensteinSecondTermHypotheses.lean:72-73`)
applies `every_character_of_green_v_win` to three things: a statement named
`Green` obtained from `P.greenRegularCharacters`, the Prop `VWin` (section 6,
item 17), and a `Nonempty (HypsAlt …)` obtained from
`nonempty_hyps_definite_side_of_closed_bound`
(`TPS/SiegelEisensteinSecondTermHypotheses.lean:44`).

**S6. The top plug.**

`TPS/TopPlug.lean:12-17`
```lean
theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
theorem UpperTheory.Top.every_character_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : UpperTheory.EveryCharacter :=
```

Reading: the window exponent is fixed here, `la = 3/2`. A twin of this pair
with a different hypothesis structure sits at `CB/EveryCharacter.lean:8-11`;
the chain from `Main.lean` uses the `TopPlug` version.

**S7. From imprimitive to primitive characters.**

`CB/Imprimitive.lean:5-7`
```lean
theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
```

`TGC/ExplicitFormulaErrorOfHostConditions.lean:11-18`
```lean
def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

def ZeroFreeEven : Prop := ZeroFreeOn fun ψ => ψ.χ.Even

def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True
```

`PChar` is a bundled primitive Dirichlet character
(`TGC/PrimePairSizeCondition.lean:7-11`). Reading: `ZeroFreeAll` says that no
primitive Dirichlet L-function vanishes for `Re s > 1/2`. For the level-one
character this includes the point `s = 1`, where Mathlib's function has a
conventional value; that instance is a fact about the convention.

**S8. The reduction to families on windows.**

`CB/ZeroFreeAllOfTopG.lean:12-14`
```lean
def TopG : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) → FamilyClassConnected (G.cls la)
```

`CB/DivinNOfHypV.lean:13-15`
```lean
def FamilyClassConnected (ℰ : FamClass) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ →
    ∃ Fm : FamP eps, ℰ Fm ∧ ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x
```

`CB/ZeroFreeAllOfTopG.lean:26-29`
```lean
theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG) (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll := by
  have key : ZeroFreeOn fun _ => True :=
    zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm) hla
      (fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _) (fun ψ _ => UpperTheory.Comparison₂.formB _) fun ψ _ => by
```

Reading: `TopG` says that for every window exponent `la > 1` and every
requirement on "hosts" that can be met on windows (`HostExW`) and whose
families satisfy the cohomological bound `HypV`, there is, for each small
`eps`, a parameter family whose members at every scale `x` in the family's
windows satisfy `ChainTied`. `ChainTied`
(`Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97-114`) is the
conjunction of every numeric and arithmetic relation of the construction.
Everything that is not analytic number theory sits behind it. This atlas does
not go below it.

**S9. The epsilon argument.**

`TGC/TopWin.lean:26-32`
```lean
def ChebyshevInequalityOnWindows (Λ : Level) : Prop :=
  ∀ (eD eL eps : ℝ), 0 < eps → ∀ Fm : Fam eps, EFamC Λ (core Fm) → ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL →
    ∃ x1 : ℝ, ∀ x ≥ x1, x ∈ (core Fm).Win → Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

def ChebyshevInequalityAtWindowScale (la : ℝ) (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ Fm : Fam eps, EFamC Λ (core Fm) ∧
    (core Fm).Windows la ∧ ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL
```

`TGC/TopWin.lean:68-69`
```lean
theorem level_of_tiedWin {Λ : Level} {la : ℝ} (h112 : ChebyshevInequalityOnWindows @core @Tied Λ) (hB : Λ.FormBAt la)
    (h : ChebyshevInequalityAtWindowScale @core @Tied la Λ) : Λ.ZeroFreeLevel := by
```

Reading: `eD` and `eL` are quantified before `eps`, so the loss
`(eD + eL + 7)·eps` in the exponent tends to zero. The proof text
(`TGC/TopWin.lean:70-81`) picks, for a given `s` with `Re s > 1/2`, an `eps`
with `1/2 + (eD + eL + 7)·eps` below `Re s` and applies `FormBAt`.
`zeroFreeOn_of_tiedWin_cyc` (`TGC/TopWin.lean:90-93`) instantiates the level
with `Level.cyc ψ`.

**S10. The objects: three functions of a real variable.**

`Formalism/StatementOC.lean:11-13`
```lean
def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)

def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x
```

`TGC/Analytic.lean:14-24`
```lean
def G (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0) -
    y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def sumLamChi {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (y / n - 1) 0 : ℝ) : ℂ)

open Classical in

def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then ((G y : ℝ) : ℂ) else sumLamChi χ y + (y : ℂ) * logDerivativeAtOne χ
```

`TGC/ExplicitFormulaErrorOfHostConditions.lean:36-38`
```lean
def wt (ψ : PChar) : ℝ := if Λ.psK = some ψ then 1 else (3 * (Λ.o : ℝ) + 1)⁻¹

def Gm (y : ℝ) : ℝ := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re
```

`abelian₂` is an abbreviation for the von Mangoldt function
(`TGC/Analytic.lean:9`), and `logDerivativeAtOne χ` is `L'(1, χ)/L(1, χ)`
(`TGC/Analytic.lean:11-12`). `Level.cyc ψ`
(`TGC/ExplicitFormulaErrorOfHostConditions.lean:105-121`) keeps the primitive
characters inducing the powers of `ψ.χ`, sets `psK := none` and takes `o` to
be the order of the group. Reading, for `x ≥ 1` and `χ` of order `o`:

    Gz(x)   = Σ_{n ≤ x} Λ(n)(x/n − 1) − x log x + (1 + γ) x
    g_χ(x)  = Σ_{n ≤ x} Λ(n) χ(n)(x/n − 1) + x · L'(1,χ)/L(1,χ)        (χ ≠ 1)
    Gm_χ(x) = Gz(x) + (3o + 1)^(−1) · Σ_{k=1}^{o−1} Re g_{(χ^k)*}(x)

where `(χ^k)*` is the primitive character inducing `χ^k`. `Gz` equals
`An.G` and a third copy `Deduction.G` (`PC/GzEq.lean:6-7`). A remark derived
here, not in the archive: for `n` coprime to the modulus the coefficient of
`Λ(n)(x/n − 1)` in `Gm_χ` is `o·(3 + [χ(n) = 1])/(3o + 1)`, which is positive.

**S11. The windowed Landau statement: the last step that mentions zeros.**

`TGC/Window.lean:7-8`
```lean
def HasWindows (S : Set ℝ) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ S
```

`TGC/Window.lean:30-33`
```lean
def FormBAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x ^ θ} la → Λ.ZeroFreeAbove θ

def FormB : Prop := ∀ la : ℝ, 1 < la → Λ.FormBAt la
```

`PC/Imports.lean:8-13`
```lean
theorem UpperTheory.Comparison₂.formB :
    ∀ Λ : Level, Λ.FormB := by
  intro Λ la hla θ hθ0 hθ1 hW
  obtain ⟨F, hG, hZ⟩ := UpperTheory.Comparison₂.level_family Λ
  rw [← hZ]
  refine Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_
```

`LT/ZeroFreeOfRpowWindow.lean:11-14`
```lean
theorem zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ZeroFree F θ :=
  lemmaL F hθ hθ1 hδ (windowHyp_of_rpow F hδ h)
```

`DL/CharFamily.lean:36-45`
```lean
def Gm (F : CharFamily) (y : ℝ) : ℝ := ∑ i, F.a i * (Gchi (F.χ i) y).re

def ZeroFree (F : CharFamily) (θ : ℝ) : Prop :=
  ∀ i, ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction (F.χ i) s ≠ 0

def WindowHyp (F : CharFamily) (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∃ R : ℝ → ℝ,
    MeasureTheory.IntegrableOn (fun y => R y * y ^ (-θ - 1)) (Set.Icc Y (Y ^ (1 + δ))) ∧
    (∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), 0 ≤ R y ∧ Gm F y ≤ R y) ∧
    ∫ y in Set.Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η
```

`LT/lemmaL.lean:13-22`
```lean
theorem lemmaL (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    ZeroFree F θ := by
  intro i s hs hzero
  obtain ⟨Φ, hP⟩ := poleData F
  have hZ := landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)
  by_cases h1 : 1 ≤ s.re
  · exact charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero
  · have hmem : s ∈ zeroSet F := ⟨by linarith, i, Or.inl hzero⟩
    have := hZ s hmem
    linarith
```

`DL/LandauZeroFreeCriterion.lean:11-13`
```lean
def zeroSet (F : CharFamily) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ∃ i, DirichletCharacter.LFunction (F.χ i) ρ = 0 ∨
    DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) ρ) = 0}
```

Reading. Let `F` be a finite family of Dirichlet characters, each either the
trivial character of level 1 or non-trivial (`adm`,
`DL/CharFamily.lean:24-32`), with positive weights `a_i`, and let
`Gm_F = Σ a_i Re G_{χ_i}`. Fix `0 < θ < 1` and `δ > 0`. Suppose that for every
`η > 0` there are arbitrarily large `Y` and a non-negative `R` on
`[Y, Y^(1+δ)]` with `Gm_F ≤ R` there and `∫ R(y) y^(−θ−1) dy ≤ Y^η`. Then no
`L(s, χ_i)` vanishes for `Re s > θ`. It is a one-sided, localised form of
Landau's oscillation theorem: one sign, and windows `[Y, Y^(1+δ)]` instead of
all large `y`.

`lemmaL` is where the spine stops mentioning zeros: its proof text takes a
zero `s` with `θ < Re s < 1`, places it in `zeroSet F`, and contradicts
`landau_window` (`LT/landauWindow.lean:83-84`), which says every point of the
zero set has real part at most `θ`. For `Re s ≥ 1` it uses the classical
non-vanishing (`LT/CharFamilyLFunctionNeZeroOfOneLeRe.lean:9`). `poleData`
(`LT/poleData.lean:248`) supplies the Laplace transform with a simple pole at
each zero; the structure it fills is `PoleData`
(`DL/LandauZeroFreeCriterion.lean:15-23`).

A measured fact that makes this node a natural first target for an
independent check: the import closure of `lemmaL` inside the archive is 28
modules and 2,396 lines, all of them in
`Development/AutomorphicArithmetic/DedekindLFunctions`. The statement is in
Mathlib vocabulary (`DL/CharFamily.lean:1` imports only Mathlib). Whether a
theorem of this windowed shape is in the literature was not searched here.

Below S11 the zeros of the target L-functions are not mentioned again. The
supply side does carry conditions on auxiliary L-functions (values of `L'/L`
at `s = 1`, and a clause that may ask for zero-free boxes near `Re s = 1`):
see 10.5.

## 3. The single analytic interface

Three lines.

1. **Object.** For a primitive character `χ` of order `o`:
   `Gm_χ(x) = Gz(x) + (3o + 1)^(−1) Σ_{k=1}^{o−1} Re g_{(χ^k)*}(x)` (S10).
2. **What everything below must supply.** For every primitive `χ` and every
   small `eps`: `Gm_χ(x) ≤ x^(1/2 + (eD + eL + 7)·eps)` for all large `x` in
   windows `[Y, Y^(3/2)]` with `Y` arbitrarily large, with `eD`, `eL` fixed
   before `eps` (S9, and the theorem below).
3. **What consumes it.** The windowed Landau statement (S11): a one-sided
   bound `Gm_χ(x) ≤ x^θ` on such windows forces `L(s, χ^k) ≠ 0` for
   `Re s > θ`, zeta included; `eps → 0` gives `Re s > 1/2`.

The statement that crosses the interface from below:

`PC/CoreGm.lean:12-15`
```lean
theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by
```

Reading: `EAtH` ties the level to a "host" abelian field and `CoreAtH`
(`PC/CoreAtH.lean:29-40`) is the arithmetic and geometric inequality. The
interface inequality is a statement about primes only. If GRH holds for the
characters involved, each `G` is of size about `√x` (a standard
explicit-formula heuristic, derived by the readers and not found in the
archive text), so the inequality is then true with room and no finite
computation can contradict it. The content is in how the upper bound is
produced, not in the bound.

Numerics for this interface (the measured size of `Gz` and `Gm`, the
calibration of the explicit formula, the rival comparisons) belong to hunt
#161, `hunts/rh_claim_interface/`, written in parallel with this atlas.
Nothing numerical is repeated here.

## 4. Where the Euler product and the Galois structure enter

Two layers, each at a quotable place.

**Layer 1: the logarithmic derivative as a von Mangoldt series.**

`LT/mellinGchiOfNeOne.lean:116-119`
```lean
theorem mellin_Gchi_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          s * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) / (s * (s - 1)) := by
```

`LT/mellinGchiOfNeOne.lean:126-127`
```lean
  have hL : LSeries (fun n : ℕ => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s = _ :=
    χ.LSeries_twist_vonMangoldt_eq hs
```

Reading: for `Re s > 1` the Mellin transform of `G_χ` is
`−(L'/L(s, χ) − s·L'/L(1, χ))/(s(s − 1))`. The arithmetic input is Mathlib's
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`, that is
`−L'/L(s, χ) = Σ Λ(n) χ(n) n^(−s)`: the Euler product in
logarithmic-derivative form, which Mathlib derives from the complete
multiplicativity of `χ`. Together with non-vanishing on `Re s ≥ 1` this is
the whole analytic input of S11 about each L-function.

**Layer 2: a Dirichlet character as a Galois character of a host field, and
prime sums as Frobenius-class sums.**

`CB/ExistsPageN.lean:19-25`
```lean
def IsChiField (ψ : PChar) (e q d : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    2 ^ (e + 2) ∣ N ∧ ψ.N ∣ N ∧ q ∣ N ∧ d ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔
        (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ ψ.val a = 1 ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1)
```

Reading: `E` is the subfield of a cyclotomic field fixed by the residues `a`
with `a ≡ ±1 mod 2^(e+2)`, `ψ(a) = 1` and Jacobi symbols 1 at the auxiliary
primes `q` and `d`. That set is a subgroup because `ψ` is a homomorphism.
This is where `χ` becomes a character of an abelian Galois group. The host
record `HostRaw` (`TGC/ConjEMemHostFIff.lean:12-46`) carries the field, an
embedding into a cyclotomic field and a map `art` from `(Z/N)^×` to the group,
pinned to the action on roots of unity.

`SWB/FirstPrimeNeSecondPrime.lean:65-66`
```lean
def primVal (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (n : ℕ) : ℂ :=
  ∏ p ∈ n.primeFactors, cosetMean (D.inertia p) (n.factorization p • D.frob p) ψ
```

`SWB/FirstPrimeNeSecondPrime.lean:84-87`
```lean
def ASK (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ := by
  classical
  exact (∑ p ∈ (range (N + 1)).filter (IsInert D), 2 * Real.log p * askP D N a t w p)
    + Real.log D.d * askD D N a t w
```

`SWB/FirstPrimeNeSecondPrime.lean:98-101`
```lean
def AskMainBalance : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ),
    0 < a → (∀ ρ, InPhi ρ → 0 < w ρ) → ∀ N : ℕ, (∀ ρ, InPhi ρ → a / w ρ ≤ N) →
      (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w
```

`SWB/FirstPrimeNeSecondPrime.lean:110-114`
```lean
def OrthoUnram : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (p i : ℕ), p.Prime → p ≠ 2 → p ≠ D.q1 → p ≠ D.d → 1 ≤ i →
    ∀ g : E0 × H, (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * primVal D ψ (p ^ i)
      = if i • D.frob p = g then 2 else 0
```

Reading: `primVal` is a character value defined prime by prime from inertia
groups and Frobenius elements: the Euler product written as Frobenius data.
`ASK` is a sum of non-negative terms `2 log p · max(a/p^i − w, 0)` over
primes `p` whose Frobenius lies outside a distinguished half `InPhi` of the
group (`Formalism/ThickAverageLoss/PartnersToFactorsAt.lean:20`) and
exponents `i`, plus a term at the ramified prime `d`. `AskMainBalance` says
that `ASK` minus an explicit main term `MAIN`
(`SWB/FirstPrimeNeSecondPrime.lean:89-91`) equals a character combination
`De` of the smoothed sums `GPsi` (`SWB/FirstPrimeNeSecondPrime.lean:68-70`),
and `OrthoUnram` is the orthogonality of characters that drives it. The
archive states these as theorems at
`SWB/ChainSlopeWindows/StronglyIrreducible.lean:318` and
`SWB/ChainSlopeWindows/StronglyIrreducible.lean:695`. The bridge between the
Mathlib-side sum and the Galois-side sum:

`PC/GmAEq.lean:61-64`
```lean
theorem UpperTheory.Comparison₂.gmA_eq :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ),
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell → ∀ y,
        GmA (arith H.toHostRaw) ell (keptA Λ H.toHostRaw) (3 * (Λ.o : ℝ) + 1)⁻¹ y = Λ.Gm y := by
```

So an upper bound for `Gm` is obtained from an upper bound
`ASK ≤ MAIN + error` for a count of prime powers by Frobenius class
(`LT/ChTop.lean:37-44` and `LT/ChCore.lean:343-351`), and that bound is what
the geometric side is asked for through `SizeData₂`
(`SWB/SChain.lean:17-19`), a conjunct of `ChainTied`.

**What the standing rivals fail.** Read off the hypotheses above, not
computed:

- *As typed*, S11 is a statement about a `CharFamily`, a family of Dirichlet
  characters with positive weights (`a_pos`). The Davenport-Heilbronn function
  is a linear combination of two L-functions modulo 5, and the Epstein zeta
  function of a form of class number above one is a linear combination of
  Hecke L-functions. Neither is a member of such a family, and neither is a
  factor of a product of its members, so the conclusion says nothing about
  them.
- *If one retypes Layer 1 for a general Dirichlet series `f`*, two
  hypotheses fail for both rivals. (a) The identity
  `−f'/f(s) = Σ Λ(n) a(n) n^(−s)` with coefficients supported on prime powers:
  their coefficients are not multiplicative. (b) Non-vanishing for
  `Re s ≥ 1`, which the proof text of `lemmaL` uses and which the convergence of
  the von Mangoldt series for `Re s > 1` needs: both rivals have zeros with
  `Re s > 1` (Davenport and Heilbronn 1936, recalled from the literature, not
  rechecked today).
- *Layer 2 cannot be formulated for them.* `IsChiField` needs the set
  `{a : ψ(a) = 1}` to be a subgroup, `primVal` is a product over primes of
  Frobenius values, and `ASK` sorts primes by Frobenius class. There is no
  Galois character whose Frobenius values reproduce the coefficients of
  either rival.

Caution, in the terms of `ALIGNMENT.md` section 5: a rival that fails a
hypothesis excludes nothing about the proof. This section only says that, on
the text, the route does not obviously apply to functions known to violate
its conclusion. It is a statement about the shape of the argument and not
about its correctness. The Landau step is also a lemma the rivals would share
in a retyped form with the abscissa 1 moved to the right of all zeros, so a
battery comparison should aim at the step that distinguishes: the upper bound
`ASK ≤ MAIN + error`, which needs actual primes, Frobenius classes and
non-negative coefficients.

## 5. How RH for zeta is obtained, and what the functional equation is for

By specialisation to the trivial character of modulus 1, with no limiting
argument.

`Formalism/GammaFactorNonvanishing/CritLine.lean:29-32`
```lean
theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Formalism.VW.rh_of_right fun s hs hs1 => by
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this
```

`Formalism/GammaFactorNonvanishing/RhOfRight.lean:5`
```lean
theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
```

Reading: `rh_of_right` takes non-vanishing of zeta for `Re s > 1/2`, `s ≠ 1`
and returns Mathlib's `RiemannHypothesis`. Its file imports only Mathlib and
is 62 lines. For a zero with `Re s < 1/2` the proof text applies Mathlib's
`riemannZeta_one_sub` (`Formalism/GammaFactorNonvanishing/RhOfRight.lean:28`)
and the non-vanishing of the Gamma and cosine factors.

For primitive characters the reflection is the same, through the completed
L-function:

`Formalism/GammaFactorNonvanishing/CritLine.lean:11-12`
```lean
theorem Formalism.VW.critLine (h : UpperTheory.EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 := by
```

with Mathlib's `IsPrimitive.completedLFunction_one_sub` at
`Formalism/GammaFactorNonvanishing/CritLine.lean:22`.

So the functional equation is used for one thing: to reflect a zero with
`Re s < 1/2` to one with `Re s > 1/2`. It plays no part in the right
half-plane statement `EveryCharacter`, which is where the whole claim lives.

The archive states RH from `EveryCharacter` three times, by three short
routes (the readers reported two; the third was found on re-reading): `rh_of_every` above (the one `Main.lean` uses); `Claim.zeta`
(`CB/ClaimStrip.lean:75`), with

`CB/ClaimStrip.lean:102`
```lean
theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl
```

and `UpperTheory.riemannHypothesis_of_everyCharacter`
(`CB/RiemannHypothesisOfEveryCharacter.lean:215`), consumed at
`CB/MainConclusion.lean:13-14`. The import closure of `ClaimStrip` is 2
modules and 114 lines. These top files are small enough to re-derive
independently against Mathlib, which would isolate the whole claim in the one
Prop of S2.

## 6. The note's 20 timeline items against the tree

Status key. **Q**: located, with a quoted statement that matches the item's
mathematics. **A**: located by area only (a directory or a definition in the
right area; the match to the item is this lab's inference). **N**: name
evidence only. **0**: not located.

| # | item (note's date) | status | where, and on what evidence |
|---|---|---|---|
| 1 | Stepanov determinant (10/6) | 0 | The string "Stepanov" occurs in no file. Nothing was found that ties a determinant statement to the item. |
| 2 | `D^p ≡ 0` on a CM curve, divisibility by `p^(a/p + a/p³ + …)` (10/9) | Q, in part | The exponent shape is quoted below (`vonMangoldtClassSum`, odd `i` only) and is the per-prime term of `ASK` (section 4). The statement about the invariant derivation itself was not located. |
| 3 | `qN = M^k + R`, the path quadric (10/19) | 0 | Not in the archive. See the finding below the table. |
| 4 | `W(1_S) ≥ 0` via a determinant (10/6) | A | No explicit-formula functional is defined: "Guinand" occurs in no file, and the only identifiers containing `weil_functional` are `linear_weil_functional_*`, in 9 files under `AVT/Proofs`, none of which mentions `riemannZeta` or `vonMangoldt`. The role is played by the one-sided bound `ASK ≤ MAIN + error` (section 4). |
| 5 | switch to `Σ_{n≤X} Λ(n)(X/n − 1) − X log X + (1+γ)X` (10/20) | Q | `Formalism/StatementOC.lean:11-13`, quoted in S10: this expression exactly. |
| 6 | a one-sided inequality "gives `> 1 − η`" (10/8) | Q, in shape | `ZetaLandau`, quoted below: a one-sided `x^θ` bound on `Gz` gives zero-freeness for `Re s > θ`. The literal two-step test function of the note was not found. |
| 7 | GGP periods, interlacing weights (10/14) | A | A definition named `Interlace` with interlacing inequalities at `Formalism/LocalRingCardinality/DataTheta.lean:529-530`. The link to Gan-Gross-Prasad is at the level of names ("GGP" occurs in 262 files). |
| 8 | iterated theta lifts `U(X_0) → … → U(X_m)`, `m` like `√X` (11/15) | Q | `LiftChain`, quoted below, and the chain length: `x^(1/2 − ε) ≤ m` in `RestSize` (`SWB/SChain.lean:53-58`) against `m ≤ x^(1/2 + ε/2)` in `ch_core` (`LT/ChCore.lean:343-351`). |
| 9 | norms of the lifts, Chowla-Selberg, Weyl, Siegel mass (11/15) | A | `GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg`, `Formalism/PeriodIntegrals/UnitaryGroupMassFormula` (3,615 files), and a period constant of Chowla-Selberg shape, `logOm` at `Formalism/RankGapBounds/MeanBoundSecondForm.lean:88`. |
| 10 | lower bound on divisibility of the m-fold lift (11/15) | A | `DIV` at `Formalism/RankGapBounds/MeanBoundSecondForm.lean:118-121`, a conjunct of `SizeData₂`. That it encodes a divisibility bound is a reading. |
| 11 | Iwasawa tower by analogy with pigeonhole (10/6) | Q | `PageN` at `CB/ExistsPageN.lean:39`: a 2-power tower with `2^e` between `x^(2+8·eps)` and twice that; `IsChiField` (section 4) requires `2^(e+2) ∣ N`. The string "Iwasawa" occurs in 14,698 files but in only 1,023 outside import lines: most hits are imports of modules under a directory named `IwasawaDecomposition` (section 8). |
| 12 | seesaw, Bessel period independent of the Hecke characters, Rallis (11/15) | A | "seesaw" occurs in 3,248 files, 3,139 of them outside import lines; `RallisHyp` is defined at `Formalism/ThetaLiftIndependence/Statement.lean:232-235`. No statement was matched to the item. |
| 13 | Bost slope inequality (10/6) | Q, in shape | `SlopeIneq`, quoted below. No identifier contains "Bost": the 7 files that match the letters do so only in import lines, across the words "…Bo" and "Statement" of a module name. That `SlopeIneq` is a numeric shadow of a Bost-type inequality is a reading. |
| 14 | the cost of each lift, "stop at 2/3 a priori" (11/15) | 0 | Not located. A caution about names: the spine passes through a term named `boundAtTwoThree_linked_of_recT` (S5), which looks like the item and is not. Its family is about bounds at the primes 2 and 3 (`BoundAtTwoAndThreeForFamily`, `Development/AutomorphicArithmetic/ResidueCharacters/ClosedOfAll.lean:11`). |
| 15 | integral structure glued across Hecke characters, a "gcd" (11/15) | N | A directory `FND/GaloisRepresentations/IntegralStructures`, which holds the term of S3. |
| 16 | relative trace formula, sixfold cover of `GL_5`, Poincaré series (10/14) | N | "sixfold" and "relative trace" occur in no file. A directory `Formalism/LocalToGlobal/GlobalTheory/GL5` (15 files) and Poincaré series statements (`Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PoincareSeriesFinite.lean:5`) exist. |
| 17 | a weakening of Vandiver for classes in `H¹(O_E[1/ℓ], Q_ℓ/Z_ℓ(−e))` (11/15) | Q | `VVle` and `VWin`, quoted below. "Vandiver" occurs in no file. |
| 18 | covolumes, theta series' index, congruences (11/15) | A | The term of S4 applies `topCovolSlim2_use_alt_alt` (`TPS/EveryCharacterOfLiteratureOfVWin.lean:812`); the lattice directories `Formalism/MeanHeightDescent` and `Formalism/LatticeSlopes` were not read for this item. |
| 19 | the choice of tower, "using Behrend" (10/19) | Q | `HostThickExists`, quoted in section 9, with a theorem site whose proof text uses Mathlib's `Behrend.sphere` (`Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:85-86`). |
| 20 | GRH (11/16) | Q | `Main.lean:4-12`. |

String counts in this table are measured by `recount.py` (fixed strings,
any letter case) and recorded in `stats.json`.

Count: 9 located with a quoted statement (three of them in part or in shape),
6 by area only, 2 by name only, 3 not located.

**Finding: the function-field toy of the note is not in the archive.** Item 3
and footnote 3 of the note describe a weighted point count on a path quadric
over a finite field, `qN = M^k + R`, and call it the setting in which the two
ideas were first combined. The archive contains no trace of it: "Stepanov"
occurs in no file, no identifier contains "SignOnly" or "sign_only", and the
archive has no comments or docstrings in which prose could survive. What does
exist is the classical unweighted count for a non-degenerate quadric, for
example

`CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean:108-112`
```lean
theorem card_quadric_even (k : Type) [Field k] [Fintype k] (hchar : ringChar k ≠ 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M)
    (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (s : k) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
```

`Development/EtaleCohomology/WeilConjectures` (24 files) reads, by its Prop
names, as a plan toward Deligne's theorem. The one statement read there,
`FermatCount`
(`Development/EtaleCohomology/WeilConjectures/FermatCount.lean:170-172`),
occurs nowhere else in the tree outside import lines, so it is defined and
never asserted. No statement of the Weil conjectures as a theorem was
located. The toy is not needed for the number-field statement, so its
absence is not a gap in the claimed chain. It does mean that the note's
account of how the argument was found cannot be checked against the archive.

**Corrections to reader notes made while re-verifying this section.** One
reader reported that the strings Quillen, Lichtenbaum and Vandiver occur
nowhere and that the tree has no K-theory object. "Quillen" occurs in 5 files,
all in a 286-file directory `AV/LiteratureResults/KTheoryStability` on
homological stability for `GL_n` (for example
`AV/LiteratureResults/KTheoryStability/HomologicalStability/LinkExactnessStability/QuillenStabilisationSurjectiveBottom.lean:40`).
What that directory states about K-groups of the integers, which the note's
footnote 6 mentions, was not read. Another reader counted 29 files with a
"Bost" or slope-inequality identifier; the recount finds no identifier
containing "Bost", 53 files containing `SlopeIneq` in any letter case and 14
containing `slope_inequality`.

Quotes for the table.

Item 2, `Formalism/LocalRingCardinality/DataParams₂.lean:240-242`
```lean
def vonMangoldtClassSum (j : ℕ) (t : D.host.TT) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Nat.log p (L.aT t).toNat + 2),
    if Odd i then max 0 ((L.aT t : ℝ) / (p : ℝ) ^ i - L.wPart j t p i) else 0
```

Item 6, `Formalism/StatementU.lean:14-17`
```lean
def ZetaLandau : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
```

with a theorem site at `Formalism/ZetaNonvanishing/ZetaLandau.lean:258`.

Item 8, `Formalism/SharpRestriction/Divisibility/ZetaProductPairs.lean:240-242`
```lean
def LiftChain (T : ThetaX D) (μ : D.what₂.Tup) (F : D.what₂.Amb μ) (G : ∀ j, T.cusp (D.sp.Y j)) : Prop :=
  G D.R.m = T.rowAF μ D.R.m ((D.what₂.multTop μ).symm F) ∧
  ∀ j, j < D.R.m → ((G j : T.cusp (D.sp.Y j)) : T.AF (D.sp.Y j)) = vth T μ j (G (j + 1))
```

Item 13, `Formalism/RankGapBounds/MeanBoundSecondForm.lean:151-156`
```lean
def SlopeIneq : Prop :=
  ∀ u0, 0 ≤ D.del u0 → D.del u0 < 1 → 0 ≤ D.η u0 → 0 ≤ D.e u0 → D.e u0 ≤ 1 / 4 →
    D.s u0 - D.muMinCC u0 ≤ D.HH u0 → 0 < D.HH u0 →
    D.s u0 - Real.log (Fintype.card (W u0) : ℝ)
      - (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤ D.muCC u0
```

Item 17, `CB/ExistsPageN.lean:12-17`
```lean
def VVle (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData E Ω p),
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → Formalism.GaloisCohomology.shaLen (ld p) (e : ℤ) ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes,
      ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@Formalism.GaloisCohomology.shaLen E Ω _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) (e : ℤ)).toNat : ℝ) ≤ B
```

`CB/ExistsPageN.lean:41-49`
```lean
def VAt (ψ : PChar) (eps Ct : ℝ) (q d e : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E → VVle E ⌊x ^ Ct⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

def VWinAt (ψ : PChar) (Ct : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ e : ℝ → ℕ, (∀ x ≥ (1 : ℝ), PageN eps x (e x)) →
    ∃ J : ℝ, 1 ≤ J ∧ ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
      ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → VAt ψ eps Ct q d (e x) x

def VWin : Prop := ∀ ψ : PChar, VWinAt ψ 401
```

Reading of item 17: for the field `E` of section 4, the twisted
Tate-Shafarevich-type groups `Sha` (`Formalism/GaloisCohomology/Statement.lean:75-78`)
have finite length for `0 < e < x^401` and the sum over primes `l` of
`log l` times their total length is at most `exp(x^eps / 2)`, on windows
`[Y, Y²]`. Vanishing of Vandiver type would make the lengths zero; the
archive asks for a subexponential total. `VWin` is given a term by
`UpperTheory.One.vwin_of_row`
(`AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`)
from the one Prop of S3.

## 7. Whole-tree statistics

Grade: measured count. Tool: `recount.py`; tables: `stats.json`. All
directory rows at depth 1 and depth 2 were recomputed and agree with the
reader's tables in files and lines.

| | |
|---|---|
| `.lean` files | 175,187 |
| other files under the source directory | 0 |
| lines | 17,374,215 |
| bytes | 1,030,531,854 |
| modules in the import closure of `Main` | 175,187 (all) |
| import edges between archive modules (distinct pairs) | 753,261 |
| unresolved imports of archive modules | 0 |
| modules on an import cycle | 0 |
| longest import chain | 202 steps, ending at `Main` |
| import leaves (no import of an archive module) | 5,927, of which 5,920 import Mathlib only |
| modules that nothing imports | 1 (`Main`) |
| import lines naming Mathlib | 156,238 |
| lines beginning a comment (`--`) or containing `/-` | 0 |

Nothing is dead by import: every module is reachable from `Main`. Import
reachability is not use. Whether a given theorem is consumed by the five top
theorems is not decided by these numbers.

**The archive has no comments.** No line starts with `--` and no file
contains `/-`: no docstrings, no module documentation, no attributions. Every
human-readable hint is an identifier, and the identifiers are
machine-generated.

Mass by top-level directory:

| directory | files | share | lines | share | import leaves | depth range |
|---|---|---|---|---|---|---|
| `Development` | 141,928 | 81.0% | 12,232,663 | 70.4% | 4,265 | 0..198 |
| `Formalism` | 18,254 | 10.4% | 3,200,748 | 18.4% | 766 | 0..93 |
| `GroundTheory` | 8,507 | 4.9% | 1,119,138 | 6.4% | 448 | 0..68 |
| `ReciprocityTheory` | 3,845 | 2.2% | 563,016 | 3.2% | 256 | 0..76 |
| `CompanionTheory` | 2,027 | 1.2% | 194,218 | 1.1% | 35 | 0..114 |
| `PositivityTheory` | 449 | 0.3% | 55,130 | 0.3% | 6 | 0..111 |
| `Lemmata` | 167 | 0.1% | 9,232 | 0.1% | 145 | 0..17 |
| `BuildAid` | 5 | 0.0% | 20 | 0.0% | 5 | 0..0 |
| `Supplements` | 3 | 0.0% | 22 | 0.0% | 0 | 199..201 |
| (root: `Main`, `Statements`) | 2 | 0.0% | 28 | 0.0% | 1 | 0..202 |

The eight largest directories at depth 2:

| directory | files | lines |
|---|---|---|
| `Development/AbelianVarietyTheory` | 99,187 | 8,142,960 |
| `Development/AutomorphicArithmetic` | 18,431 | 1,776,375 |
| `Development/AutomorphicSpectrum` | 15,147 | 1,195,844 |
| `Development/WeilBound` | 7,051 | 848,547 |
| `GroundTheory/HeightsAndTheta` | 6,410 | 641,322 |
| `Formalism/LocalToGlobal` | 5,501 | 955,843 |
| `Formalism/PeriodIntegrals` | 4,350 | 451,856 |
| `Formalism/SharpRestriction` | 3,093 | 709,436 |

One directory at depth 3, `Development/AbelianVarietyTheory/Proofs`, holds
95,418 files and 7,436,698 lines: 54% of all files (reader's table, depth 3
not recomputed).

Import depth (longest path from an import leaf), in bins of 25:

| depth | 0-24 | 25-49 | 50-74 | 75-99 | 100-124 | 125-149 | 150-174 | 175-199 | 200-202 |
|---|---|---|---|---|---|---|---|---|---|
| modules | 61,596 | 42,070 | 30,679 | 26,053 | 12,209 | 2,225 | 273 | 79 | 3 |

Declaration counts, approximate (a keyword at the start of a line, after
attributes and modifiers):

| theorem | lemma | def | abbrev | structure | instance | example | inductive | class |
|---|---|---|---|---|---|---|---|---|
| 784,092 | 34,663 | 212,819 | 13,202 | 8,286 | 7,598 | 4,662 | 121 | 43 |

The recount agrees with the reader on every one of these except `instance`
(7,598 here, 8,199 in the reader's table: the two regular expressions treat
modifiers differently). The reader's import edge count is 753,569; the
recount of distinct importer-imported pairs is 753,261, and the difference is explained: 753,569 is
the number of import lines naming an archive module, 308 of which repeat an
import the same module already makes.

File shape: the median file has 58 lines, the mean is 99.2, and the largest
has 17,981 (`Formalism/HermitianCurvature/HermitianCurvatureProofs/IsAdmissibleSplittingCharPairMulTwist.lean`).
8,735 files have a line longer than 1,000 characters; the median over files
of the longest line is 224 characters. `Formalism` has 107 sub-directories,
86 of which contain a file whose name begins with `Statement`: there the
claims are written as `def Name : Prop := …`, and those files are the
readable interface of the archive.

Sizes of some import closures inside the archive (modules, lines), measured:

| root | modules | lines |
|---|---|---|
| `Formalism.GammaFactorNonvanishing.RhOfRight` | 1 | 62 |
| `Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip` | 2 | 114 |
| `Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.lemmaL` | 28 | 2,396 |
| `Formalism.ZetaNonvanishing.ZetaLandau` | 18 | 2,338 |
| `Formalism.SuccessiveMinima.MinkowskiIIUpper` | 15 | 1,693 |
| `ReciprocityTheory.Chebotarev.StatementHolds` | 47 | 4,382 |
| `Development.AutomorphicArithmetic.PrimitiveCosets.Imports` (`formB`) | 132 | 23,723 |
| `Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG` | 754 | 128,349 |

The build configuration (`lakefile.toml`, read, not run) sets
`maxHeartbeats = 4000000`, `maxSynthPendingDepth = 3` and
`--tstack=400000`.

## 8. Directory names that mislead

Names are machine-generated. Each row says what the directory was found to
hold, on the evidence cited.

| directory | what the name suggests | what it holds |
|---|---|---|
| `Development/WeilBound` (7,051 files) | the Weil bound for curves over finite fields | An automorphic and p-adic Hodge development, by its sub-directory names (`AutomorphicKernels`, `PadicHodgeComparison`, `PublishedTheorems`, `ThetaLifts`, …). No file in it mentions `riemannZeta`, `vonMangoldt` or `WeierstrassCurve` outside import lines. Its sub-directories are `CoreStatements` (3,746 files), `RepresentationTheoryGL` (2,486), `ThetaLifts` (788) and seven small ones. |
| `PositivityTheory` (449 files) | a positivity criterion for zeta | Automorphic inputs, by its sub-directory names: `PositivityTheory/AutomorphicForms/PublishedInputs` (445 of the files) is divided into `JacquetLanglands`, `HilbertEisenstein`, `CyclicBaseChange`, `CuspidalContinuity` and four more. No file in it mentions `riemannZeta` or `vonMangoldt` outside import lines. |
| `PositivityTheory/PublishedTheorems` | published theorems | 3 files, 105 lines: two one-line import stubs and one file of four lemmas, `ExistsUnitKillsOfIdempotent.lean`. |
| `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition` | the Iwasawa decomposition | A mixed bag of 7,769 files, of which 21 contain the string "Iwasawa" outside import lines. It holds, among others, a quadric point count (`AVT/Proofs/IwasawaDecomposition/CardQuadricSubSqLe.lean:66`), a non-vanishing statement for zeta on the real interval (0, 1) (`AVT/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean:256-257`), and the inhabitation statement for a p-adic comparison guard (section 10.4). |
| `AV/SmallClassNumbers` | a table of class numbers | One literal class number, `classNumber (Kstar 3) = 1` (`AV/SmallClassNumbers/ClassNumberThree.lean:32`), and a Selmer-group bound of Vandiver type (section 9). `Main.lean` imports it through `Supplements/Kernels/MainTheoremsAll.lean:1-2`. |
| `Formalism/GammaFactorNonvanishing` | Gamma factors | The two files of section 5: the logical plumbing from the half-plane statement to `RiemannHypothesis`. |
| `Development/AutomorphicArithmetic/DedekindLFunctions` | Dedekind zeta functions | The windowed Landau lemma for Dirichlet characters (S11) and the prime-sum inequalities `ch_top` and `ch_core`. The string `dedekindZeta` does not occur in it. |
| `Formalism/ProductFormula` | the product formula for valuations | One file, `StatementOCCM.lean`, of Props for this argument (`OCCMEstimate`, `OCCMToZeta`, `ZetaQuarterPowerCorollary`, and one named `ProductFormula`); not read. |
| `Formalism/BehrendSets` | Behrend's construction | Fourteen files of statements and some proofs (B5 of section 9 is here). The Behrend bound itself, `BehrendBound` (`Formalism/BehrendSets/Statement.lean:54-56`), is defined and occurs nowhere else in the tree. The Behrend-type statement with a theorem site is next door, in `Formalism/FrobeniusOrbits` (section 9). |
| `Formalism/ArtinHasse` | the Artin-Hasse exponential | Two files. The integrality statement `ArtinHasseIntegral` (`Formalism/ArtinHasse/Statement.lean:53`) and `KummerZp` are defined and occur nowhere else in the tree. |
| `Development/EtaleCohomology/WeilConjectures` | the Weil conjectures | A 24-file plan toward Deligne's theorem, by its Prop names. The one statement read, `FermatCount`, is defined and never asserted (section 6); no statement of the Weil conjectures as a theorem was located. |
| `Development/ResolutionOfSingularities` | resolution of singularities | Here the name is accurate (section 9). |

Identifiers mislead in the same way. `abelian₂` is the von Mangoldt function
(`TGC/Analytic.lean:9`). `ChebyshevInequalityOnWindows` (S9) is not
Chebyshev's inequality. Theorems named `*_of_literature` are not hypotheses
taken from the literature: a field of the hypothesis structure is written at
four places only, and the rest name in-archive terms (S4).

## 9. By-products of independent interest

Statements in Mathlib vocabulary, or close to it, that would be of interest
on their own if a kernel accepts them. "Theorem site" means a line
`theorem name : Statement := …` was read at the cited place. It says the
archive states the theorem as closed. It says nothing about a kernel. "Not in
Mathlib" is the readers' recollection and was not searched: no novelty claim
is made.

**Closed theorem sites.**

*B1. Minkowski's second theorem, upper bound.*

`Formalism/SuccessiveMinima/StatementMink.lean:18-24`
```lean
def MinkowskiIIUpper : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
      μ.real K * ∏ i : Fin (finrank ℝ E), succMin L K ((i : ℕ) + 1)
        ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ
```

Theorem site: `Formalism/SuccessiveMinima/MinkowskiIIUpper.lean:14`. The
statement file imports only Mathlib, and `succMin` (three lines, same file)
is the only archive-local definition. Closure: 15 modules, 1,693 lines.

*B2. Chebotarev, qualitative form over Q.*

`ReciprocityTheory/Chebotarev/CycStatement.lean:7-10`
```lean
def Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (σ : Gal(K/ℚ)) (T : Finset ℕ),
    ∃ p : ℕ, p.Prime ∧ p ∉ T ∧ ∃ P : Ideal (𝓞 K), ∃ _ : P.IsPrime,
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ Algebra.IsUnramifiedAt ℤ P ∧ IsArithFrobAt ℤ σ P
```

Theorem site: `ReciprocityTheory/Chebotarev/StatementHolds.lean:6`. No
archive-local definition in the statement. Closure: 47 modules, 4,382 lines.

*B3. A Behrend-type set avoiding three-term relations with bounded
coefficients.*

`Formalism/FrobeniusOrbits/HostThickExists.lean:13-16`
```lean
def NoRel (T : Finset ℕ) (L : ℕ) : Prop :=
  ∀ s₁ ∈ T, ∀ s₂ ∈ T, ∀ s₃ ∈ T, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
    ∀ i j : ℤ, 0 < |i| → |i| ≤ L → 0 < |j| → |j| ≤ L → i ≠ j →
      j * ((s₂ : ℤ) - s₁) ≠ i * ((s₃ : ℤ) - s₁)
```

`Formalism/FrobeniusOrbits/HostThickExists.lean:30-32`
```lean
def HostThickExists : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n L : ℕ, 2 ≤ L → ∃ T : Finset ℕ, (∀ s ∈ T, 4 * L * s < n) ∧ NoRel T L ∧
    (n : ℝ) * Real.exp (-C * Real.sqrt (Real.log n * Real.log L)) / L ≤ T.card
```

Theorem site: `Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:181`.
Reading: for every `n` and `L ≥ 2` there is a set `T` in `[0, n/(4L))` with
no three distinct elements satisfying `j(s₂ − s₁) = i(s₃ − s₁)` for distinct
non-zero `|i|, |j| ≤ L`, of size at least `(n/L)·exp(−C√(log n · log L))`.

*B4. Functorial resolution of singularities in characteristic zero.*
`FunctorialResolutionCharZero` is defined at
`Development/ResolutionOfSingularities/Statements.lean:150-152`, in a file
that imports only Mathlib, with a theorem site at
`Development/ResolutionOfSingularities/HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean:15`
and principalization at
`Development/ResolutionOfSingularities/HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean:102`.
The definitions of blow-up and of a resolution rule are archive-local and
should be read before any reuse.

*B5. No non-trivial finite g-subgroup of `GL_k` over a number field of small
degree.*

`Formalism/BehrendSets/StatementE.lean:89-91`
```lean
def TrivStab : Prop := ∀ (E : Type) [Field E] [NumberField E] (k g : ℕ), g.Prime →
  Module.finrank ℚ E * k < g - 1 →
  ∀ Γ : Subgroup (GL (Fin k) E), Finite Γ → IsPGroup g Γ → Γ = ⊥
```

Theorem site: `Formalism/BehrendSets/BehrendVariance/TotientLeOfIsPrimitiveRoot.lean:65`.

*B6. Dirichlet's theorem in logarithmic-density form.* `APLogDensity` at
`Formalism/DirichletDensity/Statement.lean:36-38`, theorem site
`Formalism/DirichletDensity/DirichletDensityProofs/APLogDensity.lean:103`.

*B7. Local reciprocity for p-adic fields.* `LocalReciprocity` is defined at
`ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:88-89`. The theorem
site `ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportC.lean:155-156`
carries `[CharZero K]`: the statement covers p-adic fields and not local
fields of positive characteristic.

*B8. Linnik's theorem.*

`AVT/PublishedTheorems/PublishedFoundations/PrimesInProgressionNonempty.lean:9-11`
```lean
def Linnik : Prop :=
  ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
    (leastPrimeMod a q : ℝ) ≤ C * (q : ℝ) ^ L
```

Theorem site: `Development/AutomorphicArithmetic/ThetaCorrespondence/Linnik.lean:142`.

*B9. The eventual one-sided Landau criterion for zeta* (`ZetaLandau`, section
6, item 6). Closure: 18 modules, 2,338 lines. The live chain does not use it:
it uses the windowed form S11.

*B10. A Selmer bound of Vandiver type.*

`AV/SmallClassNumbers/ClassNumberThree.lean:16-20`
```lean
def Bound : Prop :=
  ∃ C A : ℕ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), 1 ≤ e → Even e →
    ∀ (c : ∀ l : Nat.Primes, Coef l) (Ls : Finset Nat.Primes), (∀ l ∈ Ls, 5 ≤ (l : ℕ) ∧ ¬ (l : ℕ) - 1 ∣ 2 * e) →
      (∀ l ∈ Ls, len Ω l (c l) e ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * (((len Ω l (c l) e).toNat : ℝ) / ((eO l (c l).O).toNat : ℝ)) ≤ C * ((e : ℝ) + 1) ^ A
```

Theorem sites: `bound_of` at `AV/SmallClassNumbers/ClassNumberThree.lean:88`
and `bound` at `AV/SmallClassNumbers/CorGKOf.lean:25-27`. Reading: for even
`e`, a group of locally trivial classes in `H¹` with coefficients twisted by
the `(−e)`-th power of the cyclotomic character has finite length for every
prime `l ≥ 5` with `(l − 1) ∤ 2e`, and the sum over `l` of `log l` times the
normalised length is at most `C(e + 1)^A` for absolute, non-explicit `C` and
`A`. The definition of `len` (`AV/SmallClassNumbers/ClassNumberThree.lean:13-14`)
was read; the objects under it were not. This is a second formal counterpart
of the note's "significant weakening of Vandiver", beside `VWin`. The
vanishing consequence `Large` (`AV/SmallClassNumbers/LenEqZeroIff.lean:65-68`)
has the implication `large_of`
(`AV/SmallClassNumbers/LenEqZeroIff.lean:70`); no closed site for `Large`
itself was found.

**Props that are only defined.** Each name below occurs exactly once in the
whole tree outside import lines, at its definition: it is never asserted and
never used.

| Prop | defined at |
|---|---|
| `BehrendBound` | `Formalism/BehrendSets/Statement.lean:54-56` |
| `MinkowskiIILower` | `Formalism/SuccessiveMinima/StatementMink.lean:26` |
| `ArtinHasseIntegral`, `KummerZp` | `Formalism/ArtinHasse/Statement.lean:53`, `Formalism/ArtinHasse/Statement.lean:59` |
| `LocalExistence` | `ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:91-93` |
| `GlobalExistence`, `RayClassFieldExistence`, `ChebotarevDensity'` | `ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:150`, `ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:242`, `ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:306` |
| `FermatCount` | `Development/EtaleCohomology/WeilConjectures/FermatCount.lean:170-172` |
| `OCStep`, `RiemannHypothesisOfLowerBounds` | `Formalism/StatementOC.lean:23`, `Formalism/StatementOC.lean:65` |
| `RHofG` | `Formalism/Statement.lean:46` |
| `ForcedSumCM` | `Formalism/StatementCM.lean:35` |

The four at the bottom are earlier forms of the analytic criterion (a
lower-bound variant and a CM-type variant). They read as design layers that
the live chain no longer uses. They remain precise statements that can be
tested.

The ledger of S4 names a much larger set. By this builder's rule, 445
parameterless Props are defined in the namespace `GlobalTheory.Published` and
its sub-namespaces, and a one-line theorem of exactly that type was found for
181 of them (a reader's rule gave 419 and 177). Both are regular-expression
counts and approximate. The other 264 are not shown to be open: multi-line
theorem headers, structure fields and renamed copies are invisible to the
rule.

## 10. Where an auditor should look first

In the order a kernel run should watch them. None of these is shown to be a
defect: each is a place where the text alone cannot decide.

**10.1 The command that adds declarations without source text.**

`Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:76-82`
```lean
    match ci with
    | .defnInfo d =>
      addDecl (.defnDecl { d with name := n', type := subst tainted d.type, value := subst tainted d.value })
      k := k + 1
    | .thmInfo t =>
      if defsOnly then continue
      addDecl (.thmDecl { t with name := n', type := subst tainted t.type, value := subst tainted t.value })
```

The command `cpt_copy_thms` (`Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:87-89`)
re-adds existing definitions and theorems under new names with constants
substituted. `addDecl` sends each declaration to the kernel, so this is not
by itself a bypass. It is the one file in the tree where `addDecl` occurs,
and the one place where declarations enter the environment that no source
line states. It is invoked once, at
`Formalism/HermitianCurvature/HermitianCurvatureProofs/CutMainCpt.lean:945`,
under `set_option maxHeartbeats 0`. The copies start from six named roots
(`Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:28-30`)
and take the suffix `Cpt`.

**10.2 Custom tactics that assign a goal without an elaboration-time check.**

`Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:5-8`
```lean
elab "kexactB " e:term : tactic => withMainContext do
  let g ← getMainGoal
  let v ← Term.elabTermAndSynthesize e none
  g.assign (← instantiateMVars v)
```

`kexactB` elaborates a term with no expected type and assigns it to the
goal. A second tactic, `kcopy`
(`Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:53-58`), copies a
term across structures. An assigned term is checked by the kernel when the
enclosing theorem is added, so a wrong assignment should fail there and not
pass silently; that is what a replay will show. `kexactB` occurs on 234 lines in 50 files,
counting a macro `kc%` that expands to it; `kcopy` is used at three places.

Related text facts, all measured: no `sorry`, no `admit`, no `axiom`
declaration, no `native_decide`, no `implemented_by`, no `@[extern`, no word
`unsafe`. There are 5 `run_cmd` lines, all in `BuildAid/D1.lean` to `D5.lean`
(`BuildAid/D1.lean:4`), each adding a namespace to a library-suggestion deny
list. There are 88,139 `set_option` occurrences and 220 `open private` lines.
A grep is not an axiom audit: only `#print axioms` on the five theorems of
`Main.lean` after a build shows what they depend on.

**10.3 Structures named for hypotheses, and where they are given terms.**
The tree has 106 `structure` declarations whose name contains "Hypothes",
"Literature" or "Published". On the spine:

- `OpenLiteratureStatements` (S4), three fields, filled at
  `CB/MainConclusion.lean:7-11` by `⟨h, recTExists, h⟩`.
- The three structures built at lines 666, 727 and 781 of the ledger (S4).
- `OpenImageCondition`, built by `.mk h` at
  `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`.

At text level each is given a constructor term; none is left as a hypothesis
of the five theorems. So the audit question is not "what is assumed" but
"what do these Props say". The one everything rests on:

`FND/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69-73`
```lean
def Row0b : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), PropsB Rc π ι r wt HT
```

A term of this type is a claim to have formalised the existence of Galois
representations for polarized regular algebraic cuspidal representations of
`GL_a` over CM fields. The meaning of `CuspSub`, `IsRegAlg`, `PolarizedPair`,
`PropsB` and `Rc` is the first audit target. The second field,
`RecTExists` (`FND/LocalLanglands/IsRecTOfIsRec.lean:78-80`), reads as
existence of a local Langlands correspondence for `GL_n`, but five of its
laws (twist, central character, dual, injectivity, depth) are stated only for
representations satisfying `Good`
(`FND/LocalLanglands/IsRecTOfIsRec.lean:65-71`), and

`FND/LocalLanglands/IsRecTOfIsRec.lean:20-24`
```lean
def GoodCusp (y : IrrGL k) : Prop :=
  y.1 = 1 ∨ ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) ∧
    ∃ (y₀ : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), GlobalTheory.PRep.fixed y₀.rep (GlobalTheory.SplitWeil.KOne k (Fin y₀.1)) ≠ ⊥ ∧ y = y₀.tw χ hχ)

def Good (x : IrrGL k) : Prop := ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, GoodCusp y
```

A reader left the meaning of `Good` open. Reading: `Good` holds when the
cuspidal support consists of characters or,
over a field isomorphic to some `Q_p`, of twists of representations with a
vector fixed by the first congruence subgroup. So `RecTExists` is weaker than
the local Langlands correspondence its name suggests. Whether the weaker form
suffices where it is used is for the replay and for a reader of
`FND/LocalLanglands`.

**10.4 Guards that could be vacuous.** Several statements are guarded by a
`Nonempty` hypothesis. The clause of `PropsB` about places above `l`:

`FND/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:64-67`
```lean
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveB Rc π ι r HT P h Bw hj
```

If `LocTied l P AI` (`Formalism/LocalRingCardinality/AdicCompletionLocal/LocTied.lean:11`,
a record of isomorphisms with crystalline and de Rham period rings) were
never inhabited, this clause would be empty. "Nonempty (LocTied" occurs in
190 files. A reader asked whether the guard is ever inhabited. The archive
does state inhabitation, in a directory whose name gives no hint of it:

`AVT/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinfStatement.lean:8`
```lean
theorem _root_.GlobalTheory.T.exists_local_prime_ainf : ∀ (l : ℕ) [Fact l.Prime], ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) := by
```

The same question applies to every other `Nonempty (…) →` and every
structure-valued hypothesis in the ledger. The spine itself passes through
one: `Nonempty (HypsAlt …)` in S6, obtained in S5. A systematic pass over
these guards was not made.

**10.5 A bound of GRH strength at one scale, whose supply was not traced.**
The hypothesis `EAtH` of the interface theorem contains, for the characters
of the host field other than the kept ones, a pointwise bound of the same
strength as the conclusion, at the single scale `x`:

`TGC/ExplicitFormulaErrorOfHostConditions.lean:144-151`
```lean
structure EAtH (Λ : Level) {φ : Frame} (H : HostRaw φ) (TT : Finset φ.A) (x eps C : ℝ) : Prop where
  o_eq : φ.o = Λ.o
  kept : H.KeptInXp Λ.KEPT
  ps : H.ExceptionalCharacterKept Λ.KEPT Λ.psK
  shares : φ.Shares TT (x ^ (-1 + eps))
  bdG : H.BoundedCharsPointwise Λ.KEPT x eps
  bdL : ∀ θ ∈ H.Bounded Λ.KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.logDerivativeAtOne χ‖ ≤ C * Real.log x
```

`TGC/Analytic.lean:154-156`
```lean
def BoundedCharsPointwise (S : Finset PChar) (x eps : ℝ) : Prop :=
  ∀ θ ∈ H.Bounded S, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps)
```

`Bounded` (`TGC/Analytic.lean:136`) is the set of host characters of the
class `Xp` that are not kept, together with all of the class `Xm`. The requirement is stated to be supplied by a choice of the host
field:

`CB/SupplyChi.lean:8-9`
```lean
theorem UpperTheory.Top.supplyChi :
    ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req := by
```

through `supplyOfAdm` (`CB/HostOfField.lean:17-23`) and the existence
statement `HostExW`
(`AVT/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:120-123`). The
auxiliary primes are very large compared with `x` (`WinPair`,
`CB/ExistsPageN.lean:27-37`: `log q` of order `Y^(eps/5)`), and an earlier
layer states the same shape as an existence statement over prime pairs
(`ExistsSplitGoodPrimePair`,
`SWB/SmoothedRemainderRealIntegralFormula.lean:50-60`). How a pointwise bound
`‖g_χ(x)‖ ≤ x^(1/2 + eps)` is obtained for those characters, without assuming
what is to be shown, is the most delicate analytic point on the spine. It was
not traced. It is not circular on its face, since an existence statement over
many auxiliary primes at one scale is weaker than a bound for a given
character at all scales, but the text read here does not show the mechanism.

The same existence statement carries further analytic conditions on the host
(`HostGood`, same file). One clause, `BoxH`
(`AVT/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:68-71`), asks a
predicate named `GoodFor` of the real characters of the host field. Four
definitions named `GoodFor` exist in the tree. The one read
(`SWB/SmoothedRemainderRealIntegralFormula.lean:41-45`) asks for a primitive
real character of bounded conductor with no zero in the box
`Re s > 1 − 1/400`, `|Im s| ≤ Q`: a condition of classical strength. Which of
the four `BoxH` refers to was not resolved.

**10.6 Finite tables closed by `decide +kernel`.** 34 files contain
`decide +kernel` (151 occurrences). These are kernel-evaluated decision
procedures, not compiler-trusted ones, and each is a place where a build can
be slow or fail for resource reasons. The first files in tree order are
listed in `stats.json`.

**10.7 The Props named for published theorems.** See S4 and section 9. The
highest-value human reading in the whole archive is whether those Props are
faithful.

## 11. Open questions

Stated as questions. None is answered by a text-level reading.

1. Does the archive compile at the pinned toolchain, and what does
   `#print axioms` report for the five theorems of `Main.lean`? (Owned by the
   replay, pending.)
2. Is the windowed one-sided Landau statement of S11 true as stated, and is
   it in the literature (Turán, Pintz, Knapowski-Turán, Kaczorowski)? Its
   closure is 28 modules: can it be re-derived or kernel-checked on its own?
3. How is the pointwise bound `bdG` of 10.5 supplied for the characters that
   are not kept? Is the mechanism an average over auxiliary primes, and where
   is it stated?
4. Which definition named `GoodFor` does the host clause `BoxH` refer to,
   and are the zero-free boxes it asks for supplied by a zero-density
   argument of classical strength?
5. Do `Row0b`, `PropsB`, `CuspSub`, `IsRegAlg` and `PolarizedPair` say what
   the theorem of Harris-Taylor, Shin, Chenevier-Harris and Caraiani says? Is
   `Row0b` inhabited for the reasons its term's name suggests ("of theta
   lift"), and is the class of `π` it quantifies over non-empty and as large
   as the use in `vwin_of_row` needs?
6. Is the restricted `RecTExists` of 10.3 enough at each place it is used?
7. Which of the `Nonempty` guards and structure-valued hypotheses on the
   path from `Main` are inhabited, and where?
8. Are the Props of the ledger (S4) faithful statements of the theorems they
   are named for? For how many is there a closed theorem site?
9. Below `ChainTied`: where do theta lifts, lattices and the chain of length
   about `√x` become actual objects, and where is `SizeData₂` (with `DIV`,
   `SlopeIneq` and the loss bounds) established for the families that exist?
10. Is the twin plug at `CB/EveryCharacter.lean:8-11` equivalent to the
   `TopPlug` pair of S6, or a remnant of an earlier design?
11. Do the three alternative routes that read as earlier layers (the
    eventual `ZetaLandau`, the lower-bound `OCStep`, the CM-type
    `ForcedSumCM`) feed the live chain anywhere?
12. What does `AV/LiteratureResults/KTheoryStability` state about K-groups,
    and does it bear on the note's footnote 6?
13. Where, if anywhere, is the note's item 14 (the cost of each lift and the
    a priori exponent 2/3)?
14. What does `cpt_copy_thms` copy when it runs, under what names, and do
    any of the five top theorems depend on a copied declaration?
15. Why is the function-field toy absent, and does an independent
    reconstruction of it (the function-field reader has one at float grade,
    not part of this hunt) match what the note describes?

## 12. How to replay this atlas

Anyone with the public tarball can check every citation above.

    python -I hunts/rh_claim_atlas/verify_quotes.py PATH/lean/src --mathlib PATH_TO_MATHLIB_v4.33.1

`quotes.json` holds one entry per citation: the tree, the path, the first and
last line, and the sha256 of exactly those lines. A citation followed by a
`lean` block is a displayed quote and its text is stored; a bare citation is
a pointer and only a short head of its first line is stored. The script
exits non-zero on any mismatch. `recount.py` reproduces the counts of section
7, and the string counts of sections 6, 8 and 10, in about two and a half
minutes on one core. `RUNS.md` records the runs behind this
file.

A pass of `verify_quotes.py` says that the cited text is what this atlas
read. It says nothing about whether a kernel accepts the archive.
