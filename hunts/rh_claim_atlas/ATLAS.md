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
step whose statement mentions zeros, the analytic interface, where arithmetic
enters,
how the author's 20 timeline items sit against the tree, how large the tree
is, which directory names mislead, what else is stated along the way, and
where an auditor should look first.

**Grades.** Two only, and neither is a rung above *measured* on the lab's
ladder.

- *Text-level reading, quotes replayable.* A claim of the form "the archive
  states X at `path:line`". Each one rests on a citation recorded in
  `quotes.json` with the sha256 of the cited lines; `verify_quotes.py` replays
  all of them against any unpacked copy.
- *Measured count.* A number produced by `recount.py` or `ledger_count.py`
  from file text (lines, import lines, line-start keywords, fixed strings).
  Declaration counts are regex counts and approximate.

A third kind of sentence carries neither grade. A *reading* is this lab's
own mathematics about a quoted text: what a statement says in plain terms,
what follows from it, how it compares with the literature. Readings are
marked as readings. They were not tested, and where they lean on the
literature it is recalled, not searched.

**Wording.** "The archive states" means a line of text says so. It never
means the statement has been checked: that is the kernel replay's question.
Names in the archive are machine-generated and several are shown below to be
misleading, so a reading is meant to rest on a quoted statement and not on a
name. Review found three places where the first version rested on a name or
a letter after all; each is now either given its quote or marked (section 4,
Layer 2; section 6, items 8 and 14).

**"Uses" and "names".** Throughout, "the proof text names X" or "uses X"
means the identifier X occurs in the text of a proof. A chain of such
occurrences is a chain of names. Whether the kernel term of a theorem depends
on X is decided by the replay and by nothing in this atlas.

**Provenance.** Nine readers worked the archive this morning. Their notes
were the starting point; every claim kept here was opened again in the archive
and re-read by the builder. Several reader statements were corrected or
sharpened in the process, and three questions the readers left open were
closed at text level; each is flagged where it occurs (sections 5, 6, 7, 9
and 10). This atlas is original to the lab. It
makes no novelty claim.

**Review.** Two reviewers then attacked the first version, one for the
faithfulness of the readings and one for the numbers and the rules. Twenty
findings came back. Two sentences of the first version were wrong and are
corrected in place, with the old wording kept beside the correction: that
the functional equation plays no part below `EveryCharacter` (section 5),
and that every ledger theorem but four ignores its hypothesis (S4). Several
more were stronger than what had been read and are narrowed. Each change
says so where it stands, and `RESULTS.md` lists all twenty with their
dispositions.

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

Four of the five types are defined in a file that imports only Mathlib. Two
are shown; the other two are pointed to, so that this atlas does not
reproduce the file.

`Statements.lean:3-8`
```lean
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

`DirichletLZerosOnLine` (`Statements.lean:10-12`) says, for every modulus `N`,
every Dirichlet character `χ` modulo `N` and every `s` with `0 < Re s < 1`:
if `DirichletCharacter.LFunction χ s = 0` then `Re s = 1/2`.
`PrimitiveDirichletLZerosOnLine` (`Statements.lean:14-16`) is the same
sentence with the extra hypothesis `χ.IsPrimitive`.

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

`Supplements/Kernels/MainTheorems.lean:7-9`
```lean
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi
```

The other two terms are `critAll`
(`Supplements/Kernels/MainTheorems.lean:11-13`), which applies
`Formalism.VW.critLine` to `allChi`, and `claimAll`
(`Supplements/Kernels/MainTheorems.lean:15-16`), a triple whose components
are `allChi`, `Claim.strip allChi` and `Claim.zeta allChi`.

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
`TPS/EveryCharacterOfLiteratureOfVWin.lean:810`. Counted by
`ledger_count.py` on the text after the binder of `O`:

| how the theorem's text treats `O` | theorems |
|---|---|
| reads a field of `O` (lines 284, 286, 460, 618) | 4 |
| does not read a field, passes `O` on to other theorems of the file | 39 |
| does not mention `O` | 152 |
| reads a field, or names a theorem of the file that does, transitively | 13 |

The first three rows add up to 195; the fourth overlaps the first two. The
first version of this atlas said that every theorem but four ignores `O`.
That was wrong: 39 pass it on, and the theorem S3 consumes (line 810) is one
of the 13 that reach a field through other theorems of the file. All three
fields are read: `localLanglandsExists` at line 284,
`galoisRepOfPolarizedPairLit` at line 286, `caraianiLocalGlobalDual` at lines
460 and 618. A theorem of the 152 looks like this:

`TPS/EveryCharacterOfLiteratureOfVWin.lean:219-220`
```lean
theorem UpperTheory.LiteratureTheorems.logDerivOne (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Mem.An.LogDerOne :=
  GlobalTheory.LogDerOneProof.logDerOne_holds
```

Reading: the file is a ledger that re-exports 195 results, most of them
under names of published theorems (Linnik, Deligne-Ribet, Casselman-Wallach,
Howe duality, Siegel-Weil, Kawamata-Viehweg, Bhatt-Scholze and so on). For
152 of them the hypothesis `O` plays no part in the text. Whether each Prop
states the theorem its name suggests was checked for none of them here.
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

Reading: the window exponent is fixed here, `la = 3/2`. The first theorem
passes two arguments to `zeroFreeAll_of_topG` (S8). The first is a term of
`TopG`, the geometric side. The second, `fun ψ => supplyChi ψ (hV ψ)`, is the
supply of hosts, of type `∀ ψ, HostExW (3/2) (GChi ψ).req`. That second
argument is where the classical analytic number theory of the archive is
named (10.5).

A twin of this pair with a different hypothesis structure, `plugWin` and
`plugAll`, sits at `CB/EveryCharacter.lean:8-18`; the chain from `Main.lean`
uses the `TopPlug` version. Outside import lines, `plugAll` is named at one
place only: `everyE₂`
(`Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/EveryCharacterE.lean:67-71`),
a theorem with seven hypotheses that concludes `EveryCharacter` and whose own
name occurs nowhere else in the tree. So the twin reads as a second route to
the same Prop that nothing consumes (question 10).

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
here, not in the archive, and a reading in the sense of section 0: for `n`
coprime to the modulus the coefficient of `Λ(n)(x/n − 1)` in `Gm_χ` is
`o·(3 + [χ(n) = 1])/(3o + 1)`, which is positive. A reviewer re-derived it
by hand and added the remaining case: for `n` not coprime to the modulus the
coefficient is at least `1 − (o − 1)/(3o + 1)`, also positive. Neither
derivation was checked by a test.

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

**What "the last step that mentions zeros" covers.** It is a statement about
the spine as quoted: in S8 to S10 and in the interface theorem of section 3,
zeros of the target L-functions occur in conclusions only. It is not a
statement about the tree, and not even about those statements unfolded: the
hypothesis `HostExW` of S8 unfolds to conditions on zeros of auxiliary
L-functions. The first version of this atlas said here that below S11
zeros are not mentioned again, and that the supply side carries only values
of `L'/L` at `s = 1` and possibly zero-free boxes. Review found that this
understates the text. The supply argument of S6 names a chain of classical
theorems about zeros of Dirichlet L-functions: a truncated explicit formula
with a sum over zeros, a count of zeros in windows, a zero-free region, a
count of moduli with a zero in a box, and the functional equation. They are
stated for the characters of the host field and are used at scales far above
the window. Section 10.5 quotes the statements and gives the chain of names.

## 3. The analytic interface: one inequality, supplied under two hypotheses

One inequality is consumed by the Landau step. Three lines.

1. **Object.** For a primitive character `χ` of order `o`:
   `Gm_χ(x) = Gz(x) + (3o + 1)^(−1) Σ_{k=1}^{o−1} Re g_{(χ^k)*}(x)` (S10).
2. **What everything below must supply.** For every primitive `χ` and every
   small `eps`: `Gm_χ(x) ≤ x^(1/2 + (eD + eL + 7)·eps)` for all large `x` in
   windows `[Y, Y^(3/2)]` with `Y` arbitrarily large, with `eD`, `eL` fixed
   before `eps` (S9, and the theorem below).
3. **What consumes it.** The windowed Landau statement (S11): a one-sided
   bound `Gm_χ(x) ≤ x^θ` on such windows forces `L(s, χ^k) ≠ 0` for
   `Re s > θ`, zeta included; `eps → 0` gives `Re s > 1/2`.

"Single" needs two qualifications, both found in review. First, the
inequality is the only thing the Landau step consumes, and no route to the
top was found that avoids it, by name: `EveryCharacter` is the stated type
of eight theorems (the six of S1, S3, S4, S5 and S6, and the twin `plugAll`
with its one consumer `everyE₂`), each of which names another of the eight
or applies `imprimitive` (S7) to a term of `ZeroFreeAll`; and `ZeroFreeAll`
is the stated type of three theorems (`CB/ZeroFreeAllOfTopG.lean:26-29`,
`CB/EveryCharacter.lean:8-18`, `TPS/TopPlug.lean:12-17`), of which the second
and third apply the first. A theorem whose type is the same Prop written
out, without either name, would escape this search. Second, the theorem that
supplies the inequality takes two hypotheses, and both carry analytic
conditions of their own.

The statement that crosses the interface from below:

`PC/CoreGm.lean:12-15`
```lean
theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by
```

Reading: `CoreAtH` (`PC/CoreAtH.lean:29-40`) is the arithmetic and geometric
inequality; one of its conjuncts is `ThinScales`, a bound at much larger
scales (section 4, end of Layer 2). `EAtH` (quoted in 10.5) has six fields.
Four tie the level to a "host" abelian field (`o_eq`, `kept`, `ps`,
`shares`). Two are analytic:
`bdG`, a pointwise bound `‖g_χ(x)‖ ≤ x^(1/2 + eps)` of the same strength as
the conclusion for the host characters that are not kept, and `bdL`, a bound
on `L'/L(1, χ)` for the same characters. So `core_gm` does not turn pure
geometry into the inequality: it turns geometry plus a bound of the same
strength for other characters, at the one scale `x`, into the inequality for
the kept ones. Where the archive states the supply of `bdG` is in 10.5.

The interface inequality is a statement about primes only. If GRH holds for
the characters involved, each `G` is of size about `√x`. That is a standard
explicit-formula heuristic, derived by the readers; this builder did not
look for it in the archive. (The archive does state a truncated explicit
formula with a sum over zeros, and uses it on the supply side at much larger
scales: 10.5.) Under GRH the inequality is then true with room, and no
finite computation can contradict it. The content is in how the upper bound
is produced, not in the bound.

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

Reading: for `Re s > 1` and `χ ≠ 1` the Mellin transform of `G_χ` is
`−(L'/L(s, χ) − s·L'/L(1, χ))/(s(s − 1))`. The arithmetic input is Mathlib's
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`, that is
`−L'/L(s, χ) = Σ Λ(n) χ(n) n^(−s)`: the Euler product in
logarithmic-derivative form, which Mathlib derives from the complete
multiplicativity of `χ`.

That theorem carries `hχ : χ ≠ 1`, so it does not cover the Riemann zeta
function, the case in the title. The first version of this atlas cited it
alone. The level-one character has its own file and its own Mathlib
identity:

`LT/mellinGchiModOne.lean:115-118`
```lean
theorem mellin_Gchi_modOne (χ : DirichletCharacter ℂ 1) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1 - (1 + Real.eulerMascheroniConstant) * s) /
        (s * (s - 1)) := by
```

whose proof text names
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
(`LT/mellinGchiModOne.lean:191`), that is `−ζ'/ζ(s) = Σ Λ(n) n^(−s)`.

What the 28 modules under `lemmaL` read from Mathlib about each L-function,
as far as the text was followed:

1. the von Mangoldt series identity, in the two forms above;
2. Mathlib's analytic continuation: differentiability of zeta away from
   `s = 1`, the simple pole of zeta at 1 with residue 1, and the constant
   term `γ` there (`LT/poleData.lean:149-196`, which names
   `differentiableAt_riemannZeta`, `riemannZeta_residue_one`,
   `tendsto_riemannZeta_sub_one_div` and `riemannZeta_one_ne_zero`), and
   differentiability of `L(s, χ)` everywhere for `χ ≠ 1`
   (`LT/poleData.lean:231`);
3. the conjugation symmetry `L(conj s, χ⁻¹) = conj L(s, χ)`
   (`LT/LFunctionConj.lean:88-89`), which the archive derives from Mathlib's
   Hurwitz zeta function;
4. non-vanishing on `Re s ≥ 1`
   (`LT/CharFamilyLFunctionNeZeroOfOneLeRe.lean:9`).

This is a list of what was found, not a closed inventory. One negative
count goes with it: no file under `DL` contains the strings
`completedLFunction_one_sub`, `riemannZeta_one_sub` or `LFunction_one_sub`,
so the functional equation is not named anywhere in the directory that holds
the Landau step.

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

`SWB/FirstPrimeNeSecondPrime.lean:38-42`
```lean
structure ArithData (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] where
  q1 : ℕ
  d : ℕ
  inertia : ℕ → AddSubgroup (E0 × H)
  frob : ℕ → E0 × H
```

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

Reading: `ArithData` is an abstract record: two numbers, and for each
natural number a subgroup named `inertia` and an element named `frob` of a
finite abelian group. Nothing in the record says that these are inertia
groups and Frobenius elements of a number field; that they behave like them
is asked by the hypothesis `HostFacts`
(`SWB/FirstPrimeNeSecondPrime.lean:47-59`: `inertia p` is trivial away from
2, `q1` and `d`, and so on), and the record is instantiated at a host field
in the bridge theorem below (`arith H.toHostRaw`). With that understood,
`primVal` is a character value defined prime by prime from those fields: the
Euler product written as Frobenius data.
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

So an upper bound for `Gm` is obtained from an upper bound for a count of
prime powers by Frobenius class. The two theorems that carry it do not
mention `ASK` or `MAIN` by name. They bound a quantity `gapA`:

`DL/SplitInertia.lean:50-52`
```lean
def gapA (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (u0 : H) : ℝ :=
  ∑ t ∈ TT, ∑ j : Fin m, (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re)
```

`ch_top` (`LT/ChTop.lean:37-44`) concludes `gapA ≤ x^(C·eps) · (error
bracket)` from `SizeData₂` and four further hypotheses, and `ch_core`
(`LT/ChCore.lean:343-351`) takes that bound on `gapA` as a hypothesis and
concludes `GmA ≤ x^(1/2 + (C + 3)·eps) + SigA`. The shorthand
`ASK ≤ MAIN + error` used below therefore means a bound on the double sum
over `t` and `j` of `ASK − Re MAIN`, not a bound term by term. That bound is
what the geometric side is asked for through `SizeData₂`
(`SWB/SChain.lean:17-19`), a conjunct of `ChainTied`. `ch_core` has a second
analytic hypothesis, `ThinScales`
(`SWB/GrowthBoundGivesRiemannHypothesis.lean:55-56`): a bound
`‖GPsi(y)‖ ≤ y·θ` for every character of the group and every `y ≥ X'/3`. It
is also a conjunct of `CoreAtH`, and it has the shape of the classical bound
of 10.5. The step between the two was not traced.

**What the standing rivals fail.** This paragraph is a reading, in the sense
of section 0, and nothing more: it is the lab's own mathematics about the
Davenport-Heilbronn function and Epstein zeta functions, set against the
hypotheses quoted above. Nothing in it was computed, no rival was run through
`zeta.epstein.battery`, and the facts about the rivals are recalled from the
literature, not rechecked today. It carries neither of the two grades.

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

So in the three files that lead from `EveryCharacter` to RH (`RhOfRight`,
`CritLine`, `ClaimStrip`) the functional equation is used for one thing: to
reflect a zero with `Re s < 1/2` to one with `Re s > 1/2`.

The first version of this atlas went further and said that the functional
equation plays no part in the half-plane statement `EveryCharacter`. That
sentence was asserted from those three files and never tested against the
chain below, and review showed it false at this atlas's own standard of
"names". Two things are true on the text:

- No functional-equation lemma is named in the directory of the Landau step
  (section 4, the negative count).
- The supply argument of S6 names a chain that calls Mathlib's functional
  equation twice. Once it reflects zeros of auxiliary L-functions inside a
  sum over zeros: `IsPrimitive.completedLFunction_one_sub` at
  `Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean:46-47`.
  Once it is not a reflection of zeros at all but a growth bound for
  `L(1 − w, χ)` in terms of `L(w, χ⁻¹)`: `ZMod.LFunction_one_sub` at
  `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFE.lean:62`.
  The chain of names from S6 to both lines is written out in 10.5.

Over the whole tree, outside import lines: `completedLFunction_one_sub`
stands on 14 lines in 11 files and `riemannZeta_one_sub` on 6 lines in 5
files; the string `LFunction_one_sub`, which includes the first of these and
the `ZMod` form, on 16 lines in 13 files; and `rootNumber` on 78 lines in 16
files. So the functional equation is called at a few dozen places in the
tree, not at three. Whether the kernel term of `EveryCharacter` depends on
either call of the chain is for the replay (question 16).

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
| 3 | `qN = M^k + R`, the path quadric (10/19) | 0 | Not located under any notation searched; the searches are listed in the finding below the table, with `gauss_core` as the nearest skeleton. |
| 4 | `W(1_S) ≥ 0` via a determinant (10/6) | A | No explicit-formula functional is defined: "Guinand" occurs in no file, and the only identifiers containing `weil_functional` are `linear_weil_functional_*`, in 9 files under `AVT/Proofs`, none of which mentions `riemannZeta` or `vonMangoldt`. The role is played by the one-sided bound `ASK ≤ MAIN + error` (section 4). |
| 5 | switch to `Σ_{n≤X} Λ(n)(X/n − 1) − X log X + (1+γ)X` (10/20) | Q | `Formalism/StatementOC.lean:11-13`, quoted in S10: this expression exactly. |
| 6 | a one-sided inequality "gives `> 1 − η`" (10/8) | Q, in shape | `ZetaLandau`, quoted below: a one-sided `x^θ` bound on `Gz` gives zero-freeness for `Re s > θ`. The literal two-step test function of the note was not found. |
| 7 | GGP periods, interlacing weights (10/14) | A | A definition named `Interlace` with interlacing inequalities at `Formalism/LocalRingCardinality/DataTheta.lean:529-530`. The link to Gan-Gross-Prasad is at the level of names ("GGP" occurs in 262 files). |
| 8 | iterated theta lifts `U(X_0) → … → U(X_m)`, `m` like `√X` (11/15) | Q, in shape | `LiftChain`, quoted below: a chain `G j = vth T μ j (G (j + 1))` for `j < D.R.m`. A chain length of order `√x` is stated for a number `m`: `x^(1/2 − ε) ≤ m` in `RestSize` (`SWB/SChain.lean:53-58`) against `m ≤ x^(1/2 + ε/2)` in `ch_core` (`LT/ChCore.lean:343-351`). Two links rest on a letter or a name and are not shown by a quote: that this `m`, an existential of `ChainTied` (`Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97-114`), is the `D.R.m` of `LiftChain`, and that `vth` is a theta lift. |
| 9 | norms of the lifts, Chowla-Selberg, Weyl, Siegel mass (11/15) | A | `GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg`, `Formalism/PeriodIntegrals/UnitaryGroupMassFormula` (3,615 files), and a period constant of Chowla-Selberg shape, `logOm` at `Formalism/RankGapBounds/MeanBoundSecondForm.lean:88`. |
| 10 | lower bound on divisibility of the m-fold lift (11/15) | A | `DIV` at `Formalism/RankGapBounds/MeanBoundSecondForm.lean:118-121`, a conjunct of `SizeData₂`. That it encodes a divisibility bound is a reading. |
| 11 | Iwasawa tower by analogy with pigeonhole (10/6) | Q | `PageN`, quoted below: a power of 2 with `2^e` between `x^(2+8·eps)` and twice that; `IsChiField` (section 4) requires `2^(e+2) ∣ N`, so the host field sits in a 2-power cyclotomic tower. The string "Iwasawa" occurs in 14,698 files but in only 1,023 outside import lines: most hits are imports of modules under a directory named `IwasawaDecomposition` (section 8). |
| 12 | seesaw, Bessel period independent of the Hecke characters, Rallis (11/15) | A | "seesaw" occurs in 3,248 files, 3,139 of them outside import lines; `RallisHyp` is defined at `Formalism/ThetaLiftIndependence/Statement.lean:232-235`. No statement was matched to the item. |
| 13 | Bost slope inequality (10/6) | Q, in shape | `SlopeIneq`, quoted below. No identifier contains "Bost": the 7 files that match the letters do so only in import lines, across the words "…Bo" and "Statement" of a module name. That `SlopeIneq` is a numeric shadow of a Bost-type inequality is a reading. |
| 14 | the cost of each lift, "stop at 2/3 a priori" (11/15) | 0 | Not located. A caution about names: the proof term of S5 names `boundAtTwoThree_linked_of_recT`, and a sibling `boundAtTwoThree_family_of_prints` concludes `BoundAtTwoAndThreeForFamily` (`Development/AutomorphicArithmetic/ResidueCharacters/ClosedOfAll.lean:11`). These look like the item and are not: the definition `BoundAtTwoThree`, quoted below, is a bound at the indices `i` with `l i = 2`, or `l i = 3` under a side condition. The 2 and the 3 are primes, not the exponent 2/3. |
| 15 | integral structure glued across Hecke characters, a "gcd" (11/15) | N | A directory `FND/GaloisRepresentations/IntegralStructures`, which holds the term of S3. |
| 16 | relative trace formula, sixfold cover of `GL_5`, Poincaré series (10/14) | N | "sixfold" and "relative trace" occur in no file. A directory `Formalism/LocalToGlobal/GlobalTheory/GL5` (15 files) and Poincaré series statements (`Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PoincareSeriesFinite.lean:5`) exist. |
| 17 | a weakening of Vandiver for classes in `H¹(O_E[1/ℓ], Q_ℓ/Z_ℓ(−e))` (11/15) | Q | `VVle` and `VWin`, quoted below. "Vandiver" occurs in no file. |
| 18 | covolumes, theta series' index, congruences (11/15) | A | The term of S4 applies `topCovolSlim2_use_alt_alt` (`TPS/EveryCharacterOfLiteratureOfVWin.lean:812`); the lattice directories `Formalism/MeanHeightDescent` and `Formalism/LatticeSlopes` were not read for this item. |
| 19 | the choice of tower, "using Behrend" (10/19) | Q | `HostThickExists`, quoted in section 9, with a theorem site whose proof text uses Mathlib's `Behrend.sphere` (`Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:85-86`). |
| 20 | GRH (11/16) | Q | `Main.lean:4-12`. |

String counts in this table are measured by `recount.py` (fixed strings,
any letter case) and recorded in `stats.json`.

Count: 9 located with a quoted statement (four of them in part or in shape),
6 by area only, 2 by name only, 3 not located.

**Finding: the function-field toy of the note was not located in the
archive.** Item 3 and footnote 3 of the note describe a weighted point count
on a path quadric over a finite field, `qN = M^k + R`, and call it the
setting in which the two ideas were first combined. It was not located under
any notation searched. The first version of this atlas said "the archive
contains no trace of it", which is more than a search can show. What was
searched:

- Fixed strings, any letter case, counted by `recount.py` (`stats.json`):
  "Stepanov", "SignOnly", "sign_only", "Gabber" and "pathQ" occur in no
  file. "tridiagonal" occurs in 5 files, in identifiers about a
  Weil-Deligne representation and about generators of a module, not about
  a quadric. "zeroMode" occurs in 30 files, the largest group under
  `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability`,
  where the theorem headers are about sections and fibre integrals; the
  files outside that directory were not opened.
- By a reviewer who tried to refute the absence, and not re-run by the
  builder: sums of consecutive products `x i * x (i+1)` written with
  `castSucc` and `succ` (no hit); identifiers combining path, chain or
  tridiagonal with quadric or form (only theta-chain and cochain names);
  iterated Parseval names (none).

The archive has no comments or docstrings in which prose could survive.

The nearest skeleton found is a weighted fibre count stated as a zero mode
plus a remainder, `gauss_core`
(`Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean:592-600`):
for a map `Q : U → T` into a finite abelian group of order `q^a` and a
weight `f`, the sum of `f` over the fibre `Q = 0` differs from
`(Σ f)/q^a` by at most `2·q^(1−ρ)·|U|/q^a`, given bounds on the twisted sums
`Σ ψ(Q u) f(u)`. It is the function-field reader's item Z1, which the first
version dropped without mention. It is a general lemma and not the toy.

What also exists is the classical unweighted count for a non-degenerate
quadric, for example

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

Item 11, `CB/ExistsPageN.lean:39`
```lean
def PageN (eps x : ℝ) (e : ℕ) : Prop := x ^ (2 + 8 * eps) ≤ (2 : ℝ) ^ e ∧ (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps)
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

Item 14 (the caution), `AVT/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean:52-53`
```lean
def BoundAtTwoThree (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (C : ℝ) : Prop :=
  ∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i = 2 ∨ (D.nd.l i = 3 ∧ D.nd.l i ∉ D.host.small)) → ∀ π ∈ D.nd.Zgood i, Bd ρ i π (midF L C)
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

Grade: measured count. Tool: `recount.py`; tables: `stats.json`, which
`build_stats.py` writes from the recount and from nothing else except the
reader's figures it is compared against (`reader_values.json`). All
directory rows at depth 1 and depth 2 were recomputed and agree with the
reader's tables in files and lines. Every number in this section, and every
string count in sections 4, 5, 6, 8, 9 and 10, is a field of `stats.json`.

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
| occurrences of `--` anywhere, or of `/-` | 0 |

Nothing is dead by import: every module is reachable from `Main`. Import
reachability is not use. Whether a given theorem is consumed by the five top
theorems is not decided by these numbers.

**The archive has no comments.** The two characters `--` occur nowhere in
the tree, at a line start or after code, and no file contains `/-`: no
comments, no docstrings, no module documentation, no attributions. Every
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

The import-leaf and depth-range columns of the first table were the
reader's in the first version; `recount.py` now computes them, with the same
values.

One directory at depth 3, `Development/AbelianVarietyTheory/Proofs`, holds
95,418 files and 7,436,698 lines, 54% of all files, in 36 sub-directories
(recomputed; the first version copied it from the reader's table).

Import depth (longest path from an import leaf), in bins of 25:

| depth | 0-24 | 25-49 | 50-74 | 75-99 | 100-124 | 125-149 | 150-174 | 175-199 | 200-202 |
|---|---|---|---|---|---|---|---|---|---|
| modules | 61,596 | 42,070 | 30,679 | 26,053 | 12,209 | 2,225 | 273 | 79 | 3 |

Declaration counts, approximate (a keyword at the start of a line, after
attributes and modifiers):

| theorem | lemma | def | abbrev | structure | instance | example | inductive | class |
|---|---|---|---|---|---|---|---|---|
| 784,092 | 34,663 | 212,819 | 13,202 | 8,286 | 7,598 | 4,662 | 121 | 43 |

The `instance` figure in this table excludes `scoped instance` and
`local instance`. With those two modifiers accepted the count is 8,199,
which is the reader's figure; no other column changes. The first version
recorded 7,598 against 8,199 as a disagreement "not reconciled". A reviewer
reconciled it, the reader's count was the fuller one, and the table above
undercounts instance declarations by 601.

The reader's import edge count is 753,569; the recount of distinct
importer-imported pairs is 753,261, and the difference is explained: 753,569
is the number of import lines naming an archive module, 308 of which repeat
an import the same module already makes.

File shape: the median file has 58 lines, the mean is 99.2, and the largest
has 17,981 (`Formalism/HermitianCurvature/HermitianCurvatureProofs/IsAdmissibleSplittingCharPairMulTwist.lean`).
8,735 files have a line longer than 1,000 characters, and 11,594 have a line
longer than 1,000 bytes: the second is the reader's figure, which the first
version also left unreconciled. The median over files of the longest line is
224 characters. `Formalism` has 107 sub-directories. In 86 of them a file
whose name begins with `Statement` lies somewhere below, and in 82 it lies
directly inside: there the claims are written as `def Name : Prop := …`, and
those files are the readable interface of the archive.

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
Chebyshev's inequality. Theorems named `*_of_literature` are mostly not
hypotheses taken from the literature: of the 195 theorems of the ledger, 152
do not mention the hypothesis structure in their text, 4 read a field of it
and 13 reach a field through other theorems of the file (S4).

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
6, item 6). Closure: 18 modules, 2,338 lines. The spine of section 2 does
not name it: it uses the windowed form S11. The first version said "the live
chain does not use it", which was not checked and is withdrawn: the theorem
`zetaLandau` has consumers. It is applied at
`Formalism/SizeWindowBrackets/ChainSlopeWindows/RiemannHypothesisOfPowerBound.lean:11`
and at
`Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/LandauZeroFreeHalfPlane.lean:16`,
in two theorems that are both named `landau_zero_free_half_plane`; a theorem
of that name is applied in turn inside `chain_epsilon_half_plane`
(`Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:708-716`).
Whether any of that reaches the five top theorems was not traced (question
11).

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
lower-bound variant and a CM-type variant). Since each name occurs once,
nothing in the tree asserts or consumes them by name. They remain precise
statements that can be tested.

The ledger of S4 names a much larger set. How many parameterless Props are
defined in the namespace `GlobalTheory.Published` and its sub-namespaces,
and for how many a one-line theorem of exactly that type exists, depends on
the regular expression. Three rules gave three answers:

| rule | Props | with a one-line theorem |
|---|---|---|
| a reader's (not re-run) | 419 | 177 |
| this builder's first rule (line-start `def`, namespaces only) | 445 | 181 |
| a wider rule (indentation, attributes, `section` and `_root_.` handled) | 467 | 191 |

The wider rule is a reviewer's; `recount.py` now implements both and
reproduces both rows. The 445 names are a subset of the 467. So the honest
figure is a range: 419 to 467 Props, 177 to 191 of them with a one-line
theorem. The remaining 242 to 276 are not shown to be open: multi-line
theorem headers, structure fields and renamed copies are invisible to all
three rules.

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
goal. An assigned term is checked by the kernel when the enclosing theorem
is added, so a wrong assignment should fail there and not pass silently;
that is what a replay will show.

How far the tactic reaches. The first version of this atlas gave one figure,
"234 lines in 50 files, counting a macro `kc%`". That figure counts the
token `kexactB` itself: the definition, the direct uses and the lines that
define macros. It does not count the lines where a macro is used, so it
under-sized the audit target. A reviewer found the rest, and `recount.py`
now counts both:

| token | lines | files | what it is |
|---|---|---|---|
| `kexactB` | 234 | 50 | the tactic, by name |
| `kc%` | 182 | 32 | term macro, `(by kexactB e)`; seven definitions, one of them scoped (`AVT/Definitions/AutomorphicMembership/PlaceModelImp.lean:27`) |
| `kq%` | 3 | 2 | the same macro under another name; one definition is in a directory of the spine (`TPS/ExistsSelectionPairLocalLanglands.lean:29`) |
| `kd%` | 1 | 1 | the same again; the one line is its definition (`AVT/Proofs/TwistedOperators/TwoLeMOf.lean:72`) |
| `tr_via` | 49 | 8 | tactic macro that ends in `kexactB` (`AVT/Definitions/AutomorphicMembership/GoodPartEq.lean:17`) |
| `tr_clause` | 22 | 5 | tactic macro that ends in `kexactB` (`AVT/Definitions/AutomorphicMembership/RealIoX.lean:111`) |
| any of the six | 469 | 72 | lines that reach the tactic by name or through a macro |

Two further tactics act on a goal from meta-level code. `kcopy`
(`Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:53-58`) copies a
term across structures; as a whole word it stands on 5 lines in 4 files, two
in its own file and three uses. And `run_tac` blocks, on 32 lines in 16
files, of which one assigns the goal directly, with no elaboration-time
check at all:

`AVT/Proofs/IwasawaDecomposition/ExistsGIs.lean:81-83`
```lean
  run_tac do
    let m ← Lean.Elab.Tactic.getMainGoal
    m.withContext do m.assign (← Lean.Meta.getFVarFromUserName `h)
```

Another `run_tac` block builds a proof term by hand at
`AVT/Proofs/DivisorProofs/FramesTildeGammaValues.lean:70`; the other 14 files
were not opened.

Other meta-level code found: a `positivity` extension in a directory of the
spine (`TGC/EvalFrameOrd.lean:7-16`), and the command of 10.1. This is a
list of what was found, not of all meta-level code. As a size for the rest:
91 lines in 67 files begin with `elab`, `macro` or `syntax`, and only the
ones named in 10.1 and 10.2 were read.

Related text facts, all measured by `recount.py`:

- Zero occurrences: `sorry` as a word, and as a substring in any letter
  case; `admit` as a word (it occurs inside longer identifiers); `axiom` as a
  word, and as a declaration; `native_decide`; `implemented_by`; `@[extern`;
  `unsafe` as a word.
- `#print axioms` occurs 4 times and `#check` twice, in two files under
  `Formalism/PeriodIntegrals/UnitaryGroupMassFormula`
  (`Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/Transf.lean:100`;
  `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UnitaryClassMass.lean:22-27`).
  They are about four intermediate theorems, not about the five of
  `Main.lean`, and their output will appear in the replay's build log.
- `set_option allowUnsafeReducibility true` occurs 37 times in 33 files. It
  is the only place the letters "unsafe" occur.
- `partial def` occurs twice, both in meta-level helpers
  (`Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:41`,
  `Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:18`).
- 5 `run_cmd` lines, all in `BuildAid/D1.lean` to `D5.lean`
  (`BuildAid/D1.lean:4`), each adding a namespace to a library-suggestion
  deny list.
- 88,139 `set_option` occurrences and 220 `open private` lines.

A grep is not an axiom audit: only `#print axioms` on the five theorems of
`Main.lean` after a build shows what they depend on.

**10.3 Structures named for hypotheses, and where they are given terms.**
The tree has 106 `structure` declarations whose name contains "Hypothes",
"Literature" or "Published". That is a lower bound on hypothesis-style
structures, not a census: the pattern misses `ThetaLocalInputs`, one of the
three that S4 itself lists, and by the same kind of count 40 structures have
"Input" in their name and 256 `def`s have "Hypothes". On the spine:

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

**10.5 The supply side: a bound of GRH strength at one scale for auxiliary
characters, and a classical chain about zeros.** The first version of this
section was titled "whose supply was not traced" and said that the text read
did not show the mechanism. Review traced it at the level of names and
statements, and found on the way that the supply side holds the classical
analytic number theory which the first version said was absent. Both are
recorded here. Everything in this section is a chain of names in proof
texts, in the sense of section 0.

*(a) What is asked.* The hypothesis `EAtH` of the interface theorem
contains, for the characters of the host field other than the kept ones, a
pointwise bound of the same strength as the conclusion, at the single scale
`x`:

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

through `supplyOfAdm` (`CB/HostOfField.lean:17-23`), whose conclusion is
`HostExW (3/2)` of the requirement `EAtH … ∧ VVle …`, and the existence
statement `HostExW`
(`AVT/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:120-123`). The
auxiliary primes are very large compared with `x` (`WinPair`,
`CB/ExistsPageN.lean:27-37`: `log q` of order `Y^(eps/5)`), and an earlier
layer states the same shape as an existence statement over prime pairs
(`ExistsSplitGoodPrimePair`,
`SWB/SmoothedRemainderRealIntegralFormula.lean:50-60`). How a pointwise bound
`‖g_χ(x)‖ ≤ x^(1/2 + eps)` is obtained for those characters, without assuming
what is to be shown, is the most delicate analytic point on the spine.

*(b) Where the archive states the supply of `bdG`.* The proof text of
`supplyOfAdmOf` names two things
(`Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:29` and
`Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean:125`): a
term `QH.pairEx` of the Prop `PairEx`, and the theorem `boundedTw`.

`CB/PairGood.lean:18-26`
```lean
structure PairGood (M : ℕ) (eps Y X : ℝ) (q d : ℕ) : Prop where
  pair : WinPair eps Y q d
  coprime : Nat.Coprime M (q * d)
  bounds : ∀ (ξ : DirichletCharacter ℂ M) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw (fun a => ξ (a : ZMod M)) q d i j) (2 * M * q * d) →
      ∀ y : ℝ, Y ≤ y → y ≤ X → ‖An.gChi χ y‖ ≤ y ^ ((1 : ℝ) / 2 + eps / 2) ∧ ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log y
  boxes : ∀ ρ : PChar, ρ.IsReal → ρ.N ∣ 8 * M → ∀ i j : Fin 2, (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw ρ.val q d i j) (2 * M * q * d) →
      ZeroBox (height M eps Y j) χ
```

`CB/PairGood.lean:28-30`
```lean
def PairEx : Prop :=
  ∀ (M : ℕ), 0 < M → ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ A →
    ∃ Y1 : ℝ, ∀ Y ≥ Y1, ∃ q d : ℕ, PairGood M eps Y (Y ^ A) q d
```

Reading. `tw ξ q d i j` (`CB/PairGood.lean:9-10`) is the function
`a ↦ ξ(a)·(a/q)^i·(a/d)^j` with Jacobi symbols. `PairGood M eps Y X q d` says
that `q` and `d` are a pair of primes of the prescribed sizes (`WinPair`),
coprime to `M`, and that, for every character `ξ` modulo `M` and every
`(i, j) ≠ (0, 0)`, the primitive character inducing the twist satisfies
`‖g_χ(y)‖ ≤ y^(1/2 + eps/2)` and `‖L'/L(1, χ)‖ ≤ 4 log y` for all `y` in
`[Y, X]`; a fourth field asks zero-free boxes for the real ones. `PairEx`
says that for every `M`, `eps` and `A` and every large `Y` such a pair exists
with `X = Y^A`. So the bound of GRH strength is asked of the twists by the
auxiliary primes, on a range of scales, for one well-chosen pair: it is an
existence statement, as the first version guessed, and this is where it is
written.

`boundedTw` (`CB/BoundedTw.lean:45-49`) concludes `BoundedCharsPointwise`
and the bound of `bdL` from `PairGood`; its key lemma
(`CB/BoundedTw.lean:5-9`) says that every character in `Bounded` is induced
by such a twist with `(i, j) ≠ (0, 0)` of a power of `ψ`. On this reading
the kept characters are the untwisted powers of `ψ`, and the bound is asked
only of the twisted ones. `PairEx` is given the term `QH.pairEx`
(`Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112-113`),
whose proof text names `pair_exists`
(`Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean:9-12`).
The directory `Development/AutomorphicArithmetic/MeanSquareBounds` (35 files,
4,301 lines) states what kind of argument this is:

`Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:26-27`
```lean
def MeanSq (C Z : ℝ) (P : Finset ℕ) (A : Set ℝ) : Prop :=
  ∀ y ∈ A, ∀ κ : ℕ → ℂ, (∀ n, ‖κ n‖ ≤ 1) → ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤ C * y * Real.log y * P.card
```

a mean-square bound over a set `P` of auxiliary primes `q` for the sums `S`
(`Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:13-14`:
a sum over `n ≤ Z` of a weight `cN y n` times a bounded sequence times the
Jacobi symbol `(n/q)`), stated as a theorem for primes in a progression
(`meanSqK`,
`Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:51-54`),
and a count of exceptional moduli: at most `C·Q^(1/4)` primes `q` can each
carry a primitive character of modulus `f·q ≤ Q`, with `f` below a bound
that `q` exceeds, that has a zero in the box (`count_bad`,
`Development/AutomorphicArithmetic/MeanSquareBounds/CountBad.lean:9-12`).

Reading: on the statements, the mechanism is an average over the auxiliary
primes, of large-sieve type, from which one pair `(q, d)` is selected. A
bound of GRH strength for some member of a family, on one range of scales,
is the kind of conclusion a mean-value theorem gives without any hypothesis
on zeros, so the step is not circular on its face. That is a reading of
statements. The proof texts between `meanSqK` and `pair_exists` were not
read, and whether the selection delivers the pointwise bound for every
twist at once, as `PairGood` asks, is the thing to check there (question 3).

*(c) The classical chain about zeros.* The existence statement `HostExW`
asks more of a host than `EAtH`: its conjunct `HostGood`
(`AVT/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:101-109`)
includes `ThinOK` and `BoxW`.

`AVT/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:61-63`
```lean
def ThinOK (s : Scale) (c : ℝ) (H : Host R) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharH H χ →
    ∀ y : ℝ, Real.exp (s.x ^ (s.eps / 3)) / 3 ≤ y → ‖GlobalTheoryTheory.gChi χ y‖ ≤ y * Real.exp (-(c * s.x ^ (s.eps / 8)))
```

`ThinOK` quantifies over every character of the host, kept ones included,
and bounds `g_χ(y)` by `y·exp(−c·x^(eps/8))` at scales `y` above
`exp(x^(eps/3))/3`: far above the window, where a bound of
prime-number-theorem strength is enough. The archive states it as a theorem
by this chain of names, each link read:

1. S6: `fun ψ => supplyChi ψ (hV ψ)` (`TPS/TopPlug.lean:12-17`, line 15).
2. `supplyChi` names `supplyOfAdm` (`CB/SupplyChi.lean:8-11`), which is
   `supplyOfAdmOf hostOfField` (`CB/HostOfField.lean:17-23`), and
   `hostOfField` is `hostOfFieldOf shortNorm smallOne`
   (`CB/HostOfField.lean:8-15`).
3. `hostOfFieldOf` names `QH.thinH` and uses it for the `ThinOK` conjunct
   (`Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:169`,
   `Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:247`).
4. `thinH` names `thin`
   (`Development/AutomorphicArithmetic/MeanSquareBounds/GaussSumFunctionEq.lean:55-60`),
   and `thin` names `psi_thin`
   (`Development/AutomorphicArithmetic/MeanSquareBounds/Thin.lean:15`). The
   statement of `thin`:

`Development/AutomorphicArithmetic/MeanSquareBounds/Thin.lean:10-13`
```lean
theorem thin :
    ∀ ε A c c₀ : ℝ, 0 < ε → 0 < A → 0 < c → 0 < c₀ → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      Real.log N ≤ A * x ^ (ε / 5) * Real.log x ^ 2 → (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) →
      ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → ‖G0 χ y‖ ≤ y * Real.exp (-(c * x ^ (ε / 8))) := by
```

5. `psi_thin`
   (`Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean:385-392`)
   names three classical inputs: `explicitFormula_closed`,
   `zerosWindow_closed`, and, through `pt_zero_free`
   (`Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean:353-357`),
   the zero-free region `Formalism.ZeroFreeDirichlet.zFRDirichlet`. Further
   down (`Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean:401`)
   it names `pt_zero_symm`
   (`Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean:27-29`),
   the reflection `L(ρ, χ) = 0 ⇒ L(1 − ρ, χ⁻¹) = 0` for a zero in the strip,
   whose proof text contains the first functional-equation call of
   section 5.
6. `explicitFormula_closed`
   (`Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean:8-10`)
   is `explicitFormula_of`
   (`Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ExplicitFormula.lean:8-10`),
   which is `explicitFormula_main`. That names `localLemma_of_helpers`,
   which names `lGrowth_of` (both at
   `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalLemmaOfHelpers.lean:14-23`);
   `lGrowth_of` names `L_nontriv_growth`
   (`Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthMain.lean:96`),
   which names `norm_L_one_sub_le`
   (`Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthMain.lean:55`),
   whose statement
   (`Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFE.lean:49-51`)
   bounds `‖L(1 − w, χ)‖` by `6·N^5·‖w + 1‖^5·‖L(w, χ⁻¹)‖` for primitive `χ`
   and `1/2 ≤ Re w ≤ 5`, and whose proof text contains the second
   functional-equation call.

The statement at the centre of the chain is a truncated explicit formula
with a sum over zeros, for every primitive Dirichlet character:

`Formalism/PeriodIntegrals/ExplicitFormula.lean:16-24`
```lean
def ExplicitFormulaWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖)
```

with `psi0 χ u = Σ_{n ≤ u} Λ(n) χ(n) − [χ = 1]·u` and `ZerosBelow χ T` the
zeros with `0 < Re ρ < 1`, `|Im ρ| < T`
(`Formalism/PeriodIntegrals/ExplicitFormula.lean:9-14`). Beside it stands a
count of zeros in unit windows, at most `C·log(N(|t| + 2))`
(`ZerosWindowWith`, `Formalism/PeriodIntegrals/ZerosWindow.lean:10-14`).

Reading: this is the prime number theorem for arithmetic progressions with a
classical zero-free region, stated and given terms inside the archive in the
classical way (explicit formula, zero count, zero-free region, functional
equation), under the hypothesis that the real characters involved have no
exceptional zero (`NoExc`,
`Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean:71-72`).
It is ordinary analytic number theory: zeros enter through an explicit
formula over all zeros of the strip and through a zero-free region near
`Re s = 1`, and no statement of the chain, as far as read, assumes or
concludes anything about `Re s = 1/2`. What the first version got
wrong is the picture: the archive is not an argument that never looks at
zeros below the Landau step. It contains a classical treatment of zeros,
and the supply of hosts names it. Whether the kernel term of `EveryCharacter`
depends on it is for the replay (question 16).

*(d) The zero-free boxes.* The clause `BoxH`
(`AVT/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:68-71`) asks a
predicate written `GlobalTheoryTheory.GoodFor` of the real characters of the
host field. Four definitions named `GoodFor` exist in the tree, and the
first version read one and left open which is meant. On the text, only one
of the four sits in a namespace whose last component is
`GlobalTheoryTheory`
(`Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/FiltrationCocycleLiftCriterion.lean:42-44`,
in `Formalism.MainNotions.GlobalTheoryTheory`, and the file of `BoxH` opens
`Formalism.MainNotions`). It asks for a primitive real character of
conductor at most `Q` with no zero in the box `Re s > 1 − 1/400`,
`|Im s| ≤ Q`: a condition of classical strength, and the same content as
the definition read first
(`SWB/SmoothedRemainderRealIntegralFormula.lean:41-45`). Name resolution is
the elaborator's business, so this is a text-level answer. The boxes are
stated to come with the pair of primes: the field `boxes` of `PairGood`
above, turned into `BoxH` and `RealBox` at
`Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:135-136`,
with `count_bad` as the statement that few moduli are bad.

**10.6 Finite tables closed by `decide +kernel`.** 34 files contain
`decide +kernel` (151 occurrences). These are kernel-evaluated decision
procedures, not compiler-trusted ones, and each is a place where a build can
be slow or fail for resource reasons. The first files in tree order are
listed in `stats.json`.

**10.7 The Props named for published theorems.** See S4 and section 9. The
highest-value human reading in the whole archive is whether those Props are
faithful.

## 11. Open questions

Stated as questions. Two were answered in part at text level during review
and say so. The rest are not answered by a text-level reading.

1. Does the archive compile at the pinned toolchain, and what does
   `#print axioms` report for the five theorems of `Main.lean`? (Owned by the
   replay, pending.)
2. Is the windowed one-sided Landau statement of S11 true as stated, and is
   it in the literature (Turán, Pintz, Knapowski-Turán, Kaczorowski)? Its
   closure is 28 modules: can it be re-derived or kernel-checked on its own?
3. Answered in part at text level (10.5 b): the pointwise bound `bdG` is
   stated to come from `PairGood`, an existence statement over pairs of
   auxiliary primes, with a mean-square bound over the primes `q` behind it.
   Still open: do the proof texts between `meanSqK` and `pair_exists`
   deliver the bound for every twist at once, as `PairGood` asks, and is
   the mean-square statement a known large-sieve inequality for real
   characters or something new?
4. Answered in part at text level (10.5 d): `BoxH` writes
   `GlobalTheoryTheory.GoodFor`, and one of the four definitions is in a
   namespace of that name. Still open: is `count_bad`, the bound
   `C·Q^(1/4)` on the number of bad moduli, a zero-density estimate of
   classical strength, and is it enough for the selection of the pair?
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
10. Is the twin plug at `CB/EveryCharacter.lean:8-18` equivalent to the
   `TopPlug` pair of S6, or a remnant of an earlier design? At text level
   its only consumer is `everyE₂` (S6), a theorem with seven hypotheses that
   nothing names. Does the kernel see either?
11. Do the alternative routes that read as earlier layers feed the five top
    theorems anywhere? `OCStep` and `ForcedSumCM` are named nowhere but at
    their definitions. `ZetaLandau` is different: its theorem `zetaLandau`
    has consumers (section 9, B9), and where they lead was not traced.
12. What does `AV/LiteratureResults/KTheoryStability` state about K-groups,
    and does it bear on the note's footnote 6?
13. Where, if anywhere, is the note's item 14 (the cost of each lift and the
    a priori exponent 2/3)?
14. What does `cpt_copy_thms` copy when it runs, under what names, and do
    any of the five top theorems depend on a copied declaration?
15. Is the function-field toy really absent, or present under a notation
    the searches of section 6 missed? If absent, why, and does an
    independent reconstruction of it (the function-field reader has one at
    float grade, not part of this hunt) match what the note describes?
16. Does the kernel term of `EveryCharacter` depend on the classical chain
    of 10.5 (c): the explicit formula, the zero count, the zero-free region
    and the two functional-equation calls? The atlas shows a chain of names
    from S6 to each of them. Only `#print axioms` and a dependency walk on
    the built environment can say whether the chain is a dependency.
17. Is the rival paragraph of section 4 right? It is a reading from
    recalled literature. A battery comparison aimed at the step that
    distinguishes (the bound on `gapA`, and now also `PairGood`) has not
    been made.
18. Which of the 91 line-start `elab`, `macro` and `syntax` declarations,
    and of the 16 files with `run_tac`, act on a goal or on the environment
    from meta-level code, and what do they do? Only the ones named in 10.1
    and 10.2 were read.
19. The links of section 6 that rest on a name or a letter and have no
    quoted statement behind them, moved here so that no reading stands on
    a name alone: is the `m` of `ChainTied` (an existential) the `D.R.m` of
    `LiftChain`, and is `vth` a theta lift (item 8)? Does `DIV` encode a
    divisibility bound for the lifts (item 10)? Is `SlopeIneq` a numeric
    shadow of a Bost-type slope inequality (item 13)? Does `Interlace` bear
    on Gan-Gross-Prasad periods (item 7)? Do the directories cited for
    items 15 and 16 hold what their names say? Each needs a statement read
    and quoted before it can be graded above a name.

## 12. How to replay this atlas

Anyone with the public tarball can check every citation above.

    python -I hunts/rh_claim_atlas/verify_quotes.py PATH/lean/src --mathlib PATH_TO_MATHLIB_v4.33.1

`quotes.json` holds one entry per citation: the tree, the path, the first and
last line, and the sha256 of exactly those lines. A citation followed by a
`lean` block is a displayed quote and its text is stored; a bare citation is
a pointer and only a short head of its first line is stored. The script
exits non-zero on any mismatch.

The counts replay in three steps, four to five minutes on one core:

    python -I hunts/rh_claim_atlas/recount.py PATH/lean/src --out recount.json (arguments: stats.json, field recount_arguments)
    python -I hunts/rh_claim_atlas/ledger_count.py PATH/lean/src --out ledger.json
    python -I hunts/rh_claim_atlas/build_stats.py recount.json ledger.json --check

`build_stats.py --check` rebuilds `stats.json` from the two outputs and from
`reader_values.json`, and exits non-zero if the result differs from the
committed file in anything but the timing. Every number in sections 2 (S4),
4, 5, 6, 7, 8, 9 and 10 that is called a count is a field of `stats.json`.
The test file checks the prose against those fields row by row.

Read by hand, with no replay path: the three settings of `lakefile.toml`
(section 7), which lies outside the source directory; the number of
definitions of each macro in 10.2, read off one `rg` listing of line-start
`macro` and `elab` lines; and what the identifiers containing "tridiagonal"
and "zeroMode" are about (section 6).

A pass of `verify_quotes.py` says that the cited text is what this atlas
read. A pass of the recount says that the counts are counts of that text.
Neither says anything about whether a kernel accepts the archive, and a
matching hash does not show that a quoted line supports the reading placed
next to it: that is for a reader to judge.
