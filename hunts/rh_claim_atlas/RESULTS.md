# Results: hunt #160, an atlas of the Alpoge archive

Status: built 2026-11-20. A text-level reading of an archive that no kernel
has checked. The kernel replay is a separate hunt (`hunts/alpoge_replay/`, on
another branch) and is pending; nothing here is a verdict on it. Nothing is
promoted. The atlas is original to the lab and claims no novelty.

Two grades are used. **T**: text-level reading, quotes replayable (the claim
is "the archive states X at `path:line`", recorded in `quotes.json` and
replayed by `verify_quotes.py`). **M**: measured count (`recount.py` on file
text; declaration counts are regex counts and approximate). A plain
mathematics reading placed next to a quote is the lab's reading of that text.

## What the atlas establishes

| # | finding | grade |
|---|---|---|
| 1 | The five theorems of `Main.lean` are stated in Mathlib's vocabulary; `RiemannHypothesis` is Mathlib's at the pinned tag, and no archive declaration is named `riemannZeta`, `RiemannHypothesis`, `completedRiemannZeta` or `vonMangoldt`. | T, M |
| 2 | All five are obtained from one term of one Prop, `UpperTheory.EveryCharacter`: `L(s, χ) ≠ 0` for `Re s > 1/2`, every Dirichlet character. | T |
| 3 | The spine from `Main.lean` to the last step that mentions zeros is eleven named nodes (ATLAS section 2). The half-plane statement is stated to follow from one Prop, read as existence of Galois representations for polarized regular algebraic cuspidal representations of `GL_a` over CM fields, which is given a term. | T |
| 4 | There is a single analytic interface: a one-sided bound `Gm_χ(x) ≤ x^(1/2 + O(eps))` on windows `[Y, Y^(3/2)]` for a positive combination of smoothed von Mangoldt sums over the powers of `χ`. | T |
| 5 | The last step that mentions zeros is a windowed, one-sided Landau lemma (`lemmaL`). Its import closure inside the archive is 28 modules and 2,396 lines, in Mathlib vocabulary. | T, M |
| 6 | The Euler product enters at two quotable places: Mathlib's `LSeries_twist_vonMangoldt_eq` in the Mellin identity, and the prime-by-prime character `primVal` with the orthogonality statement behind `ASK − MAIN`. The Galois structure enters where `χ` is realised on a subfield of a cyclotomic field (`IsChiField`). | T |
| 7 | The Davenport-Heilbronn function and Epstein zeta functions of class number above one fail hypotheses of both layers: they are not members of a character family with positive weights, their logarithmic derivatives are not von Mangoldt series, they vanish for some `Re s > 1` (recalled, not rechecked), and no Galois character reproduces their coefficients. Read off the hypotheses, not computed. A rival failing a hypothesis excludes nothing about the proof. | T |
| 8 | RH for zeta is the case of the trivial character modulo 1. The functional equation is used only to reflect a zero with `Re s < 1/2`; it plays no part in the half-plane statement. The archive states RH from `EveryCharacter` by three short routes. | T |
| 9 | Of the note's 20 timeline items, 9 are located with a quoted statement (three in part or in shape), 6 by area only, 2 by name only, 3 not located. The function-field toy of the note (`qN = M^k + R`) is not in the archive. | T, M |
| 10 | The tree has 175,187 files, 17,374,215 lines, 753,261 distinct import edges, a longest import chain of 202, 5,927 import leaves, and every module is in the import closure of `Main`. `Development` is 81% of the files. | M |
| 11 | The archive has no comments at all, and no `sorry`, `admit`, `axiom` declaration, `native_decide`, `implemented_by` or `@[extern`. This is a text scan, not an axiom audit. | M |
| 12 | Several directory names mislead (`Development/WeilBound`, `PositivityTheory`, `…/IwasawaDecomposition`, `…/SmallClassNumbers`, `Formalism/GammaFactorNonvanishing` and others); ATLAS section 8 says what each holds. | T, M |
| 13 | Ten by-products have a closed theorem site in the text (among them Minkowski's second theorem, a qualitative Chebotarev over Q, a Behrend-type set, functorial resolution in characteristic zero, Linnik, a Selmer bound of Vandiver type). Thirteen named Props are defined once and occur nowhere else. | T, M |
| 14 | Audit targets: one command adds declarations with no source text and is invoked once; a goal-assigning tactic occurs in 50 files; hypothesis-named structures are all given terms; the local Langlands Prop is restricted by a predicate `Good`; a `Nonempty` guard has a stated inhabitation; a bound of GRH strength at one scale is required of auxiliary characters and its supply was not traced; 34 files use `decide +kernel`. | T, M |

Spot-checks of the statistics: 25 quantities from the first reader's tables
were recomputed. 22 agree exactly, including all 10 depth-1 rows and all 330
depth-2 rows. Three disagree and are recorded in `stats.json`: the `instance`
count (a regex difference), the import edge count (the reader counted import
lines, 308 of which are repeats; explained), and the number of files with a
line over 1,000 (characters here, presumably bytes there; not reconciled).

Corrections to reader notes found on re-reading: a K-theory directory exists
(one reader reported none); no identifier contains "Bost"; a name on the
spine that looks like the note's "2/3" is about the primes 2 and 3; there are
three routes from the half-plane statement to RH, not two. Three reader
questions were closed at text level: `riemannZeta₁` is Mathlib's, the meaning
of the guard `Good`, and the stated inhabitation of the guard `LocTied`.

## What it does not establish

- That the archive compiles, or that any statement in it is a theorem. No
  Lean was run. "Uses" on the spine means a name appears in a proof text.
- That any Prop means what its name suggests. The Props named for published
  theorems were not read, with four exceptions quoted in the atlas.
- That the windowed Landau statement is true, or whether it is in the
  literature. No search was made.
- Anything about the Riemann hypothesis or GRH, or about the correctness of
  the claimed argument below the interface, which this atlas does not enter.
- Completeness. A few hundred of 175,187 files were opened. The readers'
  notes cover more ground than was re-verified, and what was not re-verified
  was dropped, not kept on trust.
- Novelty of any by-product: "not in Mathlib" is recollection, unsearched.
- Numerics for the interface: those belong to hunt #161
  (`hunts/rh_claim_interface/`).

This hunt measures no ceiling and owes no door analysis.

## Replay

    python -I hunts/rh_claim_atlas/verify_quotes.py PATH/lean/src --mathlib PATH_TO_MATHLIB_v4.33.1
    python -I hunts/rh_claim_atlas/recount.py PATH/lean/src

The first checks 168 citations in under a second and exits non-zero on any
mismatch. The second recounts the tree in about two and a half minutes on one
core. `RUNS.md` has the runs behind this page.
