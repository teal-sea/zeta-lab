# Results: hunt #160, an atlas of the Alpoge archive

Status: built 2026-11-20 and revised the same day after two adversarial
reviews. A text-level reading of an archive that no kernel has checked. The
kernel replay is a separate hunt (`hunts/alpoge_replay/`, on another branch)
and is pending; nothing here is a verdict on it. Nothing is promoted. The
atlas is original to the lab and claims no novelty.

One shared test was red while this hunt was being built, and the hunt could
not make it green: `tests/test_hunt_probe_discipline.py` failed in
`test_every_hunt_directory_is_covered_by_the_case_log` until
`hunts/README.md` gained entries for the hunts opened that day. That file is
shared and outside what this hunt may write. The entries were added the same
day when the hunts were landed, and the test passes.

Three labels are used. **T**: text-level reading, quotes replayable. The
claim is "the archive states X at `path:line`", recorded in `quotes.json`.
**M**: measured count (`recount.py` and `ledger_count.py` on file text;
declaration counts are regex counts and approximate). **R**: a reading, the
lab's own mathematics about quoted text. An R item was not tested and leans
on recalled literature; it is below both grades and is listed so that it is
not mistaken for either.

## Findings

| # | finding | label |
|---|---|---|
| 1 | The five theorems of `Main.lean` are stated in Mathlib's vocabulary; `RiemannHypothesis` is Mathlib's at the pinned tag, and no archive declaration is named `riemannZeta`, `RiemannHypothesis`, `completedRiemannZeta` or `vonMangoldt`. | T, M |
| 2 | All five are obtained from one term of one Prop, `UpperTheory.EveryCharacter`: `L(s, χ) ≠ 0` for `Re s > 1/2`, every Dirichlet character. | T |
| 3 | The spine from `Main.lean` to the last step whose statement mentions zeros is eleven named nodes (ATLAS section 2). The half-plane statement is stated to follow from one Prop, read as existence of Galois representations for polarized regular algebraic cuspidal representations of `GL_a` over CM fields, which is given a term. | T |
| 4 | One inequality is consumed by the Landau step: a one-sided bound `Gm_χ(x) ≤ x^(1/2 + O(eps))` on windows `[Y, Y^(3/2)]` for a positive combination of smoothed von Mangoldt sums over the powers of `χ`. No route to the top that avoids it was found, by name. The theorem that supplies it takes two hypotheses and both carry analytic conditions: `EAtH` (a bound of the same strength for other characters at the one scale) and `CoreAtH` (a bound at much larger scales). "Single analytic interface", as the first version put it, was too strong. | T |
| 5 | The last step on the spine whose statement mentions zeros is a windowed, one-sided Landau lemma (`lemmaL`). Its import closure inside the archive is 28 modules and 2,396 lines, in Mathlib vocabulary. | T, M |
| 6 | The Euler product enters the Landau step at two Mathlib identities, one for `χ ≠ 1` (`LSeries_twist_vonMangoldt_eq`) and a different one for zeta (`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`); the first version cited only the first, which does not cover zeta. On the other side it enters through the prime-by-prime character `primVal` of an abstract record `ArithData`. The Galois structure enters where `χ` is realised on a subfield of a cyclotomic field (`IsChiField`). | T |
| 7 | The Davenport-Heilbronn function and Epstein zeta functions of class number above one fail hypotheses of both layers. This is read off the hypotheses from recalled literature. Nothing was computed and no battery was run. A rival failing a hypothesis excludes nothing about the argument. | R |
| 8 | RH for zeta is the case of the trivial character modulo 1. In the three files from `EveryCharacter` to RH the functional equation is used only to reflect a zero with `Re s < 1/2`. The first version added that it plays no part in the half-plane statement. That is withdrawn: the supply argument of spine node S6 names a chain that calls Mathlib's functional equation twice, once for a growth bound (finding 15). The archive states RH from `EveryCharacter` by three short routes. | T |
| 9 | Of the note's 20 timeline items, 9 located with a quoted statement (four of them in part or in shape), 6 by area only, 2 by name only, 3 not located. The function-field toy of the note (`qN = M^k + R`) was not located under any notation searched; the nearest skeleton is a general fibre-count lemma, `gauss_core`. | T, M |
| 10 | The tree has 175,187 files, 17,374,215 lines, 753,261 distinct import edges, a longest import chain of 202, 5,927 import leaves, and every module is in the import closure of `Main`. `Development` is 81% of the files. | M |
| 11 | The archive has no comments at all, and no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `@[extern`. It does contain four `#print axioms` lines about intermediate theorems. This is a text scan, not an axiom audit. | M |
| 12 | Several directory names mislead (`Development/WeilBound`, `PositivityTheory`, `…/IwasawaDecomposition`, `…/SmallClassNumbers`, `Formalism/GammaFactorNonvanishing` and others); ATLAS section 8 says what each holds. | T, M |
| 13 | Ten by-products have a closed theorem site in the text (among them Minkowski's second theorem, a qualitative Chebotarev over Q, a Behrend-type set, functorial resolution in characteristic zero, Linnik, a Selmer bound of Vandiver type). Thirteen named Props are defined once and occur nowhere else. Props named for published theorems: 419 to 467 depending on the counting rule. | T, M |
| 14 | Audit targets: one command adds declarations with no source text and is invoked once; a goal-assigning tactic is reached on 469 lines in 72 files (234 lines in 50 files by its own name, the rest through five macros); a `run_tac` block assigns a goal directly; hypothesis-named structures are all given terms; the local Langlands Prop is restricted by a predicate `Good`; a `Nonempty` guard has a stated inhabitation; 34 files use `decide +kernel`. The list is of what was found. | T, M |
| 15 | The supply side, which the first version left untraced. The bound of GRH strength asked of auxiliary characters is stated to come from `PairGood`, an existence statement over pairs of auxiliary primes, behind which stands a mean-square bound over the primes. And the supply of hosts names a classical chain about zeros of Dirichlet L-functions: a truncated explicit formula with a sum over zeros, a zero count, a zero-free region, a count of bad moduli, and the functional equation. These are chains of names in proof texts. Whether the kernel term of `EveryCharacter` depends on them is for the replay. | T |
| 16 | The ledger file of S4: of its 195 theorems 152 do not mention the hypothesis, 39 pass it on, 4 read a field and 13 reach a field through other theorems, the one the spine consumes among them. The first version said all but four ignore it. | M |

Comparison with the first reader's tables: 27 comparisons, 24 agree exactly,
among them all 10 depth-1 rows (files, lines, import leaves, depth range),
all 330 depth-2 rows and the depth-3 row. Three disagree, and each is now
reconciled by the row after it in `stats.json`: the `instance` count (7,598
without `scoped` and `local`
instances, 8,199 with them, which is the reader's figure), the import edge
count (the reader counted import lines, 308 of which are repeats), and the
number of files with a line over 1,000 (8,735 in characters, 11,594 in
bytes, which is the reader's figure). The first version called two of these
"not reconciled"; a reviewer reconciled both. Three of the reader's figures
enter two rows each, so the 27 rows compare 24 distinct figures.

Corrections to reader notes found on re-reading: a K-theory directory exists
(one reader reported none); no identifier contains "Bost"; a name on the
spine that looks like the note's "2/3" is about the primes 2 and 3; there are
three routes from the half-plane statement to RH, not two. Reader questions
closed at text level: `riemannZeta₁` is Mathlib's, the meaning of the guard
`Good`, the stated inhabitation of the guard `LocTied`, and, after review,
which `GoodFor` the host clause refers to.

## What this does not show

- Whether the archive compiles, or whether any statement in it is a
  theorem. No Lean was run. "Uses" and "names" mean an identifier occurs in
  a proof text. A chain of names is not a dependency of a kernel term.
- That any Prop means what its name suggests. The Props named for published
  theorems were not read, with four exceptions quoted in the atlas.
- That the windowed Landau statement is true, or whether it is in the
  literature. No search was made.
- That the mean-square statements of finding 15 deliver what `PairGood`
  asks. Their proof texts were not read.
- Anything about the Riemann hypothesis or GRH, or about the correctness of
  the claimed argument below the interface, which this atlas does not enter.
- Completeness. A few hundred of 175,187 files were opened. The readers'
  notes cover more ground than was re-read, and what was not re-read was
  dropped, not kept on trust. The lists of meta-level code and of analytic
  inputs are lists of what was found.
- That a quoted line supports the reading next to it. A matching hash says
  only that the line is unchanged.
- Novelty of any by-product: "not in Mathlib" is recollection, unsearched.
- Numerics for the interface: those belong to hunt #161
  (`hunts/rh_claim_interface/`).

This hunt measures no ceiling and owes no door analysis.

## Review findings and dispositions

Two reviewers attacked the first version. One read for faithfulness (F1 to
F8), one for numbers, replayability and rules (N1 to N12). Every finding was
reproduced against the archive by the builder before anything was changed.
All twenty were found real in substance; none was rejected. Where a
reviewer's figure could not be reproduced to the digit, that is said.

F1 and F4 each show a reading of the first version contradicted by archive
text, which is the second kill condition of `MISSION.md`. The two sentences
are withdrawn in place and the atlas is kept as a revised map; `MISSION.md`
leaves to the owner whether more should be retired.

| id | severity | what was wrong | reproduced | disposition |
|---|---|---|---|---|
| F1 | major | "The functional equation plays no part in `EveryCharacter`"; "below S11 zeros are not mentioned again"; explicit-formula reasoning "not found in the archive text". | Yes, every link of the chain re-read: S6 names `supplyChi`, and from there names lead to `psi_thin`, to `ExplicitFormulaWith`, to `completedLFunction_one_sub` (`PsiThin.lean:46-47`) and to `ZMod.LFunction_one_sub` (`LGrowthFE.lean:62`). `ThinOK` quantifies over every host character. | ATLAS section 5 restricted to the three files, the old sentence kept as withdrawn; end of S11 and section 3 rewritten; 10.5 (c) gives the chain with three quotes; question 16; findings 8 and 15. The reviewer's whole-tree figures (102 lines in 28 files for functional-equation names, 113 files for "explicit formula") were not reproduced to the digit because the pattern was not stated; the recount's own string counts are in `stats.json` and point the same way. |
| F2 | major | The Euler product was cited at a lemma with `χ ≠ 1`, which does not cover zeta; "the whole analytic input" omitted what `poleData` reads. | Yes. The level-one statement is at `mellinGchiModOne.lean:115-118` (the finding said 116-119) and names the zeta identity at line 191. | Section 4 quotes both entry points and replaces "whole analytic input" by a list of four inputs, marked as not a closed inventory, with the negative count that no functional-equation string occurs in the 36 files of the Landau directory. Finding 6. |
| F3 | minor | "Single analytic interface" too strong; section 3 read `EAtH` as tying the level to a host only. | Yes: `core_gm` has two hypotheses; `EAtH` has the fields `bdG` and `bdL`; `CoreAtH` has the conjunct `ThinScales`. | Section 3 retitled and rewritten; "no second route" recorded with its evidence (`EveryCharacter` is the stated type of eight theorems, `ZeroFreeAll` of three); 10.5 (b) quotes `PairGood` and `PairEx` and names `boundedTw`; question 3 answered in part. Finding 4. |
| F4 | minor | "Every other theorem in the ledger ignores `O`". | Yes, by `ledger_count.py`: 4 read a field, 39 pass `O` on, 152 do not mention it. | S4 gives the table; section 8 echo corrected. Finding 16. |
| F5 | minor | B9 said the live chain does not use `ZetaLandau`; the twin plug's consumer was not mentioned. | Yes: `zetaLandau` is applied at two sites and a theorem of the resulting name inside `chain_epsilon_half_plane`; `plugAll` is named only by `everyE₂`. | B9 withdrawn and hedged with the sites; S6 and questions 10 and 11. |
| F6 | minor | The audit list of 10.2 was incomplete. | Yes: the `run_tac` assignment at `ExistsGIs.lean:81-83`, the macros `kq%` and `kd%`, the `#print axioms` and `#check` lines, the `positivity` extension. | 10.2 rewritten with a table, the third site quoted, and the sentence that the list is of what was found; question 18. Finding 14. |
| F7 | minor | Three readings rested on a name or a letter. | Yes, all three. | Item 14 now quotes the definition `BoundAtTwoThree`; item 8 is graded "Q, in shape" and says which two links are name-based; `ArithData` is quoted and its reading says the record is abstract. Section 0 no longer says that no reading rests on a name. |
| F8 | minor | The rival paragraph was graded T though it is the lab's own unchecked mathematics. | Yes, by reading the paragraph. | New label R; ATLAS section 4 says the paragraph carries neither grade; question 17. The reviewer's hand re-derivation of the coefficient remark of S10 is recorded there. Finding 7. |
| F9 | minor | "The archive contains no trace of" the function-field toy. | The overstatement, yes. The absence itself survived the reviewer's further searches, which the builder did not re-run and which are attributed. | Section 6 says "not located under any notation searched" and lists the searches and who ran them; `gauss_core`, the reader's item Z1 dropped by the first version, is restored; question 15 reworded. The reviewer's 17 files for "zeroMode" are the files of one directory outside import lines; over the tree the recount finds 30 in any letter case. |
| N1 | major | The same sentence as F4, with the further count that 13 theorems depend on a field transitively, the consumed one among them. | Yes, exactly: 13, listed by name in `stats.json`. | As F4. |
| N2 | major | "`kexactB` in 50 files" under-sized the audit target: macro use sites were not counted. | Yes, exactly: 469 lines in 72 files; by token 234/50, `kc%` 182/32, `kq%` 3/2, `kd%` 1/1, `tr_via` 49/8, `tr_clause` 22/5; `run_tac` on 32 lines in 16 files. The reviewer's 400, 49, 22 and 7 are occurrences; the recount counts lines. | 10.2 gives both figures in a table; `recount.py` counts tokens by line; finding 14. |
| N3 | major | The tests guarded far less than `RUNS.md` and the test names said: zero counts, string counts, closures and the ledger were pinned by nothing; seven mutants survived. | Yes, by reading the test file. | `build_stats.py` and `reader_values.json` are committed and are the only writers of `stats.json`; with the archive the test reruns the recount with the recorded arguments, the ledger count and the build, and compares every field; without it the prose is checked against the table by more than 120 sentences and rows built from `stats.json`, with the reviewer's seven mutants and a dozen more planted and seen; the wording check is widened and planted, and is described as what it is, a tripwire that a hedged sentence passes; `recount.py` and `ledger_count.py` have fixture tests. `RUNS.md` corrected. Still unguarded: the readings, and the hand-read items listed in ATLAS section 12. |
| N4 | minor | Two disagreements with the reader were "not reconciled"; the tally 22 of 25 double-counted a figure. | Yes, exactly: 8,199 with `scoped` and `local` instances; 11,594 in bytes. | Section 7 and the paragraph above; each disagreement in `stats.json` is followed by the row that reconciles it. |
| N5 | minor | 445 and 181 Props are one rule's answer; a wider rule gives 467 and 191. | Yes, exactly, with the wider rule now in `recount.py`; the 445 are a subset of the 467. | Section 9 gives three rules and a range. Finding 13. |
| N6 | minor | Numbers in the atlas with no replay path; two table columns were the reader's. | Yes. | `recount.py` gained `--dirs`, `--words` and `--decl-names`, and `ledger_count.py` was added; the depth-3 row and the two columns are recomputed and agree; section 12 lists what is still read by hand. |
| N7 | minor | Adjacent quotes reproduced two files in full. | Yes: `Statements.lean` 11 of 11 content lines, `Main.lean` 5 of 5, `MainTheorems.lean` 7 of 8. | `Statements.lean` is now 5 of 11 and `MainTheorems.lean` 2 of 8, with the rest described and pointed to. `Main.lean` stays whole: its five one-line theorems are the claim, and `MISSION.md` says so. `quotes.json` records coverage per file and a test pins the closed list of five files more than half shown. |
| N8 | minor | An absolute machine path in `RUNS.md`. | Yes. | Removed; a test forbids such paths in the documents and tables here. |
| N9 | minor | The shared case-log test fails and the headline did not say so; the hunt number is not in the case log. | Yes. | Not fixable here: `hunts/README.md` is shared. It is now in the headline of this file, and `MISSION.md` marks the number #160 as provisional until the case-log entry lands. |
| N10 | minor | Three citations whose lines do not carry the reading. | Yes. | (a) as F7; (b) `gapA` is quoted and "`ASK ≤ MAIN + error`" is explained as a bound on a double sum; (c) `PageN` is displayed, and a test requires a displayed quote for every item graded Q. |
| N11 | minor | Text facts missing from 10.2. | Yes for `#print axioms` (4), `#check` (2), `allowUnsafeReducibility` (37 in 33 files, the only place the letters "unsafe" occur) and `partial def` (2). | Added to 10.2 and to `stats.json`. Not re-measured, and so not in the atlas: the reviewer's counts of "axiom" and "admit" as substrings, and what the `open private` lines open. |
| N12 | minor | "86 contain a Statement file" counts anywhere below; 106 excludes `ThetaLocalInputs`. | Yes: 82 directly inside; 40 structures named Input; 256 defs named Hypothes. | Section 7 gives both figures; 10.3 calls 106 a lower bound. |

One more defect was found by the new guard and by no reviewer. On its first
full run with the archive, the test that rebuilds `stats.json` from a fresh
recount failed in one field: the list of the twelve largest directories of
each import closure. The module and line counts of the closures were equal;
the list broke ties by set order, which changes from one Python process to
the next, so two runs could keep different directories at the cut. The
first version had the same defect and no test that could see it.
`recount.py` now breaks ties by name. No number printed in the atlas was
affected.

The repair was cut off once by a usage limit and finished by a second pass
the same day. That pass re-checked every row above against the files and
against the reviewers' reports, reran `verify_quotes.py` against the archive
(238 citations, all matching) and the full archive-gated tests, recount
included. It found two places the first repair pass had missed and fixed
them:

- F9: the timeline table of ATLAS section 6 still said "Not in the archive"
  in the row for item 3, beside the corrected finding below the table. The
  row now says "not located under any notation searched" and points to the
  searches and to `gauss_core`.
- F7 and N10: item 8 kept two links that rest on a letter or a name, and
  items 7, 10, 13, 15 and 16 lean on names for the link to the note. They
  keep their stated grades (A and N say "by area" and "by name"), and every
  name-resting link is now also an open question (ATLAS question 19), so
  that no reading stands on a name without being marked open.
- The tie-break fix of the next paragraph had been made in `recount.py`
  but `stats.json` had not been rebuilt with it when the first pass was
  cut off, so the archive-gated test of the whole table failed in
  `import_closures`. The table was rebuilt from a fresh recount; only
  directories tied at the cut of four closure lists changed, no module or
  line count did, and a second fresh recount in a new process then matched
  it in every field.

What the reviews confirmed and this revision did not change: all 168
citations of the first version replayed, and one reviewer compared every
displayed block byte for byte with a second parser; the whole-tree
statistics reproduced under two independent scanners; the spine S1 to S11
was re-read link by link and stands; the thirteen Prop names occur once; the
joined tarball hash was recomputed from the 14 parts by a reviewer and
equals the recorded value.

## Replay

    python -I hunts/rh_claim_atlas/verify_quotes.py PATH/lean/src --mathlib PATH_TO_MATHLIB_v4.33.1
    python -I hunts/rh_claim_atlas/recount.py PATH/lean/src --out recount.json (arguments: stats.json, recount_arguments)
    python -I hunts/rh_claim_atlas/ledger_count.py PATH/lean/src --out ledger.json
    python -I hunts/rh_claim_atlas/build_stats.py recount.json ledger.json --check

The first checks every citation in under a second and exits non-zero on any
mismatch. The other three recount the tree in four to five minutes on one core
and exit non-zero if `stats.json` is not what they give. `RUNS.md` has the
runs behind this page.
