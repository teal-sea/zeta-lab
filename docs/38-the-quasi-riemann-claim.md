# 38. The quasi-Riemann claim: OpenAI's 7/8 half-plane, read against this tree

**7 October 2026.** On 2026-10-06 OpenAI published `github.com/openai/math`
(Apache-2.0, one commit, `adc7f1241b42e322a6451854ab7e4b4c146bf78a`): 722
manuscripts in 372 result families produced by an unreleased internal model,
with a Lean library and 405 Comparator challenge statements. Family 003 claims
that every Dirichlet L-function, including zeta, has no zero with real part
above 7/8, uniformly in modulus and character. That is a fixed zero-free strip
of the exact kind `docs/08` section 1.1 names as a research target and as the
thing the classical regions do not give. This document records what the claim
is, what its formal statements pin, what was checked here, what was not, what
it would change in this tree if it survives a replay, and what a replay needs.

The short version: the four Lean statements say what the paper says, against
Mathlib's own `riemannZeta` and `DirichletCharacter.LFunction`, with no extra
hypothesis. A regex scan of the complete import closure of the proof modules
finds no `sorry`, no axiom declaration and no unsafe tactic, including inside
the one third-party dependency that carries two `sorry`s upstream, because
OpenAI's patch deletes them. **On 2026-10-08 this laboratory replayed the
build on its own default compute** (section 7): Lean 4.34.1's kernel accepted
the zeta, Dirichlet and Siegel-zero statements, and `#print axioms` on each
returned exactly `propext`, `Classical.choice`, `Quot.sound`. On this tree's
ladder (`AGENTS.md`) that is *kernel-checked*, on one kernel: the formal
statement `riemannZeta s ≠ 0` for `7/8 < s.re`, against Mathlib's own
`riemannZeta`, is a theorem of Lean 4.34.1 with Mathlib `d13f23b7` and OpenAI's
patched dependencies, rebuilt from the pinned commit by someone other than its
producer. What it is not: checked by a second kernel (the NanoDa run is
section 7's open item), reviewed by any person (the 195-page argument remains
unread past its third section), or a statement about RH (7/8 is not 1/2, and
the paper says so). `docs/08` section 1.1 is updated accordingly.

---

## 1. What was released

Measured from the clone on 2026-10-07; commands and raw output are in the
companion record (section 9).

| Item | Count |
| --- | --- |
| Preprint directories | 722 |
| Result families (`overview.tex`) | 372 |
| Families with a `lean/docs/NNN.md` scope page | 235 |
| Papers in `lean/formalization.yaml` (a formalized main result) | 162 |
| Comparator challenge files (`.lean` / `.json`) | 405 / 405 |
| Challenge configs with the second kernel (NanoDa) enabled | 1 of 405 |
| `.lean` files under `lean/OAI/` | 121,734 (1.7 GB of source) |
| Third-party Lean dependencies carrying an OpenAI "compatibility patch" | 23 patches, 160,187 patch lines |
| Reasoning summaries released | 10 families; 003 is not one of them |

Two press figures that look contradictory are both right: 162 is the number of
papers in the formalization catalogue, 235 is the number of families with a
Lean scope page.

The README states the procedure: one unreleased model, about 4,000 problems
posed, an average of three hours of ChatGPT Pro compute per result, and then
"aggregating the output into result families and manuscripts and requiring an
appropriate level of significance". It names two exceptions to that fixed
procedure, and the zero-free region for zeta is one of them. It also says the
write-up of the 11/12 region "was human edited for readability", and the
October 5 preprint's own README says "This paper was written with human
assistance". It warns that "some of the unformalized results could have
issues".

Toolchain: `leanprover/lean4:v4.34.1`, Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. This tree's Lean arm is on
`v4.35.0-rc2` with a different Mathlib pin, so a replay is a separate
checkout, not an addition to `lean/`.

## 2. The claim

Three preprints make up family 003:

| Preprint | Date | Statement |
| --- | --- | --- |
| *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8* | 2026-09-30 | Theorem 1.1: every finite-order Hecke L-function over Q(sqrt(-3)) has no zero in Re s > 7/8; the same for every Dirichlet L-function including zeta, a pole at s = 1 allowed. Table of contents runs to page 194 |
| *The Quasi-Riemann Hypothesis* (alternate 11/12 proof) | 2026-10-05 | Theorem 1.1: the same families have no zero in Re s > 11/12. Written with human assistance. About 45 pages |
| *Uniform exclusion of Landau-Siegel zeros* | 2026-10-01 | Theorem 1: an absolute c > 0 with (1 - beta) log q >= c for every real zero beta in (0, 1) of every primitive nonprincipal real Dirichlet L-function of conductor q >= 3 |

The paper is explicit about scope: "The theorem does not establish the Riemann
hypothesis or its generalized versions, which place nontrivial zeros on
Re s = 1/2. The Riemann hypothesis remains open."

**The mechanism, as the paper describes itself.** The analytic object is not
zeta but the family of finite-order Hecke characters of F = Q(sqrt(-3)); zeta
and the Dirichlet L-functions are reached at the end by composing a Dirichlet
character with the ideal norm and factoring L(s, chi) L(s, chi chi_{-3}) off
finitely many Euler factors. Section 2 proves a "continuation from a common
signal" criterion (Proposition 2.1): a smoothed character sum against the
Fourier coefficients of Patterson's cubic theta function on Kubota's
metaplectic cover is bounded directly and also compared with a Mellin integral
containing 1/L_F(s, eta); a power saving in both comparisons continues the
reciprocal past the rightmost hypothetical zero, contradiction. Part I runs
the criterion at 11/12 with the balanced normalisation C(s) = s - 2/3 using
cubic-theta reflection, Poisson summation and a "sextic large sieve". Part II
runs it at 7/8 with C(s) = s - 11/16, adding prime compensation, asymmetric
scales and two moment estimates for the Dirichlet polynomials the zero
detector produces. The inputs it names are Dunn and Radziwill's unconditional
cusp expansions, Goldmakher and Louvel's quadratic Hecke-family estimate,
Blomer, Goldmakher and Louvel's norm recursion, Heath-Brown's cubic large
sieve, the Hecke functional equation and prime counting in a fixed ray class.
None of that has been checked here beyond reading sections 1 to 3.

**Consequences the papers draw.** Vinogradov's least-quadratic-nonresidue
conjecture (n(p) <= C (log p)^A, with A = 32 quoted from Bhargava, Ivanyos,
Mittal and Saxena), hence deterministic square roots modulo p in polynomial
time; from the 11/12 paper, pi(x; q, a) with error O(x^{11/12} log x)
uniformly in q <= x, an effective h(D) >> sqrt|D| / log log |D|, and the
completeness of Euler's list of 65 idoneal numbers. The Lean scope page says
"the paper's later applications are not included" in the formalization.

## 3. The formal statements

`lean/docs/003.md` lists four Comparator challenge files. The theorem
signatures, verbatim from the clone (each challenge body is `sorry` by design;
the solution module named in the `.json` is what Comparator checks against it):

```lean
-- ComparatorChallenges/QuasiRiemannHypothesis.lean
theorem riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0

-- ComparatorChallenges/DirichletSevenEighths.lean
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0

-- ComparatorChallenges/SiegelZeros.lean
theorem exists_absolute_real_zero_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ)
```

What these pin, and what they do not:

- **Zeta and Dirichlet use Mathlib's definitions.** `riemannZeta` and
  `DirichletCharacter.LFunction` are Mathlib's, so the statement-matches-claim
  question that `docs/32` and the Palomar arm exist to ask has a clean answer
  for these two: the formal statement is the informal one, with no hidden
  hypothesis. Mathlib's `riemannZeta` is total, so no pole clause is needed
  for zeta; the Dirichlet statement excludes only the principal pole.
- **The Hecke statement is built on definitions the challenge file itself
  supplies.** `HeckeSevenEighths.lean` defines a `WeakFEPair`-based lattice
  theta sum, a `Character` structure, and `LFunction χ s := continuedLattice χ s / 6`,
  then states nonvanishing for that object. Comparator does pin those
  definitions: its source (`leanprover/comparator` at `ca04cfc7`,
  `Comparator/Compare.lean`) requires every constant in a pinned theorem's
  type, transitively, to be identical between challenge and solution up to
  alpha equivalence, and only names listed in `definition_names` are exempt
  (this file lists none). What no tool in the release checks is whether that
  challenge-file text is the finite-order Hecke L-function of the paper. The
  only bridge is the 136-word scope page. *(Corrected 2026-10-08: the first
  version of this bullet said Comparator "does not pin" the definitions. It
  pins them to the challenge text; the gap is between that text and the
  mathematics, not inside the tool. Section 9 has the release-wide count.)*
- **The Siegel statement is proved independently of the 7/8 module.** Its
  solution module `OAI.NumberTheory.SiegelZeros.Main` does not import
  `OAI.NumberTheory.DirichletL.Nonvanishing`. The two are separate arguments.
  (The 7/8 statement would imply the Siegel one with c = (log 3)/8, so a
  replay of the Dirichlet statement alone covers both conclusions.)
- **Permitted axioms** in all four configs are exactly `propext`,
  `Classical.choice`, `Quot.sound`. **`enable_nanoda` is `false` in all
  four.** The independent second kernel that Palomar ran on this tree's
  submissions (`docs/32`) is off for family 003 in OpenAI's own configuration.
  One challenge in 405 enables it, and it is not this one.

## 4. What was checked here, and how

A breadth-first walk over `import` lines from each solution module, followed
by regex scans of every file in the closure. Scripts and output are in the
companion record. The grade of this check is **a text scan**: it can find a
`sorry` or an `axiom` that is there; it cannot find a proof that does not
compile, a definition that means the wrong thing, or a kernel bug.

| Solution module | OAI modules in closure | Source | Outside Mathlib | `sorry` / `axiom` / `native_decide` / `implemented_by` / `extern` / `unsafe` / `opaque` |
| --- | --- | --- | --- | --- |
| `OAI.NumberTheory.DirichletL.Nonvanishing` (zeta, Dirichlet) | 2,924 | 25.0 MB | `PrimeNumberTheoremAnd.Wiener`, `RellichKondrachov...Rellich` | 0 / 0 / 0 / 0 / 0 / 0 / 0 |
| `OAI.NumberTheory.DirichletL.Hecke.Nonvanishing` | 2,925 | 25.0 MB | same | all 0 |
| `OAI.NumberTheory.SiegelZeros.Main` | 306 | 3.1 MB | `PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport` | all 0 |

Across the whole `lean/OAI/` library: zero files contain the word `sorry`, and
zero lines declare an `axiom` (four lines match the word, all inside doc
comments).

**The third-party dependency is where the record gets interesting.** The
lakefile pins `AlexKontorovich/PrimeNumberTheoremAnd` (PNT+) at
`c39a751132c88b6e8080b74c74023fd95b3d8be0` (2026-10-01, "Bump to V4.34.0") and
applies `patches/PrimeNumberTheoremAnd-lean4341.patch` to it at `lake update`.
At that upstream commit:

- `PrimeNumberTheoremAnd/Wiener.lean`, which the 7/8 closure imports, contains
  two `by sorry` theorems, `prelim_decay_2` (line 327) and `prelim_decay_3`
  (line 347);
- `PrimeNumberTheoremAnd/SiegelZeros/`, which the Siegel closure imports, does
  not exist.

The patch is 39,904 lines. It deletes both sorried theorems and the `decay_alt`
lemma that used them, adds 47 new `.lean` files (+31,002 / -3,075 lines)
including the whole `SiegelZeros/` directory, and bumps the toolchain. Its
`SiegelZeros/NOTICE.md` credits the support to PNT+ and retains copyright
notices for Matteo Cipollina and Stefan Kebekus. Applied here with `git apply`
(clean, 226 whitespace warnings), the result is:

| PNT+ module, after patch | Modules in closure | `sorry` |
| --- | --- | --- |
| `PrimeNumberTheoremAnd.Wiener` | 4 | 0 |
| `PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport` | 12 | 0 |

Thirty-two files in the patched PNT+ tree still contain `sorry`; thirty are
under `IEANTN/` and two elsewhere, and none is in either closure. The
`rellich-kondrachov` dependency at its pin has a 15-module closure with no
`sorry`.

So the honest sentence is: **at text level, the complete import closure of the
7/8 proof is sorry-free and axiom-free only after a 31,000-line patch to a
third-party library is applied**, and `formalization.yaml` records that
dependency as `builds-on`. That is not an accusation; the patch is published,
pinned and applied by the build. It is the kind of fact a replay has to be
told about, and the kind that `docs/20` says to write down before the
headline.

## 5. What was not checked

- **A second kernel.** The 2026-10-08 replay (section 7) is Lean's own
  kernel on this laboratory's runner. NanoDa, the independent kernel Palomar
  ran on this tree's submissions (`docs/32`), has not yet accepted these
  proofs; OpenAI's configs leave it off, and the workflow's comparator mode
  that turns it on is experimental and recorded in section 7 when it lands.
- **The Hecke statement.** `OAI.NumberTheory.DirichletL.Hecke.Nonvanishing`
  was not built; the replay built the zeta, Dirichlet and Siegel modules only.
- **Correspondence between a challenge file's own definitions and the
  paper's object**, for the Hecke statement here and for 387 of the 405
  challenges in the release (sections 3 and 9). The zeta, Dirichlet and
  Siegel statements are among the nine challenges that need no such
  definitions at all.
- **The argument itself.** Sections 1 to 3 of the 7/8 paper were read; the
  remaining 180 pages were not. No one here has an opinion on whether
  Proposition 2.1's two power savings are actually established in Parts I
  and II.
- **Novelty.** Not searched. The paper's own prior-art section cites the
  classical regions, Guth and Maynard, and the Chowla-style inputs; nobody
  here has checked that the 11/12 or 7/8 bound is absent from the literature,
  and nobody expects it to be present.
- **The other 371 families** were read only as titles and abstracts
  (section 8).

## 6. What it would change in this tree, if it survives

Conditional on a replay, and written now so the consequences are priced before
the fact rather than after.

- **`docs/08` section 1.1** would become history in its first paragraph: the
  distinction between a shrinking region and a fixed strip would no longer be
  the frontier, and the sentence "a new estimate that would imply a fixed
  zero-free strip can be a research target" would have a citation. Its
  closing rule, that a strip is not RH, is untouched: 7/8 is not 1/2, and the
  paper says so itself.
- **The registered and candidate simple-zero proportions** (`README.md`,
  `hunts/four_point_pressure/`) take no zero-free strip as input. Nothing
  moves.
- **The de Bruijn-Newman record does not move.** In the normalisation of
  `docs/05`, where de Bruijn's strip bound reads Lambda <= Delta^2 / 2 with
  Delta = 1 giving 1/2, a zero-free half-plane Re s > 7/8 puts every zero of
  H_0 in |Im z| < 3/4 and gives Lambda <= 9/32 = 0.28125. The Platt-Trudgian
  record is 0.2. (The Delta^2 / 2 step is de Bruijn 1950, Theorem 13, as
  cited in `docs/37`; the arithmetic here is the only thing added.)
- **Davenport-Heilbronn** (`docs/29`, `hunts/lambda_dh_bounds/`) is a linear
  combination of two L-functions, not an L-function with an Euler product.
  The claim says nothing about it in either direction, and its off-line zeros
  are consistent with each constituent L-function being zero-free past 7/8.
- **`hunts/prime_pair_error/`** is the one place a fixed strip is an input the
  tree has already priced. `SW_EFFECTIVE.md` observes that the q = 1
  component of `UPPER_BOUND.md` (1) rests on the classical de la Vallee
  Poussin remainder; a fixed strip would replace that remainder by a power
  saving. Whether a saving of x^{1/8} moves that component, which the hunt
  records as "a full power of N short of (31)", is a re-pricing question for
  whoever next opens the hunt. It is not answered here.
- **PR #268's equivalence** (RH iff Re(xi'/xi) > 0 on Re s > 1/2) and its
  finite Li positivity are untouched; both are statements at 1/2.
- **Two numbering coincidences, killed before they grow.** OpenAI family 126
  ("Exponential semidefinite complexity of perfect matching") has nothing to
  do with Erdos problem #126, which hunts #91 to #107 work on. OpenAI family
  040 ("Bloch's conjecture for complex surfaces") has nothing to do with
  Bloch's constant, which hunt #80 (`bloch_ceiling/`) measures.

## 7. What a replay needs

Recorded as a recipe with its cost shape. Scheduling it is an allocation
decision (`ALIGNMENT.md` section 3), not something this document starts.

```sh
git clone --depth 1 https://github.com/openai/math && cd math/lean
# toolchain v4.34.1 via elan; then, exactly as their README says:
lake update              # fetches 24 git dependencies, applies the 23 patches
lake exe cache get       # Mathlib oleans at d13f23b7
lake build OAI.NumberTheory.DirichletL.Nonvanishing OAI.NumberTheory.SiegelZeros.Main
lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json
lake env comparator ComparatorChallenges/DirichletSevenEighths.json
lake env comparator ComparatorChallenges/SiegelZeros.json
```

**The unit, timed (2026-10-08).** The workflow
`.github/workflows/replay-openai-003.yml` on branch `claude/replay-003-workflow`
ran its pilot on a four-core `ubuntu-24.04` runner (run 37723649679): `lake
update` fetched the 24 dependencies and applied all 23 patches in 3m14s
(PNT+ at `c39a7511` with the patch applied, `prelim_decay_2` gone,
`SiegelZeros/HadamardSupport.lean` present); `lake exe cache get` brought
6.7 GB of Mathlib oleans in 18 s with 95 GB of disk left; and three leaf
modules of the 7/8 closure, which import Mathlib only, elaborated in

| module | source | elaboration | wall incl. Lake | peak RSS |
| --- | --- | --- | --- | --- |
| `DirichletL.Detector.Euler` | 1.4 KB | 1.9 s | 4.4 s | 2.5 GB |
| `DirichletL.Descent.Marks` | 4 KB | 1.9 s | 4.5 s | 2.5 GB |
| `DirichletL.Arithmetic.EisensteinCoordinates` | 30 KB | 5.2 s | 8.3 s | 4.2 GB |

with every Mathlib job reported up to date and no `sorry` warning. Lake 4.34.1
rejected `-j` and its `build --help` lists no `--jobs`, so the build runs at
Lake's default parallelism (four on this runner). Multiplying the measured
rate, about 0.2 s per KB on shallow leaves, over the 25 MB closure gives
roughly 70 CPU-minutes; allowing a factor five for deeper modules with heavier
tactics gives about six CPU-hours, or one to two hours of wall time at four
jobs. That is an estimate from three shallow leaves, not a measurement of the
closure, and the peak RSS of 4.2 GB on one module makes memory, not time, the
likelier failure at four jobs on a 16 GB runner. Build mode was dispatched the
same day with a 300-minute timeout.

**The build, landed (2026-10-08, run 37725739710, job 113143362584).**
`lake build OAI.NumberTheory.DirichletL.Nonvanishing OAI.NumberTheory.SiegelZeros.Main`
on the same four-core runner at Lake's default parallelism ran from 04:09:27Z
to 06:24:37Z, 2 h 15 min of wall time, and ended `Build completed successfully
(12186 jobs)` with no `declaration uses 'sorry'` warning in the log; the
estimate above was right about the order of magnitude and wrong about the
likelier failure, since memory never bound. The saved OAI build outputs are
1.01 GB. Then, from a file importing the two built modules:

```
'OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Three lines, no `sorryAx`, nothing outside the standard three; the guard that
fails on any other outcome passed. `#print axioms` walks every constant the
proof uses, transitively, through the patched PrimeNumberTheoremAnd modules
and Mathlib alike, so the axiom set covers the whole dependency chain this
runner compiled. The evidence (run record, update log, cache log, build log,
axioms) is the artifact `replay-openai-003-build-37725739710` on the run.

What this establishes, in this tree's words: the three statements of
section 3 are theorems of Lean 4.34.1 with Mathlib `d13f23b7` and the patched
dependencies, rebuilt from the pinned public commit by this laboratory. On the
ladder that is *kernel-checked*. The composite takes the grade of its weakest
step, and the weakest step is now the trust in one kernel and in Mathlib's
`riemannZeta` meaning what its name says, which is the same trust every
registered result in this tree rests on. Open: the second kernel (comparator
mode, dispatched after the build; experimental), the Hecke module, and
everything a kernel cannot do, which is to say whether the mathematics is
what the paper says it is and whether it is new.
The `lean/README.md` warns that compiling the whole library can exhaust
`vm.max_map_count`; building two named modules should not. Two settings the
replay changes from OpenAI's: `enable_nanoda` set to `true` in the three
configs, and `#print axioms` run on the three theorem names directly, so the
axiom set is observed and not read from a config.

Whoever runs it should also know that `lake update` applies 160,187 lines of
patches to other people's libraries, and that the sorry-freedom of the 7/8
closure depends on one of them (section 4).

## 8. The rest of the catalogue, against this tree

The 372 family abstracts were scanned for every subject this tree works on.
No family addresses Robin's inequality (PR #270), Erdos #126 (hunts #91 to
#107), Bloch's constant (hunt #80), sphere packing or kissing numbers (issue
#110), the Erdos minimum-overlap problem (hunts #85, #86), Montgomery pair
correlation, simple zeros, the de Bruijn-Newman constant, Li's criterion,
Lehmer pairs, Mertens's constants, Hardy-Ramanujan, Erdos-Kac, the prime zeta
function or Davenport-Heilbronn. Nothing in this tree is superseded or
contradicted by a stated result in the release.

Families adjacent to the subject, listed so the next reader does not have to
rescan: 007 (ordinary two-point Chowla and the corrected Elliott conjecture,
Lean), 011 (Poisson-Dirichlet law for the prime factors of p - 1), 012
(Erdos-Pomerance joint Dickman), 013 (Ostmann's inverse Goldbach, Lean), 021
(Jacobsthal), 023 (Patterson's first moment for cubic Gauss sums, the same
objects family 003 consumes), 024 (totients), 025 (short Egyptian fractions,
Lean), 026 (positive density of large prime gaps), 029 (Artin primitive
roots). Each is a claim at the same grade as 003: stated, in some cases
formalized by its producer, replayed by nobody known here.

## 9. The rest of the verification surface, measured

The same text-level questions, asked of the whole release on 2026-10-08 with
scripts kept in the companion record. Every number is a regex count over the
clone and is reproducible from the commit; none is a kernel check.

**What Comparator pins.** Read from its source rather than assumed: for each
name in `theorem_names` it requires an identical name, universe parameters and
type in challenge and solution, then walks every constant the type uses,
transitively through types and values, and requires full `ConstantInfo`
equality up to alpha equivalence. Only `definition_names` entries ("holes")
escape value comparison; they are checked by name, type, universes and safety
level, and Comparator's README says such solutions must always be checked by
an additional, possibly human, verifier.

| Measure, over the 405 challenge files and configs | Count |
| --- | --- |
| Definition-like declarations in challenge files (`def` 8,210, `abbrev` 1,176, `instance` 596, `structure` 474, `inductive` 89, `class` 12) | 10,557 |
| Challenges carrying their own definitions, with no holes declared | 387 |
| Challenges stated purely in Mathlib or upstream terms (among them `QuasiRiemannHypothesis`, `DirichletSevenEighths`, `SiegelZeros`) | 9 |
| Challenges with declared holes / holes in total / holes that are `Prop`-valued | 9 / 45 / 17 |
| Holes written out in full in the challenge file yet exempt from value comparison | 43 of 45 |
| Challenges whose pinned theorem is, or rests directly on, a `Prop`-valued hole (`KServer`, `OccupiedOverlap`, `EuclideanFiveColor`) | 3 |
| Pinned theorem names, all resolving to a declaration in their challenge file | 507 |
| `sorry` occurrences (506 in pinned theorems, 3 inside definitions) | 509 |
| `axiom` declarations (`HarmonicGrowth`: `axiom mainStatement : MainClaim`, the stand-in instead of `sorry`) | 1 |
| Configs whose permitted axioms are not exactly the standard three | 0 |
| Configs with `enable_nanoda` true / key missing | 1 / 2 |
| Challenge files running elaboration-time metaprograms (`run_cmd Lean.modifyEnv` resetting auxiliary-lemma and matcher caches, 15; `elabCommand`, 2) | 17 |
| Families whose scope page links at least one challenge with its own definitions | 228 of 235 |

So the three statements that matter for this document sit in the nine-of-405
class that needs no challenge-side definitions, which is the strongest
position a Comparator statement can be in. The Hecke statement sits in the 387.

**What the scope pages say.** The 235 `lean/docs/NNN.md` pages run 67 to
1,122 words, median 136. Seventy-four (31.5 percent) use at least one of ten
narrowing phrases; "not included" appears on 31. Four state that the
formalized result is itself conditional on an unproved input (families 187,
260, 281 and 331). Phrase counts measure wording, not scope: several
"conditional" hits are the word "unconditional", several "assum" hits say
nothing is assumed, and 124 pages narrow in other words.

**What the patches add.** Across the 23 patches: 90,125 lines added, 34,139
removed, 111 new `.lean` files, 3,355 new `theorem`/`lemma` declarations, and
no `sorry` or `axiom` on any added line. Removed lines carry 14 `sorry`
mentions, of which two are PNT+'s `prelim_decay_2` and `prelim_decay_3`
(section 4) and one is AINTLIB's `wronskian_Φ_ΨSq_nat`, deleted with its
consumer rather than proved. All 111 new files are absent from upstream at
the pinned commit and at upstream HEAD on 2026-10-08. Twenty-seven of them
(39,928 lines, the `Erdos970/` directories in PNT+ and StrongPNT) are
namespaced forks of existing upstream modules at line-similarity 0.70 to
0.90; ClassFieldTheory's 52 new files (16,975 lines) and PNT+'s `SiegelZeros/`,
`Catalan/` and `ZetaFive/` have no upstream counterpart. Load-bearing by
import closure: 39 of PNT+'s 47 new files, 45 of ClassFieldTheory's 52, 7 of
StrongPNT's 8. Thirteen of the 23 patched dependencies are never imported by
the release's own Lean code, and AINTLIB's 23,288-line patch reaches nothing
the release imports.

**Reading.** The patches are not a trick and not padding either: a third of
their new volume is other people's modules copied under a new namespace, the
rest is new Lean that lives inside third-party repositories under the word
"compatibility", and the part of it the 7/8 and Siegel proofs stand on is
sorry-free at text level. A replay inherits all of it, which is why section 7
says `lake update` must be told about.

## 10. Sources and the companion record

- `github.com/openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
  `README.md`, `CONTENTS.md`, `overview.tex`, `lean/docs/003.md`,
  `lean/formalization.yaml`, `lean/ComparatorChallenges/{QuasiRiemannHypothesis,DirichletSevenEighths,HeckeSevenEighths,SiegelZeros}.{lean,json}`,
  `lean/lakefile.lean`, `lean/lake-manifest.json`,
  `lean/patches/PrimeNumberTheoremAnd-lean4341.patch`, and the three family
  003 preprints.
- `AlexKontorovich/PrimeNumberTheoremAnd` at `c39a7511`, and
  `abenenson/rellich-kondrachov` at `70f85d4c`, fetched shallow at those
  commits.
- The scan scripts, their full output, the 2026-10-08 release-wide audit
  (scripts, CSVs, upstream comparisons) and SHA-256 hashes of the three PDFs
  and the patch are kept in the operator's private vault under
  `raw/2026-10-07-openai-math-release/`; the numbers above are reproducible
  from the public commit with any import-walking script and the regexes
  named in section 9.
- Context, not evidence: the Advisory Group on Mathematics and Artificial
  Intelligence (hosted at the IAS) published release guidelines on 2026-09-29
  and has said its advisory role endorses neither the manuscripts nor the
  process; twenty-five Fields medalists signed a declaration on 2026-09-11
  objecting to the use of open problems as benchmarks. Both are reported from
  secondary coverage and were not read in the original here.

Related: `docs/08` section 1.1, `docs/20`, `docs/32`, `references/papers.md`
section 9.
