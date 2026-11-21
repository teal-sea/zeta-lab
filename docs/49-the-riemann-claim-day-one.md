# 49. The Riemann claim, day one: what was read, tested and built before any kernel verdict

> On 2026-11-20 Levent Alpoge posted a four-page note and a Lean 4 archive of
> 175,187 files, claiming a proof of the Riemann Hypothesis and of the
> generalized Riemann hypothesis for Dirichlet L-functions. There is no paper.
> As this page is written no kernel has finished checking the archive: this
> laboratory's replay is a separate hunt, in progress, and has no verdict.
> This page records what the laboratory did on the day while that question
> was open. It read the archive as text, tested what could be tested without
> a kernel, and built one result on the hypothesis. Nothing here says the
> claim is true, and nothing here says it is false.

> **Update, 2026-11-21.** The archive has since been checked outside this
> laboratory. A joint statement by the Lean and Mathlib communities, endorsed
> by the Lean FRO and the Mathlib Initiative and dated 2026-11-21, says that
> the library compiles, that the theorem proved is exactly Mathlib's statement
> of the Riemann Hypothesis, and that the exported proof was accepted by
> several independent checkers; it states full confidence that the proof is
> correct. A. Sutherland's verification page, as updated at 12:55 UTC that
> day, reports that all 175,187 modules compiled, that the five theorems of
> the top file rest on the three standard axioms only, that every module was
> replayed through the Lean kernel, that two independently written kernels
> accepted the full export, and that all five statements, the Dirichlet ones
> included, were matched against a challenge file importing only Mathlib. Its
> scope note agrees with section 3: Dirichlet L-functions, not Dedekind zeta
> functions or Hecke L-functions. Both pages were read by the session that
> wrote this note; neither check was rerun here, and this laboratory's own
> replay (hunt #159) had not finished when the note was written.
>
> The body of this page is left as it was written on 2026-11-20. Read "no
> kernel has finished checking" and every "if the replay passes" below as of
> that date. Nothing was regraded by this note. In particular hunt #163 still
> states its result as given its hypothesis. That hypothesis is among the
> statements now reported as checked, so the hunt's weakest step is on its
> way to being its own written proof, which no person has reviewed. How this
> laboratory words a result that rests on an outside theorem is an owner
> decision, as it was for the 7/8 theorem (`ROADMAP.md`, decision of
> 2026-10-08).

> **Decision, 2026-11-21.** The owner then directed the laboratory to build on
> the theorem, stating results that use it as "proved, given the Alpoge
> theorem", with the scope and the reversion rule set out in `ROADMAP.md`,
> "Decision: build on the Alpoge theorem (2026-11-21)".

> **This laboratory's own build, 2026-11-21, 20:07 UTC.** Hunt #159 finished
> building all 175,187 modules on hosted runners with the archive's own
> toolchain, with no failed module, and its verdict run printed, for each of
> the five theorems of the top file, a dependence on `propext`,
> `Classical.choice` and `Quot.sound` and on no other axiom. The same run
> printed the same three axioms for four interior statements this page's
> hunts rely on, among them the windowed Landau lemma of section 4. The
> record is the section "The verdict" of `hunts/alpoge_replay/RUNS.md` on
> branch `claude/bold-ramanujan-x7z42m`, which was read for this note. That
> record does not yet grade the result on this laboratory's ladder: it is one
> kernel, the kernel replay of the stored outputs was not complete, and a
> check of the axioms that runs none of the archive's commands was still
> running. So this laboratory's build now agrees with the outside checks, and
> its grade is still pending in hunt #159.

Every item below carries its own grade, and the grades are low on purpose. A
text-level reading is a reading. A finite computation is never a uniform
result. A result built on the hypothesis is conditional on the hypothesis,
which today is not a theorem. A composite claim takes the grade of its weakest
step (`AGENTS.md`).

The same exercise was done six weeks earlier for a weaker claim, a zero-free
half-plane at 7/8: [docs/38](38-the-quasi-riemann-claim.md) read it and
[docs/39](39-built-on-the-quasi-riemann-theorem.md) built on it. This page is
the counterpart of both for the claim at 1/2, written before the replay
instead of after it.

## 1. What was released

- **The note** (`alpo.ge/remark.pdf`, four pages, sha256
  `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`). It says
  the argument was found working with an AI model, that the method "easily
  extends" to the generalized hypothesis, that the author expects a further
  extension with more time, and that he chose to post Lean only. It gives a
  twenty-item timeline of the argument and no proof.
- **The archive** (fourteen parts, 239,275,554 bytes joined, sha256
  `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`):
  175,187 Lean files and 17,374,215 lines, pinned to Lean 4.33.1 and to Mathlib
  at commit `0df444a360ea`, which is Mathlib's own tag `v4.33.1`. The archive
  contains no comments at all.

Two sessions fetched the archive independently and got the same sha256.

## 2. What was done, and at what grade

| Item | What it is | Grade | Where |
| --- | --- | --- | --- |
| The replay | A sharded build of the whole archive on hosted runners, then an axiom printout, then a kernel replay of every built module on fresh runners | **in progress, no verdict** | hunt #159, `hunts/alpoge_replay/` on branch `claude/bold-ramanujan-x7z42m`; its `RUNS.md` carries the per-round table |
| The atlas | A map of the archive: the statements, the chain from the top theorem down to the last step that mentions zeros, where arithmetic enters, the note's timeline against the tree, statistics, audit targets | text-level reading, 238 citations replayable by hash; attacked by two reviewers, two sentences withdrawn | [hunt #160](../hunts/rh_claim_atlas/ATLAS.md) |
| The inequality | The one-sided prime-sum bound the archive's chain rests on, computed for zeta, for characters, for planted off-line zeros and for rival functions | measured; two extreme values enclosure-carrying; the identity behind it is published | [hunt #161](../hunts/rh_claim_interface/RESULTS.md) |
| The statements | 79 intermediate statements written in Mathlib's vocabulary, each tested by a route that needs no kernel | 10 complete enclosure-carrying covers, 15 exact on a finite domain, 54 measured; none failed | [hunt #162](../hunts/rh_claim_statements/RESULTS.md) |
| Class numbers | The complete list of imaginary quadratic fields of class number h for every h up to 5000, given GRH for the quadratic characters | candidate, pending external review; conditional on a hypothesis that is not a theorem | [hunt #163](../hunts/grh_class_number/RESULTS.md) |
| The Lean socket | A module that restates the archive's four propositions verbatim and derives, from each as a hypothesis, the forms this tree consumes | built by `lake build` in CI, zero sorry; axioms not printed | `lean/ZetaLean/RiemannClaim.lean` |
| The regrade board | What changes in this tree if the claim is accepted by a kernel | a reading, attacked once, revision unreviewed | `docs/reviews/2026-11-20-rh-claim-regrade-board.md` |

## 3. The statements

The archive's top file proves five theorems. Their statements are four
propositions in a sixteen-line file that imports only Mathlib, plus Mathlib's
own `RiemannHypothesis`:

- `RiemannHypothesis`, Mathlib's definition at the pinned tag: every zero of
  `riemannZeta` that is not a trivial zero and not the point 1 has real part
  1/2.
- `DirichletLNonvanishingRightOfHalf`: for every modulus and every Dirichlet
  character, `L(s, chi)` does not vanish for `Re s > 1/2`, the pole of the
  trivial character at 1 excepted.
- `DirichletLZerosOnLine` and its restriction to primitive characters: every
  zero in the open strip has real part 1/2.

So the claim is RH and GRH for Dirichlet L-functions. Dedekind zeta functions
and Hecke L-functions are not in it. No archive declaration redefines
`riemannZeta` or `RiemannHypothesis` (a text scan, hunt #160).

## 4. The shape of the argument, read as text

Hunt #160 read a few hundred of the files and kept only what it could quote.
Its wording is "the archive states", never "the archive proves".

- **One proposition carries everything.** All five theorems are obtained from
  one term of one proposition, the half-plane statement for every character.
  RH for zeta is the case of the trivial character modulo 1.
- **The last step that mentions zeros is a Landau lemma.** The archive states
  a windowed, one-sided form of Landau's theorem: if a positive combination
  `Gm` of smoothed von Mangoldt sums satisfies `Gm(y) <= C y^theta` on windows
  `[Y, Y^(1 + delta)]` for arbitrarily large `Y`, then no L-function of the
  family has a zero with `Re s > theta`. Its import closure inside the archive
  is 28 modules and 2,396 lines, in Mathlib vocabulary. That makes it the
  natural first target for an independent check, and this page claims no such
  check.
- **Everything else supplies one inequality.** The rest of the archive is
  stated to produce that upper bound for every `theta` above 1/2. The theorem
  that supplies it takes two hypotheses that are themselves analytic. One of
  them is a bound of the same strength for auxiliary characters at one scale.
  How it is supplied was not traced, and it is where a reader should look
  first.
- **Where arithmetic enters.** The Euler product enters the Landau step through
  two Mathlib identities for the logarithmic derivative, one for nontrivial
  characters and a different one for zeta. On the other side the character is
  realised on a subfield of a cyclotomic field.
- **Two sentences of the first reading were wrong.** The first version said
  the functional equation is used only to reflect zeros, and that the Euler
  product enters through a single identity. Reviewers found archive text
  contradicting both: a second chain calls the functional equation, and zeta
  uses its own identity. Both sentences are withdrawn in place in the hunt.
- **The note's toy is not in the archive.** The function-field warm-up the note
  describes was not located under any notation searched. Several directory
  names mislead: `Development/WeilBound` holds the Weil representation, not
  Weil's bound for curves.
- **Rivals.** The Davenport-Heilbronn function and Epstein zeta functions of
  class number above one fail hypotheses of the Landau step, because the
  coefficients of their logarithmic derivatives are not supported on prime
  powers. This is the laboratory's own reading. A rival that fails a
  hypothesis excludes nothing about the argument (`docs/08` section 4).

## 5. The inequality, measured

For zeta the combination is one function,

    G(y) = sum_{n <= y} Lambda(n) (y/n - 1) - y log y + (1 + gamma) y.

For `y >= 1`,

    G(y) = sum_rho y^rho / (rho (1 - rho)) + log(2 pi) + T(y),

with `T` a bounded explicit term. This identity is Lemma 2.1 of O. Ramare's
corrigendum (Acta Arith. 211 (2023), 93 to 96), multiplied by `y`. It is not
new. The first version of hunt #161 missed the corrigendum and presented the
sign as its own finding; a reviewer caught it and the wording is withdrawn.

Under RH every `rho (1 - rho)` is a positive real number, so
`|G(y) - log 2pi - T(y)| <= c0 sqrt(y)` with
`c0 = 2 + gamma - log 4pi = 0.0461914...`. What hunt #161 measured:

- Over `2 <= y <= 10^9` the normalised quantity stays between `-0.4910 c0` and
  `+0.5346 c0`. The scan is float grade. The two extreme values are enclosed
  in Arb at two precisions.
- For the 35 character levels of conductor at most 20 the same quantity stays
  within 0.7180 of the envelope GRH predicts, up to `10^7`. One character
  modulo 19 comes much closer to its own envelope because its L-function has a
  zero at height about `-0.019`, which a second route confirmed.
- **The scan cannot test RH.** Ramare's 2013 theorem already gives
  `G(y) <= sqrt(y)` unconditionally on `[8950, 8.2 * 10^22]` (read, not
  re-proved here), and a planted off-line zero at the verified height
  `3 * 10^12` would first act near `10^49`. A scan to `10^9` tests the
  transcription and the instrument, and nothing else.
- The rival functions' smoothed sums grow at the exponents of their known
  off-line zeros (measured 0.808 against 0.80852 for Davenport-Heilbronn).
  Within reach the inequality does not separate zeta from Davenport-Heilbronn.

## 6. Seventy-nine statements, tested

A statement that is false as Lean reads it cannot be accepted by a kernel, so
the archive's statements in plain Mathlib vocabulary are cheap refutation
targets. Hunt #162 transcribed 79 of them with Lean's conventions written out
and tested each by exact arithmetic or Arb ball arithmetic. None failed. Each
test also had to reject a mutant of its statement, and all 98 mutants were
rejected.

What that is worth is limited, and the hunt says so. Every one of the 79 is a
classical fact or a finite computation. Seventeen of the 68 that are not
explicit primes have constants loose by a factor of 2 or more. The tightest is
`pi(m) log m < 1.26 m` below `2^17`, whose true maximum is 1.2550587 at
`m = 113`. Survival says nothing about the main claim: the archive's strength
enters through layers of defined propositions that this hunt did not read.

## 7. Built on the hypothesis: class numbers to 5000

Hunt #163 reran the class-number argument of
[docs/39](39-built-on-the-quasi-riemann-theorem.md) at abscissa 1/2.

**Given GRH for the real primitive characters, the imaginary quadratic fields
of class number h are listed completely for every h up to 5000: 102,746,940
fields, the largest with discriminant -6,912,348,787 (h = 4967).** The
hypothesis is needed only for discriminants above 16,396,235,837, because the
search below that bound is exact and reads no GRH.

- **The delta.** The published frontier is Garcia, Grenie, Lee and Molteni
  (arXiv:2610.14257, 9 October 2026): every h up to 2000 under GRH. For h up
  to 2000 this list equals theirs, their table and their per-field file. The
  new part is `2000 < h <= 5000`, which holds 86,293,447 fields. Whether their
  list also rests on a further GRH, through PARI's class-group routine, is
  unresolved here.
- **The weak points.** The hypothesis is not a theorem. The written proof is
  the sibling hunt's, audited line by line at 1/2 and reviewed by no person.
  For even h above 2000 no outside table exists, so the control is an
  independent full-range sweep that shares no code with the search. It is a
  detector, not a proof, and found nothing missing or wrong.
- **Not the best route.** A reviewer measured a different classical route as 7
  to 16 percent stronger in `L(1, chi)`, at float grade. It is recorded as the
  hunt's first door and not adopted.

This result is a GRH-conditional theorem candidate whatever happens to the
archive. If the archive is accepted by a kernel, the hypothesis is discharged
and the written proof becomes the weakest step.
*Updated 2026-11-21:* the result is now stated as proved, given the Alpoge
theorem, whose third verified statement contains the hypothesis for every
chi_D (through the routine bridge from chi_D to Mathlib's L-function, not yet written here); its weakest step is the written proof, reviewed by no person, so it
stays a candidate pending external review (`ROADMAP.md`, decision of
2026-11-21; `hunts/grh_class_number/RESULTS.md`, update at the top).

## 8. The Lean socket

`lean/ZetaLean/RiemannClaim.lean` restates the archive's four propositions
verbatim, as definitions, and asserts none of them. From each, as an explicit
hypothesis, it derives:

- that the archive's zeta statement is Mathlib's `RiemannHypothesis`, by
  definitional unfolding;
- the 7/8 half-plane in exactly the shape `lean/qrh` consumes from the
  quasi-Riemann theorem, so results stated against 7/8 can be restated against
  the claim by one application;
- nonvanishing of `riemannZeta` to the right of 1/2, from either hypothesis;
- that under `RiemannHypothesis` every zero of zeta with positive real part is
  `1/2 + i t` with `t` a zero of the laboratory's Hardy function `hardyZ`.

The module was written and reviewed by reading Mathlib's source at the arm's
pin, with no compiler. The root build then accepted it unchanged: the `lean`
job of `full.yml`, run 44786911196, at commit `a00d7e68`, with the arm's sorry
scan green. `#print axioms` was not run on its theorems, so "standard axioms
only" is read off the source and not printed. The archive is pinned to Lean
4.33.1 and this arm to a later toolchain, so discharging the hypotheses is a
porting step that has not been taken.

## 9. What it would change in this tree

`docs/reviews/2026-11-20-rh-claim-regrade-board.md` classifies 79 groups of
this tree's claims by what happens to them if the replay passes. Nothing is
regraded by it. In short:

- The five results of [docs/39](39-built-on-the-quasi-riemann-theorem.md)
  would be overtaken by results already in print under RH or GRH. For the
  class-number lists that rests on the unresolved point in section 7.
- The de Bruijn-Newman constant would become 0, given Rodgers and Tao's lower
  bound. The criteria in `zeta/criteria.py`, `zeta/li.py` and `zeta/weil.py`
  would stop testing a conjecture and start checking a theorem, so that a
  measured violation is a bug.
- The rivals stand untouched. The kernel-checked Davenport-Heilbronn zero
  ([docs/47](47-the-davenport-heilbronn-zero.md)) and the kernel-checked
  count and simplicity of the zeros to height 100
  ([docs/45](45-rh-to-height-fifty.md)) do not depend on the claim.
- Simplicity of the zeros, their spacing, moments beyond upper bounds and the
  next family of L-functions stay open under the claim.

**Corrections owed to the public record whatever happens to the claim.** These
were found on the day and are not applied by this change:

1. The class-number comparison in the front door, in
   [docs/39](39-built-on-the-quasi-riemann-theorem.md) and in five other files
   names Cremona and Sutherland (h up to 1000 under GRH) and does not cite
   Garcia, Grenie, Lee and Molteni, whose list to 2000 was posted one day
   after this laboratory's. Their count for h up to 1500 equals this
   laboratory's exactly (9,245,562 fields), which is an independent
   confirmation as well as a stale comparator.
2. Four comparison cells give only the weakest published comparator, or not
   the first source.
3. A candidate, not audited: the course states the de Bruijn-Newman upper
   bound 0.2 as proved, while hunt #147 recorded a step of that chain that no
   source it read carries out.

The board lists the sentences. Applying them is the owner's decision.

## 10. What was not checked

- **Whether the archive is accepted by a kernel.** That is the replay. As of
  this page it has built a fraction of the modules with no error and has no
  verdict on any of the five theorems. Cite its `RUNS.md`, not this page.
- **Whether a clean build would be enough.** The replay hunt records that a
  clean build with a clean axiom printout is not sufficient by itself, which
  is why it replays every built module through the kernel as a second pass.
- **The mathematics.** Nobody here read the argument. The atlas stops where
  the analytic statements stop; nothing below the inequality (theta lifts,
  slopes, Galois representations) was entered.
- **The windowed Landau lemma.** It is the only step on the chain that
  mentions zeros and it is small. Its proof text was not read and no
  literature search was made for it.
- **Novelty.** None is claimed for anything on this page. The one identity
  that looked new on the day is published.

## 11. Sources and companion records

- L. Alpoge, note and archive, `alpo.ge`, 2026-11-20.
- "Lean verification of the Riemann Hypothesis", joint statement by the Lean
  and Mathlib communities, Lean community blog, 2026-11-21
  (`leanprover-community.github.io/blog/posts/riemann-hypothesis/`).
- A. Sutherland, "Verification files for the Lean proof of the Riemann
  Hypothesis", `math.mit.edu/~drew/grh/`, as updated 2026-11-21 12:55 UTC.
- O. Ramare, "Explicit estimates for the summatory function of
  Lambda(n)/n from the one of Lambda(n)", Acta Arith. 159 (2013), and its
  corrigendum, Acta Arith. 211 (2023), 93 to 96.
- S. R. Garcia, L. Grenie, E. S. Lee, G. Molteni, "Bounds for the residue of
  Dedekind zeta functions under GRH and applications", arXiv:2610.14257.
- The literature notes of the day, with each item labelled as read that day,
  read second-hand or recalled:
  `docs/reviews/2026-11-20-rh-claim-literature-notes.md`.
- Hunts #160 to #163 in `hunts/README.md`; hunt #159 on its own branch.
