# 14 — How New Mathematics Gets Invented

*A companion to `docs/12-how-hard-problems-die.md`. That document is a kill board: eight problems,
the mechanism that killed each, and RH scored against them. This one asks the prior question — where
the mechanisms' raw material comes from. When a problem needs objects that do not exist yet, how have
mathematicians historically produced them? Eleven recurring moves, each with cases, each scored
against the one gap this laboratory keeps running into: `docs/11`'s missing Frobenius over `Spec Z`.*

## The short version

Nothing here is a method you can execute. These are *post-hoc* patterns in how new mathematics
appeared, and the sample is heavily survivorship-biased — the failed attempts to invent objects are
not written down. Read it as a catalogue of shapes, not a recipe.

The one useful output is the scoring in Section 12. Mechanisms 1, 3, 4, 7 and 11 have all been aimed
squarely at the Frobenius-over-`Z` gap by very strong people; each produced real mathematics and none
closed it. Mechanism 9 — compute until a pattern demands explanation — is the only one a
computational laboratory can actually execute, and it is also, historically, among the most
productive. That is the honest reason this repository exists in the shape it does.

**Dates and attributions below are as commonly cited; I have not verified them against primary
sources, and the historical claims in this document are not testable by anything in `tests/`.**
That is a real difference from the rest of the docs, where every number is pinned. Treat this
document as orientation, not as reference.

---

## 1. Invent the missing objects so a law survives

Unique factorisation fails in the cyclotomic rings `Z[zeta_p]`. Kummer's response was not to abandon
the law but to posit "ideal numbers" that restore it; Dedekind later showed these could be realised
as *subsets* of the original ring — ideals. A ghost object acquired a body, and algebraic number
theory followed.

The detail worth stealing: **Kummer had a computable membership test before anyone knew what the
objects were.** Divisibility by an ideal number was checkable. The posited object was falsifiable
from the start.

## 2. Negate a stubborn assumption and see if the world stays consistent

Non-Euclidean geometry (Bolyai, Lobachevsky; Gauss privately earlier). Also Cantor's transfinite
numbers, and Robinson's nonstandard analysis reviving infinitesimals on model-theoretic footing.
What looked like a necessary truth turned out to be an independent axiom, and dropping it gave a
consistent alternative rather than a contradiction.

`docs/11` §2 is explicitly this move applied to the field axioms: `0 != 1` forbids `F1`, so every
`F1` program is a proposal to change what "field" or "geometry" means.

## 3. Change the base ring or the characteristic

`Z -> Z/p`, `-> Z_p` (Hensel), `R -> C`. And the big one for us: treating function fields over `F_q`
as a parallel universe to number fields, which is what made the Weil conjectures a *template* rather
than a curiosity.

Note the axis carefully. This is not a change of *notation* — base ten versus base two versus base
sixty is invisible to every object in this repository, since the Euler product runs over primes and
the primes do not move when you change how you spell them. The productive change is of coefficient
ring and characteristic.

## 4. Replace a number-valued invariant with an object-valued one

Betti numbers were numbers until Noether insisted they be groups; then maps between spaces induce
maps between invariants and functoriality does the work. Lefschetz's fixed-point formula is the
payoff, and `zeta/finitefield.py` verifies it directly (`docs/11` §1).

The direction of travel is worth noting: **Weil specified the cohomology theory by its required
behaviour before it existed**, and Grothendieck and Artin then built étale cohomology to that
specification, with Grothendieck introducing topoi as a replacement for the notion of space. Naming
the machine you need is a legitimate move, not a wish.

## 5. Name the pattern that keeps recurring

Abstract groups out of permutation groups; vector spaces; and category theory itself — Eilenberg and
Mac Lane needed "natural transformation" to be precise in algebraic topology, and had to invent
functors and categories in order to define it. The same argument appearing in unrelated places is
the signal.

## 6. Complete the category until an operation is total

Negative numbers (subtraction), `C` (roots), Schwartz distributions (so everything is
differentiable), sheaves, stacks (so quotients exist), motives. An operation is partial; formally
adjoin the missing values and check nothing old breaks. `docs/11` §2 lists `i` and the delta function
as precedents for exactly this.

## 7. Build a dictionary and transport proofs across it

Weil's Rosetta Stone: number fields / function fields over `F_q` / Riemann surfaces. Langlands is the
industrial-scale version. Fermat's Last Theorem is the cleanest case — Frey's curve, Serre's
conjecture, Ribet's theorem turned FLT into a corollary of modularity, which Wiles proved. Nobody
attacked FLT head-on. `docs/12` §2 scores this mechanism as BRIDGE BETWEEN WORLDS.

## 8. Reformulate until it becomes another field's routine problem

Poincaré became a question about Ricci flow and singularity control — topology handed to PDE
(`docs/12` §5). RH → Weil positivity is the same move already made (`docs/07` §7,
`docs/10`); the difficulty is that the analytic side is not easier.

## 9. Compute until a pattern demands explanation

Gauss's prime tables gave the Prime Number Theorem conjecture a century before its proof. Birch and
Swinnerton-Dyer read their conjecture off machine output. Monstrous moonshine began with the
observation that `196884 = 196883 + 1`. And the one this repository lives inside: Montgomery's pair
correlation meeting Dyson's random matrices, which is why `docs/06` and
`scripts/16_repulsion_floor.py` measure what they measure.

**This is the only mechanism on the list a computational laboratory can execute.** Two cautions from
the cases, both of which the repository already enforces elsewhere:

- The productive computations are the ones that produce *a number that should not be that number*.
  A computation confirming what was expected is a check, not a lead.
- Every candidate pattern must clear the standing counterexample gate (`docs/09` §5 gate 3). The
  moments programme is the worked example of a pattern that looked structural and was explained by
  controls instead (`NULLCONTROLS.md`); `scripts/18_dh_li_coefficients.py` is the same gate applied
  to a criterion.

## 10. Import structure from physics

Random matrix theory described nuclear energy levels before it described zeta zeros. Mirror symmetry
arrived as a string-theory prediction about counts of curves on Calabi–Yau manifolds that
mathematicians then had to verify and eventually prove. Witten's work on topological quantum field
theory is the general case.

## 11. Relax rigidity to build a bridge, then rigidify

Weak solutions first, regularity afterwards. The instance most relevant here is **perfectoid spaces**
(Scholze, building on Fontaine–Wintenberger; Fields Medal commonly cited as 2018): a systematic
bridge between characteristic `p` and characteristic `0` via tilting, letting problems move into the
world where Frobenius exists and come back. It has transformed `p`-adic Hodge theory. It has not
produced RH.

---

## 12. Scoring the mechanisms against the Frobenius gap

`docs/11` §5 gives four falsification gates for any `F1` or Deninger-style program. This table asks
the narrower question: which invention mechanism is each known attempt using, and where did it stop?

| Mechanism | Aimed at the gap by | Status |
| --- | --- | --- |
| 1 — posit the missing object | the `F1` programs generally | **PROGRAM.** No object; and unlike Kummer's ideal numbers, no computable membership test to falsify a candidate |
| 2 — negate an axiom | every `F1` formalism (`0 != 1`) | **PROGRAM.** Formalisms genuinely differ; each proves real theorems internally |
| 3 — change the base ring | Weil's function-field analogy | **THEOREM** on the `F_q` side, and the source of the template. Does not transport |
| 4 — object-valued invariants | Deninger's conjectural cohomology | **PROGRAM.** The required `H^1` is infinite-dimensional, so the standard machinery does not apply |
| 7 — dictionary transport | Connes–Consani, Langlands-adjacent work | **PROGRAM.** Restates RH on a space that genuinely exists (`docs/10` §5); restatement is not reduction |
| 11 — bridge characteristics | perfectoid spaces | **THEOREM**, and a large one. Not aimed at RH and has not touched it |
| 9 — compute for anomalies | this repository, among many | The only one executable here. Has produced GUE agreement, which is consistent with the operator existing and proves nothing |

Borger's `lambda`-rings deserve a separate line because they are the closest thing to a direct answer
to "invent a Frobenius over `Z`": they *define* `F1`-structure as a commuting family of Frobenius
lifts, one per prime, and `Z` carries such a structure canonically (`docs/11` §3). That is mechanism
1 executed cleanly — the operator is declared to be the structure. What it has not produced is the
cohomology or the positivity, which by `docs/11` §1 is where the content of the finite-field proof
actually lives.

> **Plain-words recap.** Eleven shapes, all post-hoc, sample biased by the failures nobody recorded.
> Five of them have been pointed at the Frobenius gap by strong people and none closed it, which is a
> measurement of the size of the ask rather than an argument that it is hopeless. The one this
> laboratory can run is "compute until something is anomalous", and the discipline that makes it
> worth running is the counterexample gate, not the computing.

---

## Where to go next

- **`docs/12-how-hard-problems-die.md`** — the sibling: mechanisms that finished specific problems,
  and RH scored against them. Sections 1 and 2 there are mechanisms 4 and 7 here, seen from the
  problem's end rather than the object's.
- **`docs/11-f1-and-the-missing-geometry.md`** — the gap this document scores against, in full:
  space, operator, positivity, and the programs stuck on the first two.
- **`docs/09-new-ontologies.md`** §5 — the four falsification gates in their original form. Any
  invention that "explains" RH must survive them, gate 3 in particular.
- **`docs/08-why-it-is-hard.md`** — why no computation in this repository is evidence about RH, and
  the Davenport–Heilbronn function that powers the counterexample gate.
- **In code:** `scripts/11_finite_field_rh.py` for mechanism 3 where it is a theorem;
  `scripts/17_f1_fingerprints.py` for the `q -> 1` fingerprints of mechanism 1;
  `scripts/16_repulsion_floor.py` and `scripts/18_dh_li_coefficients.py` for mechanism 9 with the
  gate attached.
