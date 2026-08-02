# 11 — F1 and the Missing Geometry

*A companion to `docs/09-new-ontologies.md`. That document surveyed the "new objects" landscape and
`docs/10-trace-formulas-and-connes.md` slowed down on the trace-formula corner; this one slows down
on the strangest corner: the geometry that is supposed to sit underneath the integers, and the
"field with one element" nobody can define but everybody keeps finding fingerprints of.*

## The short version

The one proven Riemann Hypothesis — the finite-field version, Deligne 1974 — worked because three
things existed: an actual *space*, an actual *operator* on it (Frobenius), and an actual *positivity
theorem* pinning the operator's eigenvalues to the critical value. For the integers, all three are
missing. The organising dream: `Spec Z` — the geometric object whose points are the primes — should
be a *curve* over a mysterious base `F1`, "the field with one element," so Weil's template can run.
A literal field with one element cannot exist (a field's axioms require `0 != 1`), so every attempt
is really an attempt to *rewrite the rulebook* for "field" and "geometry" until the object does
exist — the same move that produced schemes and étale cohomology last time. Below: the recap, the
dream, the attempts (Tits, Soulé, Connes–Consani, Borger, Deninger), and the honest scorecard.
Every attempt is a **PROGRAM**, not a result. None is close, by its own authors' account.

---

## 1. The template that worked once

Recall the finite-field story from `docs/09-new-ontologies.md`, in three beats.

**First, there was a space.** Counting solutions of `y^2 = x^3 - x` modulo a prime `p` sounds like
arithmetic, not geometry — the "solution set" is a scatter of residues, not a surface you could sand.
Grothendieck's rebuild of the 1960s changed what *space* means: a space is anything that obeys the
rulebook. Under the new rulebook the scatter of residues *is* a curve, and — the part that matters
here — `Spec Z`, the set of primes wearing a geometric structure, is also a legitimate space, a kind
of one-dimensional curve whose points are the prime numbers.

**Second, there was an operator.** Over `F_p` there is a map you get for free: `x -> x^p`
(Frobenius), whose fixed points are exactly the solutions defined over `F_p`. Étale cohomology
attaches to the curve a finite list of honest finite-dimensional vector spaces, and Frobenius acts
on them as an honest matrix. The Lefschetz fixed-point formula converts *counting solutions* into
*taking traces of a matrix* — the same move as modal analysis, where a messy time signal becomes a
clean sum over eigenvalues. Counting became linear algebra.

**Third, there was a positivity.** Symmetry alone (the functional equation, supplied by duality)
never pins eigenvalues down; `docs/08-why-it-is-hard.md` proves that with counterexamples. The
closing input in Weil's proof for curves is the Castelnuovo–Severi inequality — a Hodge-index-type
statement, a cousin of "this quadratic form is definite" — and the crucial staging detail is *where
it lives*: to prove RH for the curve `C`, you work on the square `C x C` and apply positivity to the
graph of Frobenius. (Deligne's general 1974 proof took a different analytic route, but still
symmetry-plus-positivity at bottom; `docs/09`, §1.3.) The output: the Frobenius eigenvalues have
absolute value exactly `sqrt(p)` — all zeros on the critical line, as a **THEOREM**.

> **Plain-words recap.** The only RH ever proved needed three ingredients: a space, a matrix acting
> on something built from it, and a positivity theorem — applied on the space's *square* — forcing
> the eigenvalues onto the critical value. Space, operator, positivity. Keep the checklist; the rest
> of this document is people trying to build item one.

---

## 2. The dream: `Spec Z` as a curve over `F1`

Here is the gap, stated as an engineering problem. Weil's proof runs on `C x C`, the square of the
curve — and "square" means square *over the base field*: a curve over `F_p` is a one-parameter
object with `F_p` as its fixed ground, so the product is a genuine two-parameter object, a surface.
Try the same with the integers. What is the ground under `Z`? Nothing: `Z` is the bottom of the
tower, and the product collapses — `Z (x)_Z Z = Z`, a theorem-level fact (`docs/09`, §4.1). The
square of `Spec Z` over its only available base is just `Spec Z` again: a one-dimensional object
whose square is one-dimensional. The staging area for the positivity argument does not exist.

The dream postulates a basement. Suppose there were a field `F1` *below* `Z` — a "field with one
element" — such that `Spec Z` is a curve *over* `F1`. Then `Spec Z x_{F1} Spec Z` would be an honest
surface, Weil's positivity argument would have its home, and the finite-field template could run on
the actual Riemann zeta function. The shape of the dream is completely precise. Only the object is
missing.

And here is the charming catastrophe: **a literal field with one element cannot exist.** A field is a
number system where you can add, subtract, multiply, and divide by anything nonzero; its axioms
require a zero `0` and a unit `1` with `0 != 1` — written into the definition, because if `0 = 1`
everything collapses to `0`. The smallest field has two elements; "`F1`" is a contradiction in
terms. The response is not to give up but to make the objects-and-rulebooks move of `docs/09`, §2:
if the object you need is forbidden by the current definition, *change the definition* — carefully,
so everything old survives — until the object exists. You have seen this move before. No real number
squares to `-1`; mathematics rebuilt "number" until `i` existed. No function is zero everywhere,
infinite at a point, with integral 1; analysis rebuilt "function" (distributions) until the delta
function existed. `F1` asks for the same manoeuvre one level deeper: rebuild "field" — or rebuild
"geometry" so it no longer needs a field at the bottom.

Why believe the basement is there at all? Because its fingerprints keep showing up.

> **Plain-words recap.** The proof template needs the square of `Spec Z`, and over the integers the
> square collapses — there is no ground field under `Z` to take it over. The dream: invent the
> missing ground, `F1`. A one-element field is flatly impossible under the current axioms
> (`0 != 1`), so every `F1` program is really a proposal to redefine "field" or "geometry" — the
> same legal move that gave us `i` and the delta function.

---

## 3. The fingerprints, and the attempts

All three items below (and Deninger's program in Section 4) are labelled **PROGRAM**, per the house
convention: genuine theorems inside their own formalisms, no proof of RH, none claimed.

**Tits' observation (1950s) — the original fingerprint. PROGRAM.** Many counting formulas over the
field `F_q` are polynomials in `q`, and something eerie happens at `q = 1`. The projective plane
over `F_q` has `q^2 + q + 1` points: `7` at `q = 2`, `13` at `q = 3` — and `3` at the forbidden
value `q = 1`: exactly a triangle, the degenerate "projective plane" with three points and three
lines. Deeper: the number of complete flags in `F_q^n` (a nested chain
line-inside-plane-inside-space) is the *q-factorial* `[n]_q! = (1)(1+q)(1+q+q^2)...` — at `n = 3`,
`q = 2` that is `21`, verified here by brute-force enumeration of the subspaces of `F_2^3` — and at
`q = 1` it becomes `n!`, the number of *permutations* of `n` things. Tits noticed this pattern
across the algebraic groups: at `q = 1` the geometry degenerates into pure combinatorics (Weyl
groups — finite symmetry skeletons). As if every `F_q`-geometry were a `q`-parameter family whose
`q -> 1` limit is the geometry over a one-element field. The limit of the *formulas* exists; the
object they count at `q = 1` is what nobody can exhibit.

**Soulé (2004) and Connes–Consani — rulebook rewrites. PROGRAM.** Direct attempts to write the new
definition. Soulé proposed a candidate definition of "variety over `F1`" in the category-theoretic
style: since an object is completely determined by how it maps to and from other objects (`docs/09`,
§2), you can *define* an `F1`-object by prescribing its interactions — roughly, what its sets of
points over every actual field must be — without ever saying what it is made of. Connes and Consani
have developed several successive formalisms in the same spirit (some deliberately weakening
"addition," since `F1` should have a `1`, a `0`, and essentially nothing else). The honest state of
play, unchanged from `docs/09`: the formalisms genuinely differ, each proves real theorems
internally, and none has produced the thing the dream needs — the surface `Spec Z x_{F1} Spec Z`
with a workable intersection theory, the staging area for positivity.

**Borger's lambda-rings — F1-structure as symmetry. PROGRAM.** Borger's approach (commonly cited
from around 2009; I have not verified the date) is the most engineer-friendly: it identifies "being
defined over `F1`" not with a new kind of point-set but with *extra structure carried by the ring* —
a lambda-ring structure, which for our purposes means a commuting family of maps lifting the
Frobenius `x -> x^p` for *every* prime `p` at once. Read it as a design decision: last time the
operator came for free from the space; this time, since we cannot find the space, *declare the
operator to be the structure* — "Frobenius over the integers" becomes the definition rather than the
mystery. The integers carry this structure canonically, which is the program's founding observation;
whether it yields the cohomology and the positivity is open.

> **Plain-words recap.** The evidence for the basement: formulas keep having sensible values at the
> illegal setting `q = 1` — geometry degenerates to counting permutations. The attempts: define
> `F1`-objects by their interfaces instead of their insides (Soulé, Connes–Consani), or skip the
> space and axiomatise the operator — `F1`-structure as "all Frobenius symmetries at once" (Borger).
> Real mathematics in each; the load-bearing surface still missing in all.

---

## 4. Deninger's program: the primes as a dynamical system

Deninger's program (from the early 1990s; ICM address commonly cited as 1998) approaches the missing
object from the physics side, and it is the one this repository has been secretly preparing you for.

Start from what you already know. In `docs/04-explicit-formula.md`, every non-trivial zero
`rho = beta + i gamma` is literally a *pole* of `-zeta'/zeta`, and in the variable `u = log x` it
contributes a mode `e^{beta u} cos(gamma u - phase)` to the prime-counting error — exactly what a
pole at `s = beta + i gamma` contributes to the impulse response of a linear system: `gamma` the
ringing frequency, `beta` the growth exponent. After the natural `sqrt(x) = e^{u/2}` normalisation,
RH is a pole-placement statement: **every pole of the system sits exactly on the marginal-stability
line** — every mode a pure, undamped, ungrowing oscillation, none hot, none dead. And on the other
side of the same formula, the primes enter as the sequence `log p, 2 log p, 3 log p, ...` — for
`p = 2`: `0.6931, 1.3863, 2.0794, ...` — precisely the signature of a *closed orbit* of period
`log p` and its repeated traversals, the way periodic orbits enter trace formulas in quantum chaos
(`docs/06-hilbert-polya-and-gue.md`, the Gutzwiller connection).

Deninger's proposal takes that reading literally. **PROGRAM:** there should exist an actual
dynamical system — a flow on some infinite-dimensional foliated space, none of it yet constructed —
such that: the closed orbits of the flow *are* the primes, with period `log p`; the flow acts on an
infinite-dimensional cohomology `H^1` (the analogue of Section 1's étale spaces) with generator
`Theta`; zeta is the regularized determinant `det(s - Theta)` over that `H^1`, so the zeros are
exactly the eigenvalues of `Theta` — the modal frequencies of the flow; and the explicit formula of
`docs/04` becomes a Lefschetz-type trace formula: spectrum on one side, periodic orbits on the
other, an identity by geometry instead of contour integration. Deninger has built real fragments —
e.g. determinant formulas reproducing the Gamma factor of the functional equation (`docs/09`, §4.3;
I state the fragments at that document's level of confidence and no further). The space carrying
the flow has not been found.

Notice how this rhymes with `docs/05-de-bruijn-newman.md`. The de Bruijn–Newman heat flow is a
genuine dynamics with the exact critical behaviour RH demands (`Lambda = 0` iff RH) — but it acts on
the *function* `Xi`, a dynamics with no space underneath it. Deninger predicts the space: a flow
whose orbits are the primes, whose spectrum is the zeros, and for which a positivity — the third
checklist item — could finally be a statement about an actual system, the way "this structure's
modes are all real" is a statement about a symmetric stiffness matrix. The `F1` programs of Section
3 and Deninger's triangulate the same missing object from different sides: primes as points of a
curve, primes as closed orbits of a flow.

> **Plain-words recap.** You already read the explicit formula like an engineer: zeros are poles, RH
> says all poles sit on one vertical line, and the primes tick in at `log p, 2 log p, 3 log p` — the
> calling card of a periodic orbit. Deninger conjectures the machine behind the transfer function: a
> flow whose closed orbits are the primes and whose modal spectrum is the zeros. Fragments exist;
> the machine does not, yet.

---

## 5. What any of these must deliver, and the scorecard

The four falsification gates of `docs/09`, §5, applied to this document's programs:

- **Gate 1 — recover the classics.** Re-derive the functional equation and the Prime Number Theorem
  inside the new language. This is where the `F1` formalisms are still working: producing *any*
  classical analytic statement as output.
- **Gate 2 — a home for positivity.** A slot where a Hodge-index-like input can live — for `F1`, the
  surface with an intersection theory; for Deninger, the analogue on the conjectural `H^1`. Symmetry
  alone is provably insufficient.
- **Gate 3 — the counterexample gate.** Whatever structure gets granted to zeta must be
  *ungrantable* to the Davenport–Heilbronn function and generic Epstein zeta functions — functional
  equation, no Euler product, zeros off the line (**THEOREM**; `docs/08`). Ask any formalism: where
  exactly does Davenport–Heilbronn fail to embed?
- **Gate 4 — the Euler product must be structural.** The primes must be the points or the orbits, so
  "product over primes" is a tautology of the geometry. Every program above passes this gate *by
  design* — it is their founding requirement — which is why they are taken seriously, and why being
  stuck at Gates 1 and 2 is the honest summary.

The scorecard, soberly. The precedent cost roughly twenty years, a generation of exceptional
people, and thousands of pages of new foundations — *with* a working blueprint the whole time,
since Weil had already proven the curves case. Round two has the same blueprint and, counting from
Tits' remark, more than fifty years of searching without finding the objects. In that time: real
theorems inside each formalism, genuine restatements of RH in new languages (Connes' trace-formula
program restates it as positivity on a space that genuinely exists — `docs/09` §4.2, and in full
`docs/10-trace-formulas-and-connes.md` §5), fingerprints
of `F1` everywhere — and no space, no operator with a home, no positivity. That is not an argument
the search will fail. It is a measurement of the size of the ask: last time the answer was a rebuild
of what geometry *is*, and there is no reason to expect round two to be cheaper.

> **Plain-words recap.** Four tests: reproduce the known results; give positivity somewhere to
> live; make the known counterexample fail to fit; make the primes structurally the points or
> orbits. Fifty-plus years in, every serious program passes the fourth by design and is stuck on the
> first two. The precedent says the missing step is a foundations rebuild, not a clever estimate —
> and rebuilds are bought in decades.

---

## Where to go next

- **`docs/09-new-ontologies.md`** — the parent document: the Weil-conjectures precedent in detail,
  the Selberg-class rulebook, and the gates in their original form.
- **`docs/10-trace-formulas-and-connes.md`** — the third leg of the triangulation, deliberately thin
  here because full there: the explicit formula as a trace formula (verified to thirty-one digits),
  Weil's positivity criterion, Selberg's worked example, and Connes' adele class space.
- **`docs/04-explicit-formula.md`** — the trace formula in search of its trace. Re-read §5 and §7
  with Deninger's dictionary: mode = zero, closed orbit = prime, `u = log x` the flow time.
- **`docs/05-de-bruijn-newman.md`** — the dynamics-without-a-geometry these programs are trying to
  put a floor under. **`docs/08-why-it-is-hard.md`** — the Davenport–Heilbronn section that powers
  Gate 3.
- **In code:** `zeta.explicit.prime_spectrum` recovers the primes as spectral peaks from nothing but
  zero ordinates — the closest thing this laboratory has to *hearing* the conjectural flow; and
  `zeta.heatflow.track_zeros` runs the one dynamics on `Xi` that actually exists today.
