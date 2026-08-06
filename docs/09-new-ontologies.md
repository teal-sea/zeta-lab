# 09 — New Ontologies: What "RH Needs New Mathematics" Actually Means

*The sequel to `docs/08-why-it-is-hard.md`. That document catalogued why the existing tools provably
stall. This one describes the professional consensus about what a real attack would have to look like,
and the one time in history the strategy worked.*

## The short version

The working belief of the field is not "we need a cleverer inequality" but "we need new *objects*."
The evidence is a precedent: the Riemann Hypothesis over finite fields resisted direct attack for
roughly twenty-five years after Weil conjectured it in 1949, and it fell in 1974 — not because someone
found a smarter estimate, but because Grothendieck and his school spent the 1960s rebuilding the
ontology of geometry itself (schemes, topoi, étale cohomology) until Frobenius became an honest linear
operator on an honest cohomology group, at which point Deligne could finish. The proof is literally
unstatable in the pre-1960 language. "RH needs new mathematics" means: do that again, for the
integers. There are serious ongoing attempts — the field with one element, Connes' noncommutative
trace-formula program, Deninger's dynamical-systems program — and every one of them is a **PROGRAM**,
not a result. Below: the precedent in detail, the Selberg-class rulebook that any new ontology must
respect, the round-two attempts, and four concrete falsification gates that let you evaluate a
proposed ontology in an afternoon.

---

## 1. The one victory: the Weil conjectures

### 1.1 A Riemann Hypothesis you can check by counting

Take a polynomial equation and count its solutions over the finite field `F_p`. For the curve
`E : y² = x³ − x`, write `N_p` for the number of solutions mod `p`, plus one point at infinity.

```python
p = 1009
N = 1 + sum(1 for x in range(p) for y in range(p)
            if (y*y - (x**3 - x)) % p == 0)
# N = 1040;  a_p = p + 1 - N = -30;  2*sqrt(1009) = 63.53...
```

**THEOREM (Hasse, 1930s, for elliptic curves; Weil, 1940s, for all curves).**

```
    | N_p − (p + 1) |  ≤  2g · sqrt(p)          (g = genus; g = 1 here)
```

Run the snippet: `a_p = −30`, comfortably inside `±63.5`. Why is this a Riemann Hypothesis? Package
the counts over all extensions `F_{p^n}` into a zeta function; for a curve it is a rational function
whose numerator has roots of absolute value exactly `sqrt(p)` — i.e. "all zeros on the critical
line" for the local analogue. The `sqrt` in the point-count bound *is* the `1/2` in `Re s = 1/2`.

**THEOREM (Weil, published 1948).** RH holds for all curves over finite fields. Weil then conjectured
(1949) the analogue for varieties of every dimension: rationality of the zeta function, a functional
equation, and the RH statement that the zeros and poles have the exact absolute values `q^{i/2}`.

### 1.2 Twenty-five years, and what actually worked

Direct and partial attacks ran for a generation. Dwork proved the rationality part in 1960 by p-adic
analysis — brilliant, but a technique, not a home; it did not touch the RH part. What worked was
Grothendieck's rebuild of the foundations, roughly 1958–1970:

- **Schemes.** A "space" is no longer a set of points with structure; it is *anything that obeys the
  rulebook* (a locally ringed space glued from spectra of commutative rings). Consequence: `Spec Z`,
  the "space of primes," is a legitimate geometric object — a kind of curve — on exactly the same
  footing as an ordinary curve over `F_p`.
- **Topoi.** A "place" is characterised by nothing except the category of things that live on it
  (its sheaves). Once you accept that, you can build spaces that have no points in the classical
  sense but have perfectly good cohomology. The étale topos is one: classical topology sees a variety
  over `F_p` as a discrete dust, but the étale rulebook extracts from it cohomology groups
  `H^i_et` that behave like the topology of a complex manifold.
- **Étale cohomology** (Grothendieck with M. Artin and others, early-to-mid 1960s). Now Frobenius —
  the map `x ↦ x^p`, whose fixed points are exactly the `F_p`-points — becomes a *linear operator*
  on finite-dimensional vector spaces `H^i_et`, and the Lefschetz fixed-point formula turns point
  counts into traces:

```
    N_{p^n}  =  Σ_i  (−1)^i  Tr( Frob^n | H^i_et )
```

Rationality and the functional equation fall out of this formula almost immediately. The RH part
says: the eigenvalues of Frobenius on `H^i` have absolute value exactly `p^{i/2}`. That is a
*positivity-flavoured* statement about an operator — precisely the shape the Hilbert–Pólya dream
(`docs/06-hilbert-polya-and-gue.md`) wants for zeta.

### 1.3 The positivity input

The eigenvalue bound does not come for free from the formalism. In Weil's own proof for curves, the
input is a genuine positivity theorem: the Castelnuovo–Severi inequality (a Hodge-index-type
statement) on the surface `C × C`, applied to the graph of Frobenius. Note the move: to prove RH for
the curve `C`, you work on the *square* `C × C`. Grothendieck hoped to finish the general case the
same way, via his "standard conjectures" — positivity statements for algebraic cycles that remain
**CONJECTURES** to this day. Deligne's actual 1974 proof (*La conjecture de Weil I*) took a
different, more analytic route — a tensor-power amplification argument with monodromy, borrowing a
squaring trick from the classical theory of modular forms — so the general case was won without the
standard conjectures. But in every version, symmetry (the functional equation, supplied by duality)
plus an input of *positivity* is what pins eigenvalues to the critical absolute value. Symmetry
alone never suffices; `docs/08-why-it-is-hard.md` makes the same point on the analytic side.

**The professional meaning of "RH needs new mathematics" is exactly this template.** Find the
category in which `Spec Z` is a curve over something, in which "zeta of `Spec Z`" *is* the Riemann
zeta function, in which some Frobenius-like flow acts on a cohomology that nobody has constructed,
and in which a positivity theorem is available. Then Deligne's blueprint applies. Nobody has found
the category.

---

## 2. Category theory: the working ontology, in one paragraph

The language all of this is written in deserves one honest paragraph. In category theory an object
has *no insides*: you are forbidden from asking what it is made of, and permitted only to ask how it
maps to and from other objects, and how those maps compose. The (informal) content of the Yoneda
lemma is that this costs nothing: an object is completely determined by the totality of maps into
it. This sounds like philosophy but is an engineering decision, and it is the one that made Section 1
possible — "a space with no classical points but real cohomology" is not a paradox once *space*
means "a category of sheaves obeying axioms." Every round-two program below is an attempt to write
down a category in which the primes are forced to be the points of something.

---

## 3. The Selberg class: an actual rulebook

If new objects are coming, we should at least axiomatise the old ones. Selberg (1989) proposed a
definition of "everything that deserves to be called an L-function": the **Selberg class** `S`. A
Dirichlet series `F(s) = Σ a_n n^{−s}` belongs to `S` if it satisfies:

```
    (1) Convergence:   the series converges absolutely for Re s > 1  (a_1 = 1).
    (2) Continuation:  (s−1)^m F(s) extends to an entire function of finite order,
                       for some integer m ≥ 0.
    (3) Symmetry:      a functional equation  Φ(s) = ω · conj(Φ(1 − conj(s))), |ω| = 1,
                       where Φ(s) = Q^s · Π_j Γ(λ_j s + μ_j) · F(s),  λ_j > 0, Re μ_j ≥ 0.
    (4) Euler product: log F(s) = Σ b_n n^{−s} with b_n = 0 unless n is a prime power,
                       and b_n ≪ n^θ for some θ < 1/2.
    (5) Ramanujan:     a_n ≪ n^ε for every ε > 0.
```

**CONJECTURE (Grand Riemann Hypothesis).** Every `F` in `S` has all its non-trivial zeros on
`Re s = 1/2`. Note the design: axioms (3) and (4) are *both* required, which is exactly the lesson
of the counterexamples in `docs/08-why-it-is-hard.md` — drop either one and the conjecture is false.

The class carries an invariant, the **degree** `d = 2 Σ_j λ_j` (zeta has `d = 1`; a modular-form
L-function has `d = 2`). The rulebook is slowly being proven to contain exactly the expected
inhabitants. **THEOREM** (Conrey–Ghosh, commonly cited from their 1993 paper): the only element of
degree 0 is the constant function 1, and there are no elements with `0 < d < 1`. **THEOREM**
(Kaczorowski–Perelli, in their "structure of the Selberg class" series — degree 1 around 1999,
and the non-existence of degrees strictly between 1 and 2 in a later installment, commonly cited as
2011): the degree-1 elements are precisely `ζ(s)` and shifted Dirichlet L-functions of primitive
characters. (I am confident in the statements; verify the exact dates and paper numbers before
citing them formally.) Degree 2 — where modular forms live — is not yet classified. It is
**CONJECTURED** that `S` coincides with the class of automorphic L-functions; that identification is
the Langlands program viewed from the analytic side.

---

## 4. Round two: attempts at the missing geometry of `Spec Z`

All three items below are labelled **PROGRAM**. None contains a proof of RH, and none is close by
its own authors' account. They are serious because each one produces genuine theorems *inside its
own formalism* and each one targets the specific gap Section 1 identified.

### 4.1 The field with one element, `F1` — PROGRAM

The oldest hint predates schemes: Tits observed in the 1950s that formulas for algebraic groups over
`F_q` degenerate, at `q = 1`, into true statements about Weyl groups — as if a "field with one
element" existed. The number-theoretic dream is precise in shape: if `Spec Z` were a *curve over
`F1`*, then `Spec Z ×_{F1} Spec Z` would be a *surface*, and Weil's positivity proof for curves
(Section 1.3, which runs on `C × C`) would have a home. The obstruction in ordinary algebraic
geometry is a theorem-level fact: `Z` has no coefficient field, and the product collapses
(`Z ⊗_Z Z = Z`). So `F1`-geometry tries to rebuild the rulebook beneath rings: Soulé gave a
candidate definition of varieties over `F1` (2004); Connes–Consani have developed several
successive versions; Borger's approach identifies "descent to `F1`" with a Λ-ring structure —
roughly, a ring equipped with commuting lifts of all Frobenius maps, making "Frobenius over the
integers" the *definition* rather than the mystery. These formalisms genuinely differ and none has
yet produced the surface with a workable intersection theory. That is the state of play.

### 4.2 Connes' noncommutative trace formula — PROGRAM

**THEOREM (Weil's positivity criterion, 1952).** RH is *equivalent* to the positivity of a certain
quadratic form built from the explicit formula of `docs/04-explicit-formula.md`: RH holds if and
only if the explicit-formula functional is `≥ 0` on all test functions of the form `g * g̃`. The
equivalence is a theorem; the positivity itself is the open problem, restated.

Connes (1999) constructed a noncommutative space — the adele class space, a quotient so badly
non-Hausdorff that only the topos/operator-algebra rulebook can see it — on which a natural scaling
flow acts, and proved a trace formula for it in which the explicit formula's shape appears with the
primes on the geometric side. In this frame RH becomes exactly a Weil-positivity statement about the
flow. Connes–Consani have continued the program (the "scaling site," and papers around 2020–2021
proving positivity in restricted settings); I have not verified the precise current scope of those
results, and neither author claims RH is proven. The honest summary: the program has succeeded in
*restating* RH as positivity on a genuinely existing (noncommutative) space, and the positivity
remains open.

### 4.3 Deninger's dynamical program — PROGRAM

Deninger (from the early 1990s; see his ICM address, commonly cited as 1998) argues from the *shape*
of known formulas that there should exist an infinite-dimensional cohomology theory and a flow
(a one-parameter dynamical system on some foliated space) such that: zeta is a regularized
determinant `det(s − Θ)` over the conjectural `H^1`; the closed orbits of the flow are the primes,
with period `log p`; and the explicit formula becomes a Lefschetz-type trace formula for the flow —
compare the Guinand–Weil form in `docs/04-explicit-formula.md`, where each prime `p` really does
enter through the sequence `log p, 2 log p, 3 log p, ...`, exactly like a closed orbit and its
iterates. Deninger has built fragments (e.g. determinant formulas that reproduce the Gamma factor),
but the space carrying the flow has not been found. Note how precisely this program and 4.1–4.2
triangulate the same missing object from different sides: primes as closed orbits (Deninger), primes
as points of a curve (`F1`), primes on the geometric side of a trace on a noncommutative space
(Connes).

---

## 5. Four design gates (how to falsify a proposed ontology quickly)

Any proposed new ontology for RH can be stress-tested against four gates. *The packaging into
"four gates" is this document's own synthesis, not a standard framework you will find named in
the literature* — but each individual requirement below is standard, and the sources for each are
given with it. These are not aesthetics;
each is a concrete test with known failure modes.

**Gate 1 — Recover the classics.** Inside the new language, re-derive the functional equation and
the Prime Number Theorem. If the formalism cannot even see `docs/03-functional-equation.md` and the
zero-free region story of `docs/08`, it is not about zeta. (This is the gate most `F1` formalisms
are still working toward: producing *any* classical analytic statement as output.)

**Gate 2 — A home for positivity.** The ontology must contain a slot where a positivity input
(Hodge-index-like, Weil-criterion-like) can live. Symmetry alone is provably insufficient — the
functional equation is satisfied by functions with off-line zeros (Gate 3), so a framework whose
only mechanism is symmetry cannot possibly output RH.

**Gate 3 — The counterexample gate (the sharpest one).** Whatever structure the ontology grants to
`ζ` must be *ungrantable* to the Davenport–Heilbronn function and to generic Epstein zeta functions
(**THEOREM**, 1936 and onward: these satisfy functional equations, have no Euler product, and have
zeros off the critical line — see `docs/08-why-it-is-hard.md`). An ontology roomy enough to
accommodate them "proves too much" and is dead on arrival. Concretely: when someone presents a
framework, ask *"where exactly does Davenport–Heilbronn fail to embed?"* If there is no crisp
answer, stop reading.

**Gate 4 — The Euler product must be structural.** In the new ontology the primes must be the
*points* (or orbits, or spectrum) of the hidden object, so that the Euler product is the statement
"the zeta function is a product over points" — a tautology of the geometry, as it is over finite
fields — rather than an identity bolted on afterward. All three programs of Section 4 pass this
gate by design; it is Gates 1 and 2 where they are stuck.

### 5.1 The strengthened gates: factorization, not positivity

The four gates above are eliminative: they kill ontologies that cannot possibly work. This
subsection states the *positive* target at the same resolution — what a candidate that survived
all four would still have to deliver. The organizing observation: since Weil positivity over the
full admissible test class is already **equivalent** to RH (Section 4.2), "prove the quadratic
form is positive" is not a strategy — it is RH restated. Trying to estimate the prime-power sum
directly is merely another formulation of the problem. The demand must instead be **factorization**:

> Construct, functorially from the prime-power and archimedean data, an arithmetic cohomology or
> spectral representation in which the Weil quadratic form is the norm square of a naturally
> defined operator or vector — schematically `−W(f ∗ f̃) = ‖Φ(f)‖²` in a genuine Hilbert, Hodge,
> intersection or C*-module structure — so that its sign becomes formal.

Arithmetic supplies the quadratic form; geometry must explain its sign. Once the norm identity
holds inside a structure that is positive *for structural reasons*, `⟨v, v⟩ ≥ 0` is linear
algebra, and RH follows by the already-known equivalence. Three requirements, in causal order:

**Requirement A — arithmetic provenance.** Every ingredient of the construction is generated from
the prime-power data `{(p, m, log p, p^{−m/2})}` together with the archimedean local factor. No
zeros, no `ξ`-phases, no zero-counting functions may enter the definition. (Given any real
sequence one can manufacture a self-adjoint diagonal operator with that spectrum; a construction
that imports the zeros explains nothing.)

**Requirement B — exact trace realization.** An identity `Str π(f) = W(f)` on the *entire*
admissible test algebra, with the prime powers arising as primitive orbit repetitions, local
fixed-point terms, or an equivalent intrinsic mechanism — not inserted afterward as coefficients.
This is where the analytic difficulty relocates, not where it disappears: in the function-field
case, Castelnuovo's inequality is formal *given* the surface, but building the surface and proving
the graph–diagonal intersection computes the right thing was the hard part. Expect a real attempt
to bleed here, on the full-class quantifier.

**Requirement C — structural positivity.** A canonical positive pairing such that
`−W(f ∗ f̃) = ‖Φ(f)‖²` for test functions satisfying the pole-removal conditions, with the
signature of the pairing forced independently of the zeros. The conceptual flow is then

```
    prime arithmetic ⟶ object ⟶ pairing ⟶ norm identity ⟶ Weil positivity ⟶ RH
```

and the load-bearing arrow is not the last one (that arrow is Weil's theorem); it is
`prime arithmetic ⟶ positive pairing`.

**The pseudo-solution taxonomy.** Each of the following evasions has absorbed a real research
program, which is why they deserve names:

1. *Direct estimation* — proves positivity only for restricted support, special test functions, or
   finite numerical ranges. (The fate of the truncated-Weil numerical literature: positive-definite
   matrices `Q_N` for every computed `N`, worth nothing by Littlewood's rule, `docs/08`.)
2. *Tautological completion* — defines a Hilbert space by completing test functions under the Weil
   form itself, assuming the very positivity at issue. (The standing critique of the de Branges
   route: Hilbert spaces of entire functions are a genuine positive category, but the required
   positivity conditions on the structure function are not prime-derived facts.)
3. *Zero-importing* — defines the pairing spectrally via `Σ_ρ |ĥ(ρ)|²`. (Every Hilbert–Pólya toy
   operator since 1999; fails Requirement A.)
4. *Formal C\*-positivity* — observes that `a*a ≥ 0` somewhere, but never proves that the
   arithmetic Weil distribution *is* the resulting positive functional. (The gap between "a trace
   formula exists on the adele class space" and "RH", Section 4.2.)
5. *Finite approximants* — obtains positive matrices `Q_N` without proving the limit is the full
   Weil form on the whole admissible domain. (Variant of 1, with the gap hidden in the limit.)

**Sharpening Gate 3/4: linear combination is the destroyer.** The precise statement of what the
counterexamples prove: *functional equation, gamma factors, Dirichlet-series structure, and even
being assembled from legitimate Euler products do not suffice; the primitive multiplicative
structure must survive in the global object, and linear combination destroys it.* The
Davenport–Heilbronn function is a self-dual linear combination of the two Dirichlet L-functions of
the quartic characters mod 5; Epstein zeta functions of class number greater than one are linear
combinations of the Hecke L-functions of the class group — and both have zeros off the critical
line. So the operational form of the gate is:

> The construction must detect primitive multiplicative local data, and must not apply unchanged
> to linear combinations of completed L-functions.

`zeta.epstein.battery` runs exactly this: its default rivals are Davenport–Heilbronn plus both
discriminant −23 forms (class number 3), i.e. two independent linear combinations of genuine
Euler products. One caution keeps the gate honest in the other direction: no known example
satisfies the *full* Selberg-class package (Section 3, axioms 1–5) and violates RH — the
counterexamples conclusively reject weaker packages only. Believing the full package suffices is
essentially believing GRH; the gate is eliminative, never probative (`prime-blind ⟹ not an
explanation`, but *not* `prime-sensitive ⟹ proof`).

**What this laboratory can and cannot test.** The three requirements split cleanly. Requirement A
is mechanically checkable (provenance scans of a construction's definition — the same technology
as the `discovery/` seam tests). Requirement B is exactly what this repo is built to test: an
identity on the test algebra is a measured *defect function* in the house style — compute both
sides independently over test functions from unrelated families, the protocol that validated the
`zeta/weil.py` convention; a candidate passing at `1e-30` across families is not proof, but a
candidate failing is dead. Requirement C's norm identity is numerically checkable as an identity;
its *naturality* — "canonical", "signature forced independently of the zeros" — is a judgment no
computation can render, and marks the exact boundary where the laboratory's writ ends and human
mathematics begins. (Convention landmine for any implementation: the sign of `W` and the direction
of the inequality vary across Weil/Bombieri/Connes normalizations — calibrate numerically against
a test function of known sign, per the house rule; never trust a source's sign.)

---

## 6. Cost honesty, and the Langlands ledger

The one time this strategy worked, the bill was: roughly twenty years (late 1950s to 1974), a
generation of exceptionally strong mathematicians working in concert, thousands of pages of
foundations (EGA, SGA) — *and*, crucially, a working blueprint the whole time: Weil had already
proven the curves case, so everyone knew the target theorems and could test the machinery against
them. Round two has the same blueprint (the finite-field case is now the known model) and, counting
from Tits' remark, more than fifty years of searching without finding the objects. That is not an
argument it will fail; it is an argument about the scale of the ask.

One more piece of honesty about the **Langlands program**, the master rulebook conjecture: it
predicts that the inhabitants of the Selberg class are exactly the automorphic L-functions, all tied
together by functoriality. If the full structure existed, RH would be one line-item in the ledger —
the natural positivity statement about the whole family at once. But state it carefully: no known
formulation of Langlands functoriality is known to *imply* RH. Langlands organises the objects; it
does not, as currently formulated, supply the positivity of Gate 2. The two quests are complementary,
not identical.

---

## 7. Back to this repo: shadows of the missing ontology

Two things you can compute in this laboratory are, on this view, shadows cast by the object nobody
has found.

- **The heat flow** (`docs/05-de-bruijn-newman.md`; `zeta.heatflow.H_t`, `track_zeros`,
  `lambda_facts`). The de Bruijn–Newman flow is a *dynamics acting on `Ξ`* with the exact critical
  behaviour RH demands (`Λ = 0` ⟺ RH), but it acts on a function, not on a space — a dynamics
  without a geometry underneath it. In Deninger's program a flow with this role is supposed to live
  on an actual foliated space whose orbits are the primes.
- **The spectral statistics** (`docs/06-hilbert-polya-and-gue.md`; `zeta.statistics.pair_correlation`,
  `compare_to_random_matrix`). The zeros behave, measurably on your laptop, like eigenvalues of a
  self-adjoint operator — an operator without a home, since no Hilbert space has been exhibited. In
  the finite-field world the "home" turned out to be étale cohomology and the operator was
  Frobenius; that is the precedent that keeps the dream respectable.
- **The explicit formula** (`docs/04-explicit-formula.md`; `zeta.explicit.psi_from_zeros`,
  `prime_spectrum`). Zeros on one side, prime powers `log p, 2 log p, ...` on the other: a trace
  formula in search of its trace. Every program in Section 4 is an attempt to name the thing being
  traced.

The computations are real; the interpretation — that they are low-dimensional projections of one
missing geometry — is the field's best-supported **HEURISTIC**.

---

## Where to go next

- `docs/10-trace-formulas-and-connes.md` and `docs/11-f1-and-the-missing-geometry.md` — deeper
  digests of the two programme families sketched above, each backed by a runnable module:
  `zeta/weil.py` implements Gate 2 (the positivity criterion, live) and `zeta/epstein.py`
  implements Gate 3 (the counterexample battery, with an actual off-line zero).
- `docs/08-why-it-is-hard.md` — the failure catalogue that motivates all of this; read it first if
  you skipped it, especially the Davenport–Heilbronn section that powers Gate 3.
- `docs/06-hilbert-polya-and-gue.md` and `docs/05-de-bruijn-newman.md` — the two "shadows" of
  Section 7, each with runnable experiments.
- `docs/04-explicit-formula.md` — the trace formula whose geometric side is the mystery.
- Primary sources worth the effort: Deligne, *La conjecture de Weil I* (1974); Selberg's Amalfi
  lecture on the Selberg class (1989 conference, published in the proceedings); Connes' 1999 Selecta
  Mathematica paper on the trace formula; Deninger's ICM address. For the Weil-conjectures story
  told for humans, the appendix of Hartshorne's *Algebraic Geometry* states the conjectures cleanly.
- In code: `zeta.zeros.verify_rh_up_to` for what verification *can* do (and `docs/08` for why that
  is evidence of almost nothing), and `zeta.heatflow.lambda_facts` for the current state of the one
  quantity — `Λ` — that turns RH into an exact criticality statement.
