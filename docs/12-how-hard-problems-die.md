# 12 — How Hard Problems Die: A Kill Board

*`docs/08-why-it-is-hard.md` catalogued what fails. `docs/09-new-ontologies.md` described the one
time a rebuild worked. This document widens the sample: eight famous problems, the mechanism that
actually killed each one, and an honest scoring of which mechanisms RH's live formulations touch.*

## The short version

Hard problems do not die of effort. They die of a **mechanism** — a structural move converting the
statement into something a known tool can bite. There are not many mechanisms. Seven case studies
below: rebuild the ontology (Weil conjectures), bridge to a richer world (Fermat), reduce infinity to
a finite certified list (Four Colour, Kepler), squeeze an effective threshold down to meet a
computation coming up (weak Goldbach), deform the object by a flow and control the singularities
(Poincaré), let insight make the computation irrelevant (Catalan), build an equivalence web wide
enough that an outsider's toolkit lands on it (Kadison–Singer). Scoring RH: it touches **flow**
(de Bruijn–Newman, `docs/05`), **equivalence web** (`docs/07`, `zeta/criteria.py`) and
**real-rootedness** (Li/Jensen, `zeta/li.py`) — and provably does *not* fit finite reduction or the
effective-threshold squeeze, which is the structural reason verification to any height decides
nothing (`docs/08` §3). Labels are **THEOREM / CONJECTURE / PROGRAM**; where I could not check a date
or attribution I say so.

Two cautions. This is a **survivorship sample** — we tabulate the problems that died, not the ones
still alive. And in every case the closing input came from *outside* the problem's own language: the
board's most reliable regularity, and bad news for anyone hoping RH falls to a better estimate in the
language of `docs/01`–`docs/04`.

---

## 1. ONTOLOGY REBUILD — the Weil conjectures

**Mechanism: when the objects named in the statement cannot carry an argument, rebuild what the
objects *are* until they can.**

Count solutions of a polynomial equation over a finite field. For `E : y² = x³ − x` at `p = 1009` —
that is `zeta.finitefield.hasse_check(-1, 0, 1009)`, the module taking `y² = x³ + ax + b` — you get
`N_1 = 1040`, `a_p = p + 1 − N = −30`, against the Hasse bound `2√p = 63.5295…`; re-run while writing
this. Package the counts over all extensions into a zeta function and the `√p` *is* the `1/2` of
`Re s = 1/2` — literally: `critical_line_check(-1, 0, 1009)` returns `re_s = [0.5, 0.5]` with
`max_deviation_from_half = 0.0`.

**THEOREM (Hasse, 1930s, elliptic curves; Weil, published 1948, all curves).** The bound holds.
**Weil then CONJECTURED (1949)** the analogue in every dimension.

Twenty-five years followed. Dwork proved rationality in 1960 by p-adic analysis — a technique with no
home; it did not touch the RH part. What worked was Grothendieck's rebuild (roughly 1958–1970):
schemes, so a scatter of residues *is* a curve and `Spec Z` *is* a space; topoi, so "place" means
"category of sheaves obeying axioms"; and **étale cohomology** (Grothendieck with M. Artin),
attaching to the variety honest finite-dimensional vector spaces on which Frobenius `x ↦ x^p` acts as
an honest matrix. Lefschetz's fixed-point formula converts counting into traces:

```
    N_{q^n}  =  Σ_i  (−1)^i · Tr( Frob^n | H^i_et )
```

Read that as modal analysis (`docs/10` §1): a messy time-domain record becomes a finite sum over
eigenvalues. Rationality and the functional equation fall out immediately, and RH becomes "those
eigenvalues have modulus exactly `q^{i/2}`" — **pole placement**. You cannot place a pole you have no
coordinates for; the rebuild supplied the coordinates.

**THEOREM (Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), 273–307).** The
eigenvalue bound. The closing input is *positivity*: amplification over even tensor powers —
Rankin's trick from modular forms, at bottom "squares of real numbers are non-negative" — plus
monodromy from Lefschetz pencils (sweep the variety by a one-parameter family of hyperplane slices
and track how the cohomology twists as you go round the family; the twisting group has to be big).
(Confident in that shape and the citation, not in reciting the chain of lemmas; Kowalski's and Tony
Feng's notes on *Weil I* are the standard entry points.)
Grothendieck's own route, the **standard conjectures** on positivity for algebraic cycles, remains
**CONJECTURE**; Deligne went around it.

> **Plain-words recap.** Nobody found a cleverer estimate. They rebuilt geometry until Frobenius was
> a matrix, at which point "all zeros on the line" became "this matrix has eigenvalues of a fixed
> size," and positivity finished it. Symmetry never sufficed; symmetry plus positivity did.

---

## 2. BRIDGE BETWEEN WORLDS — Fermat's Last Theorem

**Mechanism: transport the problem into a world with far more structure, via a chain that makes a
*soft-looking* conjecture in the second world lethal to the first.**

A hypothetical solution `a^p + b^p = c^p` is one equation with no visible structure. Frey (1984–86)
attached to it the elliptic curve `y² = x(x − a^p)(x + b^p)` — the **Frey curve** — whose
discriminant is so implausibly a perfect `p`-th power that the curve looks impossible. Serre's
ε-conjecture (level lowering) made "looks impossible" precise.

**THEOREM (Ribet; proved summer 1986, published *Invent. Math.* 100 (1990), 431–476).** The
ε-conjecture. Consequence: **the Frey curve cannot be modular** — *modular* meaning its L-function is
that of a modular form, an object from complex analysis, not Diophantine algebra. So FLT reduced to
**CONJECTURE (Taniyama, 1955; Shimura; Weil, 1967)**: every elliptic curve over `Q` is modular.

**THEOREM (Wiles, *Ann. of Math.* 141 (1995), 443–551; with Taylor, ibid. 553–572).** Modularity for
*semistable* elliptic curves — those whose reduction mod every prime degenerates only in the mildest
allowed way — which is enough for FLT, because the Frey curve is one. The history matters for this
repo's temperament: Wiles announced in Cambridge in June 1993; a gap was found *during refereeing*
(Nick Katz located it) later that year; it was closed with Richard Taylor in September 1994. Peer
review worked exactly as
advertised. Full modularity is **THEOREM (Breuil–Conrad–Diamond–Taylor, *J. Amer. Math. Soc.* 14
(2001), 843–939)**.

The machinery invented on the way is now the subject's standard toolkit: **Galois representations**
(a curve's arithmetic as a matrix-valued symmetry action), Mazur's **deformation theory** (all lifts
of a mod-`p` representation, parametrised by a universal ring `R`), and the **`R = T` theorem** —
that ring equals a Hecke algebra built from modular forms — via Taylor–Wiles patching. An impedance
match: two circuits that could not talk, joined by a transformer that was itself the hard part.

A connection this repo owns: modular forms are the same family as our theta function. `docs/02` §6
identifies Jacobi's `Θ(τ) = Σ q^{n²}` as a modular form of weight `1/2` for `Γ₀(4)`, and the `√s` in
Jacobi's identity — hence the `1/2` in `Re s = 1/2` — *is* that weight. Elliptic curves land at
weight 2: same rulebook, different weight.

---

## 3. FINITE REDUCTION + MACHINE GRIND — Four Colour and Kepler

**Mechanism: prove a *reduction theorem* converting "for all of an infinite set" into "for all of
this explicit finite list," then check the list mechanically.**

The mathematics is entirely in the reduction; the grind is bookkeeping, at a scale needing its own
correctness argument.

**Four Colour.** Kempe's 1879 proof stood eleven years before Heawood found the error in 1890 — worth
remembering. **THEOREM (Appel–Haken, announced 1976, published *Illinois J. Math.* 21 (1977), in two
parts, the reducibility half with Koch).** Their reduction produced an *unavoidable set* of 1936
*reducible configurations*: unavoidable means every planar map contains one, reducible means a map
containing one shrinks to a smaller counterexample — so a minimal counterexample cannot exist if
every configuration checks out, which is what the computer did. Cut to 633 configurations by
**Robertson–Sanders–Seymour–Thomas (1997)** and formalised end-to-end in **Coq by Georges Gonthier
(2005, with Benjamin Werner)** — reduction *and* checking, machine-verified.

**Kepler** (no packing of equal spheres beats face-centred cubic, `π/√18 ≈ 74.05%`).
**THEOREM (Hales, announced 1998; published *Ann. of Math.* 162 (2005), 1065–1185).** The reduction
turns the infinite packing problem into a finite optimisation over local configurations, closed with
interval arithmetic and on the order of a hundred thousand linear programs. The referees famously
reported roughly 99% confidence and declined to certify the computational part — this mechanism's
honest scar. Hales answered with **Flyspeck**, completed **August 2014** (HOL Light and Isabelle;
*Forum of Mathematics, Pi* 5 (2017)).

The repo-relevant point: interval arithmetic is what separates a *computation* from a *theorem*.
`docs/08` §3.1 draws the same line between Platt–Trudgian and earlier zero-verification
announcements, and `zeta/rigor.py` sits on that seam.

---

## 4. ANALYTIC-COMPUTATIONAL SQUEEZE — weak (ternary) Goldbach

**Mechanism: prove "true for all `n > N₀`" with `N₀` *effective*, then drag `N₀` down while
certified computation climbs up, until the two ranges overlap.**

**THEOREM (Vinogradov, 1937).** Every sufficiently large odd integer is a sum of three primes. The
original statement was asymptotic; Borozdkin later extracted an explicit threshold around `3^(3^15)`,
roughly seven million digits (widely quoted, usually dated 1956; check the source). Liu and Wang
(2002) got it to about `e^3100 ≈ 10^1346` (conversion confirmed: `3100/log 10 = 1346.3`). Hopeless.

**THEOREM (Helfgott, arXiv:1312.7748, December 2013).** Threshold `10^27`. Combined with
**Helfgott–Platt, "Numerical verification of the ternary Goldbach conjecture up to `8.875·10^30`"
(*Experimental Mathematics* 22 (2013), 406–409)**, the ranges overlap and the conjecture is closed.
*(Accepted by the community; my understanding is that the complete proof has circulated mainly as
arXiv preprints and a book manuscript rather than one refereed journal article — verify the current
publication status before citing it as such.)*

Two things to take. The **margin**: `10^27` against `8.875·10^30` is nearly four orders of *slack* —
squeezes close because somebody buys overlap, not a knife-edge. And the **ingredient**: Helfgott's
major-arc analysis leans on rigorous interval-arithmetic verification of zeros of Dirichlet
L-functions — the same species of certified data `zeta/rigor.py` produces for `ζ` itself, one family
over. The cleanest existing case of the unglamorous work in `docs/08` §6 item 1 becoming a theorem:
not evidence, an *input*.

---

## 5. FLOW + SINGULARITY CONTROL — the Poincaré conjecture

**Mechanism: do not attack the object. Deform it by a flow that provably simplifies it, and do the
real work at the places where the flow blows up.**

**PROGRAM → THEOREM. Hamilton (*J. Differential Geom.* 17 (1982), 255–306)** introduced **Ricci
flow**, `∂g/∂t = −2·Ric(g)`: a heat equation for the metric itself. Curvature diffuses, bumps flatten,
and a manifold left alone wants to become one of a short list of round model geometries. Hamilton's
programme was to run the flow and read off the classification — with one obstruction everybody could
name: the flow develops **singularities** in finite time (necks pinch off), and the argument dies.

**THEOREM (Perelman, three arXiv preprints: math/0211159, November 2002; math/0303109, March 2003;
math/0307245, July 2003).** Singularity control, via a monotone entropy functional (a Lyapunov
function — a quantity that can only move one way, so the flow cannot cycle or hide), a
no-local-collapsing theorem, a classification of singularities up close, and **surgery**: cut at the
pinch, cap it, restart, with uniform bounds guaranteeing you do this only finitely often on any
bounded time interval. Independent expositions followed (Kleiner–Lott; Cao–Zhu; Morgan–Tian).

**Emphasise this, because the repo has a stake in it: a heat-type flow closed a Millennium problem.**
`docs/05-de-bruijn-newman.md` runs a heat flow *on* `Ξ` — the family `H_t` with `H_0 ∝ Ξ` — and the
shape is identical: the flow smooths (for `t` large enough all zeros are real, de Bruijn 1950), the
obstruction is singularities (zeros colliding and leaving the real axis, `docs/05` §4), and
everything turns on the critical time.

The asymmetry matters too. Ricci flow ran *forward*, with time to spare. RH asks about `H_t` at
exactly `t = 0`, and by **THEOREM (Rodgers–Tao, 2018/2020), `Λ ≥ 0`**, so `Λ = 0` *is* RH: no
smoothing budget at all. `docs/07` §11's blunt corollary — whatever proves RH must be exactly tight,
which rules out every argument with room to spare.

---

## 6. INSIGHT LAPPING THE COMPUTERS — Catalan's conjecture

**Mechanism: the honest counterweight to §3 and §4 — a squeeze can be fully set up, grinding, and
still be the wrong strategy, because structural insight can make the computation irrelevant.**

**CONJECTURE (Catalan, 1844 — the date usually given for his note to Crelle; I have also seen 1842
cited).** The only consecutive perfect powers are `8` and `9`: the only solution of `x^p − y^q = 1`
in integers `> 1` is `3² − 2³ = 1` (yes, `9 − 8 = 1`).

**THEOREM (Tijdeman, 1976).** Solutions are effectively bounded — precisely a §3-style finite
reduction, and celebrated as such. The bound was astronomical, so a twenty-six-year §4-style squeeze
began: narrow the exponent range analytically from above (Mignotte's bounds, commonly quoted as
`p < 7.15·10^11`, `q < 7.78·10^16` — widely cited figures, worth checking at source) while
computation pushed up from below. The gap stayed many orders wide.

**THEOREM (Mihăilescu, announced April 2002; "Primary cyclotomic units and a proof of Catalan's
conjecture", *J. reine angew. Math.* 572 (2004), 167–195).** Closed with the algebra of cyclotomic
fields — Galois modules over group rings, Stickelberger, Thaine — and no computation at all.

Twenty-six years of the mainstream strategy were bypassed. Keep this next to §3 and §4 as a permanent
corrective: "the computers are closing in" describes one strategy's progress, not the problem's.

---

## 7. EQUIVALENCE WEB + OUTSIDER TOOLKIT — Kadison–Singer

**Mechanism: a problem restated a dozen times across unrelated fields becomes *searchable* by all of
them; the killing tool arrives from a field that never cared about the original question.**

**Kadison–Singer (1959, *Amer. J. Math.* 81)**: does every pure state on the diagonal subalgebra of
bounded operators on `ℓ²` extend uniquely to the whole algebra? (A *state* is a normalised positive
linear functional — an abstract "expected value" assigning a number to each observable; *pure* means
it is not an average of two different ones, i.e. it carries no residual uncertainty of its own. Roots
in Dirac: do commuting observables determine a state?) Fifty-four years open, acquiring equivalent
formulations in operator
algebras (Anderson's paving conjecture, 1979), Banach space theory (Bourgain–Tzafriri restricted
invertibility), signal processing (the Feichtinger conjecture on frames) and discrepancy theory —
**Weaver's `KS_r`** (*Discrete Math.* 278 (2004)), about partitioning vectors so no part is
spectrally heavy.

**THEOREM (Marcus–Spielman–Srivastava, arXiv:1306.3969, June 2013; *Ann. of Math.* 182 (2015),
327–350).** Weaver's `KS₂`, hence Kadison–Singer. The method: **interlacing families** of polynomials
and *mixed characteristic polynomials*, top eigenvalue controlled by a barrier argument resting on
**real stability** (Borcea–Brändén). Stripped to the mechanism: *they bounded eigenvalues by proving
a polynomial had all real roots and then bounding the largest one.* All three authors came from
theoretical computer science; the machinery had just been built in the companion paper (*Interlacing
Families I*) to construct Ramanujan graphs, which nobody in operator algebras was watching.

The RH parallel is exact in form. `docs/07` catalogues RH's own web — error terms, Mertens, Riesz,
Li, Nyman–Beurling, Robin/Lagarias, Weil positivity, Speiser, de Bruijn–Newman — and
`zeta/criteria.py` makes several computable; RH also has a **real-rootedness face**, the subject of
`zeta/li.py`. But read `docs/07` §11 before celebrating: abundance of equivalences is evidence RH is
*true and deep*, and weak evidence it is nearly *proved*. Kadison–Singer's web paid after fifty-four
years, and only because one restatement happened to be in the native language of a tool invented for
something else.

---

## 8. Scoring RH against the board

### 8.1 The mechanisms RH's live formulations touch

**Flow (§5) — yes, and a real research frontier.** `docs/05` and `zeta/heatflow.py`: `H_t`, the
de Bruijn–Newman constant, `RH ⟺ Λ = 0` with `Λ ∈ [0, 0.2]` pinned from both sides. By `docs/07`
§11's productivity filter — an equivalence pays only if it yields something *without* proving RH —
this is one of only three items in that catalogue that has paid, because Rodgers–Tao's `Λ ≥ 0` is a
genuine new theorem. The missing piece is `docs/09` §7's: our flow acts on a *function*, not a space.
Ricci flow deforms a geometry; there is no geometry under `H_t`.

**Equivalence web (§7) — yes, extensively.** `docs/07` plus `zeta/criteria.py`, with §11's standing
question against each new entry: *where did the hard part go?* There is always an answer.

**Real-rootedness (§7's actual weapon) — yes, and computable.** The closest structural contact on the
board, worth pinning with numbers.

> **THEOREM (Pólya, 1927).** For an entire function of the appropriate growth class, having only real
> zeros is equivalent to hyperbolicity (all roots real) of every associated **Jensen polynomial**.
> Applied to `Ξ`, this makes RH exactly a real-rootedness statement.

Derived, not remembered, in the repo's own normalisation, so nothing depends on the literature's
conventions. `zeta.heatflow.Phi` satisfies `H₀(z) = ∫₀^∞ Φ(u) cos(zu) du = Ξ(z/2)/8`; expanding the
cosine with moments `b_n = ∫₀^∞ Φ(u) u^{2n} du` gives `H₀(z) = g(−z²)`, `g(x) = Σ (b_n/(2n)!) x^n`,
so RH ⟺ `g` has only real negative zeros. Writing `g(x) = Σ γ(n) x^n/n!` fixes `γ(n) = n!·b_n/(2n)!`
and `J^{d,n}(X) = Σ_{j≤d} C(d,j)·γ(n+j)·X^j`; degree 2 is hyperbolic exactly when the **Turán
inequality** `γ(n+1)² ≥ γ(n)·γ(n+2)` holds. (`zeta/li.py` computes `γ(n)` in the
Griffin–Ono–Rolen–Zagier normalisation, `8·ξ(½+z) = Σ γ(n) z^{2n}/n!`, which is this one times
`64·4ⁿ` — checked, not assumed. A positive factor per `n` rescales `X` and the polynomial as a
whole, so hyperbolicity and the ratios below are the same in either convention.) Measured at
`dps = 40`, the ratio
`γ(n+1)²/(γ(n)γ(n+2))` for `n = 0…7`:

```
    1.0748  1.0627  1.0543  1.0481  1.0432  1.0393  1.0362  1.0335
```

Above 1 — which is exactly the Turán inequality holding — and *shrinking toward 1*. `J^{d,n}` for
`d = 3,4,5` at `n = 0,2,4` also came out hyperbolic, largest `|Im(root)|` at machine-zero (measured
2.3e-132 at `dps = 30`, and the exact Sturm count in ℚ[X] agrees in every case). The known theory:
**THEOREM (Csordas–Norfolk–Varga, *Trans. AMS* 296 (1986), 521–541)** — the Turán inequalities
(`d = 2`) hold unconditionally; **THEOREM (Dimitrov–Lucas, *Proc. AMS* 139 (2011), 1013–1022)** —
`d = 3`; **THEOREM (Griffin–Ono–Rolen–Zagier, *PNAS* 116 (2019), 11103–11110)** — for *each* degree
`d`, `J^{d,n}` is hyperbolic for all sufficiently large `n`, which leaves a finite unresolved set for
every `d`, and RH needs all of them. Same shape as "a positive proportion of zeros on the line"
(`docs/08` §1.3): a real theorem on a different axis.

Note also what Marcus–Spielman–Srivastava had that we do not: a finite, explicitly constructed
polynomial family. RH's Jensen family is doubly infinite, and by `docs/07` §4 its coefficients are as
hard as the thing you wanted — computing them honestly needs the zeros. `zeta/li.py` computes them
anyway, because watching the margin shrink is the point.

### 8.2 The mechanisms RH does not fit — stated plainly

**Finite reduction (§3) — no.** That mechanism needs a *reduction theorem*: a proof that the infinite
claim follows from a finite explicit list. RH has none. There is no theorem "every zero with
`|γ| > T` lies on the line" for any `T`, and nobody expects one — the zero-free regions of `docs/08`
§1.1 all *shrink* with height, the opposite of what a reduction needs. Without one there is nothing
to grind, however large the machine.

**Effective-threshold squeeze (§4) — no, for that reason plus a second.** Vinogradov's theorem has
the form "true above `N₀`," so lowering `N₀` is measurable progress; RH has no `N₀`-shaped statement
to lower, hence no front coming down to meet the computation. And the computation is barely moving:
by `docs/08` §3.2 the fluctuation carrying the risk is `S(T) = (1/π)·arg ζ(1/2 + iT)`, of typical
size `√(log log T / 2π²)` — about `0.415` at `T = 10^13`, `0.446` at `T = 10^22`; doubling it needs a
height with roughly 350,000 decimal digits. Weak Goldbach closed with four orders of margin; here the
deficit is unbounded. **So verification to any height decides nothing** — `docs/08` §3, now with a
structural reason rather than an assertion, and with Littlewood and Mertens (§3.3–3.4 there) as
proof that unanimous numerics in this subject have in fact been wrong.

One qualification, cutting the other way: certified verification height is useless as *evidence* and
valuable as an *input*. Feeding Platt–Trudgian's `3·10^12` into the Polymath15 machinery is what
gives `Λ ≤ 0.2` (`docs/05` §3), and Platt's certified L-function zeros are an ingredient in
Helfgott's theorem (§4). That is the whole justification for `zeta/rigor.py`: not a squeeze on RH, a
supplier to other people's theorems.

**Bridge to a richer world (§2) — partial at best.** The Selberg class and Langlands organise `ζ`
into a family (`docs/09` §3, §6), a genuine bridge — but no formulation of functoriality is known to
imply RH, and there is no Ribet.

**Ontology rebuild (§1) — yes, the field's own leading bet.** `docs/09`, `docs/10`, `docs/11`:
fifty-plus years with the blueprint in hand, and still no space, no operator with a home, no
positivity. **Insight lapping the computers (§6) — the null case:** there is nothing to lap.

---

## Where to go next

- **`docs/08-why-it-is-hard.md`** §3 — the numerics argument, which §8.2 has now given a structural
  reason; and §4.3, the two-sided counterexample test.
- **`docs/09-new-ontologies.md`** §1 with **`docs/11-f1-and-the-missing-geometry.md`** — §1 of this
  document at full length, plus the four falsification gates for a proposed rebuild.
- **`docs/05-de-bruijn-newman.md`** and `zeta/heatflow.py` — the flow mechanism live, with the
  collision picture that is our analogue of Perelman's singularities.
- **`docs/07-equivalences-and-criteria.md`** §4 and §11, with `zeta/criteria.py` and `zeta/li.py`.
- **`zeta/finitefield.py`** — the one proven RH, computable. Worth an hour, because it is the only
  place in this repository where the answer is known.
