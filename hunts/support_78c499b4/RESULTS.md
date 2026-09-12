# ARM E: prior art on the certificate route, and on the LP-versus-truth gap

**Support run `78c499b4`, 2026-08-24, for run `872d7dce` (`hunts/r_c7f779`).**
This is the prior-art page the brief called `arm_e/PRIOR-ART.md`. It lives here
because this run may not write into another hunt's directory.

**Status: settled as far as a literature question can be settled in one search
pass.** Nothing here is a mathematical claim, nothing is measured, and nothing
bears on RH (`docs/08`).

---

## 0. Verdict first

**The route is untouched in the literature in its exact form, and it is live,
not known-dead.** No published work applies a Cohn–Elkies/Delsarte certificate
to an `f` of the shape `max(0, band-limited) - band-limited square`, and no
published theorem decides whether the LP value equals the lattice value for
such an `f`.

But three published facts bear on it directly, and two of them change what
`r_c7f779` should expect:

1. **Non-band-limitedness of the target is not an obstruction and is not
   novel.** The Cohn–Kumar energy LP is routinely run against non-band-limited
   targets (completely monotone potentials are not band-limited), and the
   Cohn–Elkies test-function class has already been used in *exactly* the
   parent's setting: a one-dimensional pair sum over the zeros of `zeta`
   (Carneiro–Milinovich–Ramos, arXiv:2310.01913, whose abstract says in so
   many words that they make "full use of the class of test functions
   introduced by Cohn and Elkies for the sphere packing bounds, going beyond
   the usual class of bandlimited functions"). The parent's route is a known
   *kind* of move applied to a new `f`.
2. **In dimension 1 the LP for energy is sharp against the lattice, but only
   for completely monotone potentials.** Cohn–Kumar proved the universal
   optimality of `Z` by constructing magic functions that meet the tightness
   conditions of their own LP bound, via a variant of the Whittaker–Shannon
   sampling formula. The parent's `f` is not a completely monotone function of
   squared distance: it oscillates and changes sign. **The published dimension-1
   sharpness theorem does not cover it.**
3. **For non-convex one-dimensional potentials the equidistant lattice is not
   always the ground state.** Ventevogel and Nijboer exhibited `phi(x) =
   (1+x^4)^{-1}`, for which the minimising configuration at high density is
   *not* equally spaced. So no theorem of the form "in dimension 1 the LP value
   equals the lattice value" can exist in the generality the parent needs. Any
   such statement must first assume, or prove, that the lattice is the true
   optimum for that particular `f`, which for the parent is currently a
   measurement from a finite search (run `37fb06a9` §3), not a theorem.

The practical consequence for `r_c7f779`: **nobody's theorem will decide your
question, so stop looking for one.** There is, however, published *technology*
aimed squarely at the direction that would kill the route with a witness, and
it is not the technology the parent is currently using. See §4.

---

## 1. What was searched, and how

Backends actually used, named so a stranger can judge the coverage:

* **`WebSearch`** (the Claude Code web-search tool), 9 queries, listed below
  verbatim.
* **`WebFetch`** (URL to markdown, extraction by a small model) on 7 pages.
* **The arXiv Atom API**, `https://export.arxiv.org/api/query?id_list=...`,
  by `curl`, for exact titles, author lists, submission dates, `journal_ref`
  and DOI on 14 preprints. Every arXiv id below was resolved this way rather
  than from memory.
* **`pdftotext -layout`** locally on two fetched PDFs (Cohn's PCMI notes,
  arXiv:1603.05202; Radchenko's Bourbaki-style overview of CKMRV), because the
  extraction model could not read the raw PDF byte stream. The quotations in
  §3 and §5 are from those text conversions.

Backends **not** used, and therefore not evidence: MathSciNet, zbMATH,
Google Scholar, `ontology/knownness.py` and its OEIS/arXiv/zbMATH backends.
The repository's own `references/papers.md` was grepped for
`cohn|elkies|delsarte|packing|viazovska|carneiro|beurling|selberg` and returned
**zero lines**: none of this literature is currently tracked in this tree.

The queries, verbatim:

1. `linear programming bound energy dimension 1 sharp integer lattice Cohn-Kumar universal optimality`
2. `Cohn Elkies linear programming bound sharp dimension 1 duality gap Delsarte`
3. `Beurling-Selberg extremal problem majorant positive part max(0,x) band-limited Vaaler Graham one-sided approximation`
4. `Cohn "Packing, coding, and ground states" linear programming bounds energy dimension one sharp Z lattice not sharp`
5. `Gorbachev Ivanov Tikhonov Delsarte extremal problem one dimension linear programming bound sharpness`
6. `linear programming bound energy general potential not completely monotone gap one dimension Cohn Kumar "universally optimal" proof magic function sampling`
7. `Ventevogel Nijboer one-dimensional ground state configuration not equidistant lattice non-convex potential`
8. `Fourier optimization sign conditions extremal problem Riemann zeta pair correlation Carneiro Chirre Milinovich linear programming`
9. `extremal majorant positive part of a bandlimited function nonnegative Fourier transform one-sided approximation obstruction kink`
10. `Cohn de Laat Salmon "no duality gap" Cohn-Elkies linear program sphere packing strong duality proof`

Query 9 is the load-bearing negative: it is the one aimed at the parent's
specific `max(0, ·)`-of-a-band-limited-function target, and it returned only
the classical Beurling–Selberg corpus, nothing on that composition. See §5.

---

## 2. PART 1(a): has the certificate been applied to an `f` of this shape?

**Not to this `f`. To the same class of test functions, in the same dimension,
against the same kind of object, yes.**

The framework itself:

* **Cohn and Elkies, "New upper bounds on sphere packings I"**, Annals of
  Mathematics **157** (2003), 689–714, arXiv:`math/0110009`,
  DOI `10.4007/annals.2003.157.689`. The continuous analogue of Delsarte's LP.
* **Cohn and Kumar, "Universally optimal distribution of points on spheres"**,
  J. Amer. Math. Soc. **20** (2007), 99–148, arXiv:`math/0607446`,
  DOI `10.1090/S0894-0347-06-00546-7`. Extends the LP to potential-energy
  minimisation; the Euclidean-space extension is in its concluding section.
* **Cohn, Kumar, Miller, Radchenko, Viazovska, "Universal optimality of the
  `E_8` and Leech lattices and interpolation formulas"**, arXiv:`1902.05438`,
  Annals of Mathematics **196** (2022). "The proof uses sharp linear
  programming bounds for energy."
* **Cohn, "Packing, coding, and ground states"** (PCMI 2014 lecture notes),
  arXiv:`1603.05202`. The readable statement of both bounds and of their
  sharpness conditions.

The closest published application to the parent's actual object:

* **Carneiro, Milinovich, Ramos, "Fourier optimization and Montgomery's pair
  correlation conjecture"**, arXiv:`2310.01913` (submitted 2023-10-03). This is
  a one-dimensional pair-interaction functional over the non-trivial zeros of
  `zeta`, bounded by an extremal problem with sign conditions on the test
  function and on its Fourier transform, solved numerically by semidefinite
  programming. Its extremal problem EP1 is: minimise `rho_1(g)/g(0)` over
  continuous even `g >= 0` with `g, ghat in L^1` and **`ghat(alpha) <= 0` for
  `|alpha| >= 1`**, where `rho_1(g) = ghat(0) + int_{-1}^{1} ghat(alpha)
  |alpha| d alpha`. That is a Cohn–Elkies-shaped sign constraint on the
  transform, not a band-limitedness constraint, and the paper's stated novelty
  is precisely dropping band-limitedness in favour of the Cohn–Elkies class.
* **Carneiro, Milinovich, Soundararajan, "Fourier optimization and prime
  gaps"**, Comment. Math. Helv. **94** (2019), 533–568, arXiv:`1708.04122`,
  DOI `10.4171/CMH/467`.
* **Carneiro, Chandee, Chirre, Milinovich, "On Montgomery's pair correlation
  conjecture: a tale of three integrals"**, J. reine angew. Math. (Crelle),
  February 2022. Same programme, earlier, with band-limited majorants.
* **Das, Ismoilov, Ramos, "Fourier optimization and pair correlation
  problems"**, arXiv:`2502.05106` (2025-02-07). Generic framework for pair
  correlation of sequences via two Fourier extremal problems.

**What none of them does:** run the LP against a target built as
`max(0, D) - K` with `D` band-limited. In the Fourier-optimization corpus the
non-band-limited object is always the *test function* class being widened; the
majorised target is a fixed, classical function (`sgn`, an indicator, a
Gaussian, `|x|^alpha`). I found no paper whose target is a positive part of an
oscillating band-limited function.

**Is the LP bound tight against the periodic-lattice optimum in dimension 1?**
Two separate published answers, and the parent needs the second one:

* *For packing*, dimension 1 is sharp and trivially so. Cohn's PCMI notes,
  Lecture 5: "Linear programming bounds seem not to be sharp in `R^n` except
  when `n = 1, 2, 8, or 24`. [...] The `n = 1` case follows from Exercise 4.1".
  Rupert Li (arXiv:`2206.09876`) puts it more bluntly: "The case `d=1` is
  trivial (consecutive line segments cover all of `R`)."
* *For energy*, dimension 1 is sharp **for completely monotone potentials**,
  and the proof is by explicit magic functions. Radchenko's overview of CKMRV
  states it exactly: "Cohn and Kumar [5] proved the universal optimality of the
  integer lattice in dimension 1 by constructing magic functions `f` satisfying
  the tightness conditions of their linear programming bound. Their
  construction crucially relied on the Whittaker-Shannon sampling formula". The
  original optimality result (by a different, non-LP argument) is
  **Ventevogel and Nijboer**, cited in CKMRV's introduction as having "proved
  that the integer lattice `Z` in `R` minimizes energy for every completely
  monotonic function of squared distance".

So the honest reading for `r_c7f779`: in dimension 1 the LP *can* be sharp
against the lattice, it has been made sharp, and the mechanism is known. That
is a reason to expect `V` to be reachable rather than a reason to expect a gap.
It is **not** a theorem that applies to the parent's `f`.

---

## 3. PART 1(b): the non-band-limited, positive-part target

Three things to separate, because the brief's phrasing runs them together.

**(i) Non-band-limited targets are the normal case, not the hard case.** In
Cohn–Kumar the majorised object is a potential `p(|x|)` that is completely
monotone in the squared distance (inverse power laws, Gaussians). None of those
is band-limited. The auxiliary function `f` is not band-limited either. There is
no published obstruction to running the LP against a non-band-limited target,
and it would be an error to report one.

**(ii) The technology for majorising awkward targets exists and is mature, but
its constraint is the wrong one.** The Beurling–Selberg corpus solves exactly
"majorise this non-band-limited `F` optimally in `L^1`" for a long list of `F`,
including the truncated/positive-part family:

* Beurling (late 1930s, unpublished) and Selberg: `sgn(x)` and indicators of
  intervals.
* Graham and Vaaler: the truncated and odd families including `x_+ = max(0,x)`.
* **Carneiro, Littmann, Vaaler, "Gaussian subordination for the
  Beurling–Selberg extremal problem"**, Trans. Amer. Math. Soc. **365** (2013),
  3493–3534, arXiv:`1008.4969`, DOI `10.1090/S0002-9947-2013-05716-9`. Solves
  the majorant/minorant problem for a wide class of even functions by
  subordination to the Gaussian, covering `|x|^alpha` for `alpha > -1`,
  `log((x^2+a^2)/(x^2+b^2))`, and more.
* Survey: **Carneiro and Littmann, "A survey on Beurling–Selberg majorants and
  some consequences of the Poisson summation formula"**, Matemática
  Contemporânea (SBM).

But every one of these constrains the *support* of the transform (exponential
type / band-limitedness) and optimises the `L^1` error. The parent's constraint
is a *sign* condition on the transform (`Ghat <= 0`) with no support
restriction. Those are different cones, and the Beurling–Selberg extremal
functions are not solutions to the parent's program. The huntspec already
records that the band-limited Fejér certificates fall short by 1.156 with a
frequency-domain witness, which is consistent: it is a statement about the
wrong cone.

**(iii) The specific composition `max(0, D(·))` with `D` band-limited: nothing
found.** Query 9 was aimed at it and returned only the classical corpus above,
plus unrelated hyperboloid and super-resolution work. I found **no** paper on
one-sided approximation to the positive part of an oscillating band-limited
function, under either a support constraint or a transform-sign constraint,
and **no** published obstruction specific to that shape.

That is a genuine absence in what I searched, and it is not a proof of absence:
one web-search backend and no MathSciNet/zbMATH is a thin search for a
negative. Treat it as "not found in a targeted search using the obvious terms",
which is what it is.

---

## 4. PART 2: is there a theorem that decides LP value versus lattice value?

**No theorem that covers the parent's `f`, and provably none can exist at that
level of generality.** But the sharpness criterion the brief asks about is
published, explicit, and checkable, and there is a published method for
producing the kill witness.

**(a) The sharpness criterion is published and is exactly the
"dual optimiser on the distance set" statement.**

For packing (Cohn's PCMI notes, Lecture 5, immediately after Conjecture 4.2):

> "Examining the proof of Theorem 3.1 shows that the auxiliary function `f`
> proves a sharp bound for a lattice `Lambda` iff `f(x) = 0` for all
> `x in Lambda \ {0}` and `fhat(t) = 0` for all `t in Lambda* \ {0}`. In other
> words, all we have to do is to ensure that `f` and `fhat` have certain roots
> without developing any unwanted sign changes."

For energy, CKMRV state the conditions in their introduction as (1.2)/(1.3):
`f(x) = p(|x|)` for all `x in Lambda \ {0}`, and `fhat(y) = 0` for all
`y in Lambda* \ {0}`, holding to second order in the radial variable.

This is complementary slackness: contact of the majorant with the target on the
primal lattice's distance set, and vanishing of the transform on the dual
lattice.

**(b) Strong duality for these programs is now published**, so "LP value" is a
well-defined number approachable from both sides:

* **Cohn, de Laat, Salmon, "Three-point bounds for sphere packing"**,
  arXiv:`2206.15373` (2022-06-30), proved the absence of a duality gap for the
  Cohn–Elkies linear program, a fact conjectured by Cohn. Rupert Li's paper
  states the attribution directly: "The lack of a duality gap for the
  Cohn-Elkies linear program was conjectured by Cohn and proven by Cohn, de
  Laat, and Salmon."
* **Kolountzakis, Lev, Matolcsi, "The Turán and Delsarte problems and their
  duals"**, arXiv:`2510.10172` (2025-10-11). Weak and strong duality in the
  continuous setting for the Turán and Delsarte extremal problems, existence of
  extremisers for primal and dual, and "tiling-type relations between the
  extremal functions for each problem and the extremal measures or
  distributions for the dual problem". This is the general-purpose version of
  the sharpness question the parent is asking, and the parent's program is a
  Delsarte problem with a general majorant constraint rather than the standard
  `Phi <= 0 outside a ball` constraint.
* Existence of the Delsarte extremiser: **Gorbachev, Ivanov, Tikhonov**, "On
  the existence of an extremal function in the Delsarte extremal problem",
  Mediterr. J. Math. **17** (2020), and follow-ups (arXiv:`2407.04410`,
  Analysis Mathematica 2025).

**(c) Why no theorem can decide it in the stated generality.** The dual
feasible set is a cone of positive measures/distributions, and it is strictly
larger than the set of autocorrelations of point configurations. That is the
standard source of LP looseness. In dimension 1 that looseness is not merely
theoretical for oscillating potentials, because the *primal* side also fails:

* **Ventevogel, "On the configuration of a one-dimensional system of
  interacting particles with minimum potential energy per particle"**,
  Physica A **92** (1978), 343–361; **Ventevogel and Nijboer**, same title,
  Physica A **98** (1979), 274–288 (part II) and Physica A **99** (1979),
  569–580 (part III). Part II extends the class of two-body potentials for
  which equidistance is proved; the counterexample `phi(x) = (1+x^4)^{-1}`,
  whose ground state at high density is *not* equally spaced, is theirs.
* **Roni Edwin, "Distribution of points on the real line under a class of
  repulsive potentials"**, arXiv:`2405.11428`, Pure Appl. Math. Q. **21**
  (2025), 2321ff, DOI `10.4310/PAMQ.251222233001`. Proves the clustering
  ground state for `f_alpha(x) = (1+x^alpha)^{-1}`, `alpha > 2` even, and cites
  Ventevogel–Nijboer as the origin.
* **Bétermin, Šamaj, Travěnec, "Equidistant versus bipartite ground states for
  1D classical fluids at fixed particle density"**, arXiv:`2502.16639`,
  Analysis and Mathematical Physics **15** (2025), no. 88. A second-order
  transition from the equidistant chain to a bipartite chain at a critical
  spacing.

So "in dimension 1 the lattice is the optimum" is *false* as a general
statement, hence "in dimension 1 the LP value equals the lattice value" cannot
be a theorem for general `f`. Run `37fb06a9` §3 established lattice extremality
for this `f` by a finite search with demonstrated power, which is the right
evidence, but it is a measurement and the literature says that measurement is
exactly the kind that can fail for a non-convex `f`.

**(d) The published method that would kill the route with a witness.** This is
the one item in this page that is directly actionable, and it is not what the
parent is doing.

* **Rupert Li, "Dual Linear Programming Bounds for Sphere Packing via Discrete
  Reductions"**, Adv. Math. **460** (2024), 110043, arXiv:`2206.09876`,
  DOI `10.1016/j.aim.2024.110043`. Maps feasible points of the
  infinite-dimensional Cohn–Elkies LP into a finite-dimensional problem by
  restricting `f` to a lattice and `fhat` to a discrete torus, then solves the
  *dual* of the finite problem. A dual-feasible point is a **lower bound on the
  LP value**, and if it exceeds the target it proves the LP cannot be sharp.
  Li used it to prove the Cohn–Elkies bound cannot reach the best known
  densities in dimensions `3 <= d <= 13` except `d = 8`.
* Same technique via modular forms: **Cohn and Triantafillou**, "Dual linear
  programming bounds for sphere packing via modular forms" (`d = 12, 16, 20,
  28, 32`); extended to `d = 36` by **Jumagulov**, arXiv:`2607.11319` (2026).

The parent's kill condition 1 asks for "a re-solved, well-conditioned LP whose
value exceeds `0.06750841`". A *primal* LP value is a lower bound on the true
LP value only because truncation relaxes the program, and run `37fb06a9`
already found that this lower bound sits below the achievability floor, so it
carries no content. **The discrete-reduction dual is the published way to get a
lower bound on `V` that does carry content**, and it is finite-dimensional by
construction, which is also an answer to the conditioning failure at
`s_max = 400, 600`.

---

## 5. What I did NOT find

Stated explicitly, because a failed search is not an absence of prior art.

1. **No** paper applying a Cohn–Elkies/Delsarte certificate to a target of the
   form `max(0, D) - K` with `D` band-limited.
2. **No** paper on one-sided approximation to the positive part of a
   band-limited function, under a transform-sign constraint or a
   band-limitedness constraint.
3. **No** published obstruction specific to positive-part targets. The
   obstructions I did find are about non-sharpness in particular dimensions
   (Li; Cohn–Triantafillou; Jumagulov), not about target regularity.
4. **No** theorem asserting "LP value = lattice value in dimension 1" for
   potentials outside the completely monotone class.
5. **No** dual-bound computation in the literature for a one-dimensional energy
   LP. All the published discrete-reduction dual bounds are for packing in
   `d >= 3`; dimension 1 is dismissed as trivial in the packing setting, so
   nobody has run the machinery there.
6. **Nothing** was checked in MathSciNet, zbMATH or Google Scholar, and
   `ontology/knownness.py` was not run. Items 1 to 5 are "not found by the
   searches in §1", not "does not exist".

---

## 6. Two remarks derived here, flagged as not prior art

These are consequences of the *published* criterion in §4(a) transported into
the parent's parametrisation. They are cheap for the parent to check and they
are **mine, not the literature's**. I did not find either in what I searched,
and I did not verify either numerically.

**(R1) The required contact set avoids the kinks, so the positive part does not
obstruct tightness at the lattice.** If `G` is differentiable at `s0` and
`G >= f` with `G(s0) = f(s0)`, then `G'(s0) <= f'(s0-)` and `G'(s0) >=
f'(s0+)`. At a point where `D` crosses zero upward, `f = max(0,D) - K` has
`f'(s0-) = -K'(s0)` and `f'(s0+) = D'(s0) - K'(s0)` with `D'(s0) > 0`, so both
inequalities cannot hold: **a differentiable majorant can never touch `f` at an
upward kink of the positive part.** In the parent's parametrisation `G(s) =
- int mu(w) cos(sw) dw`, `G` is differentiable whenever `int w mu(w) dw <
infinity`, and is real-analytic whenever `mu` has compact support. So a
compactly supported `mu` (which is what a bounded frequency grid gives) can
*never* achieve contact at a kink; contact there requires a Fejér-tailed `mu`
with divergent first moment, e.g. `mu(w) ~ c/w^2`.

  This looks like bad news and is not, because of a fact the parent already
  measured. Run `37fb06a9` §2 records `P = 0` on the critical lattice out to
  `d = 4000`, i.e. every multiple of `2 pi` lies **inside** a depth-1 damage
  window. If "inside" means `D > 0` strictly there, then `f` is smooth at every
  point of `2 pi Z \ {0}`, which is exactly the set where complementary
  slackness demands contact. **The kinks are not on the contact set.** That is
  a positive signal for the route and it costs nothing to confirm: check
  `D(1, 2 pi d) > 0` strictly, not just `>= 0`.

**(R2) A concrete, falsifiable prediction for the optimal measure.** Transport
the §4(a) criterion to `Lambda = 2 pi Z`. Its dual lattice under the
`e^{-2 pi i s xi}` convention is `(1/2 pi) Z`, and `Ghat` is carried by
`w = 2 pi |xi|`, so `Ghat(xi) = 0` for `xi in Lambda* \ {0}` becomes

> **`mu(w) = 0` for every nonzero integer `w`.**

Together with (R1) this says: if `V` equals the lattice value `L/2 =
0.05716501969327026`, then an optimal `mu` puts **no mass on the positive
integers** and the optimal `G` touches `f` on **all of `2 pi Z \ {0}`**.
Contrapositive, which is the usable direction: **if a well-conditioned solve
returns an optimal `mu` that insists on charging the integers, or an optimal
`G` whose contact set is not `2 pi Z \ {0}`, then `V` is strictly above the
lattice value** and the parent is somewhere in the 15% window rather than at
its floor. That is a diagnostic on solver output the parent already produces,
and it discriminates before the horizon ladder converges.

---

## 7. The one-paragraph verdict

**Untouched, and live.** The certificate route as `r_c7f779` has posed it has
not been published: no one has run a Cohn–Elkies/Delsarte LP against a
positive-part-of-band-limited target, and no theorem in the literature decides
whether its value equals the one-dimensional lattice value for such a target.
The route is not known-dead: the two things that would kill it a priori both
fail to apply. Non-band-limitedness of the target is routine in this framework
rather than an obstruction, and dimension 1 is the dimension where the energy
LP has actually been made sharp against the lattice, by Cohn and Kumar, via
Whittaker–Shannon magic functions. The route is also not known-live, and the
reason is sharper than "nobody has tried": the published dimension-1 sharpness
theorem is restricted to completely monotone potentials, and outside that class
dimension 1 has published counterexamples where the equidistant lattice is not
even the ground state (Ventevogel–Nijboer's `(1+x^4)^{-1}`), so the parent's
lattice extremality is a finite-search measurement that the literature says is
exactly the sort that can fail. The single most useful transfer from the
literature is not a theorem but a method: Rupert Li's discrete-reduction dual
bounds (Adv. Math. 2024) give finite-dimensional *lower* bounds on the value of
an infinite-dimensional Cohn–Elkies LP, which is precisely the object the
parent's kill condition 1 needs and precisely what a truncated primal solve
cannot supply.

---

## Sources

Resolved by arXiv Atom API or by the publisher page, in the order they appear.

* Carneiro, Milinovich, Ramos, *Fourier optimization and Montgomery's pair correlation conjecture*, [arXiv:2310.01913](https://arxiv.org/abs/2310.01913)
* Cohn, Elkies, *New upper bounds on sphere packings I*, Ann. of Math. 157 (2003) 689–714, [arXiv:math/0110009](https://arxiv.org/abs/math/0110009), doi:10.4007/annals.2003.157.689
* Cohn, Kumar, *Universally optimal distribution of points on spheres*, JAMS 20 (2007) 99–148, [arXiv:math/0607446](https://arxiv.org/abs/math/0607446), doi:10.1090/S0894-0347-06-00546-7
* Cohn, Kumar, Miller, Radchenko, Viazovska, *Universal optimality of the E8 and Leech lattices and interpolation formulas*, Ann. of Math. 196 (2022), [arXiv:1902.05438](https://arxiv.org/abs/1902.05438)
* Cohn, *Packing, coding, and ground states*, PCMI 2014 lecture notes, [arXiv:1603.05202](https://arxiv.org/abs/1603.05202)
* Radchenko, *Universal optimality and Fourier interpolation* (overview of CKMRV), [CNRS/INSMI](https://www.insmi.cnrs.fr/sites/institut_insmi/files/download-file/univopt-overview.pdf)
* Carneiro, Milinovich, Soundararajan, *Fourier optimization and prime gaps*, Comment. Math. Helv. 94 (2019) 533–568, [arXiv:1708.04122](https://arxiv.org/abs/1708.04122), doi:10.4171/CMH/467
* Das, Ismoilov, Ramos, *Fourier optimization and pair correlation problems*, [arXiv:2502.05106](https://arxiv.org/abs/2502.05106)
* Carneiro, Littmann, Vaaler, *Gaussian subordination for the Beurling–Selberg extremal problem*, Trans. AMS 365 (2013) 3493–3534, [arXiv:1008.4969](https://arxiv.org/abs/1008.4969), doi:10.1090/S0002-9947-2013-05716-9
* Cohn, de Laat, Salmon, *Three-point bounds for sphere packing*, [arXiv:2206.15373](https://arxiv.org/abs/2206.15373)
* Kolountzakis, Lev, Matolcsi, *The Turán and Delsarte problems and their duals*, [arXiv:2510.10172](https://arxiv.org/abs/2510.10172)
* Gorbachev, Ivanov, Tikhonov, *On the existence of an extremal function in the Delsarte extremal problem*, Mediterr. J. Math. 17 (2020), doi:10.1007/s00009-020-01626-z; see also [arXiv:2407.04410](https://arxiv.org/abs/2407.04410)
* Ventevogel, Physica A 92 (1978) 343–361; Ventevogel, Nijboer, Physica A 98 (1979) 274–288 and Physica A 99 (1979) 569–580
* Edwin, *Distribution of points on the real line under a class of repulsive potentials*, Pure Appl. Math. Q. 21 (2025), [arXiv:2405.11428](https://arxiv.org/abs/2405.11428), doi:10.4310/PAMQ.251222233001
* Bétermin, Šamaj, Travěnec, *Equidistant versus bipartite ground states for 1D classical fluids at fixed particle density*, Anal. Math. Phys. 15 (2025) 88, [arXiv:2502.16639](https://arxiv.org/abs/2502.16639)
* Li, *Dual linear programming bounds for sphere packing via discrete reductions*, Adv. Math. 460 (2024) 110043, [arXiv:2206.09876](https://arxiv.org/abs/2206.09876), doi:10.1016/j.aim.2024.110043
* Jumagulov, *A dual linear programming bound for sphere packing in dimension 36*, [arXiv:2607.11319](https://arxiv.org/abs/2607.11319)
* Hardin, Tenpas, *Universally optimal periodic configurations in the plane*, [arXiv:2307.15822](https://arxiv.org/abs/2307.15822)
