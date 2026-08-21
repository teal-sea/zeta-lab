# GATE: two-sided bounds for Lambda_DH

Adjudicated 2026-08-16 (verdict NOT YET, five closure items). **Re-adjudicated
2026-08-16 after the repairs, by a session that did not make them.** Every
field below is at post-repair state. Nothing was accepted on report: the two
load-bearing scripts were re-run here and diffed against the pre-re-run files,
the prior-art source the first pass called unread was retrieved and text-checked
in this session, and the frame arithmetic was recomputed. What the first pass
found and what each repair did to it is in the Closure log at the end, together
with four places where the repairs fell short of their own standard.

> **Hardening pass, 2026-08-18, after this gate closed.** Three tasks were run
> against the closed record and every field they touch now carries an update
> block with the superseded text kept verbatim beside it. (1) **The upper
> bound sharpened by the full factor 2.082**, and in-tree rather than by
> citation: `STRIP2.md` and `strip2.py` derive and decide the abscissa
> `sigma_0' = 1.12036249819` from a phase obstruction in the two Euler
> products, on both backends. (2) **`M2` is no longer prose**: `M2-LEMMA.md`
> proves it with decided constants and `m2_lemma.py` exercises it by four
> routes and two attacks. (3) **The three open prior-art items are closed or
> reduced**, and the novelty sentence survives unchanged. Nothing broke, no
> decided lower-bound number moved, and the verdict below is unchanged at
> **YES**. What did change is the referee's attack ordering, which is
> re-ranked honestly at the end of this file.

Vocabulary per `MISSION.md`: *measured* is one float route, *decided* is an
enclosure whose exact endpoints settle a sign or an integer, *cited* is somebody
else's theorem. A composite takes its weakest grade.

## Exact object / normalization

`Phi_DH(u) = 4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u}/5)` with `a_n` the
period-5 coefficients `(1, kappa, -kappa, -1, 0)`,
`H_t(z) = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du`, and
`Lambda_DH := inf{t : H_t has only real zeros}`; this is the frame in which
`H_0(z) = Xi_DH(z) = F(1/2 + iz)` exactly, checked in the first pass against
`zeta.epstein.completed_dh` at five points (relative 3.9e-32 to 5.8e-32).

**This is the narrow frame, `s = 1/2 + iz`. It is Stopple's published one**
(arXiv:1301.3158, his `Phi(u, chi)` and `Xi_t(x, chi)` at `D = 5`, quoted
verbatim in `FRAME.md` section 1a), and it is **not** the frame of Newman,
de Bruijn as usually quoted, Rodgers-Tao, Polymath 15 or Dobner, all of which
sit at `s = (1+iz)/2`. The conversion is now derived rather than asserted:

    Phi_F(u) = Phi_DH(2u),   xi_t^F((1+iz)/2) = H_{t/4}(z/2),
    Lambda(wide) = 4 Lambda(narrow),   Delta(wide) = 2 Delta(narrow),
    Lambda / Delta^2 invariant.

I checked the derivation algebraically this session and it closes: Dobner's (5)
inverts to `Phi_DH(2u)` because `int_R Phi_DH e^{izu} du = 2 Xi_DH(z)`, and
`u = v/2` in his (6) turns `e^{tu^2}` into `e^{(t/4)v^2}` and `cos(zu)` into
`cos((z/2)v)`. The hunt's own numerical check of the same identity is 15
significant digits against 2 significant digits for the reading the old text
licensed (`FRAME.md` section 5, `THEOREM13.md` section 6). **Every number below
travels with its frame.**

## Closest prior work

Stopple (arXiv:1301.3158) is nearest, is the published source of this hunt's
normalization, and publishes `-1.13e-7 < Lambda_Kr` for quadratic Dirichlet
L-functions, so any phrasing of the form "first quantitative bound on a
non-zeta de Bruijn-Newman constant" is false and no longer appears. Dobner
(arXiv:2005.05142) supplies existence, finiteness, nonnegativity and the closed
half-line for all of `S#` with no numbers; de Bruijn 1950 Theorem 13 (typeset
restatements: Dobner Theorem 3, Newman-Wu 2020 Theorem 7) supplies the
`Delta^2/2` engine.

**Bombieri and Ghosh, *Around the Davenport-Heilbronn function*, Russian Math.
Surveys 66:2 (2011), 221-270 is no longer unread.** The first pass called it
"unread and paywalled" and named it the likeliest place in print for `sigma_0`.
It was retrieved and read between the two passes, and **I retrieved and
text-checked my own copy in this session** rather than take that on report:
`https://www.mathnet.ru/eng/rm9410` carries a free "English version PDF
(1572 kB)" link to
`getFT.phtml?jrnid=rm&paperid=9410&what=fullteng&option_lang=eng`, which served
1,610,005 bytes, 50 pages, no login. On my own extraction:

* `sigma(tau_+, 1) = 1.120362` is present, verbatim, in their section 6, as is
  `sigma(tau_-, 1) = 2.3822861089...`;
* the strings `1.395`, `1.39513`, `0.895136` and `2.4779` are absent;
* **`Bruijn`, `Newman`, `heat`, `Polya`, `Turan` and `deformation` occur zero
  times in all 50 pages**, case-insensitive.

So the verdict is mixed and both halves are now carried in the artifacts. On
`Lambda_DH` the risk closes **in the hunt's favour**: the paper has no de
Bruijn-Newman or heat-flow content of any kind, and the bracket is not
anticipated. On `sigma_0` it closes **against the hunt**: their `tau_+` is this
hunt's `kappa` (I confirmed `-phi + sqrt(1+phi^2)` against `zeta.epstein.kappa`
to relative 1.2e-33), and their Theorem 7 determines the exact least upper
bound of the real parts of the zeros of this function, which `sigma_0` only
bounds from above. `sigma_0` is therefore **not** a new number and is no longer
described as one anywhere.

> **Update 2026-08-18.** The two halves above both stand, and the second one
> has changed character rather than direction. Bombieri and Ghosh's Theorem 7
> is no longer the source of a sharper number this hunt cannot use: the
> *necessary* half of that theorem, which is all an upper bound needs, is now
> derived in-tree from the Euler products of the two Dirichlet L-functions
> plus one Moebius image, with no Bohr theory and no Kronecker theorem
> (`STRIP2.md` section 3), and the abscissa is decided on both backends. The
> equation is theirs and is not presented as new. What is new is the grade:
> the constant is decided here rather than adopted at six published decimals.
> Their converse, which turns the bound into an exact supremum, is not used
> and not claimed. Two of their published numbers are now reproduced as
> controls that share no machinery with their Theorem 7: the finite claim
> `6323 / 420` of their section 9, and `sigma(tau_-, 1) = 2.3822861089` to all
> ten digits they print. `sigma_0` is still not a new number, and neither is
> `sigma_0'`.

## Surviving novelty

A strictly positive two-sided bracket, whose lower side is an
enclosure-carrying zero count, for the de Bruijn-Newman constant of a Dirichlet
series with a Riemann-type functional equation whose Riemann hypothesis is
false. It is not the first non-zeta constant of this type (Stopple), not the
first strictly positive one (Newman-Wu compute `ln 2` exactly for a three-atom
measure), and the upper side is a cited theorem applied to a constant computed
here rather than a new mechanism. The adopted sentence is in `NOVELTY.md`
section "The sentence", with the superseded one kept verbatim beside it:

> So far as the literature search recorded in `NOVELTY.md` reaches, these are
> the first quantitative bounds, from either side, on the de Bruijn-Newman
> constant of a Dirichlet series with a Riemann-type functional equation whose
> Riemann hypothesis is false. They are stated in the normalization of Stopple
> (arXiv:1301.3158) ... and are four times smaller than the same constant in
> the normalization of Newman, Rodgers-Tao, Polymath 15 and Dobner.

**The separation (named surviving item, added 2026-08-16, after this gate
closed).** In the common wide frame the decided floor beats the best
published zeta upper bound: `Lambda_zeta <= 0.22` (Polymath 15 Theorem 1.1,
pinned at source in `POLYMATH-PIN.md`) while `Lambda_DH > 0.2304 = 144/625`
(this hunt), so `Lambda_DH > Lambda_zeta` unconditionally, with the exact
rational core `144/625 > 11/50` (`7200 > 6875`, cross-multiplied) and the
same inequality in the narrow frame (`0.055 < 0.0576`, the identical
cross-multiplication). A dedicated novelty adversary killed the unqualified
phrasing "first strict inequality between the de Bruijn-Newman constants of
two Dirichlet series" against the function-field literature
(Andrade-Chang-Miller arXiv:1310.3477; CMMRSY arXiv:1411.2071) and
sanctioned the narrower claim: the first, so far as the searches reach, in
which both constants are nonnegative. Full statement, chain, caveat list
verbatim and grade: `SEPARATION.md`. Composite grade cited plus decided,
weakest step cited.

**The claim to `sigma_0` is withdrawn and the claim to the bracket is what is
left.** The first pass named `sigma_0` and the decided off-line zero of `H_t`
at `t = 36/625` as "the genuinely new numbers"; half of that is now known to be
wrong and the artifacts say so. What survives on the upper side is the
derivation, not the quantity: an enclosure-carrying elementary route to a
weaker bound on a constant Bombieri and Ghosh determined in 2011.

> **Update 2026-08-18.** The paragraph above is kept as written and one word
> in it is now wrong: *weaker*. The elementary route no longer stops short of
> their abscissa. `STRIP2.md` reaches it, decided on both backends, at
> `sigma_0' = 1.12036249819`, and the deep flint point at `P = 10^7` decides
> `1.1203624981833251`, which sits about `4e-17` above the decided lower end
> of the root enclosure. The withdrawal of the *originality* claim is
> unaffected: the quantity was determined in 2011 and this hunt reaches the
> same one. The novelty sentence and its footnote are unchanged; only the
> footnote's characterisation of the upper side as "a weaker bound on that
> same quantity" needed the same correction, and `NOVELTY.md` carries it.

## Lower bound

`0.0576 < Lambda_DH` narrow, with `0.0576 = 36/625` exactly; `0.2304 <
Lambda_DH` wide, `0.2304 = 144/625`. It rests on a decided argument-principle
count `N = 1` for `H_{36/625}` over a rectangle whose interior has
`Im z >= 3/1024 > 0` in exact rational arithmetic, then monotonicity for
`Lambda_DH >= t` and Dobner's closed half-line for the strict inequality,
transported through `t -> t/4`, which is an increasing bijection and so
preserves a closed half-line.

## Lower-bound status (rigorous / numerical / failed)

**Rigorous modulo one prose lemma, which is named and lesioned.** The two
analytic steps that failed "proved in-tree, or a correctly-applied cited
theorem whose hypotheses were verified" *as written* in the first pass are both
repaired at the level of justification, with no computed number moving:

* the evenness of `G`, which cancels the vertical legs and is what makes `M2` a
  bound at all, is now derived from `F(s) = F(1-s)` in three parts (Hecke's
  theta transformation for the odd primitive character mod 5 and the single
  real condition on `kappa` it forces; the Mellin transport showing the
  transformation and the functional equation are one fact, written in the sound
  direction Hecke -> functional equation and saying why the converse would need
  an inversion in a strip the two integrals do not share; and the identity
  theorem on `|Im u| < pi/4`, which is what the vertical legs at `u = +/- is`
  actually need and the old justification never reached). I checked the algebra:
  `Phi_DH(u) = 4 x^{3/4} omega(x)` at `x = e^{2u}`, so evenness is exactly
  `omega(1/x) = x^{3/2} omega(x)`, which is what the file derives.
* the citation supplying strictness is now routed through the corrected
  conversion rather than through a false claim of frame identity.

`M2` itself remains prose. It is the single load-bearing analytic step no
cross-route exercises, and its failure mode is the one this routine promises
never to produce. **That is now a recorded blind spot with a measured onset
rather than an unexamined assumption**, and a necessary-not-sufficient guard
sits in front of it with a refusal path. Read as a whole: enclosure-carrying
count, cited theorem, one prose lemma inside.

> **Update 2026-08-18, after this gate closed.** The paragraph above is
> superseded and is kept for the record. `M2` is no longer prose and is no
> longer unexercised: `M2-LEMMA.md` proves it, with every constant a reported
> ball and every hypothesis a decided predicate, and four routes plus two
> falsification attacks stand behind it (`m2_lemma.py`). The correct reading
> of the lower bound is now: enclosure-carrying count, cited theorem, and one
> proved lemma whose only non-elementary input is the cited functional
> equation already carried as assumption 5. Nothing computed moved; see
> known assumption 6 for the full replacement text and for what is left.

## Upper bound

**Sharpened 2026-08-18, in-tree, by the full factor 2.082. The superseded
statement is kept verbatim below it.**

`Lambda_DH <= 0.19242481458026887663805` narrow, `<= 0.7696992583210755065522`
wide. Both decimals are **exact**, not outward roundings: the abscissa is
decided at the exact rational `sigma_0' = 112036249819/100000000000 =
1.12036249819`, so `Delta = sigma_0' - 1/2 = 0.62036249819` is exact and
`Delta^2/2 = 3848496291605377532761/20000000000000000000000` terminates. The
wide value is that one times exactly four. (`STRIP2.md` section 5.2 prints the
narrow value rounded outward to 22 decimals, `0.1924248145802688766381`; it is
the same bound, one ulp of display above the exact value.) The ratio
upper/lower is 3.3407085864630015 and is frame-free.

What decides the abscissa is a phase obstruction rather than coefficient
domination: `f = A L(s, chi) + conj(A) L(s, conj chi)` with
`A = (1 - i kappa)/2`, so a zero with `Re s > 1` forces
`arg L(s,chi)/L(s,conj chi) = pi + 2 arctan kappa` mod `2 pi`, while each prime
`p = 2, 3 mod 5` can supply at most `2 arctan(p^{-sigma})` radians (a Moebius
image of a disc, with the maximising point of modulus exactly 1, so the
`|R| = 1` constraint is free and no modulus-phase trade sharpens it further).
The criterion is `Theta(sigma) = sum_{p = 2,3 (5)} 2 arctan(p^{-sigma}) < pi -
2 arctan kappa`, and `Theta` is decreasing, so one decided `sigma` closes the
half-plane. The tail is closed by the Euler products of `zeta` and
`L(., chi5)` themselves, so no prime-counting estimate enters.

Decided on **both** backends at `P = 10^5`, 4814 class primes: python-flint
(Arb) 192 bits gives the root in
`[1.1203624981833869487276, 1.1203624981833869487332]` (65 sign decisions) and
mpmath.iv at dps 40 gives `[1.1203624981833854, 1.1203624981841131]` (38 sign
decisions); the intervals overlap. At the headline rational,
`Theta = [2.5880182946402392454052004, 2.5880182946415650528147533]` (flint)
against the target `[2.5880182946927479869541106, 2.5880182946927479869541107]`,
margin `5.12e-11`. A flint-only deep point (320 bits, `P = 10^7`, 332442 class
primes) decides `sigma = 1.1203624981833251`, giving
`0.1924248145761280189989039` narrow / `0.7696992583045120759956154` wide.

**Superseded, kept verbatim** (the state through 2026-08-17):
"`Lambda_DH <= 0.4006343708899557` narrow, `<= 1.6025374835598228` wide. It is
`Delta^2/2` with `Delta = sigma_0 - 1/2`, rounded outward: the decided flint
interval is `[0.4006343708899556944469547527, 0.4006343708899556944469548120]`
and the headline decimal sits above its upper endpoint, so the inequality is
safe; the wide interval is that one times four and its headline likewise sits
above the endpoint. The ratio upper/lower is 6.9554578 and is frame-free."

## Upper-bound status (rigorous / numerical / failed)

**Rigorous, with the frame stated. The looseness the first pass recorded is
removed, and what replaces it is a smaller and differently located
looseness.** Every numerical step is enclosure-carrying (`kappa` at 500 bits,
`sigma_0'` bisected on both backends with exact rational sign decisions and the
headline decided at an exact rational rather than at a bisection endpoint), the
phase argument in `STRIP2.md` is elementary and complete, and Theorem 13's
hypotheses hold for `Phi_DH` exactly as before. Sections 3(d) and 3(e) of
`STRIP.md`, the gamma factor and the trivial zeros, are reused unchanged, so
the two derivations share their reflection step and differ only in how the
zero-free half-plane is reached.

Three things about the new route that a reader is entitled to before trusting
it:

* **The equation is Bombieri and Ghosh's**, term for term (their Theorem 7 at
  `q = 1`, `xi = kappa`), and `STRIP2.md` section 7 says so. Only the
  *necessary* half is used and it is derived here; their converse, which makes
  the abscissa exact rather than an upper bound, is not used and not claimed.
  So the number is theirs and the grade is this hunt's.
* **The instrument reproduces two of their published numbers by routes that
  share nothing with their Theorem 7**: their section 9 finite claim
  (threshold prime 6323, cardinality 420) and the sibling abscissa
  `sigma(tau_-, 1) = 2.38228610898712387152...` against their published ten
  digits. Nothing in the instrument was built around the second constant.
* **It forces one correction against an in-tree artifact, not against the
  paper.** At `P = 10^7` and 320 bits it decides that `BOMBIERI-GHOSH.md`
  check B's two 29-digit re-solves each sit on the wrong side of their own
  root, by about `1.2e-17` and `6e-18`. Bombieri and Ghosh print six and ten
  decimals and this instrument reproduces both exactly; what moves is
  `FRAME.md`'s 18-digit derived row, which agrees with the decided replacement
  to 17 digits.

The natural alternative sharpening was tried, decided, and rejected on the
mathematics rather than on taste. Regrouping the series into period-5 blocks
and applying the mean value theorem gives `|B_k| <= |s|[3(5k+1)^{-sigma-1} +
kappa(5k+2)^{-sigma-1}]`, correct and `O(n^{-sigma-1})` per block, but the
`|s|` is not an artifact (both pairs share the midpoint `5k+5/2` and their
first-order terms add), so it yields a height-restricted strip that climbs
back to the old `sigma_0 = 1.3951361582...` as `T` grows: 1.19585459 at
`T = 10`, 1.39224106 at `T = 10^5`. de Bruijn's theorem consumes a half-plane
statement, which this cannot give. It is recorded in `STRIP2.md` section 2 as
decided and useless.

**Superseded, kept verbatim** (the state through 2026-08-17): "**Rigorous,
with the frame stated, and now known to be loose by a factor of at least
2.08.** Every numerical step is enclosure-carrying (`kappa` at 500 bits,
`sigma_0` bisected on both backends with exact rational sign decisions, outward
rounding checked by exact rational comparison), the strip argument in
`STRIP.md` is elementary and complete including the boundary equality case and
the trivial zeros, and Theorem 13's hypotheses hold for `Phi_DH`. What changed
since the first pass is not the bound but what is known about it.
Bombieri-Ghosh's `sigma(tau_+, 1) = 1.120362` is the exact abscissa `sigma_0`
bounds, and feeding it through the same engine gives 0.192424814576128011
narrow / 0.769699258304512045 wide, a factor 2.08203. **It is correctly not
adopted**, and the artifacts say why: their value is six published decimals of
Mathematica output resting on Bohr-Kronecker machinery unverified in-tree, so
the improvement is *cited plus measured*, not decided, and swapping it into a
decided headline would launder a grade. I checked both halves of that
judgement here. The arithmetic is right, but it is right against
`BOMBIERI-GHOSH.md`'s own 29-digit re-solve `1.12036249818332508773010350311`,
not against the six decimals the `FRAME.md` row cites as its input (those alone
give 0.192424505522). And their root is reproducible: my own truncated sum over
primes `p = 2, 3 mod 5` with an integral tail correction converges to 1.1203623
at `P = 10^7`, matching all six published digits."

**What did not change.** The grade is unchanged at *cited plus decided*,
weakest step cited, because the weakest step was and remains de Bruijn 1950
Theorem 13. `STRIP.md` remains correct and is kept: it is the weaker of two
valid derivations and a reader should be able to see both.

## Independent cross-check

Four, and the adjective is now measured rather than asserted. `MISSION.md`'s
"two independent winding routes" has been replaced everywhere by the radius
that `harness/independence.py` reports, and `INDEPENDENCE.md` carries the layer
lists so a reader can check them.

| pair | radius | shared | layers | what agreement is evidence about |
|---|---|---|---|---|
| route 1 (`winding.py`) vs route 2 (`winding_quad.py`) | 9 | 9 | 12 / 12 | the bookkeeping that turns H-balls into an integer, and nothing else |
| route 1 vs route 3 (DHFlow) | 0 | 0 | 12 / 8 | everything either one runs |
| route 1 vs route 4 (quadrature-free) | 0 | 1, reconvergent (python-flint) | 12 / 6 | everything except the ball backend |
| route 3 vs route 4 | 0 | 0 | 8 / 6 | everything either one runs |

The first pass reported 8 of 11; `independence_decl.py` re-runs that coarser
merge and reproduces `8 shared of 11, radius 8` exactly, so the two counts are
one declaration at two granularities and not a disagreement. The invariant
neither depends on: **the two winding routes duplicate none of the evaluator.**

The independence the claim actually rests on is routes 3 and 4, both of which
were scratchpad code at the first pass and are now landed as reproducible
scripts with results files. I re-ran both here. Route 3 (mpmath dps 130, no
shared layer, 5814 quadrature nodes, 64 samples per edge) returns `N = 1` on
**both** published boxes, `t = 23/400` and `t = 36/625`, reproducing with zero
non-timing differences; that is the first and only second witness the headline
value 0.0576 has. Its own margin is worth quoting because it is the tightest
thing in the cross-check: the largest consecutive argument step is 0.3946
radians against the routine's 0.40 threshold, and the minimum `|H_t|` on the
boundary is 8.64e-85, which is the scale that makes the count need balls rather
than floats. Route 4 (Gauss-sum `kappa`, Hurwitz-zeta `H_0`, `acb_series`
Taylor in `t` with an explicit remainder) overlaps `instrument.H_ball` at all
eight boundary points of the `t1` box; I re-ran it here, 8 of 8, agreement
**40.3 to 42.7 decimal digits**, which corrects the first pass's "about 22
significant digits" (that was the printed width, not a measurement).

Two things the radius does not carry, both recorded in `INDEPENDENCE.md`:
route 2 ran at one `t` and its own box, so `t = 36/625` has no route-2 witness
at all; and route 3's `kappa` is a different implementation of the *same*
equation, so only route 4 makes the `kappa` equation independent.

## Known assumptions

1. **de Bruijn 1950, Duke Math. J. 17, Theorem 13**, all-zeros form, transcribed
   in `THEOREM13.md` by a visual read of an image-only scan. Independently
   re-read from the same scan by one adversary, and corroborated by two typeset
   restatements: Dobner's Theorem 3 and Newman-Wu 2020 Theorem 7.
2. **Its hypotheses for `Phi_DH`**: integrability; hermitian symmetry, here
   evenness, now derived in-tree from `F(s) = F(1-s)` including the complex-`u`
   case the vertical legs need, and measured at dps 260 to relative 1e-261 near
   the origin; and `O(e^{-|u|^b})` with `b > 2`, discharged by a 201-point grid
   standing in for an unbounded-range claim. The fact itself is immediate from
   the artifact's own domination `|Phi_DH(u)| <= 4 e^{3u/2} e^{-(pi/5)e^{2u}}
   S(0)`, so this stays a discharge gap and not a doubt.
3. **Dobner 2020 Theorem 1**, the closed half-line, used only for the
   strictness of the lower bound and now applied through the corrected
   conversion `t -> t/4`. `S#` membership of DH is verified condition by
   condition in-tree and by an adversary against Dobner's verbatim text.
   Without this citation only `Lambda_DH >= 0.0576` survives, from in-tree
   monotonicity (Theorem 13 at `Delta = 0`) or Polya.
4. **Dobner Theorem 2** (`Lambda_F >= 0`): quoted, load-bearing for neither side.
5. **Classical facts used without in-tree proof**: Gamma has no zeros and only
   the simple poles at `s = -1, -3, ...`; `F` is entire with `F(s) = F(1-s)`.
   `kappa` is decided by an Arb linear solve and agrees to 40 digits with the
   Gauss-sum route, and to 33 digits with Bombieri-Ghosh's closed form
   `tau_+ = -phi + sqrt(1+phi^2)`, which I checked here.

   **Added 2026-08-18, with the sharpened upper bound.** The new route uses
   one further classical fact that the old one did not: the Euler products of
   `L(s, chi)` and `L(s, conj chi)` for the odd primitive character mod 5,
   absolutely convergent and nonvanishing on `Re s > 1`. That is textbook and
   is the only addition; the decomposition `a_n = A chi(n) + conj(A)
   conj(chi)(n)` it rides on is decided in-tree as five acb residual balls
   containing 0 with radius below `1e-40`, with `chi` taken from flint's own
   Dirichlet character table rather than from a remembered list of values, and
   it is separately pinned by the suite through `zeta/epstein.py`'s `dh_f`
   docstring. `f` itself has no Euler product, and none is used.
6. **The analytic bound `M2`** in `winding.py`. **Rewritten 2026-08-18: the
   blind spot recorded here is closed in the form it was recorded, and what
   replaces it is narrower and named.** `M2-LEMMA.md` states the bound as
   Lemma M2 and proves it: differentiation under the integral sign with an
   explicit dominating function, Cauchy's theorem on the shifted contour with
   the far side bounded rather than asserted to vanish, the vertical-leg
   cancellation, separate proofs of the two majorants for the theta-like sum,
   and the panel-plus-tail split. Every constant of the proof is a reported
   Arb ball and every hypothesis is a decided predicate, so **no step of it
   rests on an unverified numerical claim**. It is exercised by four routes
   rather than none (`m2_lemma.py`, `m2_lemma_results.json`): an independent
   re-implementation of the bound, an unshifted majorant that reaches a valid
   bound without Cauchy's theorem and without the evenness, a pointwise Arb
   enclosure of `H_t''` that makes the cushion decided, and the pre-existing
   float quadrature guard. Two attacks are wired in beside them: the identity
   `H_t'' = -int e^{tu^2} Phi_DH(u) u^2 cos(zu) du` is checked against second
   central differences of `H_ball` (worst relative gap `7.66e-07` against
   `h^2 = 9.54e-07`), and both majorants for the theta-like sum are attacked
   against a sharp truncated enclosure at 24 probe points with no refutation.

   The independent re-derivation returns `1.1886319406e-78` at `t1` against
   `winding.py`'s `1.1886642645e-78`, a relative `-2.7e-05` traced to exactly
   one panel of 800, the crossover between the two majorants, where
   `winding.py` keeps the larger of the two valid bounds because its ball
   comparison does not decide. `winding.py`'s value is therefore the more
   conservative one and **no decided winding number moves**.

   The cushion stands and is now decided rather than measured: **55.65 at
   `t1`, 53.79 at `t2`**, from a decided `sup |H_t''| >= 2.1358e-80` (433-point
   grid of Arb enclosures) against `M2 = 1.1887e-78`. The old measured value
   `2.1357367685579024e-80` is reproduced to all 17 digits by an enclosure at
   the same point. Across a 40-unit span of `Re z`, over which `|H_t''|` falls
   by 14 orders of magnitude, the cushion stays between 33 and 204, because
   `M2` depends on `x_lo` only through `e^{-x_lo v}` with `v = pi/4 - 1/256`
   against the strip half-width `pi/4`. **The cushion is a structural constant
   of the bound, not a property of these two rectangles.**

   **What is left, stated at its true size.** (i) One cited classical input is
   load-bearing for `M2` and for nothing else in the route: the evenness
   `Phi_DH(-u) = Phi_DH(u)`, which is Hecke's theta transformation plus
   `F(s) = F(1-s)` transported through the Mellin transform, that is,
   assumption 5 above. If it failed the vertical legs would not cancel and
   `M2` would be false, and `M2-LEMMA.md` section 3 step 2 shows there is no
   numerical substitute: the quantity that must vanish is identically zero, so
   enclosing it to `1e-78` would take of order `1e78` subdivisions. (ii) The
   proof is written prose plus decided arithmetic, at the *hardened* rung. It
   is not kernel-checked and it has been read by no human. (iii) Control 5's
   lesion table is retained and its meaning has changed: with `M2` proved it
   measures the guard's sensitivity to an implementation fault, not the
   exposure of an unproven assumption. The detector still cannot see a
   corrupted `M2` by itself, which is why the guard and its refusal path stay.

   **Superseded text, kept verbatim** (the state through 2026-08-17): "an
   in-tree shifted-contour derivation whose numerical ingredients are
   ball-computed and whose derivation is prose. It is exercised by no
   cross-route. Its stated reason for the evenness of `G` is repaired, and its
   docstring's cushion is corrected from 'three digits of slack' to the
   measured factor **55.7** (measured sup `|H_t''| = 2.1357e-80` against
   `M2 = 1.1887e-78`; 53.9 at `t2`). It is now covered by two things that did
   not exist at the first pass: control 5, which lesions it, and
   `winding.measured_h2_guard`, a necessary-not-sufficient float sample of
   `|H_t''|` by quadrature of the defining integral, wired into
   `winding.main()` with a refusal that voids the floor if it fails.
   **Standing blind spot, recorded rather than repaired; the lower bound
   carries it.**"
7. **Residual float-grade steps, none load-bearing**: the dps-112 locating pass
   that places the boxes; the WP3 census over heights 412 to 600;
   `calibration.json`'s re-derivation of the `Delta^2/2` dictionary. All three
   are labelled measured in the artifacts. **Added 2026-08-18**: three of
   `STRIP2.md`'s eight controls are measured rather than decided (the series
   against the two L-functions, the phase lemma's circle sample, the
   Euler-product tail identity) and the artifact labels them so; none of the
   five decided ones, and none of the headline, depends on them.
8. **Tooling**: python-flint 0.9.0 (Arb), mpmath's `iv` context, and the
   exact-rational plumbing. Both first-pass complaints here are repaired. The
   `mpmath.iv` cross-leg now evaluates `instrument._truncated_integrand`, the
   callable the integrator actually receives, instead of `phi_ball`, which no
   decision path calls; the hoist moved no number (`H_ball` midpoint
   `4.3658433958660405e-83` and radius `1.4894837452822593e-124` are unchanged
   in `validation.json`, and both winding boxes reproduce every decided field).
   The two hand-derived tail bounds, which previously sat 36 to 41 orders below
   the delivered ball radius so that nothing could see them, now have a standing
   domination check against high-precision true remainders: 18 of 18 rows
   dominate, and the **blindness factor is 8.02**, so a tail bound deflated by
   less than about eight passes it. Both repairs are measured and neither can
   upgrade the thing it checks. There is still no second rigorous integrator;
   route 4 answers that as a route, not as a backend.
9. **Prior art**. **Rewritten 2026-08-18: all three items this entry carried as
   open are now closed or reduced, and none of them touched a computed number.**
   Bombieri-Ghosh 2011 was already read. The three that remained:

   - **academia.edu preprint 166936409 is read in full.** Every earlier route
     failed again (direct fetch HTTP 403 under two user agents, no Wayback
     snapshot), but `r.jina.ai` against the full slug URL returned the record,
     which names the author, **Mesut Ismail**, and a DOI, **10.5281/zenodo.21679490**.
     The paper is open access on Zenodo (`Ismail_rh_pf_v18.4.pdf`, 758,872 bytes,
     2026-07-29) and was downloaded and read. Its subject is the classical
     wide-frame `Lambda_zeta`; Davenport-Heilbronn appears only as instrument and
     negative control. **It contains no `Lambda_DH`, no bound on one from either
     side, and no claim about one.** Its two DH off-line lifetimes,
     `tau1 = 0.1819` and `tau2 = 0.0449` in the wide frame, are labelled *upper*
     bounds on those lifetimes inside a Numerical Observation, which is the wrong
     direction to give a lower bound on `Lambda_DH`; taken at face value anyway,
     `0.1819` wide is `0.045475` narrow, below this hunt's decided floor of
     `0.2304` wide / `0.0576` narrow by a factor `1.267`. Its witnesses are the
     same zeros `zeta/epstein.py` pins, and its frame was confirmed here by
     recomputing `2 h1^2 = 0.190365478578` (mpmath, mp.dps = 30, measured)
     against its tabulated `0.190`. A side benefit: its Lemma 3.2 states this
     hunt's factor-4 frame dictionary independently, with the same warning that a
     clock off by 4 would "prove" `Lambda <= 1/8`. **Risk closed, in the hunt's
     favour.** Details in `NOVELTY.md` section 2.
   - **Bombieri-Mueller 2008 is identified and read at abstract and
     reference-list level.** It is E. Bombieri and J. Mueller, *On the zeros of
     certain Epstein zeta functions*, Forum Math. 20:2 (2008), 359-385, DOI
     `10.1515/FORUM.2008.018`, Zbl 1217.11040, MSC 11E45 and 11M41. Per the
     zbMATH summary it bounds the **rate of approach** of zeros to the boundary of
     the zero-free half-plane for Epstein zeta functions of class number 2, by
     Bohr's method for the lower side and a diophantine-type result for the upper.
     Its five deposited references name neither de Bruijn nor Newman. So: no
     de Bruijn-Newman or heat-flow content, and no rival value for the quantity
     `sigma_0` bounds either, since it is a different family and a different
     quantity. **Its full text is still unread** (De Gruyter answers HTTP 202
     behind a human-verification wall, `r.jina.ai` gets HTTP 405, no mirror
     found), so this is *reduced to a small named residual*, not fully closed.
   - **The Dobner forward-citation sweep is no longer single-source.** It was
     re-run across three independent indexes plus a web sweep: Semantic Scholar
     (5 records, queried by DOI and arXiv id separately and agreeing),
     OpenCitations/COCI (1 record), Google Scholar (cluster
     `5851792251239807498`, 2 distinct records before it rate-limited), and a
     web-search sweep that surfaced one preprint none of the three indexes
     carried. **OpenAlex still returned HTTP 429 with `$0` daily budget and
     `retryAfter: 72359`, and was not worked around.** The union is 7 distinct
     citing works, none of which attaches a quantitative `Lambda` to any non-zeta
     object; the per-work verdicts are tabulated in `NOVELTY.md`. **One citing
     item is unread rather than unfound**: Voronov, *A Crowding-Normalized
     Reformulation of Neighboring-Gap Dynamics for the de Bruijn-Newman Flow*
     (ResearchGate, 2026), whose abstract places it on the zeta-side **real**
     spectrum and whose full text is behind Cloudflare.

   **New negative evidence, stronger than any single query.** The sweep turned up
   Tao, Trudgian and Yang's ANTEDB (`teorth.github.io/expdb`), chapter 18 of which
   is *The de Bruijn-Newman constant*, works in this hunt's wide frame
   (`H_0(z) = (1/8) xi(1/2 + iz/2)`), and tabulates the complete known bound
   history from Newman 1976 to Rodgers-Tao/Dobner `>= 0` on the lower side and
   Platt-Trudgian 2021 `<= 0.2` on the upper. **Every entry is zeta's.** A
   maintained community database of de Bruijn-Newman results with no non-zeta
   constant in it is the best available evidence that none is in print.

   **Two consequences outside this item, recorded and not acted on here.** ANTEDB's
   `Lambda_zeta <= 0.2` (Platt-Trudgian 2021) is sharper than the `<= 0.22`
   (Polymath 15) that `NOVELTY.md` and `SEPARATION.md` quote, so the separation
   corollary `Lambda_DH > Lambda_zeta` **gains headroom** rather than losing any
   (`0.2304 > 0.2`); `SEPARATION.md` should cite Platt-Trudgian. And `FRAME.md`
   now has an independent published source for its factor-4 dictionary.

   **The novelty sentence survives unchanged.** Only its footnote and the
   one-line short form moved.

## Reproduction command/artifacts

Backend first, from the repo root:
`.venv/bin/python -c "from zeta import rigor; print(rigor.BACKEND, rigor.available_backends())"`
must print `python-flint`. Then
`.venv/bin/python hunts/lambda_dh_bounds/{strip,strip2,validate,winding,winding_quad,controls,m2_lemma,census,calibrate_theorem13,independence_decl,crosscheck_quadfree,crosscheck_dhflow_winding}.py`,
each of which rewrites its own `*_results.json`. **The claim's two decided
numbers are `strip2_results.json` (`headline.upper_bound_delta_sq_over_2_narrow`,
about one minute) and `winding_results.json` (`decided_floor_t = 36/625`,
`t1_run`/`t2_stretch_run` both `status: decided, N: 1`).**
`strip_results.json` still holds the superseded and still-correct
coefficient-domination constant, and `m2_lemma.py` (about 105 seconds) writes
`m2_lemma_results.json` and touches no winding number.

The written record is `RESULTS.md` with `results.json` (each claim carrying
value / frame / grade / backend / precision / source file). Sources and
hypothesis checks: `FRAME.md`, `STRIP.md`, `STRIP2.md`, `M2-LEMMA.md`,
`THEOREM13.md`, `NOVELTY.md`, `BOMBIERI-GHOSH.md`, `INDEPENDENCE.md`,
`SEPARATION.md`, `POLYMATH-PIN.md`, `KAPPA-CLOSED-FORM.md`, `MISSION.md`.
Adversary write-ups: `attack_adversary1_normalization.md`,
`attack_adversary3_upperbound.md`, `attack_adversary4_instrument.md`,
`attack_adversary5_priorart.md`.

## What would a skeptical referee attack first

**Re-ranked 2026-08-18.** The 2026-08-16 ordering, kept below in full, put
`M2` first and the looseness of the upper side second. Both of those moved,
in opposite directions from the reader's point of view: `M2` became a proved
lemma and the upper bound sharpened by 2.082 in-tree, so the two attacks the
first ranking named as the best ones available are the two that were spent.
What is left is dominated by things this directory cannot fix by computing
harder, and the honest ranking says so. In order:

1. **The citations, which are now unambiguously the weakest steps.** The
   composite grade was always *cited plus decided* and the cited half is no
   longer sharing the stage with a prose lemma or a loose constant. Four
   citations carry the whole structure and none is verified in-tree: de Bruijn
   1950 Theorem 13 in its **all-zeros** form, transcribed from an image-only
   scan (corroborated by an independent adversary re-read of the same scan and
   by two typeset restatements, Dobner Theorem 3 and Newman-Wu Theorem 7, but
   not by an authoritative typeset original); Dobner 2020 Theorem 1, which
   supplies the strictness of the lower bound and nothing else; the evenness
   `Phi_DH(-u) = Phi_DH(u)`, which is Hecke's theta transformation plus
   `F(s) = F(1-s)` transported, on which the vertical-leg cancellation and
   hence the whole size of `M2` depends, and for which `M2-LEMMA.md` section 3
   step 2 shows there is no numerical substitute; and, for the separation
   only, Polymath 15 Theorem 1.1. An error in any one of them moves or erases
   a headline while moving nothing else in this directory.
2. **Two new proofs, both written by agent sessions, both attacked only by
   scripts written in the same sessions, both read by no human.** The phase
   obstruction of `STRIP2.md` section 3 and Lemma M2 of `M2-LEMMA.md` are the
   two pieces of mathematics this hunt now claims for itself, and each is
   prose plus decided arithmetic at the *hardened* rung, not kernel-checked.
   The specific places to press: in `STRIP2.md`, the Moebius-image lemma and
   the claim that `arg` of the absolutely convergent product is the sum of the
   factors' principal arguments modulo `2 pi`; in `M2-LEMMA.md`, the
   contour-shift step and the two `Omega` majorants. Both files hand a referee
   their own falsification runs rather than making them build them, which is
   the right posture and is not the same thing as an outside reading.
3. **The detector still cannot see a corrupted `M2` by itself.** This is item
   1 of the old ranking, reduced to what survives: the lemma is proved but the
   implementation could still be wrong, control 5's lesion table still shows
   three wrong and silent integers from deflation 75, and the health metric
   still moves the wrong way across the lesion (chord margin 0.02 to 1.11).
   The two implementations agree exactly on 799 panels of 800 and differ on
   the crossover panel in the conservative direction, with `winding.py`
   holding the larger value, so no decided winding number moves; but a reader
   should know that the agreement is between two implementations and not
   between two mathematical routes. The guard and its refusal path stay.
4. **What is left of the looseness, and where it now sits.** The bracket ratio
   is 3.341, down from 6.955, and the strip constant is no longer where the
   slack is: the sieve-limit sweep shows the abscissa converging like
   `P^{1-3 sigma}`, so accuracy there is essentially free. Two honest gaps
   remain. The engine: with `Delta = 0.62036249819` the de Bruijn theorem
   returns `0.19242481458` narrow while the deepest measured DH zeros reach
   `|Im z| = 0.347`, which would give `0.0602` against a decided floor of
   `0.0576`, so most of the remaining factor is the engine plus the sparsity
   of the extreme zeros. And the converse: this argument bounds the supremum
   of the real parts of the zeros and does not show it is attained, which is
   Bombieri and Ghosh's converse and is neither used nor claimed. If their
   converse holds, `Delta` cannot be improved at all.
5. **Whether the new derivation is independent of the paper it reproduces.**
   `STRIP2.md`'s criterion is Bombieri and Ghosh's Theorem 7 equation, term
   for term, at `q = 1` and `xi = kappa`. The artifact states this plainly and
   claims only the grade rather than the equation, and it reproduces two of
   their published numbers by machinery their Theorem 7 does not share (the
   `6323 / 420` finite claim and `sigma(tau_-, 1)` to ten digits). A referee
   can still ask whether the necessary half was genuinely re-derived or
   reconstructed from a known answer. The answer available is the derivation
   itself, which uses only the Euler product, absolute convergence and one
   Moebius image, and the fact that the deliberately-tried alternative (the
   five-term block regrouping) failed and is recorded as failing.
6. **The remaining prior art, largely spent.** See item 3 of the old ranking
   below, whose 2026-08-18 update stands: what is left is the full text of
   Bombieri-Mueller 2008 (publisher wall) and of one citing preprint (Voronov
   2026, Cloudflare), both unread, neither able to touch a computed number.

**Superseded ranking, kept verbatim** (2026-08-16, with its own 2026-08-18
in-place updates):

1. **`M2`.** It is prose, it is load-bearing, no cross-route touches it, and
   the artifacts now hand the referee the exact lesion table rather than making
   them build it. The honest reading of that table is the uncomfortable one:
   the guard trips at deflation 55.7 and the first wrong integer appears at 75,
   so the guard happens to fire first **on this box**, by luck rather than by
   structure, and a derivation wrong by a factor under 55 would pass it and
   could still be wrong. `winding.py` says exactly that.

   **Update 2026-08-18.** The first two clauses are no longer true and the
   paragraph is kept for the record. `M2` is proved in `M2-LEMMA.md` and is
   exercised by four routes. What a referee should attack instead, in order:
   the cited evenness `Phi_DH(-u) = Phi_DH(u)` on which the vertical-leg
   cancellation and hence the whole size of `M2` depends; the fact that the
   proof is written prose rather than kernel-checked, and has been read by no
   human; and the implementation agreement between `winding.py` and
   `m2_lemma.py`, which is exact on 799 panels of 800 and differs on the
   crossover panel in the conservative direction. The lesion table survives as
   a measurement of the detector's sensitivity to a corrupted `M2`, which is
   still real: the winding routine cannot see one by itself.
2. **Looseness of the upper side.** 0.4006 is a factor 2.082 above a constant
   published in 2011, and further above the truth: the deepest measured DH
   zeros reach `|Im z| = 0.347` against `Delta = 0.895`, and a phase-minimum
   refinement in the hunt's own materials already gives 0.3871 narrow. The
   calibration that shows how loose the *method* is, rather than this instance
   of it, is running the same coefficient domination on zeta: it returns
   `Delta^2/2 = 3.0191480758` in the wide frame where the truth is 1/2, a
   factor 6.04. A referee will ask why the sharper published constant is not
   used, and the answer, that it is cited-plus-measured while the headline is
   decided, is a good one that has to be given rather than assumed.
3. **The remaining prior art.** **Update 2026-08-18: this item is largely spent.**
   academia.edu 166936409 is read in full and contains no `Lambda_DH` and no
   bound on one; Bombieri-Mueller 2008 is identified and carries no
   de Bruijn-Newman content; the Dobner sweep now runs on three independent
   indexes. What a referee can still press on is small and named: the full text
   of Bombieri-Mueller 2008 (publisher wall) and the full text of one citing
   preprint (Voronov 2026, ResearchGate, Cloudflare), both unread. Neither can
   touch a computed number, and the superseded wording of this item is kept
   below.

   **Superseded, kept verbatim:** "The remaining prior art. academia.edu
   166936409, Bombieri-Mueller 2008, and a single-source forward-citation sweep.
   Each is named in `NOVELTY.md` with what it might contain. None of them can
   touch a computed number"."

Note added 2026-08-16, after this gate closed: the separation
`Lambda_DH > Lambda_zeta` (`SEPARATION.md`) offers the same referee nothing
new to attack but inherits both exposures above through its two kinds of
links. Through its decided link (the winding floor `36/625`) it inherits the
`M2` blind spot of item 1 in full; through its cited link it stands on
Polymath 15's Theorem 1.1 as published, unverified in-tree, so an error in
that paper's `0.22` would erase the separation while moving nothing else in
this directory.

**2026-08-18: the separation is untouched by the hardening.** It rests on the
lower bound and on the cited zeta upper bound, and neither moved. The
sharpened upper bound changes only the last, unused link of its chain, from
`<= 1.6025374835598228` to `<= 0.7696992583210755065522` in the wide frame,
which is printed there so the claim travels with the whole bracket. Its two
inherited exposures are now item 1 (the citations, including Polymath 15) and
item 3 (the detector's blindness to a corrupted `M2`) of the ranking above.

## Closure log

The first pass listed five closure items. The re-adjudication brief split them
slightly differently, and both letterings are recorded here so neither reader is
lost: the first pass's `(b)` bundled the winding repair and the missing control,
and carried Bombieri-Ghosh as its own `(d)`; the brief splits those into `(b)`
winding repair and `(c)` missing control, and merges the novelty restatement and
the prior-art item into `(d)`. The brief's lettering is used below.

**Everything in this section was verified by re-running or re-reading in this
session. Not one item was accepted on the repairing session's report.**

### (a) Frame. CLOSED.

`FRAME.md` is new and carries the two conventions, the scaling law derived from
scratch (`Phitilde(u) = (c/a)Phi(u/a)` gives `Htilde_t(z) = c H_{a^2 t}(az)`,
hence `Lambda -> Lambda/a^2` and `Delta -> Delta/a`), a four-row conversion
table, and a numerical check of every row. `THEOREM13.md` section 6's false
sentence, "so the two share zeros and share Lambda exactly", is **preserved
verbatim inside a correction box** with the derivation that replaces it and a
record of what was routed through it, which is the repo's correction style
rather than a deletion. Frame banners are in `MISSION.md`, `STRIP.md` and
`NOVELTY.md`, each saying explicitly that the preregistration below it is
unaltered. `NOVELTY.md` now prints the zeta record in both frames, so the
comparison that flattered by a factor of 4 cannot recur, and it prints the
consequence the old text concealed: in the common wide frame,
`Lambda_zeta <= 0.22 < 0.2304 < Lambda_DH`.

Verified here: the derivation closes algebraically; `4 * 36/625 = 144/625`;
`4 *` the narrow `Delta^2/2` interval is the wide one endpoint for endpoint; the
ratio 6.9554578 is identical in both frames. A side finding the repair
volunteered and that runs against tidiness: Newman-Wu's own kernel is *narrow*,
so the `1/2` on their page 9 and Stopple's page 4 are wide-frame numbers carried
across a frame change unconverted by two refereed papers. That is the best
argument for `FRAME.md` existing and it was not asked for.

### (b) Winding repair. CLOSED.

The false parenthesis, "`n a_n e^{-pi n^2 e^{2u}/5}` is even in `u` termwise",
is superseded by a three-part functional-equation derivation and is **kept
verbatim in a CORRECTION block**. The overstated cushion is corrected to 55.7
with the measurement described (41 x 9 grid plus a 65-point left-edge sweep,
mpmath dps 140, direct quadrature sharing no code with the shifted-contour
bound), and the file states plainly that the correction costs about three extra
halvings of `h` and no decision.

**Re-run here.** `winding.py` reproduces with **zero non-timing differences**
against the pre-re-run file: `t1` decided `N = 1`, 71 segments, chord margin
0.02, ball margin 40.32, `M2 = 1.1886642645115153e-78`, guard PASS at ratio
55.66; `t2` decided `N = 1`, 79 segments, chord 0.02, ball 39.87,
`M2 = 1.137082903400534e-78`, guard PASS at 53.88; `decided_floor_t = 36/625`.
The repair moved no number, as claimed.

### (c) Missing control. CLOSED, and the blind spot is recorded as blind.

Control 5 exists in `controls.py` and `controls_results.json`, holds the `t1`
box, `t`, precision, instrument and subdivision rule fixed and divides only
`M2`. **Re-run here**, zero non-timing differences:

| deflation | status | N | segments | min_chord_margin_digits | min_ball | guard |
|---|---|---|---|---|---|---|
| 1 | decided | **1** | 71 | 0.02 | 40.32 | PASS |
| 10 | decided | **1** | 30 | 0.06 | 40.32 | PASS |
| 72 | decided | **1** | 18 | 0.08 | 40.32 | FAIL |
| 75 | decided | **0** | 11 | 0.00 | 40.32 | FAIL |
| 100 | decided | **0** | 4 | 0.11 | 42.61 | FAIL |
| 1000 | decided | **0** | 4 | 1.11 | 42.61 | FAIL |

Three rows are wrong and silent; the wrong-answer onset is deflation 75; and
both health metrics move the **wrong** way across the lesion, chord 0.02 to
1.11 and ball 40.32 to 42.61. (**2026-08-18**: the table is unchanged and the
history above stands as written. What it measures changed when `M2` became a
proved lemma; see known assumption 6.) The record does not soften any of that: the
verdict field is `BLIND SPOT`, not a pass, `all_pass` is now `false` with
`controls_1_to_4_pass` preserving the older true statement unchanged, and the
`blind_spot` record names the perverse metric, the countermeasure, and three
things still blind including that the guard-before-failure ordering is luck.
Controls 1 to 4 all still pass. This is the item where the repair had the
clearest opportunity to flatter the hunt and did not take it.

### (d) Novelty restatement. CLOSED on substance; residual named and bounded.

"L-function" and "first quantitative" are gone from the deliverable, the gate's
recommended sentence is adopted with Stopple's kernel spelled out, the
superseded sentence is kept verbatim with all four of its faults itemised, and
`NOVELTY.md` ends with three standing instructions ("Do not use 'L-function'.
Do not drop 'so far as the search reaches'. Do not drop the frame.").

The prior-art half went further than the item asked. It asked for a human to
read Bombieri-Ghosh **or** for the `sigma_0` originality claim to be dropped;
both happened. The `sigma_0` claim is withdrawn in `NOVELTY.md`, `FRAME.md`,
`RESULTS.md` and `results.json`, and a misattribution the reading surfaced
(Righetti's 2.3822861089 is originally Bombieri-Ghosh's) is corrected. Two
caveats stated plainly rather than buried: the reading was done by an agent
session and verified by a second agent session, **not by a human**, so if the
gate's word "human" was load-bearing it is still outstanding; and what makes
that tolerable is that the decisive checks are mechanical absence counts over
50 pages, which I ran on my own independently retrieved copy and which agree.

Residual, and it is bounded because every part of it is named: academia.edu
166936409 unread, Bombieri-Mueller 2008 unconsulted, and the Dobner
forward-citation sweep single-source. All three are prior-art risks. **A
prior-art risk bounds novelty, not correctness**: none of them can move an
enclosure, and the claim is conditioned on the search by its own opening words.
The worst case is that the novelty sentence loses the word "first" and the
bracket stands unchanged.

### (e) Independence. CLOSED.

`INDEPENDENCE.md` is new, `independence_decl.py` declares four routes against
`harness/independence.py`, and the adjective is replaced by the measurement
everywhere including `MISSION.md`'s WP1 note and `RESULTS.md`'s P2 row.
**Re-run here**: radius 9 of 12 for routes 1 and 2, radius 0 for the other
three pairs, `matches_gate_8_of_11: true` at the coarser merge, anchors all
present. Both validation gaps are repaired and both repairs re-run clean:
`validate.py` reproduces with zero non-timing differences, `all_pass = True`,
six checks; the `iv` cross-leg now hits the decision-path integrand at 7 of 7
points; the tail-domination check dominates in 18 of 18 rows with minimum ratio
**8.0169**, which is the reported blindness factor 8.02. Route 4 re-run here,
8 of 8 boundary points, 40.3 to 42.7 digits.

Both repairs come with their blindness radius attached, which is the point:
the `iv` leg misses a planted recurrence fault at `u = 5/2` (1 of 7 points,
because at large `u` the sum is its own `n = 1` term), and a tail bound
deflated by less than about 8 passes check 6.

### What the repairs got wrong or left short

Four things, none of which moves a number, all of which are one-line fixes:

1. **`STRIP.md` does not carry the Bombieri-Ghosh finding.** It is the file
   that derives and presents `sigma_0`, and its "Honest scope" section does not
   say that a sharper exact value has been in print since 2011. It makes no
   originality claim, so nothing in it is false, and the finding is in four
   other artifacts. Still, a reader who opens `STRIP.md` alone would overrate
   the constant by omission. One line in section 6.

   **FIXED 2026-08-18.** `STRIP.md` now opens with a superseded-constant
   banner naming both facts: Bombieri and Ghosh's published `1.120362`, and
   that the same abscissa is now derived and decided in-tree in `STRIP2.md`.
   It says in as many words that the upper bound of record is the one in
   `STRIP2.md`, and why this page is kept anyway.
2. **`MISSION.md`'s preregistered deliverable still reads "any RH-violating
   L-function"** with no superseding note, while that same file carries notes
   for items (a) and (e) from this round. The sentence is true as written and
   `MISSION.md` is explicitly a preregistration, but the file is inconsistent
   with itself about which corrections get a note.
3. **`FRAME.md`'s Bombieri-Ghosh row prints 18 digits from an input it labels
   "1.120362 (cited, six decimals)".** The digits are right, but they come from
   `BOMBIERI-GHOSH.md`'s own 29-digit re-solve, not from the citation, and the
   row does not say so. Six decimals alone give 0.192424505522.

   **SUPERSEDED 2026-08-18, and the underlying number corrected.** The row is
   no longer a cited row: `FRAME.md` section 6 now prints the decided in-tree
   value. The 18 digits it used to carry, `0.192424814576128011`, are the
   `tau_+` re-solve's, and that re-solve is now decided to sit about `1.2e-17`
   above its own root, so the correct replacement from the deep flint point is
   `0.1924248145761280190`, agreeing with the old row to 17 digits. The
   headline is the `P = 10^5` two-backend value, which is a different and
   slightly more conservative number and is exact.
4. **`results.json` open item 2 is itself stale**, in the safe direction: it
   warns that `validation.json` may predate the item (e) repairs. It does not;
   the stored file already carried both, and re-running produced zero
   non-timing differences. Discharged by this adjudication.

## PUBLICATION-CANDIDATE RESULT: YES / NO / NOT YET

**YES.** Items (a), (b), (c) and (e) are closed, verified here by re-running the
two load-bearing scripts to zero non-timing differences and by re-reading every
repaired file, and item (d)'s residual is a bounded, named prior-art risk rather
than an unknown.

The first pass's verdict was that the mathematics survived every attack while
two defects stood in the sentences a reader would quote. Both of those sentences
are now repaired, with the false text preserved rather than deleted, and no
computed number moved except by the factor of 4 the frame demands. The prior-art
source that pass called "the unresolved risk" has been read, and I retrieved and
text-checked my own copy rather than trust that: it does not anticipate the
bracket, and it does displace `sigma_0`, which the artifacts now say against
their own interest.

What the reader is being handed, stated at its true strength: a bracket whose
lower side is an enclosure-carrying integer count made strict by a cited
theorem and resting on one prose lemma, and whose upper side is a decided
constant fed to a cited theorem and known to be loose by at least 2.08. Grade
**cited plus decided**, taking the weakest step. Two things must travel with it
and both are in the artifacts: the frame, because the number quadruples without
it, and the `M2` blind spot, because the lower bound carries it and the
detector's own health metric moves the wrong way when it breaks.

**Amended 2026-08-18.** The second of those two is now smaller than it was.
`M2` is a proved lemma (`M2-LEMMA.md`) whose constants are all decided, so
what must travel with the bound is no longer "a prose lemma inside" but the
named cited input the proof needs, the evenness `Phi_DH(-u) = Phi_DH(u)`,
which is assumption 5 restated. The composite grade of the bracket is
unchanged at **cited plus decided**, taking the weakest step, because the
weakest step was and remains a citation.

**Amended again 2026-08-18, after the hardening pass, and the verdict is
still YES.** Nothing in the three tasks broke a claim. What they changed:

* the upper side is no longer "known to be loose by at least 2.08". That
  factor is taken, in-tree and on both backends, and the bracket is
  `0.0576 < Lambda_DH <= 0.19242481458026887663805` narrow and
  `0.2304 < Lambda_DH <= 0.7696992583210755065522` wide, ratio 3.341;
* the lower side is unchanged in every digit. The separation
  `Lambda_DH > Lambda_zeta` rests on the floor alone and is untouched;
* one word in an old sentence is now wrong and is corrected in place: the
  upper side is no longer "a weaker bound on a constant Bombieri and Ghosh
  determined", it is a decided in-tree bound at the same abscissa;
* the referee's first attack is no longer `M2` and no longer the looseness.
  It is the citations, and after them the fact that this directory's two new
  proofs are prose plus decided arithmetic that no human has read.

**What the reader is being handed, restated.** A bracket whose lower side is
an enclosure-carrying integer count made strict by a cited theorem and resting
on one proved lemma whose own weakest input is a citation, and whose upper
side is a decided constant, reached by an elementary in-tree derivation, fed
to a cited theorem. Grade **cited plus decided**, taking the weakest step.
Two things must travel with it and both are in the artifacts: the frame,
because the number quadruples without it, and the detector's blindness to a
corrupted `M2`, because its own health metric moves the wrong way when the
implementation breaks.

What remains is three kinds of residual. The four short items above are
cosmetic; two of them are now fixed and the other two still move no number.
The `M2` blind spot is narrower than it was, real as an implementation
exposure, and disclosed at every headline that depends on it. The two
remaining unconsulted sources bound only the word "first". None of that is a
reason to withhold the work, and all of it is a reason to publish the work
with its caveats attached rather than sanded off, which is the state the
artifacts are now in.

Pending external verification, which is not ours to award.
