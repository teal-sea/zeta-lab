# GATE: two-sided bounds for Lambda_DH

Adjudicated 2026-08-16 (verdict NOT YET, five closure items). **Re-adjudicated
2026-08-16 after the repairs, by a session that did not make them.** Every
field below is at post-repair state. Nothing was accepted on report: the two
load-bearing scripts were re-run here and diffed against the pre-re-run files,
the prior-art source the first pass called unread was retrieved and text-checked
in this session, and the frame arithmetic was recomputed. What the first pass
found and what each repair did to it is in the Closure log at the end, together
with four places where the repairs fell short of their own standard.

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

## Upper bound

`Lambda_DH <= 0.4006343708899557` narrow, `<= 1.6025374835598228` wide. It is
`Delta^2/2` with `Delta = sigma_0 - 1/2`, rounded outward: the decided flint
interval is `[0.4006343708899556944469547527, 0.4006343708899556944469548120]`
and the headline decimal sits above its upper endpoint, so the inequality is
safe; the wide interval is that one times four and its headline likewise sits
above the endpoint. The ratio upper/lower is 6.9554578 and is frame-free.

## Upper-bound status (rigorous / numerical / failed)

**Rigorous, with the frame stated, and now known to be loose by a factor of at
least 2.08.** Every numerical step is enclosure-carrying (`kappa` at 500 bits,
`sigma_0` bisected on both backends with exact rational sign decisions, outward
rounding checked by exact rational comparison), the strip argument in
`STRIP.md` is elementary and complete including the boundary equality case and
the trivial zeros, and Theorem 13's hypotheses hold for `Phi_DH`.

What changed since the first pass is not the bound but what is known about it.
Bombieri-Ghosh's `sigma(tau_+, 1) = 1.120362` is the exact abscissa `sigma_0`
bounds, and feeding it through the same engine gives 0.192424814576128011
narrow / 0.769699258304512045 wide, a factor 2.08203. **It is correctly not
adopted**, and the artifacts say why: their value is six published decimals of
Mathematica output resting on Bohr-Kronecker machinery unverified in-tree, so
the improvement is *cited plus measured*, not decided, and swapping it into a
decided headline would launder a grade. I checked both halves of that judgement
here. The arithmetic is right, but it is right against
`BOMBIERI-GHOSH.md`'s own 29-digit re-solve `1.12036249818332508773010350311`,
not against the six decimals the `FRAME.md` row cites as its input (those alone
give 0.192424505522). And their root is reproducible: my own truncated sum over
primes `p = 2, 3 mod 5` with an integral tail correction converges to 1.1203623
at `P = 10^7`, matching all six published digits.

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
6. **The analytic bound `M2`** in `winding.py`: an in-tree shifted-contour
   derivation whose numerical ingredients are ball-computed and whose derivation
   is prose. It is exercised by no cross-route. Its stated reason for the
   evenness of `G` is repaired, and its docstring's cushion is corrected from
   "three digits of slack" to the measured factor **55.7** (measured sup
   `|H_t''| = 2.1357e-80` against `M2 = 1.1887e-78`; 53.9 at `t2`). It is now
   covered by two things that did not exist at the first pass: control 5, which
   lesions it, and `winding.measured_h2_guard`, a necessary-not-sufficient
   float sample of `|H_t''|` by quadrature of the defining integral, wired into
   `winding.main()` with a refusal that voids the floor if it fails. **Standing
   blind spot, recorded rather than repaired; the lower bound carries it.**
7. **Residual float-grade steps, none load-bearing**: the dps-112 locating pass
   that places the boxes; the WP3 census over heights 412 to 600;
   `calibration.json`'s re-derivation of the `Delta^2/2` dictionary. All three
   are labelled measured in the artifacts.
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
9. **Prior art**: **Bombieri-Ghosh 2011 is read** (above), so the novelty line
   no longer assumes anything about it. Three sources remain unconsulted and all
   three bear on novelty, not on correctness: academia.edu preprint 166936409,
   whose subject is the Riemann xi function but which measures DH off-line zero
   lifetimes under this same flow and so may contain an implicit float-grade
   lower bound; Bombieri-Mueller, Forum Math. 20:2 (2008), the parent of the
   method that produced the constant which displaced `sigma_0`; and the forward-
   citation sweep on Dobner, which ran on Semantic Scholar alone because
   OpenAlex returned HTTP 429 with no daily allowance, and is therefore
   single-source.

## Reproduction command/artifacts

Backend first, from the repo root:
`.venv/bin/python -c "from zeta import rigor; print(rigor.BACKEND, rigor.available_backends())"`
must print `python-flint`. Then
`.venv/bin/python hunts/lambda_dh_bounds/{strip,validate,winding,winding_quad,controls,census,calibrate_theorem13,independence_decl,crosscheck_quadfree,crosscheck_dhflow_winding}.py`,
each of which rewrites its own `*_results.json`. The claim's two decided numbers
are `strip_results.json` (`upper_bound_delta_sq_over_2`) and
`winding_results.json` (`decided_floor_t = 36/625`, `t1_run`/`t2_stretch_run`
both `status: decided, N: 1`).

The written record is `RESULTS.md` with `results.json` (64 keyed claims, 16 open
items, each carrying value / frame / grade / backend / precision / source file).
Sources and hypothesis checks: `FRAME.md`, `STRIP.md`, `THEOREM13.md`,
`NOVELTY.md`, `BOMBIERI-GHOSH.md`, `INDEPENDENCE.md`, `MISSION.md`. Adversary
write-ups: `attack_adversary1_normalization.md`,
`attack_adversary3_upperbound.md`, `attack_adversary4_instrument.md`,
`attack_adversary5_priorart.md`.

## What would a skeptical referee attack first

Not the frame any more, and not the novelty sentence. In order:

1. **`M2`.** It is prose, it is load-bearing, no cross-route touches it, and
   the artifacts now hand the referee the exact lesion table rather than making
   them build it. The honest reading of that table is the uncomfortable one:
   the guard trips at deflation 55.7 and the first wrong integer appears at 75,
   so the guard happens to fire first **on this box**, by luck rather than by
   structure, and a derivation wrong by a factor under 55 would pass it and
   could still be wrong. `winding.py` says exactly that.
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
3. **The remaining prior art.** academia.edu 166936409, Bombieri-Mueller 2008,
   and a single-source forward-citation sweep. Each is named in `NOVELTY.md`
   with what it might contain. None of them can touch a computed number.

Note added 2026-08-16, after this gate closed: the separation
`Lambda_DH > Lambda_zeta` (`SEPARATION.md`) offers the same referee nothing
new to attack but inherits both exposures above through its two kinds of
links. Through its decided link (the winding floor `36/625`) it inherits the
`M2` blind spot of item 1 in full; through its cited link it stands on
Polymath 15's Theorem 1.1 as published, unverified in-tree, so an error in
that paper's `0.22` would erase the separation while moving nothing else in
this directory.

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
1.11 and ball 40.32 to 42.61. The record does not soften any of that: the
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
2. **`MISSION.md`'s preregistered deliverable still reads "any RH-violating
   L-function"** with no superseding note, while that same file carries notes
   for items (a) and (e) from this round. The sentence is true as written and
   `MISSION.md` is explicitly a preregistration, but the file is inconsistent
   with itself about which corrections get a note.
3. **`FRAME.md`'s Bombieri-Ghosh row prints 18 digits from an input it labels
   "1.120362 (cited, six decimals)".** The digits are right, but they come from
   `BOMBIERI-GHOSH.md`'s own 29-digit re-solve, not from the citation, and the
   row does not say so. Six decimals alone give 0.192424505522.
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

What remains is three kinds of residual. The four short items above are
cosmetic and none moves a number. The `M2` blind spot is real and is disclosed
at every headline that depends on it. The three unconsulted sources bound only
the word "first". None of that is a reason to withhold the work, and all of it
is a reason to publish the work with its caveats attached rather than sanded
off, which is the state the artifacts are now in.

Pending external verification, which is not ours to award.
