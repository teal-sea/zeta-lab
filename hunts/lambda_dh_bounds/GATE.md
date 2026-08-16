# GATE: two-sided bounds for Lambda_DH

Adjudicated 2026-08-16, after four adversary reports and one prior-art report.
Every defect accepted below was reproduced in this session, and every claim
credited to this file was recomputed here rather than taken on report.
Vocabulary per `MISSION.md`: *measured* is one float route, *decided* is an
enclosure whose exact endpoints settle a sign or an integer.

## Exact object / normalization

`Phi_DH(u) = 4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u}/5)` with `a_n` the
period-5 coefficients `(1, kappa, -kappa, -1, 0)`,
`H_t(z) = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du`, and
`Lambda_DH := inf{t : H_t has only real zeros}`; this is the frame in which
`H_0(z) = Xi_DH(z) = F(1/2 + iz)` exactly, which I checked against
`zeta.epstein.completed_dh` at five points with my own quadrature at dps 40
(relative 3.9e-32 to 5.8e-32, including complex `z`). It is a published frame,
Stopple's (arXiv:1301.3158, his `Phi(u,chi)` and `Xi_t(x,chi)` at `D = 5`,
read at source this session), and it is **not** the frame of Newman,
de Bruijn as usually quoted, Rodgers-Tao, Polymath 15 or Dobner, all of which
sit at `s = (1+iz)/2`. I confirmed the conversion numerically, Dobner's
`G_0(z) = Xi_DH(z/2)` and `G_t(z) = H_{t/4}(z/2)` to full quadrature
agreement, so `Lambda(Dobner frame) = 4 Lambda(this frame)` and every number
below must travel with its frame attached.

## Closest prior work

Stopple (arXiv:1301.3158) is nearest and was verified at source: he defines
this normalization character for character, defines `Lambda_{-D}` by the same
closed half-line and `Lambda_Kr = sup Lambda_{-D}`, and publishes the
quantitative bound `-1.13e-7 < Lambda_Kr` for quadratic Dirichlet
L-functions, so any phrasing of the form "first quantitative bound on a
non-zeta de Bruijn-Newman constant" is false. Dobner (arXiv:2005.05142)
supplies existence, finiteness, nonnegativity and the closed half-line for all
of `S#` with no numbers, and de Bruijn 1950 Theorem 13 (typeset restatements:
Dobner's Theorem 3, Newman-Wu 2020 Theorem 7) supplies the `Delta^2/2` engine.
The unresolved risk is Bombieri and Ghosh, *Around the Davenport-Heilbronn
function*, Russian Math. Surveys 66:2 (2011), 221-270, unread and paywalled,
whose published description (Moebius inversion related to the distribution of
zeros in the half-plane of absolute convergence) is exactly the mechanism that
produces `sigma_0`.

## Surviving novelty

A strictly positive two-sided bracket, whose lower side is an
enclosure-carrying zero count, for the de Bruijn-Newman constant of a
Dirichlet series with a Riemann-type functional equation whose Riemann
hypothesis is false. It is not the first non-zeta constant of this type
(Stopple), not the first strictly positive one (Newman-Wu compute `ln 2`
exactly for a three-atom measure), and the upper side is a cited theorem
applied to a constant computed here rather than a new mechanism. The
genuinely new numbers are the Davenport-Heilbronn zero-strip constant
`sigma_0 = 1.39513615823510972106135889...` and the decided off-line zero of
`H_t` at `t = 36/625`, and the first of those is precisely what
Bombieri-Ghosh may already own.

## Lower bound

`0.0576 < Lambda_DH`, with `0.0576 = 36/625` exactly (`0.2304 < Lambda_F` in
the Dobner frame). It rests on a decided argument-principle count `N = 1` for
`H_{36/625}` over a rectangle whose interior has `Im z >= 3/1024 > 0` in exact
rational arithmetic, then monotonicity for `Lambda_DH >= t` and Dobner's
closed half-line for the strict inequality.

## Lower-bound status (rigorous / numerical / failed)

**Numerical**, and only by the letter of this gate's rule: the count is
enclosure-carrying, not float grade (Arb at 420 bits, exact rational contour,
winding ball `[1.0, 1.0]`, minimum ball margin about 40 digits, refusal rather
than a guess on every undecidable segment). Two analytic steps fail "proved
in-tree, or a correctly-applied cited theorem whose hypotheses were verified"
*as written*: `winding.py` justifies the evenness of `G`, the step that
cancels the vertical legs and makes `M2` a bound at all, by a statement that
is false (`n a_n e^{-pi n^2 e^{2u}/5}` is not even in `u` termwise), and the
citation that supplies strictness is routed through `THEOREM13.md` section 6's
false sentence that the hunt's `H_t` and Dobner's deformation "share Lambda
exactly". Both conclusions are true, I measured `Phi_DH(u) = Phi_DH(-u)` to
relative 1.0e-34 and the correct conversion `t -> t/4` preserves the closed
half-line, so both are one-line repairs after which this line reads rigorous.

## Upper bound

`Lambda_DH <= 0.4006343708899557` (`<= 1.6025374835598228` in the Dobner
frame). It is `Delta^2/2` with `Delta = sigma_0 - 1/2`, rounded outward: the
decided flint interval is
`[0.4006343708899556944469547527, 0.4006343708899556944469548120]` and the
headline decimal sits above its upper endpoint, so the inequality is safe.

## Upper-bound status (rigorous / numerical / failed)

**Rigorous**, with the residuals listed below and with the frame stated. Every
numerical step is enclosure-carrying (`kappa` at 500 bits, `sigma_0` bisected
on both backends with exact rational sign decisions, outward rounding checked
by exact rational comparison), the strip argument in `STRIP.md` is elementary
and complete including the boundary equality case and the trivial zeros, and
Theorem 13's hypotheses hold for `Phi_DH`. My own third route (kappa from the
Gauss sum of the odd character mod 5, mpmath Hurwitz zeta at dps 60) returns
`sigma_0 = 1.3951361582351097210613588973`, inside the flint bracket, with `g`
decided negative at its upper endpoint (-1.28e-25) and positive at its lower
(+8.3e-26).

## Independent cross-check

Four, all re-run here: (1) an argument-principle count sharing no code with
the instrument (flow_repair's `DHFlow`, mpmath dps 130, uniform boundary
sampling with continuous-argument tracking) returns total argument
6.283185307179587 and `N = 1.0000000000000002` on **both** published boxes,
`t = 23/400` and `t = 36/625`, which is the first second witness the headline
value 0.0576 has had; (2) a quadrature-free ball route (Gauss-sum kappa,
Hurwitz-zeta `H_0`, `acb_series` Taylor in `t` with an explicit remainder)
reproduces `instrument.H_ball` at all eight boundary points of the `t1` box to
about 22 significant digits, zero mismatches; (3) my own quadrature reproduces
`H_0 = Xi_DH`, and (4) my own strip route reproduces `sigma_0` to every
printed digit. The hunt's own claim of "two independent winding routes" is
weaker than it sounds: measured with `harness/independence.py` the two share 8
of 11 layers, the whole evaluator, and route 2 ran only at `t = 0.0575`.

## Known assumptions

1. **de Bruijn 1950, Duke Math. J. 17, Theorem 13**, all-zeros form,
   transcribed in `THEOREM13.md` by a visual read of an image-only scan.
   Independently re-read from the same scan by one adversary, and corroborated
   by two typeset restatements: Dobner's Theorem 3 (`|Im z| <=
   max(Delta^2 - 2t, 0)^{1/2}`, which I read in the extracted arXiv text) and
   Newman-Wu 2020 Theorem 7.
2. **Its hypotheses for `Phi_DH`**: integrability; hermitian symmetry, here
   evenness, proved in-tree from `F(s) = F(1-s)` and measured by me to
   relative 1.0e-34; and `O(e^{-|u|^b})` with `b > 2`. The last is discharged
   in `THEOREM13.md` by a 201-point grid asserting a margin function is
   increasing on `[2, 30]`, a bounded-range numerical check standing in for an
   unbounded-range claim. The fact itself is immediate from the artifact's own
   domination `|Phi_DH(u)| <= 4 e^{3u/2} e^{-(pi/5) e^{2u}} S(0)`, so this is
   a discharge gap and not a doubt.
3. **Dobner 2020 Theorem 1**, the closed half-line, used only for the
   strictness of the lower bound and applied through the conversion
   `t -> t/4` that the tree states incorrectly. `S#` membership of DH is
   verified condition by condition in-tree and by an adversary against
   Dobner's verbatim text. Without this citation only `Lambda_DH >= 0.0576`
   survives, from in-tree monotonicity (Theorem 13 at `Delta = 0`) or Polya.
4. **Dobner Theorem 2** (`Lambda_F >= 0`): quoted, load-bearing for neither
   side.
5. **Classical facts used without in-tree proof**: Gamma has no zeros and only
   the simple poles at `s = -1, -3, ...`; `F` is entire with `F(s) = F(1-s)`
   (structural, `F = c Lambda(s,chi) + conj(c) Lambda(s,chibar)`). `kappa` is
   decided by an Arb linear solve and agrees to 40 digits with the value I
   derived independently from the Gauss sum `tau(chi)`.
6. **The analytic bound `M2`** in `winding.py`: an in-tree shifted-contour
   derivation whose numerical ingredients are ball-computed but whose
   derivation is prose. It is the single load-bearing step that no control
   exercises; its stated reason for the evenness of `G` is false; and its
   docstring overstates the cushion ("three digits of slack" against a
   measured sup `|H_t''|` of 2.14e-80 versus `M2 = 1.1887e-78`, a factor of
   55.7).
7. **Residual float-grade steps, none load-bearing**: the dps-112 locating
   pass that places the boxes; the WP3 census over heights 412 to 600;
   `calibration.json`'s numerical re-derivation of the `Delta^2/2` dictionary.
   All three are labelled measured in the artifacts.
8. **Tooling**: python-flint 0.9.0 (Arb), mpmath's `iv` context, and the
   exact-rational plumbing. The instrument's two hand-derived tail bounds are
   valid (re-derived and dominated in 59 of 59 adversary tests) but sit 36 to
   41 orders of magnitude below the delivered ball radius at every validation
   point and at the decision point, so `validation.json` has no purchase on
   them; and the only `mpmath.iv` cross-leg in `validate.py` exercises
   `phi_ball`, which no decision path calls, since `_H_core` carries its own
   copy of the series.
9. **Prior art**: the novelty line assumes Bombieri-Ghosh 2011 and
   academia.edu 166936409 contain neither `sigma_0` nor a bound on this
   constant. Neither has been read.

## Reproduction command/artifacts

Backend first, from the repo root:
`.venv/bin/python -c "from zeta import rigor; print(rigor.BACKEND, rigor.available_backends())"`
must print `python-flint`. Then
`.venv/bin/python hunts/lambda_dh_bounds/{strip,validate,winding,winding_quad,controls,census,calibrate_theorem13}.py`,
each of which rewrites its own `*_results.json`; the claim's two decided
numbers are `strip_results.json` (`upper_bound_delta_sq_over_2`) and
`winding_results.json` (`decided_floor_t = 36/625`, `t1_run`/`t2_stretch_run`
both `status: decided, N: 1`). Sources and hypothesis checks are `STRIP.md`,
`THEOREM13.md`, `NOVELTY.md`, `MISSION.md`; adversary write-ups are
`attack_adversary1_normalization.md`, `attack_adversary3_upperbound.md`,
`attack_adversary4_instrument.md`, `attack_adversary5_priorart.md` (the fourth
adversary wrote no file into this directory). This session's checks live in
the scratchpad: `gate_frame2.py` (frame and evenness), `a4_indep_winding.py`
with log `gate_indep_winding.log` (the independent count at both `t`),
`a4_box.py` (quadrature-free evaluator on the box boundary), `a11_deflate.py`
(the `M2` lesion).

## What would a skeptical referee attack first

The frame, and they would be right: `THEOREM13.md` section 6 asserts the hunt
and Dobner "share Lambda exactly" when the truth is a factor of 4, and
`NOVELTY.md` then calibrates 0.4006 against the zeta record 0.22 and 1/2,
which in this frame read 0.055 and 1/8, so the comparison flatters by exactly
that factor. Second, `M2`: deflate it by 100 and `winding.py` returns status
`decided` with the wrong integer `N = 0` after four segments while reporting
`min_chord_margin_digits = 0.11`, five times healthier-looking than the
correct run's 0.02, which I reproduced exactly, so the one unguarded analytic
step is also the one whose health metric moves the wrong way. Third, novelty
and sharpness together: Bombieri-Ghosh is unread and is the likeliest place in
print for `sigma_0`, and 0.4006 is visibly loose (a phase-minimum refinement
inside the hunt's own materials already gives 0.3871, the deepest measured DH
zeros reach `|Im z| = 0.347` against `Delta = 0.895`, and the same domination
applied to zeta returns 3.019 where the truth is 1/2).

## PUBLICATION-CANDIDATE RESULT: YES / NO / NOT YET

**NOT YET.** The mathematics survived every attack, including two independent
recomputations of each side that I ran myself, but two major defects stand in
the artifacts and both sit on the sentences a reader would quote. What closes
it: (a) delete the false sentence in `THEOREM13.md` section 6, replace it with
`G_t(z) = H_{t/4}(z/2)` and `Lambda(Dobner) = 4 Lambda(hunt)`, put the frame
in the headline, cite Stopple for it, and print both pairs of numbers wherever
the zeta record is quoted; (b) repair `winding.py`'s evenness justification to
the functional-equation derivation, correct the overstated slack, and add the
missing fifth control that lesions `M2` and records that a deflated `M2`
yields a wrong integer rather than a refusal; (c) restate the deliverable
without the word "L-function" and without "first quantitative", positioned
explicitly against Stopple; (d) have a human read Bombieri-Ghosh 2011, or drop
the originality claim on `sigma_0` and claim only the bracket; (e) replace
"two independent winding routes" with the measured radius of 8 of 11 plus the
quadrature-free evaluator leg, point the `mpmath.iv` cross-leg at `_H_core`
rather than `phi_ball`, and make the tail-bound domination a standing check.
None of that moves a computed number except by the factor of 4 the frame
demands, so this is a rewrite of the claim's surroundings, not a retraction.
