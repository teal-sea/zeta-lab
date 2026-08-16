# RESULTS: two-sided bounds for the de Bruijn-Newman constant of the Davenport-Heilbronn function

Written 2026-08-16, after the gate (`GATE.md`) returned **NOT YET** with a
five-item closure list, and after those repairs were made. This file is the
hunt's written record. It is not a promotion: per `hunts/README.md` and
`MISSION.md`, nothing in this directory is a result until the case log says
how the hunt ended, and the gate's verdict on the artifacts as they stood was
that the mathematics survived every attack while two defects stood in the
sentences a reader would quote.

Vocabulary, per `MISSION.md`. **Measured** is one float route. **Observed** is
a pattern in measured data. **Decided** is an enclosure whose exact endpoints
settle a sign or an integer, stated with backend and precision. **Cited** is
somebody else's theorem. A composite takes the weakest grade of its steps, and
this file says so at every headline. The reserved enclosure vocabulary of
`zeta/rigor.py` appears nowhere in this directory.

Machine-readable form of every number below: `results.json`.

---

## 0. The claim, in both frames

The de Bruijn-Newman constant is not a number attached to a function. It is a
number attached to a function **plus a choice of where the critical line is
parameterised**, and two conventions are in circulation, both refereed, neither
announcing itself. Full derivation, sources and per-row numerical checks:
`FRAME.md`.

    narrow frame :  s = 1/2 + i z     (Stopple arXiv:1301.3158; this hunt;
                                       Newman-Wu's kernel)
    wide frame   :  s = (1 + i z)/2   (de Bruijn as usually quoted; Newman;
                                       Rodgers-Tao; Polymath 15; Dobner;
                                       zeta/heatflow.py)

    Lambda(wide) = 4 * Lambda(narrow),    Delta(wide) = 2 * Delta(narrow).

**In the normalization of Stopple (arXiv:1301.3158), `s = 1/2 + iz`, in which
`Phi_DH(u) = 4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u}/5)` and
`H_t(z) = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du`:**

    0.0576 < Lambda_DH <= 0.4006343708899557,      0.0576 = 36/625 exactly.

**In the normalization of Newman, Rodgers-Tao, Polymath 15 and Dobner,
`s = (1 + iz)/2`, where the same constant is four times larger:**

    0.2304 < Lambda_DH <= 1.6025374835598228,      0.2304 = 144/625 exactly.

The ratio upper/lower is 6.955 and is frame-free (`FRAME.md` section 6). It is
the honest measure of how loose the bracket is.

**Grade of the headline: cited plus decided, and neither side is decided
alone.** The lower side is an enclosure-carrying integer count (decided) turned
into an inequality by monotonicity from de Bruijn 1950 Theorem 13 at `Delta = 0`
(cited) and made strict by Dobner 2020 Theorem 1 (cited), and it additionally
rests on one analytic step, `M2`, whose derivation is prose rather than an
enclosure or a cited theorem (section 5). The upper side is a decided strip
constant (both backends) fed to de Bruijn 1950 Theorem 13 (cited). Taking the
weakest step, **the bracket is a cited-theorem statement about decided
constants, with one prose lemma inside the lower side.**

Why publishing both columns is not pedantry. Read in the common wide frame,
where the zeta literature lives (`FRAME.md` section 7):

    Lambda_zeta <= 0.22     (Polymath 15, cited)
    Lambda_DH   >  0.2304   (this hunt, decided modulo two cited theorems)

so the Davenport-Heilbronn constant sits **above** the best known upper bound
for zeta. Stated in the narrow frame alone, `0.0576` sits below `0.22` and a
reader draws the opposite conclusion. That single comparison is the reason the
frame goes in the sentence every time.

That comparison is now carried as a named claim, **the separation**
(`SEPARATION.md`; sources pinned at source in `POLYMATH-PIN.md`). The chain
in full, every link graded:

    0 <= Lambda_zeta                     cited (Rodgers-Tao Theorem 1)
    Lambda_zeta <= 0.22                  cited (Polymath 15 Theorem 1.1,
                                         unconditional)
    0.22 = 11/50 < 144/625 = 0.2304      exact rational arithmetic:
                                         144 * 50 = 7200 > 6875 = 11 * 625
    0.2304 = 4 * (36/625) < Lambda_DH    decided (winding N = 1 at t = 36/625
                                         narrow, python-flint 0.9.0 (Arb),
                                         420 bits; second witness mpmath dps
                                         130) modulo cited (Dobner Theorem 1)
                                         and the derived frame factor 4
    Lambda_DH <= 1.6025374835598228      decided strip constant fed to cited
                                         de Bruijn 1950 Theorem 13 (not
                                         needed for the separation)

hence, in the wide frame, `Lambda_DH > Lambda_zeta` **unconditionally**.
Composite grade cited plus decided, weakest step cited; the decided link
carries the `M2` prose lemma of section 5. Frame-invariant: in the narrow
frame the chain reads `0 <= Lambda_zeta <= 0.055 < 0.0576 < Lambda_DH`, the
same inequality by the same cross-multiplication (`36 * 200 = 7200 > 6875`).
The sanctioned novelty phrasing, its qualifier ("both constants
nonnegative") and the function-field precedents that make the qualifier
mandatory are in `SEPARATION.md` sections 5 and 6; the exact rational core
is pinned by `tests/test_lambda_dh_separation.py`.

---

## 1. Instrument truth-telling

The instrument is `instrument.py`: exact rational inputs, an Arb ball for
`H_t(z)` and `H_t'(z)` by rigorous adaptive integration of a truncated series
with two hand-derived tail bounds. `validate.py` is its validation runner and
`validation.json` its output.

### 1.1 What validation reports

From `validation.json` (backend python-flint 0.9.0 (Arb)), **six checks after
the gate's repairs**, `all_pass: true`, total 160.0 s:

| check | result |
|---|---|
| 1. containment at 11 points, `H_ball` must contain the independent mpmath float route (and `zeta.epstein.completed_dh` at `t = 0`) | `all_contained: true` |
| 2. `kappa` ball at 500 bits inside `KAPPA_REF +/- 1e-39` | `ball_inside_ref_pm_1e-39: true`, ball radius 1.520111982412233e-148 |
| 3. evenness of `Phi_DH`, enclosures at `u` and `-u` overlap | `all_overlap: true` |
| 4. precision response at `z = 240.4165 + 0.02i`, `t = 23/400` | `strictly_shrinking: true` |
| 5. `mpmath.iv` cross-leg, **now on `instrument._truncated_integrand`**, the exact callable `_H_core` hands to the integrator | `all_overlap: true` |
| 6. **tail-bound domination** against a high-precision computation of the true remainder | `all_dominate: true`, min ratio 8.016926817753845, max 2.06e+96, 7 stress points at large `|Im z|` with min ratio 15.616543746598456 |

Checks 5 and 6 are the gate's closure item (e) landed. Check 5 was pointed at
`instrument.phi_ball`, which no decision path calls; check 6 did not exist.
The superseded text of each is kept at its check in `validate.py` rather than
deleted.

### 1.2 What the gate found that validation does **not** have purchase on

This subsection is as load-bearing as the previous one and is stated at the
same prominence, per the gate's own instruction.

1. **The two hand-derived tail bounds are outside validation's reach.**
   Adversary 4 (`attack_adversary4_instrument.md` section 2e) measured them at
   the parameters `validate.py` uses: the series tail is about 9.47e-210 and the
   `u` tail about 1.68e-160 at the decision point, against a delivered ball
   radius of 1.49e-124 and a float-reference allowance of 1e-135. Both sit 36 to
   41 orders of magnitude below the ball radius. `validation.json`'s containment
   rows would read `contains_float: true` even if `_u_tail` were understated by
   a factor of 1e25 and `_series_tail_finite` by 1e75. The eleven containment
   rows establish that the integrator and the series are right. They establish
   nothing about the tails.

   The tails themselves were audited, independently and for the first time, by
   that adversary: 36 cases for the omega tail, 12 for the series-truncation
   tail, 11 for the integral tail beyond `U`, **all dominating**, with the
   discriminating case at the actual decision parameters clearing the true tail
   by a factor of only 2.28. That is real evidence and it is **measured**, not
   decided.

2. **The only `mpmath.iv` cross-leg pointed at code no decision path calls.**
   `phi_ball` appears in `instrument.py` and `validate.py` and nowhere else;
   `_H_core` carries its own inline copy of the theta-recurrence series, and the
   two copies were never checked against each other. Adversary 4 section 3
   demonstrated this with a planted fault in a copy of the module: dropping the
   factor `n` from the `n = 4 (mod 5)` coefficient inside `_H_core` alone leaves
   `phi_ball` bit-identical while moving `H` at the box corner from 6.2078e-82 to
   1.6608e-07, a shift of 75 orders of magnitude that both winding routes would
   inherit identically.

3. **Four of validation's twenty-two component checks are decided by the
   widening allowance rather than by the data.** On the four real-`z` rows the
   imaginary component's `eps/radius` is about 1.14e+25 (7.1e+28 at prec 600),
   and the unwidened comparison fails, because the dps-150 float reference
   returns a spurious imaginary part around 2.7e-154 while the instrument's
   imaginary ball has radius 8.78e-161 and correctly contains 0. This is the
   reference's round-off and not an instrument defect, and the docstring
   anticipates it, but the reported boolean does not show it.

### 1.2b What the repairs bought, and what they left blind

All three gaps in section 1.2 are now repaired in `validate.py` and the
artifact in section 1.1 is the repaired run. `INDEPENDENCE.md` section 5
records both repairs in full, and two of its numbers belong here because they
bound what the repairs are worth:

- **The `iv` cross-leg now has measured purchase, with one named blind spot.**
  `instrument._truncated_integrand` was hoisted out of `_H_core` as a
  module-level factory, unchanged in operations, order and precision, so the
  callable the integrator receives is reachable; the refactor moved no number
  (`H_ball` at `z = 240.4165 + 0.02i`, `t = 23/400`, prec 420 returns midpoint
  4.3658433958660405e-83 and radius 1.4894837452822593e-124, bit-identical to
  the values already in `validation.json`). Planting a fault in the recurrence,
  seeding `w = q^2` instead of `q^3` so every term carries the wrong power of
  `q`, is caught at **6 of the 7 points**. The point that misses is `u = 5/2`,
  where `exp(-pi e^{2u}/5)` is about `e^{-93}` and the truncated sum is its own
  first term to well below the interval width. **A check at large `u` sees only
  `n = 1`, and that is the blind spot to know about.**
- **The tail check has a stated blindness radius: 8.02.** That is the smallest
  domination ratio over all eighteen rows, so a bound deflated by more than
  about a factor of 8 is caught at one of these points and a bound deflated by
  less is not. The stress regime the gate asked for is included, `|Im z|` up to
  50, which is where the `|cos(zu)| <= cosh(yu) <= e^{yU}` step would fail
  first if it were wrong, and it does not. One row is a deliberate refusal:
  `_u_tail` returns nothing when its own hypothesis cannot be decided, and
  `_H_core` then raises rather than integrating.

Both checks are **measured** and both are necessary rather than sufficient,
exactly like `winding.measured_h2_guard`. Passing does not make a bound right;
failing proves one wrong. Reporting the blindness radius rather than only the
lesion threshold is `docs/25`'s standing consequence, and it is the same lesson
control 5 teaches in the other direction.

### 1.3 What has a second implementation, and what does not

`kappa` is well covered: the Arb self-duality linear solve (`kappa_ball`, 500
bits), the `zeta.epstein` mpmath solve behind `KAPPA_REF`, adversary 4's Gauss
sum route from `tau(chi)` for the odd character mod 5 (a different equation,
overlapping at 200, 400 and 600 bits), adversary 3's independent linear solve at
`s = 2.3 + 1.7i` (dps 50), and `FRAME.md`'s own route, agreeing to 32 digits.
Bombieri and Ghosh's `tau_+ = -phi + sqrt(1 + phi^2)` is the same constant and
agrees to 34 digits (`BOMBIERI-GHOSH.md` section 2).

Not covered by any second implementation before the gate: `_H_core`'s inline
series (checked only against a float route), the three tail bounds at the
`rho = 1` call site, `default_U`, and `acb.integral` itself.

The one genuinely independent evaluator leg is adversary 4's quadrature-free
route, since landed in this directory as `crosscheck_quadfree.py` with output
`crosscheck_quadfree_results.json`: `kappa` from the Gauss sum of the odd
character mod 5 (a different *equation*, not merely a different
implementation), `H_0` by Hurwitz zeta with no quadrature at all, `H_t` by
Taylor in `t` from `dH/dt = -d^2H/dz^2` with an explicit truncation remainder.
At `K = 100`, prec 900, remainder ball 3.0012585847746115e-158 against the
instrument's radius 1.1628170864163578e-124, it agrees with
`instrument.H_ball` at **8 of 8 points on the boundary of the very box that
decides `N = 1` at `t = 23/400`**, zero mismatches, with a
`min_measured_agreement_digits` of 40.32. Both sides are enclosures and the
independent one is about 34 orders of magnitude tighter, so the overlap is a
real agreement rather than a wide ball swallowing a narrow one.

That artifact also corrects a number in the gate's own summary, which is worth
recording because it runs against the hunt's interest: the gate wrote that this
route reproduces the instrument "to about 22 significant digits", and that was
the width of the printed comparison rather than a measurement. The measured
relative agreement, an upper bound for `|taylor - instrument|` over a lower
bound for `|instrument|`, is 40.32 digits at worst over the eight points.

---

## 2. The lower bound

### 2.1 What was decided

`winding.py` (route 1: segment-argument winding), backend python-flint 0.9.0
(Arb), prec 420 bits, exact rational contour, from `winding_results.json`:

| run | `t` | box (Re lo, Re hi, Im lo, Im hi) | segments | winding sum / 2 pi | status | `N` |
|---|---|---|---|---|---|---|
| `t1_run` | 23/400 = 0.0575 | 122929/512, 123185/512, 3/512, 61/1024 | 71 | [1.0, 1.0], width 1.89e-40 | decided | 1 |
| `t2_stretch_run` | 36/625 = 0.0576 | 245909/1024, 123159/512, 3/1024, 35/1024 | 79 | [1.0, 1.0], width 5.45e-40 | decided | 1 |

Both boxes lie strictly inside the open upper half-plane in exact rational
arithmetic: the `t2` box has `Im z >= 3/1024 > 0` throughout. `min_ball_margin_digits`
is 40.32 and 39.87; `min_chord_margin_digits` is 0.02 for both, and section 5
explains why that second number is not a health metric.

`decided_floor_t = 36/625`. The conjugate rectangle in the lower half-plane
carries the same decided count by `H_t(conj z) = conj(H_t(z))`, which the
`kappa` ball plus real coefficients establish (`winding_results.json`,
`symmetry_note`).

### 2.2 By which routes

Four counts reached the same integer, and they are not four independent ones.
The measured radius, per gate closure item (e), replaces the phrase "two
independent winding routes" that `MISSION.md` WP1 and prediction P2 used:

- **Route 1**, `winding.py`, decided `N = 1` at `t = 23/400` and at `t = 36/625`.
- **Route 2**, `winding_quad.py` (ball quadrature of `H'/H`, degree-48
  panel-local Taylor models, prec 420 with Taylor coefficients at prec 700),
  decided `N = 1` at `t = 23/400` on an overlapping but different box
  (`Re` in [2400953/10000, 2405953/10000], `Im` in [1/250, 3/50]). Its winding
  ball is `1 +/- 1.28e-12`. **Route 2 was run only at `t = 23/400`, not at the
  headline `t = 36/625`.**
- **Routes 1 and 2 share 9 of 12 declared layers, independence radius 9**, per
  `independence_results.json`: the whole evaluator is one implementation run
  twice, and their agreement is evidence about the bookkeeping that turns
  `H`-balls into an integer and about nothing upstream of it. The gate's own
  coarser declaration reported 8 of 11, and `independence_decl.py` re-runs that
  granularity to show the two differ by one layer split in two and by nothing
  else (`matches_gate_8_of_11: true`). The load-bearing invariant does not depend
  on the granularity: **the routes duplicate none of the evaluator.** The
  standing caveat is `harness/independence.py`'s own and is not a formality: it
  measures a *declaration*, not the code, and an undeclared shared layer is
  precisely the fault the structure cannot see.
- **The genuinely independent legs are the gate's own**, now landed here rather
  than living in a scratch directory. `crosscheck_dhflow_winding.py` (route 3)
  is an argument-principle count sharing no code with the instrument:
  `hunts/flow_repair`'s `DHFlow` composite Gauss-Legendre evaluator, mpmath
  floats at dps 130, uniform dense boundary sampling with continuous-argument
  tracking refined until every step is under 1 radian. From
  `crosscheck_dhflow_results.json`: 5814 `DHFlow` nodes, 256 boundary
  evaluations per box, maximum consecutive argument step 0.2854607296912167 and
  0.39463362905733557, total argument 6.283185307179587 and
  `N = 1.0000000000000002` on **both** published boxes, `t = 23/400` and
  `t = 36/625`, using route 1's own boxes as recorded in `winding_results.json`;
  `agrees_at_both_t: true`, 348.2 s. The minimum `|H_t|` on the boundary was
  2.4488139927472482e-84 at `t = 23/400` and 8.644114156488054e-85 at
  `t = 36/625`, which is the scale that makes the count hard and is why the
  instrument needs balls rather than floats. Measured radius against route 1:
  **0 shared layers**. That is the first and only second witness the headline
  value 0.0576 has, and it is **measured, float grade, by
  construction**: it cannot decide an integer and does not claim to,
  its job is to catch a wrong one. One layer it does *not* duplicate: its `kappa`
  comes from `zeta.epstein.kappa`, the mpmath form of the *same* self-duality
  linear solve, so its agreement is not evidence about the equation that defines
  `kappa`. Route 4, `crosscheck_quadfree.py` (section 1.3), supplies that leg by
  deriving `kappa` from the Gauss sum instead, and shares with route 1 only the
  Arb backend, reconvergent, radius 0.

### 2.3 The exact logic from a nonreal zero to `Lambda_DH > t`

Let `t2 = 36/625`. The decided count says `H_{t2}` has exactly one zero in a
rectangle whose interior lies in `Im z >= 3/1024 > 0`, so `H_{t2}` has a zero
that is not real, so `H_{t2}` does not have only real zeros.

**Weak inequality, with no appeal to Dobner.** `THEOREM13.md` section 4c: if all
zeros of `H_{t0}` are real, then `Phi_{t0}(u) = e^{t0 u^2} Phi_DH(u)` still
satisfies Theorem 10's conditions (integrable, hermitian, `O(e^{-|u|^{b'}})` for
any `2 < b' < 3`), so Theorem 13 applies to it with `Delta = 0` and gives all
zeros of `H_t` real for every `t > t0`, since `max(0 - lambda^2, 0)^{1/2} = 0`.
Rodgers-Tao attribute the same monotonicity to Polya. Contrapositive: since
`H_{t2}` is not all-real, no `t <= t2` is all-real. Hence

    Lambda_DH >= t2 = 36/625 = 0.0576.

**Strictness, and only here, from Dobner.** Dobner 2020 Theorem 1 states that
`{t : xi_t^F has only real zeros} = [Lambda_F, inf)`, closed at the left end.
Without closedness the all-real set could be `(t2, inf)` and `Lambda_DH` would
equal `t2`. Dobner's theorem is a statement in the **wide** frame. The
conversion, derived in `THEOREM13.md` section 6 and `FRAME.md` section 3 from
his own equations (5) and (6), is

    Phi_F(u) = Phi_DH(2u),      xi_t^F((1+iz)/2) = H_{t/4}(z/2),

and `t -> t/4` is an increasing bijection of the real line, so it carries closed
half-lines to closed half-lines. Hence `{t : H_t all real} = [Lambda_F/4, inf)`
is closed at the left in this frame too, and `Lambda_DH = t2` would force
`H_{t2}` all-real, contradiction. Therefore

    Lambda_DH > 36/625 = 0.0576   (narrow),
    Lambda_F  > 144/625 = 0.2304  (wide, since Lambda_F = 4 Lambda_DH).

`S#` membership of the Davenport-Heilbronn function, which is what licenses
Dobner's theorem, is verified condition by condition in `THEOREM13.md` section 5
and independently against Dobner's verbatim (i)-(iii) by adversary 1 section 4.
No Euler product is required by `S#`, and the function genuinely has none
(`a_6 = a_1 = 1` while `a_2 a_3 = -kappa^2`), which is exactly why it can violate
its own Riemann hypothesis.

**What the frame error did and did not damage.** The earlier text asserted that
this hunt's deformation and Dobner's "share Lambda exactly". That sentence was
false by a factor of 4 and is preserved, inside a correction box, in
`THEOREM13.md` section 6. It did **not** damage the strictness argument, because
only the increasing-bijection property of `t -> t/4` is used there. What it
would have licensed is quoting Dobner's `Lambda_F` for this function as this
hunt's number, four times too large, and what it did cause is the zeta
calibration in `NOVELTY.md`, now repaired.

### 2.4 The margin, honestly

The binding constraint on route 1 is not ball precision. `min_ball_margin_digits`
is 40.32, while `min_chord_margin_digits` is 0.02, so the chord-clearance versus
Taylor-tube inequality clears by a factor of about 1.05. That inequality depends
on `M2`, and `M2` is where section 5 records a standing blind spot.

---

## 3. The upper bound

### 3.1 The strip argument

`STRIP.md` and `strip.py`. With `g(sigma) = sum_{n>=2} |a_n| n^{-sigma} - 1` for
`sigma > 1`:

**(a) Uniqueness.** Every term with `a_n != 0` is strictly decreasing in
`sigma`, and `0 < kappa < 1` is decided by the Arb ball, so `g` is strictly
decreasing and continuous on `(1, inf)`, tends to `+inf` as `sigma -> 1+` and to
`-1` as `sigma -> inf`. Exactly one root `sigma_0`.

**(b) No zeros of `f` for `Re s > sigma_0`.** Strict monotonicity gives
`sum_{n>=2} |a_n| n^{-sigma} < 1`, so `|f(s)| >= 1 - sum_{n>=2} |a_n| n^{-sigma} > 0`.
The bound depends on `Re s` alone, so there is no large-height escape route
(adversary 3 section 2.5).

**(c) The boundary-equality case, `Re s = sigma_0` exactly.** This is the case a
triangle-inequality argument usually leaves open, and it is closed exactly.
Suppose `f(sigma_0 + it) = 0`. Then `W = sum_{n>=2} a_n n^{-s} = -1` with
`|W| = 1 = sum_{n>=2} |a_n| n^{-sigma_0}`, so the triangle inequality is an
equality and every nonzero term is a strictly negative real multiple of a common
unit vector: `n^{-it} = -1` when `a_n > 0` and `n^{-it} = +1` when `a_n < 0`.
Take `n = 3` (`a_3 = -kappa < 0`): `3^{-it} = 1`. Take `n = 4` (`a_4 = -1 < 0`):
`4^{-it} = 1`. Take `n = 12` (`12 = 2 mod 5`, `a_12 = kappa > 0`):
`12^{-it} = -1`. But `12^{-it} = 3^{-it} 4^{-it} = 1`. Contradiction, and `t = 0`
fails the same constraints. Adversary 3 section 2.2 confirms this as airtight and
adds that it is not load-bearing: step (b) at the decided rational
`sigma* = 1.3951361582351097210613589375` already delivers the closed strip
Theorem 13 wants.

**(d) The gamma factor and the reflection.** `(pi/5)^{-(s+1)/2}` is entire and
nonvanishing; `Gamma((s+1)/2)` is nonvanishing with simple poles only at
`s = -1, -3, -5, ...`, all at `Re s <= -1`. So on `Re s >= sigma_0 > 1` the
gamma factor is analytic and nonvanishing and `F = gamma f` has no zero there;
`F` entire with `F(s) = F(1-s)` reflects this to `Re s <= 1 - sigma_0`. Every
zero of `F` lies in the open strip `1 - sigma_0 < Re s < sigma_0`.

**(e) The trivial zeros, and why the claim is about `F` and not `f`.** `1/gamma`
has a simple zero at each `s_m = -(2m+1)`, so `f` vanishes there: `f` has
trivial zeros at `s = -1, -3, -5, ...`, outside the strip, forced by the
functional equation exactly as zeta's are and shifted to the odd negative
integers because the character is odd. "All zeros of `f` lie in the strip" would
therefore be **false**. The decided statement is about `F`, whose zeros are
exactly the nontrivial zeros of `f`. Adversary 3 section 2.4 checked this has
teeth rather than being a formality: measured at dps 50, `f(-1) = 1.02e-51`,
`f(-3) = 3.92e-51`, `f(-5) = 4.89e-50`, `f(-7) = 1.22e-48` while
`F(-1) = F(2) = 1.77952795928`, `F(-3) = 4.29503671195`,
`F(-5) = 16.9670072265` are finite and nonzero, so the zeros of `f` at those
points are simple and cancel the gamma poles exactly. A double zero at any `s_m`
would put a zero of `F` outside the strip and collapse the upper bound; it cannot
happen, because `F(s_m) = F(1 - s_m)` and `1 - s_m = 2m + 2` sits in
`Re s >= 2` where `g(2) < 0` already keeps `f` away from zero.

### 3.2 The decided `sigma_0`, on both backends

From `strip_results.json`. Intervals are outward-rounded decimal strings
containing the exact rational bisection endpoints.

| quantity | python-flint (Arb), 192 bits | mpmath.iv, dps 40 |
|---|---|---|
| `sigma_0` | [1.3951361582351097210613588712, 1.3951361582351097210613589375] | [1.395136158235109178, 1.395136158235109747] |
| `Delta = sigma_0 - 1/2` (narrow) | [0.8951361582351097210613588712, 0.8951361582351097210613589375] | [0.895136158235109178, 0.895136158235109747] |
| `Delta^2/2` (narrow) | [0.4006343708899556944469547527, 0.4006343708899556944469548120] | [0.400634370889955208, 0.400634370889955718] |
| `g(2)` | [-0.7333360538690251425955054390, -0.7333360538690251425955054389] | [-0.733336053869025143, -0.733336053869025142] |

`kappa` is decided at 500 bits in
[0.284079043840412296028291832393126169091088088,
0.284079043840412296028291832393126169091088089], inside `KAPPA_REF +/- 1e-39`
by exact rational comparison. `Delta^2/2 < 0.4007` is decided on both backends
against 4007/10000; `g(2) < 0` is decided on both. 79 flint sign decisions and
46 `iv` decisions, every bisection endpoint an exact rational, every sign settled
by an enclosure excluding zero, an undecided sign a loud abort. The backend
intervals overlap and both sit inside the mission's scouted
`1.39513615823511 +/- 5e-15`. Whole run 1.03 s.

In the wide frame `Delta` doubles to 1.7902723164702194421227177424 and
`Delta^2/2` quadruples to the decided interval
[1.6025374835598227777878190108, 1.6025374835598227777878192480] (`FRAME.md`
section 6).

An independent recomputation from Hurwitz zeta at dps 50, sharing no code with
`strip.py`, returned `sigma_0 = 1.3951361582351097210613588973265388` (adversary
3 section 2.7), inside the flint bracket; adversary 5 section 7 returned
`1.39513615823510972106135889733` by a third route; the gate's own fourth route
returned `1.3951361582351097210613588973` with `g` decided negative at the
bracket's upper endpoint (-1.28e-25) and positive at its lower (+8.3e-26).

### 3.3 de Bruijn Theorem 13, as pinned

`THEOREM13.md` section 1 transcribes Theorem 13 (Duke Math. J. 17 (1950), p. 205)
from the image-only publisher scan by visual page reads:

> THEOREM 13. If F(t) satisfies the conditions of Theorem 10, and if all the
> roots of (3.6) lie in the strip |Im z| <= Delta, then all the roots of
> g(z) = int_{-inf}^{inf} F(t) e^{(1/2)lambda^2 t^2} e^{izt} dt lie in the strip
> (3.8) |Im z| <= {Max (Delta^2 - lambda^2, 0)}^{1/2}.

**All zeros, in both hypothesis and conclusion.** The
"(all but a finite number of the roots)" parenthetical appears in Theorems 11
and 12 on the same and facing pages and is absent from Theorem 13. Adversary 3
section 2.1 re-read the same scan independently and reports Theorems 10 to 14
matching word for word. Two typeset restatements corroborate: Dobner's Theorem 3
(`|Im z| <= max(Delta^2 - 2t, 0)^{1/2}`) and Newman-Wu 2020 Theorem 7
(`|Im z| <= max(Delta^2 - lambda, 0)^{1/2}` for the multiplier
`e^{lambda t^2/2}`). Kill condition 1 of `MISSION.md` is not triggered.

Theorem 10's class conditions are the complete hypothesis set: integrability,
hermitian symmetry `F(t) = (F(-t))*`, and decay `O(e^{-|t|^b})` with `b > 2`.
**There is no positivity condition**, which matters because `Phi_DH` has
mixed-sign coefficients. `Phi_DH` satisfies all three: it is real, so hermitian
symmetry reduces to evenness, which is the functional equation
`F(s) = F(1-s)` in disguise (`THEOREM13.md` section 5 item 2; measured by the
gate to relative 1.0e-34, by `FRAME.md` to 2.0e-41 at `u = 0.1`, and by
adversary 1 to 5.3e-57 in the theta form); and
`|Phi_DH(u)| <= 4 e^{3u/2} e^{-(pi/5) e^{2u}} S(0)` with
`S(0) = 1.32368007594847` gives `b = 3 > 2` (`calibration.json`,
`phi_dh_decay_domination`).

Writing the multiplier as `e^{t u^2}` sets `t = lambda^2/2`, so the all-real
threshold is `t >= Delta^2/2`. This is a statement about the multiplier and is
frame-free, because `Lambda/Delta^2` is invariant under the `z`-rescaling that
separates the two frames (`FRAME.md` section 2). A bound of the form
`Lambda <= Delta^2/2` is a statement about a ratio; a bound of the form
`Lambda <= 0.4006` is not.

### 3.4 The `Delta^2/2` calibration, derived rather than recalled

`calibrate_theorem13.py`, output `calibration.json`. All measured, one route
each. Route 0 first checks that the `e^{tu^2}` multiplier under the integral and
the finite polynomial series both satisfy the backward heat equation
`dG/dt = -d2G/dz2` (worst relative residual 0.0 for the quadrature route at
dps 30, 4.195e-06 for float64 central differences at `h = 1e-5`, consistent with
the `h^2` truncation), which is what licenses calibrating the integral multiplier
with polynomials.

- **Route A, bare conjugate pair** `p(z) = z^2 + Delta^2`: `2t*/Delta^2` is
  1.0 at `Delta = 0.6`, 1.0000000000000 at `Delta = 0.895136` (the DH strip's own
  `Delta`, landing at `t* = 0.40063422924800`), 1.0 at `Delta = 1.2`. A claimed
  factor `Delta^2/8` is violated by a factor of 4 and `2 Delta^2` is slack by 4.
- **Route B, cosine polynomial** `cos z + c`: ratios 0.8366, 0.9839, 0.99967 at
  `c = 2.0, 1.05, 1.001`, climbing to 1 as `c -> 1+`. The constant 1/2 is sharp
  in this family.
- **Route C, pair plus distant real zeros**: ratios 0.9329, 0.99506, 0.99980 at
  `A = 5, 20, 100`. Spectator zeros only accelerate the landing.

Adversary 3 section 2.8 reproduced the same dictionary independently at
`D = 0.3, 0.6, 0.895136, 1.0, 2.0`, all ratios 1.0000000000, and refuted
`D^2/8` and `2D^2` each by a factor of 4.

### 3.5 The upper bound itself

All zeros of `H_0 = Xi_DH` satisfy `|Im z| < Delta` (strictly, section 3.1),
hence a fortiori `|Im z| <= Delta`, so Theorem 13 gives all zeros of `H_t` real
for `t >= Delta^2/2`, hence `Lambda_DH <= Delta^2/2`. The headline decimal
0.4006343708899557 sits above the decided flint upper endpoint
0.4006343708899556944469548120, by 5.553e-18 (adversary 3 section 2.7), so the
inequality is safe and the rounding is outward. It is a rounding, not an exact
value, and should be read as one.

---

## 4. The census and prediction P4

`census.py`, output `census_results.json`. **Everything in the census is
measured, not decided: there are no enclosures anywhere in it** (its own
`summary.grades.counts`).

Coverage: 25 windows spanning heights 412.05 to 600.0, `all_windows_closed: true`.
Accounting `n_strip = n_line + 2 * n_quadruples`: 179 = 167 + 2*6, true. Six
off-line quadruples found, at `gamma` = 440.4845, 520.9438, 531.2797, 548.9068,
566.5097, 595.0234, with depths `y0` = 0.2089, 0.0159, 0.3470, 0.2295, 0.2866,
0.0829.

**P4 verdict: held, observed.** No pair in (412.05, 600.0) beats the
`flow_repair` landing floor 0.05765184034869543 (its pair 5 at `gamma` 240.4047,
measured). The one candidate whose naive `y0^2/2` exceeds the floor is
`gamma = 531.27972689652` with `y0 = 0.34695380309204904` and naive
0.060188470740018166. It lands at 0.05033975468118168 by the N-body ODE null
control (float grade; the instrument matched the Xi-plane contour measurement
within 0.04 percent on `flow_repair` pairs 1 to 5) and at 0.048403 by the fitted
shave model, 12 to 16 percent below the floor.

**A budget honesty note carried from the artifact.** The Xi-plane contour-moment
measurement at `gamma` 531 was **skipped**: it needs dps about 206 and about
27000 quadrature nodes per flow evaluation, projected at 35 to 60 minutes,
more than the whole census budget. The screening question was decided by the ODE
route at the precision that route was validated to. The candidate needs a shave
below 4.4 percent to beat the floor and every surveyed pair of comparable depth
shaves 12.5 to 15.6 percent.

The census does not feed the headline. The decided floor 36/625 = 0.0576 comes
from the winding count at the pair-5 site, and it sits slightly **below**
`flow_repair`'s measured float floor 0.0576518, which is the expected direction:
a decided value is the largest rational the enclosures will carry, not the
measured landing time.

---

## 5. The controls, including the M2 blind spot

`controls.py`, output `controls_results.json`, backend python-flint 0.9.0 (Arb),
geometry from `winding_results.json` `t1_run`.

| control | expectation | observed | verdict |
|---|---|---|---|
| 1, displaced box (`Re + 2`) | `N = 0` decided on an empty box | decided, `N = 0`, 23 segments, winding ball `[-7.6e-42, +7.6e-42]`, ball margin 41.11 digits | PASS |
| 2a, on-axis box (`Im lo = 0`) | loud failure or undecided, never an integer | `ValueError` from the box validator before any `H` evaluation, `n_H_evals = 0` | PASS |
| 2b, edge through the zero (edge-to-zero distance about 2e-18) | undecided, never an integer | `undecided`, failure reason `min_halflen reached`, after 72 segments | PASS |
| 3a, precision response at a fixed point | strictly shrinking radii, factor > 1e10 per 100 bits | 1.42e-94, 1.16e-124, 8.94e-155 at 320/420/520 bits; factors 1.23e30 and 1.30e30 | PASS |
| 3b, precision response of the `N` ball width | strictly shrinking | 2.32e-10, 1.89e-40, 1.45e-70; factors 1.22e30 and 1.30e30 | PASS |
| 4, artifact check on the ball margin | more than 10 digits of growth per 100 bits | 10.23, 40.32, 70.44 digits; growth 30.09 and 30.12 | PASS |
| **5, `M2` deflated** | a detector that could see this lesion would refuse, never return an integer | **it returns integers** | **BLIND SPOT** |

`controls_1_to_4_pass: true`. **`all_pass: false`.** Reporting only
`controls_1_to_4_pass` would be the flattering read and is not the headline.

### 5.1 Control 5, in full

`M2` is the uniform bound for `|H_t''|` on the box. It is the single
load-bearing analytic step in the lower-bound route whose derivation is prose
rather than an enclosure or a cited theorem: its numerical ingredients are
ball-computed (`M2_upper_float = 1.1886642645115153e-78` at the `t1` box,
`1.137082903400534e-78` at `t2`, prec 300, 800 panels), but the shifted-contour
argument that assembles them is written out in `winding.py` and nowhere checked.
Controls 1 to 4 all hold `M2` fixed: two move geometry, two move precision.

The lesion holds the `t1` box, `t = 23/400`, prec 420, instrument and
subdivision rule fixed and changes only the number `M2`:

| deflation | `M2` | status | `N` | correct | segments | `min_chord_margin_digits` | measured-`H''` guard |
|---|---|---|---|---|---|---|---|
| 1 | 1.1886642645115153e-78 | decided | 1 | yes | 71 | 0.02 | PASS |
| 10 | 1.1886642645115153e-79 | decided | 1 | yes | 30 | 0.06 | PASS |
| 72 | 1.6509225895993268e-80 | decided | 1 | yes | 18 | 0.08 | FAIL |
| 75 | 1.5848856860153537e-80 | decided | **0** | **no** | 11 | 0.00 | FAIL |
| 100 | 1.1886642645115152e-80 | decided | **0** | **no** | 4 | **0.11** | FAIL |
| 1000 | 1.1886642645115152e-81 | decided | **0** | **no** | 4 | **1.11** | FAIL |

`wrong_answer_onset_factor: 75`, `n_wrong_and_silent: 3`.

**Why it matters.** `M2` too large costs only compute. `M2` too small silently
licenses a segment whose true argument variation exceeds `pi`; the branch
resolution `Delta = Arg q` is then wrong by `2 pi`, which lands in the sum as a
whole unit of winding. The failure mode is a wrong integer with status
`decided`, which is the one output this routine promises never to produce.

**The perverse metric.** `min_chord_margin_digits` is
`log10(dist(0, chord) / tube radius)` minimised over accepted segments.
Deflating `M2` shrinks the tube, so the ratio grows: the correct run reports
0.02, the wrong `N = 0` run at factor 100 reports 0.11, and at factor 1000
reports 1.11. **The detector's own health metric reads about five times
healthier exactly as the answer becomes wrong**, and it may not be used as a
guard on `M2`. `min_ball_margin_digits` is no better here: it moves from 40.32 to
42.61 across the same lesion, because the wrong runs accept fewer and larger
segments and never sample the tight ones.

**The countermeasure now in place**, `winding.measured_h2_guard`: `M2` must
dominate a directly measured `sup |H_t''|` sampled on the box by quadrature of
the defining integral, on `flow_repair`'s `DHFlow` rule, sharing no code with
the shifted-contour derivation. On the honest `M2` it passes with
`measured_sup_absH2 = 2.1357367685579024e-80` at the `t1` box against
`M2 = 1.1886642645115153e-78`, a ratio of 55.66 (53.88 at `t2`).
`winding.py`'s `main()` refuses the floor when the guard fails.

**What is still blind, and it is three things.** (1) The guard is a finite grid
of a smooth function; a peak between nodes is invisible to it. (2) The guard is
float grade, so it cannot upgrade `M2` from prose to decided; only an in-tree or
Lean derivation of the shifted-contour step would do that. (3) **The ordering
that makes the guard useful on this box is luck, not structure**: the guard trips
once `M2` falls below the measured sup, at deflation past 55.7, while the first
wrong integer observed appears at deflation 75. Nothing guarantees that ordering
on another box, and a derivation wrong by a factor under 55 would pass the guard
and could still be wrong.

**This is recorded, not repaired.** It is a standing blind spot in the
lower-bound route, and any statement of the bound carries it. Note also, in
fairness to the artifact's own honesty, that the docstring previously described
the `M2` cushion as "three digits of slack" against the measured sup, when the
measured factor is 55.7; that overstatement was named by the gate and corrected
in `winding.py`.

### 5.2 Rival framing, carried from WP4

The same pipeline pointed at zeta yields no positive floor: the lower bound
needs a box around a zero strictly off the real axis of the corresponding `H_t`,
and no off-line zero of zeta is known, so every box this detector could honestly
place for zeta would decide `N = 0`, as the displaced-box lesion does for an
empty window. The number this hunt produces separates DH from zeta only through
the already-known off-line zeros (Davenport-Heilbronn 1936; computed by Spira
1994). **Nothing here is evidence about the Riemann hypothesis**, which is
`flow_repair`'s P5 moral restated. `zeta.epstein.battery` referees structural
claims that purport to explain RH by distinguishing zeta from an RH-violating
rival; this hunt makes no such claim, and its object of study *is* that rival.

---

## 6. The pre-registered predictions, settled

| | prediction (`MISSION.md`) | outcome |
|---|---|---|
| **P1** | the winding count at `t1 = 0.0575` decides `N = 1` in the open upper half-plane box, on the first budget, with >= 30 digits of sign margin on every boundary segment | **held on the ball margin, and the prediction was ambiguous about which margin it meant.** `t1_run`: decided, `N = 1`, 71 segments, no budget failure, `min_ball_margin_digits = 40.32`, which clears 30. But `min_chord_margin_digits = 0.02`, and that is the binding constraint (section 2.4). Control 4 records that the chord-tube margin is excluded from its gate by design, because adaptive subdivision stops at the first decided pass and so it measures the stopping rule rather than the instrument. Read as "ball margin", P1 held with 10 digits to spare. Read as "every margin", it did not. |
| **P2** | the two winding routes agree exactly (both decide `N = 1`) | **held as stated, and the adjective in it did not.** Route 1 decided `N = 1` at `t = 23/400` and `t = 36/625`; route 2 decided `N = 1` at `t = 23/400` on an overlapping box, winding ball `1 +/- 1.28e-12`. But the routes share 8 of 11 declared layers, the whole evaluator, so the agreement is evidence about the bookkeeping only, and route 2 never ran at the headline `t`. `MISSION.md`'s phrase "two independent winding routes" is replaced everywhere by that measured radius. |
| **P3** | `sigma_0` lands in [1.3949, 1.3954] on both backends and the intervals overlap | **held exactly.** flint [1.3951361582351097210613588712, ...9375], iv [1.395136158235109178, ...747], `backend_intervals_overlap: true`, both inside the scouted value plus or minus 5e-15. |
| **P4** | no surveyed pair beats 0.0576518 below height 600 | **held, observed.** 179 strip zeros, 6 quadruples, 25 closed windows, deepest new pair at `gamma` 531.28 landing 0.05034 (ODE) and 0.048403 (model) against the floor 0.0576518. |
| **P5** | the headline lands as `0.0575 < Lambda_DH <= 0.400634`, a ratio of about 7 | **held, and slightly better on the lower side**, at the stretch value: `0.0576 < Lambda_DH <= 0.4006343708899557`, ratio 6.955. The prediction carried no frame, and needs one: in the wide frame it reads `0.2304 < Lambda_DH <= 1.6025374835598228`, and the ratio is the frame-free quantity. |

---

## 7. The gate

`GATE.md`, adjudicated 2026-08-16 after four adversary reports and one prior-art
report, verdict **NOT YET**. Every defect it accepted was reproduced in that
session and every claim credited to it recomputed there.

### 7.1 What the adversaries found

- **Adversary 1 (normalization).** The interval survives as a statement about
  the object the claim defines, and does not survive as a statement about the
  object it is named after: `Lambda(Dobner) = 4 Lambda(hunt)`. `H_0 = Xi_DH` with
  `(c, a) = (1, 1)` confirmed at nine points, rivals excluded by orders of
  magnitude; the Mellin derivation, the factor 4, the `e^{3u/2}`, evenness to
  5.3e-57, and `S#` membership all confirmed. The false sentence in
  `THEOREM13.md` section 6 named and its consequences traced.
- **Adversary 3 (upper bound).** The inequality survives. Theorem 13 re-read from
  the original scan and matching word for word; the triangle-equality case
  airtight; the trivial-zero trap worked out and holding; `sigma_0` recomputed
  independently to 30 digits; the `Delta^2/2` dictionary recalibrated and
  `Delta^2/8` and `2 Delta^2` each refuted by a factor of 4. One major defect
  reported: the same normalization error.
- **Adversary 4 (instrument and independence).** The claim survives this lane:
  neither tail bound could be broken in 59 tests, and a route to `H_t` sharing no
  layer with the instrument below Arb itself agrees at 8 of 8 box-boundary points
  with a ball 34 orders tighter. The independence story does not survive: 8 of 11
  shared layers, three of five validation checks with no purchase on what is
  neither a library call nor cross-checked, and a planted fault demonstrating the
  `iv` leg's blindness.
- **Adversary 5 (prior art).** No source states a numerical bound, from either
  side, on a de Bruijn-Newman constant of this function or of any RH-violating
  function. Four corrections required, including Stopple as the published
  precedent for this hunt's own frame *and* as a prior quantitative non-zeta
  bound, Newman-Wu Theorem 7 as the typeset engine, and Bombieri-Ghosh 2011 as an
  unread high-probability risk to the strip constant.

### 7.2 What was repaired

| gate item | repair |
|---|---|
| (a) frame | The false sentence in `THEOREM13.md` section 6 is superseded and preserved inside a correction box, with `Phi_F(u) = Phi_DH(2u)`, `xi_t^F((1+iz)/2) = H_{t/4}(z/2)` and `Lambda(Dobner) = 4 Lambda(hunt)` derived in its place and checked to 15 digits by code sharing nothing with `instrument.py`. `FRAME.md` is new and carries the conversion table, the scaling law and every row's numerical check. Frame notes are added to `MISSION.md` and `STRIP.md`. `NOVELTY.md` now prints the zeta record in both frames. Stopple is cited as the frame's published source. |
| (b) winding repair | The evenness of `G` is now justified by the functional equation `F(s) = F(1-s)` rather than by the false termwise claim, and the overstated "three digits of slack" is corrected to the measured factor 55.7. |
| (c) missing control | Control 5 exists, is recorded as a blind spot rather than as a pass, and `all_pass` is now `false` with `controls_1_to_4_pass` preserving the earlier true statement unchanged. |
| (d) novelty restatement | "L-function" and "first quantitative" are gone; the gate's recommended sentence is adopted verbatim in `NOVELTY.md` and reproduced in section 8 below. |
| (e) independence | "Two independent winding routes" is replaced by the measured radius everywhere; `independence_decl.py` declares four routes against `harness/independence.py` and writes `independence_results.json`; both of the gate's genuinely independent legs are landed as reproducible scripts (`crosscheck_dhflow_winding.py`, `crosscheck_quadfree.py` with `crosscheck_quadfree_results.json`), on the principle that a cross-check living only in a scratch directory is not evidence anyone can reproduce; `validate.py`'s `iv` cross-leg now points at `instrument._truncated_integrand` rather than `phi_ball`, and a standing tail-domination check is added as check 6. |

One repair went beyond the list. `BOMBIERI-GHOSH.md`: the source the gate called
"the unresolved risk" and "unread and paywalled" was retrieved and read in full
the same day (mathnet.ru id `rm9410`, not `umn9410`, and `www.mathnet.ru` rather
than `mi.mathnet.ru`, which 503s). Its verdict is mixed and is stated in
section 8.

### 7.3 What remains open

Stated at least as prominently as the positive results, per the house rule.

1. **`M2` is a standing blind spot** (section 5.1). It is prose, it is
   load-bearing on the lower side, its lesion produces a wrong integer with
   status `decided`, and the guard that now covers it is measured, finite-grid,
   and useful on this box by luck rather than by structure. **The lower bound
   carries this.**
2. **The two validation repairs have stated blindness radii, and they are not
   large.** The `iv` cross-leg misses a planted recurrence fault at `u = 5/2`,
   because a check at large `u` sees only the `n = 1` term (1 of 7 points). The
   tail-domination check has a blindness factor of 8.02: a bound deflated by
   less than about a factor of 8 passes it. Both are measured and neither can
   upgrade the thing it checks.
3. **Route 2 never ran at the headline `t = 36/625`**, only at `t = 23/400`,
   and on its own recipe box rather than route 1's, because route 1's output
   file did not exist when it ran. So even the bookkeeping agreement of P2 is
   one `t` and one box wide, and the stretch value that carries the published
   floor has no route-2 witness at all. The second witness at the headline `t`
   is the `DHFlow` count of `crosscheck_dhflow_winding.py`, which is float
   grade at mpmath dps 130, not an enclosure, and it says so: it cannot decide
   an integer and does not claim to, its job is to catch a wrong one.
4. **The upper bound is visibly loose, by three independent measures.** The
   phase-minimum refinement inside the hunt's own materials already gives
   0.38710055 at `M = 12` (adversary 3, section 3, float grade); the deepest
   measured DH zeros reach `|Im z| = 0.347` against `Delta = 0.895`; and the same
   coefficient domination applied to zeta returns 3.0191480758 in the wide frame
   where the truth is 1/2, a factor of 6.04 that the Euler product buys zeta and
   this function cannot.
5. **A sharper strip constant is available by citation and has not been
   adopted.** Bombieri and Ghosh's `sigma(tau_+, 1) = 1.120362` gives
   `Delta = 0.620362...` and `Delta^2/2 = 0.192424814576128011` (narrow),
   `0.769699258304512045` (wide), a factor 2.082 better. It is **cited plus
   measured, not decided**: their value is a six-decimal Mathematica number and
   their Theorem 7 rests on Bohr-Kronecker machinery this tree has not verified.
   Adopting it needs their hypotheses checked in-tree and the arctan equation
   re-solved with outward rounding. **Do not silently swap the headline.**
6. **One source bearing on the claim is still unread**: academia.edu preprint
   166936409, whose recovered abstract fragments describe measured lifetimes of
   Davenport-Heilbronn off-line zeros under this same backward flow, and so may
   contain, implicitly, a float-grade lower bound. Its provenance could not be
   determined from inside this checkout.
7. **One sweep is single-source**: the forward-citation search on Dobner ran on
   Semantic Scholar alone, because OpenAlex returned HTTP 429 with zero daily
   allowance. It should be repeated against Google Scholar or MathSciNet.
8. **One hypothesis discharge is a bounded-range check standing in for an
   unbounded-range claim.** `THEOREM13.md` section 5.3 asserts the decay margin
   `g(u) = (pi/5) e^{2u} - (3/2)u - u^3` is increasing on [2, 30] from a
   201-point grid. The fact itself is immediate from the artifact's own
   domination, and one line settles it (`g'(u) = (2 pi/5) e^{2u} - 3/2 - 3u^2`,
   which is 68.6 against 13.5 at `u = 2`), so this is a discharge gap and not a
   doubt.
9. **Bombieri-Mueller 2008**, *On the zeros of certain Epstein zeta functions*,
   the parent of the constant that displaced `sigma_0`, has not been consulted.
10. **The two winding routes do not use the same box.** They overlap and both
    decide `N = 1`, which is arguably better than identical boxes, but a reader
    should not have to diff two JSON files to learn it.
11. **Classical facts used without in-tree proof**: `Gamma` has no zeros and only
    the simple poles at `s = -1, -3, ...`; `F` is entire with `F(s) = F(1-s)`
    (structural, measured in-tree to defect about 1e-50 and test-pinned).
12. **Residual float-grade steps, none load-bearing**: the dps-112 locating pass
    that places the boxes, the whole WP3 census, and `calibration.json`'s
    numerical re-derivation of the `Delta^2/2` dictionary. All three are labelled
    measured in the artifacts.
13. **There is no second rigorous integrator.** `acb.integral` has no
    counterpart in mpmath's `iv` context, and the in-tree precedent
    `zeta.rigor.enclose_weil_functional` is flint-only and says so. Route 4 is
    the answer to this and it is a route rather than a backend: it reaches
    `H_t` with no quadrature at all and agrees to the instrument's full
    resolution. What no leg supplies is a second integrator.
14. **`M2` is exercised by no cross-route.** Routes 3 and 4 evaluate `H`;
    neither computes a uniform second-derivative bound. This is item 1 seen
    from the independence side (`INDEPENDENCE.md` section 6).
15. **A declaration is not an attestation.** Nothing in
    `harness/independence.py` verifies that the layer lists are complete, and
    an undeclared shared layer is exactly the fault the structure cannot see.
    `independence_decl.check_anchors` pins ten attribute names against drift,
    which catches a rename that would make a layer name a fiction; ten anchors
    are not a completeness proof.

---

## 8. Honest scope and novelty

### 8.1 The sentence

Adopted verbatim from `NOVELTY.md`, which adopted it from the gate:

> So far as the literature search recorded in `NOVELTY.md` reaches, these are
> the first quantitative bounds, from either side, on the de Bruijn-Newman
> constant of a Dirichlet series with a Riemann-type functional equation whose
> Riemann hypothesis is false. They are stated in the normalization of Stopple
> (arXiv:1301.3158), in which
> `Phi(u) = 4 sum_n a_n n exp(3u/2 - pi n^2 e^{2u}/5)`, and are four times
> smaller than the same constant in the normalization of Newman, Rodgers-Tao,
> Polymath 15 and Dobner.

The word "L-function" is not used: the Davenport-Heilbronn function has no Euler
product, which is the entire reason it can violate its own Riemann hypothesis and
why Dobner needs the *extended* Selberg class. The phrase "first quantitative" is
not used: Stopple has an unconditional quantitative bound on a non-zeta constant
of exactly this type (`-1.12929e-7 < Lambda_Kr`), and Newman and Wu determine one
exactly (`ln 2`) for a three-atom measure. "So far as the search reaches" is not
droppable, and neither is the frame.

The mandatory footnote is in `NOVELTY.md` and is not to be compressed. Its
substance: existence, finiteness and nonnegativity are Dobner's, for all of
`S#`, with no member named and no number given; the upper bound's mechanism is
de Bruijn's 1950 theorem, surveyed as Newman-Wu Theorem 7, applied to a strip
computed here; and the strip constant is not new either.

### 8.2 What Bombieri and Ghosh cost the claim, and what they hand it

`BOMBIERI-GHOSH.md`, read in full 2026-08-16, 50 pages, English translation,
free at mathnet.ru. The verdict has two halves pointing in opposite directions.

**On `Lambda_DH`: closed, in the hunt's favour.** Zero occurrences of Bruijn,
Newman, heat, Polya, Turan, Lambda or deformation, in the text and in all 28
references. Nothing in it bears on the de Bruijn-Newman constant, on `H_t`, or
on the backward heat flow. The novelty sentence needs no change on account of it.

**On `sigma_0`: closed, against the hunt.** Their section 5 defines
`sigma(xi, q)` as the least upper bound of the real parts of the zeros; their
Theorem 7 determines it as the root of
`sum_{p = 2,3 mod 5} arctan(p^{-sigma}) = pi/2 - |theta|` with `xi = tan theta`;
their section 6 evaluates it for this very function at
`sigma(tau_+, 1) = 1.120362`, and their `tau_+` is this hunt's `kappa`, agreeing
to 34 digits. **`sigma_0 = 1.395136...` must not be described as a new number.**
It is a triangle-inequality upper bound on a quantity these authors determined
exactly, and theirs is sharper. What survives is the derivation and not the
quantity: an enclosure-carrying elementary route, from a two-line argument that
invokes no Bohr-Kronecker theory, to a weaker bound on a constant already known.

Two independent verification legs were run against their paper. Their section 9
claim that the smallest prime set with `sum arctan(p^{-1}) > pi/2` for
`p = 2, 3 mod 5` ends at 6323 with 420 primes reproduces exactly, by direct prime
summation sharing no code (**decided**, a finite exact prime set and integer
answers). Their Theorem 7 roots reproduce to every published digit at
`sigma(0,1) = 1.06702646637238936888624138422`,
`sigma(tau_+,1) = 1.12036249818332508773010350311`,
`sigma(tau_-,1) = 2.38228610898712386578711039387` and four Table 1 entries
(**measured**, and honestly a reproduction of their method rather than an
independent route).

They also supply context worth carrying: for small `xi` the zeros with
`Re s > 1` are extraordinarily rare, and for `xi = 0` a search of
`1/2 <= sigma < 1.2`, `0 <= t < 10000` found 5,358 zeros and **no** zero with
real part above 1. The Davenport-Heilbronn function proper sits at the hard end
of that spectrum, which is consistent with the looseness recorded in section 7.3
item 4. And an attribution is corrected: `sigma* = 2.3822861089...` for the
sibling root `tau_- = -1/kappa` is Bombieri and Ghosh's constant, not Righetti's;
he quotes it.

### 8.3 Scope

- **Nothing here is evidence about the Riemann hypothesis.** The lower bound
  exists only because this function has known off-line zeros, which is what makes
  it a counterexample function in the first place (`docs/08`, `docs/09`).
- The bracket is a statement about `Lambda_DH` in a named frame, and about
  nothing else. `sigma_0` and the ratio 6.955 are the frame-free quantities.
- The upper side is a **cited theorem applied to a decided constant**, not a new
  mechanism, and the constant it is fed is not new either. The lower side is a
  **decided integer count** turned into an inequality by two cited theorems, with
  one prose lemma (`M2`) inside it.
- Grades, per the vocabulary contract: `sigma_0`, `Delta`, `Delta^2/2 < 0.4007`,
  `g(2) < 0`, `kappa`, and the winding integers `N = 1` at both `t` are
  **decided**, with backends and precisions stated. The census, the calibration,
  the locating pass, the `M2` measured guard and every cross-check ratio in
  section 1 are **measured**. de Bruijn Theorem 13, Dobner Theorems 1 and 2,
  Newman-Wu Theorem 7 and Bombieri-Ghosh Theorem 7 are **cited**.
- Per `MISSION.md`, this hunt may not promote its claim into `README.md`,
  `ROADMAP.md` or `HANDOFF.md` as an established finding, and this file does not.

---

*Artifacts: `MISSION.md`, `FRAME.md`, `STRIP.md`, `THEOREM13.md`, `NOVELTY.md`,
`BOMBIERI-GHOSH.md`, `INDEPENDENCE.md`, `GATE.md`, the four
`attack_adversary*.md` reports, and the JSON outputs `validation.json`,
`calibration.json`, `strip_results.json`, `census_results.json`,
`winding_results.json`, `winding_quad_results.json`, `controls_results.json`,
`independence_results.json`, `crosscheck_quadfree_results.json` and
`crosscheck_dhflow_results.json`. Machine-readable claims: `results.json`.*
