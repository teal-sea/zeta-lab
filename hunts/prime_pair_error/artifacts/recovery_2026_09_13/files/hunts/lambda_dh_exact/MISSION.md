# MISSION: is Lambda_DH exactly Delta^2/2, or is the gap real?

**Opened 2026-08-18. Hunt #119** (renumbered from #52 on 2026-09-12).
Nothing in this directory is a result until
the case log in `hunts/README.md` says how it ended. Probe discipline as in
`hunts/lambda_dh_bounds/MISSION.md`: the strongest words used here are
*measured* (one float route), *observed*, *decided* (an enclosure whose exact
endpoints settle a sign or an integer) and *cited* (somebody else's theorem).
A composite claim takes the grade of its weakest step. The reserved enclosure
word belongs to `zeta/rigor.py` and appears nowhere in this directory.

This is the theory phase. **Nothing below has been measured on the
Davenport-Heilbronn function at a new height.** Sections 1 to 5 derive; the
numerics quoted are polynomial-flow verifications of the derivations plus a
calibration against landing times already measured in `hunts/flow_repair/` and
`hunts/lambda_dh_bounds/census_results.json`. Section 6 pre-registers what the
later phases must find, with numbers, before any of them runs.

```huntspec
id: lambda_dh_exact
question: Does the crowding shave vanish along a sequence of Davenport-Heilbronn zeros whose depth approaches Delta, so that sup t* = Delta^2/2 and the bracket 0.0576 < Lambda_DH <= 0.19242481458 collapses to a point, or does the shave stay bounded away from zero so the gap is real?
frontier: narrow frame, decided both sides: 36/625 = 0.0576 < Lambda_DH <= 0.19242481458026887663805 = Delta^2/2 with Delta = 0.62036249819 sharp (Bombieri-Ghosh 2011 Theorem 7; necessary half re-derived and decided in STRIP2.md); ratio 3.341; best measured landing 0.05765184035 at gamma = 240.4046, y0 = 0.3695261
proposed_attack: derive the landing law dy/dt = -1/y - 2 pi rho from the N-body identity dQ/dt = 2 - 4Q sum 1/((x-a)^2 - Q), calibrate it on ten already-measured Davenport-Heilbronn landings, and decide whether sup over pairs of t* can reach Delta^2/2 given that depth near Delta forces great height and great height forces large rho
dead_routes:
  - raising the floor by surveying above height 600 without first raising the depth: the census of hunts/lambda_dh_bounds found six quadruples in (412, 600) and none beat 0.0576518, and the derived law says depth, not height, is the only variable that helps
  - reading the isolated-pair law y0^2/2 as a ceiling for an individual pair: six of three hundred two-pair configurations land later than y0^2/2 under exact polynomial flow, so only Delta^2/2 is a ceiling
  - the census's linear-in-log-gamma shave fit tstar = (y0^2/2)(1 - (A + B log gamma) y0^2): it is a local linearization of a law that is quadratic in log gamma, and it under-predicts the shave when extrapolated above the heights it was fitted on
  - float64 exact polynomial flow above degree about 30 with closely spaced roots: it reports a wrong landing time that looks fine, and the t = 0 admissibility gate is what catches it
required_oracles:
  - exact polynomial heat flow, coefficients evolved in closed form, checked against the closed-form quartic root
  - the argument principle applied with directed-rounding interval arithmetic on both ball backends
  - de Bruijn 1950 Theorem 13 and Dobner arXiv:2005.05142 Theorem 1, as published
  - Bombieri and Ghosh, Russian Math. Surveys 66:2 (2011) 221-270, Theorem 7 and section 9, as published
  - the landing times already measured in hunts/flow_repair and hunts/lambda_dh_bounds, used as a holdout rather than as training data where they were not fitted
kill_conditions:
  - a single Davenport-Heilbronn pair is found whose decided landing time exceeds the calibrated model prediction by more than a factor 1.25, which retires the model
  - the depth-versus-height law is falsified: a zero with y0 > 0.55 is found below height 10^4, or no zero with y0 > 0.40 is found below height 10^4
  - the no-creation step of section 2 fails, that is, a configuration is exhibited in which forward flow drives two real zeros off the axis, which breaks Lambda_DH = sup t* and reduces every landing time to a lower bound only
  - the sup of landing times is observed to increase with height rather than peak, over at least two decades of height, which reverses the verdict
  - the model's own consistency fails: its sup falls below the decided floor 36/625
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
  - measure landing times and depths at new heights
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - state a value for Lambda_DH; the deliverable is a bracket and a mechanism
  - edit anything outside hunts/lambda_dh_exact, figures/, and one new docs/NN file
```

---

## 0. What is already fixed, and what this hunt is allowed to move

Everything in this section is inherited, with its grade, from
`hunts/lambda_dh_bounds/`. None of it is re-litigated here.

| quantity | value | grade |
|---|---|---|
| `kappa` | `sqrt(1+phi^2) - phi`, `phi` the golden ratio | decided |
| `Phi_DH(u)` | `4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u}/5)`, `a_n = (1, kappa, -kappa, -1, 0)` | derived |
| `H_t(z)` | `int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du`, `H_0(z) = F(1/2+iz)` exactly | measured to 7.2e-41 |
| frame | narrow, `s = 1/2 + iz` (Stopple). Wide frame numbers are 4x | derived, `FRAME.md` |
| `sigma_0'` | `1.12036249819` | decided, both backends |
| `Delta = sigma_0' - 1/2` | `0.62036249819` | decided |
| upper bound `Delta^2/2` | `0.19242481458026887663805` | cited (de Bruijn Th. 13) plus decided |
| floor `36/625` | `0.0576` | decided (winding `N = 1`) |
| best measured landing | `0.05765184035` at `gamma = 240.4046`, `y0 = 0.3695261` | measured |

**The one inherited fact this hunt is entirely built on, and it is cited, not
derived here.** Bombieri and Ghosh determine `sigma(tau_+, 1) = 1.120362` as
the *least upper bound* of the real parts of the zeros of `F`. `STRIP2.md`
re-derives and decides only the **necessary** half of their Theorem 7, that is,
no zero lies to the right of `sigma_0'`. Their **converse**, which is what makes
`Delta` an attained-in-the-limit supremum rather than merely an upper bound,
is neither used nor claimed anywhere in `lambda_dh_bounds`. This hunt's whole
question presupposes that converse: without it there may simply be no zeros
with `y0` near `Delta`, and the bracket would be open for the dull reason that
its upper end was never sharp. So the premise is **cited and not decided**, and
every conditional below carries it.

---

## 1. Why every landing time is a lower bound for Lambda_DH

`Phi_DH` is real and even (measured to 4.2e-51 for `|u| <= 0.5` at dps 50,
`flow_repair` section 0), so `H_t(conj z) = conj H_t(z)` and the nonreal zeros
of `H_t` occur in conjugate pairs. Write a pair as `x(t) +- i y(t)` with
`y(t) > 0`.

Dobner (arXiv:2005.05142, Theorem 1) gives, for this class, that
`{t : H_t has only real zeros}` is a closed half-line `[Lambda_DH, inf)`. So
if `H_t` has a nonreal zero then `t < Lambda_DH`.

Fix a pair `P` present at `t = 0` and let

    t*(P) := inf{ t >= 0 : the pair P is no longer nonreal } .

`t*(P)` is finite: Newman-Wu Theorem 7 (de Bruijn 1950 Theorem 13 restated)
gives `y_max(t) <= sqrt(max(Delta^2 - 2t, 0))`, so every pair has reached the
axis by `t = Delta^2/2`. For `t < t*(P)` the pair is nonreal, so `H_t` has a
nonreal zero, so `t < Lambda_DH`. Letting `t` rise to `t*(P)`,

    **Lambda_DH >= t*(P) for every pair P, hence Lambda_DH >= sup_P t*(P).**

That is the whole content of item (a), and it needs nothing beyond Dobner's
half-line. It is why `flow_repair`'s nine measured landings are floors and why
`lambda_dh_bounds` could turn one of them into a decided one.

---

## 2. Does Lambda_DH *equal* that sup? The no-creation step

Write `T*_0 := sup_P t*(P)` over the pairs present at `t = 0`, and
`T* := sup{t : H_t has a nonreal zero}`. Dobner's half-line says
`Lambda_DH = T*`. Section 1 says `T* >= T*_0`. Equality needs exactly one
thing:

> **(NC) No creation.** For `t' > t >= 0`, no nonreal zero of `H_{t'}` fails to
> be the continuation of a nonreal zero of `H_t`. Equivalently: forward flow
> never drives two real zeros off the axis.

Given (NC), for `t > T*_0` every pair of `H_0` has landed and nothing new is
off the axis, so `H_t` has only real zeros, so `Lambda_DH <= T*_0`; with
section 1, `Lambda_DH = T*_0`.

**Why (NC) should hold, derived rather than asserted.** In this repository's
sign convention `H_t = exp(-t d^2/dz^2) H_0`, because
`d^2/dz^2 cos(zu) = -u^2 cos(zu)` turns the kernel factor `e^{t u^2}` into
`exp(-t d^2/dz^2)`. Restricted to the real axis, `u(x, t) := H_t(x)` therefore
solves

    du/dt = - d^2u/dx^2 ,

which in the reversed time `s = -t` is the ordinary forward heat equation
`du/ds = d^2u/dx^2`. Sturm's classical theorem on the heat equation (Sturm
1836; in the modern form Matano 1982, Angenent, *J. reine angew. Math.* **390**
(1988) 79-96) says the number of sign changes of a solution on an interval is
non-increasing in `s`, with interior zeros never created. Reversing time: under
our flow the number of real sign changes is **non-decreasing in `t`**, and two
real zeros can never merge and leave the axis in the interior. A landing does
the opposite, converting one nonreal pair into two real zeros, which the
theorem permits. So (NC) is the time-reversed lap-number statement.

**What that derivation does not cover, stated plainly.** Sturm's theorem in the
Angenent form is proved on a bounded space-time rectangle for a solution that
does not vanish on the lateral boundary. `H_t` is entire, not compactly
supported, and lives on the whole line; the standard route for entire functions
is Polya-Wiman theory rather than parabolic comparison. The derivation above is
therefore a *mechanism*, not a proof for this object, and the honest statement
is:

- **`Lambda_DH >= sup_P t*(P)` is unconditional** (section 1), and this is what
  every floor in this tree actually uses.
- **`Lambda_DH = sup_P t*(P)` holds under (NC)**, for which the lap-number
  argument is the reason to expect it and a proof for entire functions of this
  class is not in hand here.

**The numerical check, run.** Exact polynomial heat flow (coefficients evolved
in closed form by `p_t = sum_k (-t)^k/k! p^{(2k)}`, roots by `numpy.roots`, a
`t = 0` admissibility gate rejecting any configuration whose starting roots are
not recovered):

- **400 of 400** admissible random configurations of 2 to 6 real zeros plus one
  conjugate pair at depth `0.5` to `3.0`: the count of real zeros **never
  decreased** at any of 121 sampled times in `[0, 3]`. An earlier ungated sweep
  of 200 configurations gave the same answer.
- The four-root case `(z^2-a^2)(z^2+Y^2)` is exactly solvable and was used as a
  control. Its landing time is the positive root of
  `12t^2 - 2(Y^2-a^2)t - a^2Y^2 = 0`, that is
  `t_+ = [(Y^2-a^2) + sqrt((Y^2-a^2)^2 + 12 a^2 Y^2)]/12`; the flow reproduces
  it to nine digits at `(a, Y) = (0.1, 1.0), (0.05, 1.2), (0.3, 0.8)`, and the
  real pair survives in all three (four real zeros immediately after landing).

**Verdict on (b).** `Lambda_DH = sup_P t*(P)` under (NC), and (NC) is what the
time-reversed Sturm zero-number theorem says and what 600 sampled polynomial
configurations show. So the hunt's question is exactly a question about that
sup. Without (NC) the sup is still a floor, so **no phase of this hunt is
wasted if (NC) turns out to be false**: only the word "equals" is.

---

## 3. The isolated-pair law, derived and verified

Let `H_0` carry a single conjugate pair at `x +- i y0` and nothing else, so
`p_0(z) = (z-x)^2 + y0^2`. Then `p_0'' = 2` and `p_0^{(4)} = 0`, so the flow is
a single term:

    p_t(z) = exp(-t d^2/dz^2) p_0 = p_0 - t p_0'' = (z-x)^2 + y0^2 - 2t .

Roots `x +- sqrt(2t - y0^2)`: nonreal for `t < y0^2/2`, a real double root at
`t = y0^2/2`, two real roots after. Hence

    **t*(isolated) = y0^2 / 2, exactly.**

Feeding `y0 = Delta` gives `Delta^2/2`, which is the same number de Bruijn's
Theorem 13 produces from the strip. That coincidence is the reason the collapse
question is worth asking at all: the upper bound is the isolated-pair landing
time of a pair sitting at the very edge of the strip.

Verified, exact polynomial flow, bisection to 1e-13 on `max |Im root| > 0`:

| `y0` | `y0^2/2` | landing measured | difference |
|---|---|---|---|
| 0.2 | 0.020000000000 | 0.020000000000 | +2.8e-13 |
| 0.5 | 0.125000000000 | 0.125000000000 | +1.1e-14 |
| 0.9 | 0.405000000000 | 0.405000000000 | -5.8e-14 |
| 0.620362 | 0.192424505522 | 0.192424505522 | -1.8e-15 |

(`theory.py` stage 1; the residual is the bisection tolerance, not a defect in
the law.)

Cross-route, second implementation: `zeta.heatflow.polynomial_heat_flow` run on
the real pair `+-a` flowed **backward**, which is the same law read in the other
direction. Its `collision_t` came back at `-a^2/2` to within exactly one grid
step (2.5e-3) for `a = 0.3, 0.7, 1.0`. Two implementations, opposite directions,
same constant.

---

## 4. The crowding correction, derived

### 4.1 The pair identity

For a pair `z_1, z_2` the contour moments give `q_1 = z_1 + z_2`,
`q_2 = z_1^2 + z_2^2`, and

    Delta_pair := 2 q_2 - q_1^2 = (z_1 - z_2)^2 ,      Q := Delta_pair / 4 .

Off the axis `z_{1,2} = x +- i y` gives `Q = -y^2`; on the axis `Q > 0`; the
landing is `Q = 0`, and `Q` is analytic through it, which is why `flow_repair`
tracks `Q` and not `y`.

The zeros obey `dz_k/dt = 2 sum_{j != k} 1/(z_k - z_j)` (the sign pinned by
`zeta/heatflow.py`'s four-way check: `exp(-t D^2)` pairs with `+2`, roots
repel). Write `d = z_1 - z_2`. The neighbour terms telescope,

    1/(z_1-a) - 1/(z_2-a) = -d / ((z_1-a)(z_2-a)) ,

so `dd/dt = 4/d - 2 d sum_a 1/((z_1-a)(z_2-a))`, and with
`(z_1-a)(z_2-a) = (x-a)^2 - Q`,

    **dQ/dt = 2 - 4 Q sum_a 1/((x-a)^2 - Q) .**

That is the identity `flow_repair` section 3 used, re-derived here from the
N-body law rather than recalled.

### 4.2 The shave, in one integral

Off the axis put `Q = -y^2` and `S(y) := sum_a 1/((x-a)^2 + y^2)`. Then
`dQ/dt = -2y dy/dt = 2 + 4 y^2 S(y)`, so

    dy/dt = -(1 + 2 y^2 S(y)) / y ,

and separating,

    **t* = int_0^{y0} y dy / (1 + 2 y^2 S(y)) .**                        (*)

With `S = 0` this is `y0^2/2`, recovering section 3. When every neighbour is
real, `S > 0` and `t* < y0^2/2`: the shave is a theorem about the sign, not an
empirical trend, and it explains `flow_repair`'s P1 holding 9 of 9.

### 4.3 The leading term, and the answer to "nearest neighbour at distance d"

Expanding (*) for `y0` small against the nearest-neighbour distance, with
`S_0 := S(0) = sum_a 1/(x-a)^2`:

    t* = y0^2/2 - S_0 y0^4/2 + O(y0^6) ,

    **relative shave  =  1 - t*/(y0^2/2)  =  S_0 y0^2 + O(y0^4)
                       =  y0^2 sum_a 1/(x-a)^2 ,**

and for a pair whose only close neighbours are two zeros at distance `d` on
either side, `S_0 = 2/d^2` and the leading term is `2 (y0/d)^2`. **The shave is
the square of depth over neighbour distance.** This is the derivation behind
`flow_repair`'s empirical sentence "the shave tracks `y0^2` times local zero
density", which was observed there and is derived here.

### 4.4 The deep regime, which is the one that matters

The leading term is useless for a deep pair, because `S_0 y0^2` exceeds 1 long
before `y0` reaches `Delta`. Take instead `y >> h`, `h` the local mean gap. The
sum becomes an integral over a sea of density `rho = 1/h`,

    S(y) -> rho int da/((x-a)^2 + y^2) = pi rho / y ,

so `2 y^2 S = 2 pi rho y` and (*) collapses to a law with no free parameter but
the density:

    **dy/dt = -1/y - 2 pi rho ,
      t* = [V - log(1 + V)] / (2 pi rho)^2 ,   V := 2 pi rho y0 = y0 * L ,**

where `L := 2 pi / h`. Two limits, both worth stating:

- `V << 1`: `t* = y0^2/2 - (2 pi rho) y0^3/3 + ...`, the shallow regime.
- `V >> 1`: `t* -> y0 / L`. **A deep pair lands in time proportional to depth
  and inversely proportional to the log-density, not to depth squared.**

The mechanism is the constant `-2 pi rho` in `dy/dt`: a dense real sea pulls a
pair toward the axis at a rate that does not care how deep it is.

### 4.5 The density is not a free parameter for this function

Deriving `h` rather than recalling it. `F(s) = (pi/5)^{-(s+1)/2}
Gamma((s+1)/2) f(s)` and `N(T) ~ (1/pi) Im log[(pi/5)^{-(s+1)/2}
Gamma((s+1)/2)]` at `s = 1/2 + iT`. The first factor contributes
`(T/2) log(5/pi)`; Stirling on `Gamma(3/4 + iT/2)` contributes
`(T/2) log(T/2) - T/2`. So

    N(T) ~ (T / 2pi) log(5T / (2 pi e)) ,
    **h(T) = 2 pi / log(5T / (2 pi)) .**

Checked twice against counts this tree already made, and the right comparison
is with the total strip count, since `S` sums over all zeros:

| check | measured gap | `h` | agreement |
|---|---|---|---|
| `flow_repair` pair 1, window +-40 at `gamma` 85.7, 53 strip zeros | 1.50943 | 1.48806 | 1.44% |
| `lambda_dh_bounds` census (412, 600), 179 strip zeros | 1.05028 | 1.04753 | 0.26% |

`zeta/epstein.py`'s `_dh_mean_spacing` carries the same formula, which is a
third witness and not an independent one.

### 4.6 Calibration, and what it says about where a Davenport-Heilbronn pair sits

The pure lattice at phase 1/2 (a pair sitting midway between two line zeros)
over-predicts the shave badly: it reproduces the nine measured landings only to
a factor 1.03 to 1.42, always low. Giving the model **one** parameter, a local
gap of half-width `d` with lattice spacing `h` beyond it, and fitting `d` on
each of the nine:

    d / h  =  1.4284  mean,  sd 0.0749,  range [1.3350, 1.5682] over nine pairs.

Held fixed at the mean, that one-parameter model reproduces all nine to

    pred/meas in [0.9942, 1.0094],  rms deviation 0.54% ,

and on a **holdout** it was not fitted to, the census pair at
`gamma = 531.27972689652`, `y0 = 0.34695380309204904`, whose landing
`0.05033975468118168` was measured by the N-body null control:

    calibrated model 0.049944269,  pred/meas 0.9921  (0.79% low) ,
    census's own linear-in-log-gamma fit 0.048403, pred/meas 0.9615 .

Two things follow, and the second is a correction.

1. **An off-line pair of `F` sits in a locally sparse patch.** The nearest line
   zero is about 1.43 mean gaps away, against 0.5 for a generic point. Natural,
   since the quadruple takes zeros off the line locally, and checkable
   directly at a new height.
2. **The census's shave model is a local linearization.** Its form
   `tstar = (y0^2/2)(1 - (A + B log gamma) y0^2)` is the section 4.3 leading
   term with `S_0` linear in `log gamma`; but `S_0 ~ 1.74/h^2` is **quadratic**
   in `log gamma`. The two agree across the heights it was fitted on (`S_0` of
   1.22 versus 1.27 at `gamma = 245`, 1.62 versus 1.64 at `gamma = 545`) and
   part company above them (3.55 versus 2.99 at `gamma = 10^4`). Extrapolating
   the linear fit under-predicts the shave.

### 4.7 The bias of the frozen-neighbour approximation, measured

(*) freezes the neighbours. They move. Exact polynomial flow against (*) with
the same neighbour list, degree kept at or below 30 and every configuration
gated at `t = 0`:

| `h` | `y0` | naive | landing exact | (*) frozen | exact/(*) |
|---|---|---|---|---|---|
| 1.0 | 0.15 | 0.01125000 | 0.00950712 | 0.00940233 | 1.0111 |
| 1.0 | 0.30 | 0.04500000 | 0.02899650 | 0.02745977 | 1.0560 |
| 1.0 | 0.60 | 0.18000000 | 0.07530490 | 0.06666542 | 1.1296 |
| 1.0 | 0.90 | 0.40500000 | 0.12512202 | 0.10801879 | 1.1583 |
| 0.7 | 0.60 | 0.18000000 | 0.05743180 | 0.04981368 | 1.1529 |
| 0.5 | 0.60 | 0.18000000 | 0.04392252 | 0.03775514 | 1.1634 |
| 0.35 | 0.60 | 0.18000000 | 0.03277394 | 0.02810628 | 1.1661 |

The frozen model always under-predicts `t*`, by 1% at light crowding and
saturating near 17% at heavy crowding, because the neighbours repel away from
the pair while it descends. The DH calibration of 4.6 absorbs this into the
fitted `d/h`, which is why `d/h` is bigger than the 0.5 a static lattice would
give and why the calibrated model must not be read as a claim about actual
neighbour positions until someone measures them.

**Lesion, recorded because it fired silently.** At degree 52 with spacing 0.5,
float64 `numpy.roots` on the heat-evolved coefficient vector reported 14
nonreal roots at `t = 0` where there are 2, and `max |Im|` of 0.967 where it is
0.600; the resulting landing time was wrong by a factor 3.3 and looked
perfectly ordinary. The `t = 0` admissibility gate catches it and every table
above is gated. Any later phase using exact polynomial flow must gate.

---

## 5. What closes the bracket, and what keeps it open

Combining sections 2 and 4: under (NC),

    Lambda_DH = sup over pairs of  t*(y0, gamma),   t* given by (*) with rho = rho(gamma).

`t*` is increasing in `y0` at fixed `gamma`, and **decreasing in `gamma` at
fixed `y0`** (checked: at `y0 = 0.35` the calibrated model runs
0.055394, 0.054569, 0.052795, 0.050357, 0.046041, 0.042932, 0.037521 across
`gamma` = 86, 120, 240, 600, 3e3, 1e4, 1e5; at `y0 = Delta`, 0.147092 down to
0.074538 over the same heights). So the sup is a competition between depth,
which helps, and height, which hurts.

### 5.1 The collapse criterion

**The bracket collapses if there is a sequence of pairs with `y0 -> Delta`
whose shave tends to 0**, and (given 5.3's delay mechanism) that is the only
route to collapse that does not require a pair to land *later* than its own
`y0^2/2`, which needs a second pair sitting nearly above it. By 4.4 the shave tends to 0 only if
`V = y0 L(gamma)` tends to 0, and with `y0 -> Delta > 0` that forces
`L(gamma) -> 0`, that is `gamma` bounded, in fact `gamma -> 2 pi / 5 = 1.2566`, far below the height of any zero.

But below any fixed height `F` has finitely many zeros, so a sequence with
`y0 -> Delta` must have `gamma -> infinity`, hence `L -> infinity`, hence
`V -> infinity`, hence by 4.4 `t* -> y0/L -> 0`.

    **The deepest pairs land the fastest. sup t* is not approached along a
    depth-maximizing sequence; it is attained at finite height and intermediate
    depth.**

So the collapse scenario requires exactly what Bombieri and Ghosh's section 9
denies: deep zeros at *low* height. Their measurement is that for
`xi = 0` no zero with `Re s > 1` occurs at all below height 10^4, and that
reaching one needs the arguments of `p^{it}` aligned near `0 mod pi` for
hundreds of primes at once. The Davenport-Heilbronn function proper sits at the
hard end of their difficulty scale: prime-sum targets are 0.2767872 for `tau_-`
(easy, and its deepest zero below 10^4 is already at 99.60% of its `Delta`),
1.2940091 for `tau_+`, and 1.5707963 for `xi = 0`.

The delay route is not excluded by this argument and is priced separately in
5.3: two pairs both at depth `Delta`, 3.0 apart in the real coordinate, reach
93.55% of `Delta^2/2`, so a delayed configuration can come close. It needs two
deep quadruples in near-coincidence, and quadruples arrive at about 0.032 per
unit height, so it raises the sup by a few percent rather than closing the gap.

**Therefore the pre-registered theory verdict is: the bracket does not
collapse, `Lambda_DH < Delta^2/2` strictly, and by a large factor.**

### 5.2 The numerical criterion a later phase can test

Three tests, in increasing cost.

**C1 (cheap, decides the shape).** For the calibrated model, the height above
which *no* pair, at any depth up to `Delta`, can land later than a given floor:

| floor (narrow) | crossover height |
|---|---|
| 0.0576518 (the current best measured landing) | `gamma = 3.05e6` |
| 0.08 | `gamma = 4.31e4` |
| 0.10 | `gamma = 3775` |
| 0.12 | `gamma = 615` |

**If the model is right, the entire search for a better floor lives below
height about 3e6, and a floor above 0.12 can only come from below height
about 600, where the census is already complete.** C1 is falsified by any
measured landing that violates a row.

**C2 (the model ceiling).** Even the most favourable configuration the strip
allows, a pair at exactly `y0 = Delta` sitting at the lowest height at which
`F` has any off-line zero (`gamma = 85.6993`), gives

    t*_model(Delta, 85.6993) = 0.14709209 = 76.44% of Delta^2/2 .

So the calibrated model says crowding alone costs at least 23.6% of the upper
bound, for any pair, anywhere. **A measured landing above 0.15 would break the
model outright**; a measured landing above 0.1924 would break de Bruijn's
theorem and would be a defect in the instrument, not a discovery.

**C3 (the sup).** Model the deepest available depth as
`y_max(gamma) = Delta (1 - c_p / L(gamma)^p)`, anchored at
`y_max(600) = 0.3695261`, and maximize `t*(y_max(gamma), gamma)` over `gamma`:

| `p` | `y_max(10^4)` | model sup `t*` | at `gamma` | with `y0` | wide frame 4x |
|---|---|---|---|---|---|
| 0.5 | 0.4125 | 0.055750 | 3e3 | 0.3970 | 0.223000 |
| 1.0 | 0.4481 | 0.060861 | 3e3 | 0.4214 | 0.243442 |
| 1.5 | 0.4776 | 0.066062 | 1e4 | 0.4776 | 0.264248 |
| 2.0 | 0.5021 | 0.070444 | 1e4 | 0.5021 | 0.281774 |

Two things to notice. First, the answer is remarkably stable across a factor 4
in `p`: the sup lands in `[0.056, 0.071]` narrow, always between heights 3e3
and 1e4, always at depth 0.40 to 0.50. Second, **`p = 0.5` is already refuted by
this tree's own decided floor**: its sup 0.055750 is below `36/625 = 0.0576`,
and `sup t* >= Lambda_DH >= 36/625` is decided. So the data forces `p` above
about 0.6, and the surviving band is

    **sup t* in [0.058, 0.071] narrow  =  [0.232, 0.282] wide.**

That is 30% to 37% of `Delta^2/2`. The bracket does not collapse; it closes from
above, toward a value only a little over the current floor.

### 5.3 What would keep it open, or reverse the verdict

- **(NC) false.** Then `sup_P t*(P)` is a floor and not the constant, and a
  created pair could land later than anything present at `t = 0`.
- **A deep pair at low height.** One zero with `y0 > 0.55` below height 10^4
  refutes the depth-versus-height law and puts the sup back in play; the model
  would then give `t* = 0.0789` at `(0.55, 10^4)`, still well under
  `Delta^2/2`, but the shape of the argument would be gone.
- **Delay by a deeper neighbour, which is real and is a mechanism this hunt
  found.** If a neighbour is itself off-axis at `u +- i v`, its contribution to
  `S` is `2 Re[1/((x-u-iv)^2 + y^2)]`, whose sign is the sign of
  `(x-u)^2 - v^2 + y^2`: **negative when `v^2 > (x-u)^2 + y^2`**, that is when a
  deeper pair sits nearly above the tracked one. Then crowding *delays* the
  landing and `t*` can exceed `y0^2/2`. Measured, exact polynomial flow: **6 of
  300** admissible two-pair configurations landed later than `y0^2/2`. Two
  conjugate pairs both at depth `Delta`, separated by 3.0 in the real
  coordinate, land last at 0.18000977, which is 93.55% of `Delta^2/2`. So the
  de Bruijn bound is nearly saturated by *pairs of* deep pairs, not by one.
  With DH quadruples arriving at about 0.032 per unit height near `gamma` 500,
  two of them within the required proximity is a few-percent event, so this is
  a correction to the sup rather than a reversal, but it is the mechanism most
  likely to make the model low.
- **The cited converse fails.** If Bombieri and Ghosh's supremum is not
  approached by actual zeros of `F`, the upper end `Delta^2/2` was never sharp
  and the gap is uninteresting rather than real.

---

## 6. Pre-registered predictions

Registered 2026-08-18, before any Davenport-Heilbronn evaluation at a height
above 600. Every number is from the calibrated model of section 4.6 or from the
laws of sections 3 and 4, both fixed before this list was written.

- **P1 (the headline).** The bracket does **not** collapse:
  `sup t* < 0.75 * Delta^2/2 = 0.14432` narrow. Stronger form, the one being
  bet on: `sup t*` lies in **[0.058, 0.075]** narrow, that is **[0.232, 0.300]**
  wide. Refuted by any decided landing above 0.075 narrow.

- **P2 (the deepest zero below height 10^4).** `y_max(10^4)` lands in
  **[0.40, 0.52]**, point estimate **0.45**, that is `beta_max` in
  `[0.90, 1.02]` with point estimate 0.95. Below 0.40 or above 0.52 refutes.
  For scale: `y_max(600) = 0.3695261` today, and the strip ceiling is
  `Delta = 0.62036249819`.

- **P3 (the shave at that depth).** The calibrated model at
  `(y0, gamma) = (0.45, 10^4)` predicts `t* = 0.061084`, a shave of **39.7%**
  against the isolated `y0^2/2 = 0.10125`. Predicted band for the measured
  landing of whatever the deepest pair below 10^4 turns out to be:
  **model prediction to within a factor [0.85, 1.25]**. Outside that band the
  model is retired (kill condition 1).

- **P4 (the floor rises, modestly).** A complete census to height 10^4 raises
  the best measured landing from 0.05765184035 to a value in
  **[0.055, 0.079]**, point estimate **0.061**, which is where the model's
  maximum over the whole grid below 10^4 sits (0.061084 at `(0.45, 10^4)`,
  0.060861 at `(0.4214, 3e3)`). It does not reach 0.10.

- **P5 (where the sup sits).** The maximizing pair has height between
  **10^3 and 10^5** and depth between **0.40 and 0.52**. Landing times measured
  above height 10^6 are all below the current floor 0.0576518; above
  `gamma = 3.05e6` no pair at any depth up to `Delta` can beat it. This is the
  falsifiable core: **`t*` versus height must peak and then decline.**

- **P6 (the local gap is a real structural fact, not a fitting artefact).** At a
  newly located off-line quadruple, the distance from the pair's real
  coordinate to the nearest line zero, divided by `h(gamma)`, lands in
  **[1.1, 1.8]** rather than near 0.5. Measured on the nine fitted pairs it is
  1.4284 +- 0.0749; this predicts it out of sample, and it is cheap.

- **P7 (no creation).** No configuration will be found, in `F` or in polynomial
  surrogates, in which forward flow drives two real zeros off the axis.
  Standing at 0 of 600 sampled polynomial configurations.

- **P8 (the delay mechanism appears in `F`).** At least one Davenport-Heilbronn
  pair below height 10^4 will be found whose measured landing **exceeds** its
  own `y0^2/2`, because a deeper quadruple sits nearly above it. Expected rate
  a few percent of quadruples. If the rate exceeds 15%, the section 5.2 sup is
  too low and P1's band must widen upward.

- **P9 (what does not happen).** No number produced by this hunt is evidence
  for or against the Riemann hypothesis (`docs/08`; Littlewood). `Lambda_DH` is
  a property of a function where RH is already known to be false, and
  `flow_repair` section 3 already measured that the landing clock reads zero
  geometry and not arithmetic.

---

## 6b. Reproduction

    .venv/bin/python hunts/lambda_dh_exact/theory.py          # about 3 minutes
    .venv/bin/python hunts/lambda_dh_exact/theory.py --full   # wider grids

Seven stages matching sections 2 to 5 above, writing
`hunts/lambda_dh_exact/theory_results.json`. Every polynomial-flow table is
gated at `t = 0`; the degree-52 lesion of section 4.7 is exercised as a
negative control inside stage 2, so the gate is checked to fire rather than
assumed to.

## 7. Scope

**This hunt may write**: `hunts/lambda_dh_exact/`, `figures/`, and one new
`docs/NN-*.md` if it closes with something worth a document. Nothing in
`zeta/`, `ontology/`, `harness/`, `meta/` or `lean/` without explicit
permission, and nothing in `hunts/lambda_dh_bounds/` or `hunts/flow_repair/`,
whose files are read as evidence here and must stay as they were recorded.

**Handoff**: `hunts/lambda_dh_bounds/GATE.md` is the adjudication this hunt
inherits, `STRIP2.md` is where `Delta` comes from, `SEPARATION.md` is the claim
that must not be disturbed (it rests on the floor, which this hunt can only
raise), and `hunts/flow_repair/NOTES.md` is where the nine landings and the
N-body null control live.

**Grades**: everything in sections 3, 4.7 and 5.2 is *measured*, float route,
polynomial surrogates. Everything in section 4.6 is *measured* plus a fit. The
inherited constants in section 0 are as graded there. Section 2's (NC) is
*derived with a named gap* and is the one place where the hunt's central
sentence is conditional.
