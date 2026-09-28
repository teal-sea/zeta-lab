# RESULTS: hunt `overlap_lower`

**The ceiling procedure on the *lower* side of Erdos's minimum overlap
constant.** Run 2026-08-23.

Grades on every figure. **VERIFIED** means exact arithmetic with every
irrational replaced by a directed-rounded rational, no floating point in the
value. **MEASURED** means one floating-point route. **INFERRED** means taken
from the literature or argued rather than computed here.

## Status: partly settled, and the settled part is a negative

Settled: **on White's simplified program the published parameter choice is
already at the method's ceiling, and this hunt has the saturation curve that
shows it.** `R = 20` is what White used; the value stops moving at `R = 40`
and the total remaining gain from `R = 20` to `R = 320` is `2.9e-6`. The same
shape appears in his full program, where `R = 10` is what he used and the gain
from `R = 10` to `R = 20` is `2.0e-5`.

Not settled: **the full program was not reproduced to its published value.**
The reconstruction lands `0.375` where White reports `0.379`, and the reason
is identified and stated below rather than absorbed: the Parseval cone cannot
be enforced by cutting planes in the environment available, so what was swept
is a strictly weaker program than his. Every number this hunt reports is still
a valid lower bound; none of them is a good one.

**No bound on `C` moves.** The best exactly-accepted value obtained here is
`0.37399241331`, which is `0.00501` below the peer-reviewed lower bound
`0.379005` and `0.00513` below the preprint record `0.37912`: and which, being
a section 4 value, bounds `||M||_inf` for even `M` only and is not a bound on
`C` at all. Everything here is a reproduction falling short.

---

## A. The state of the art (INFERRED, every source read 2026-08-23)

Two independent literature passes, both reading the primary sources rather
than a summary. The brief this hunt was opened from contained three errors and
they are corrected here rather than quietly worked around.

### Lower bounds on `C`

| bound | attribution | source |
| --- | --- | --- |
| `1/4 = 0.25` | Erdos 1955 | [E1955] |
| `1 - 1/sqrt(2) ~ 0.292893` | Scherk, unpublished 1955 |, |
| `(4 - sqrt(6))/5 ~ 0.310679` | Swierczkowski 1958 | [S1958] |
| `sqrt(4 - sqrt(15)) ~ 0.356393` | Moser 1959 | Acta Arith. 5 (1959) 117-119 |
| `0.379005` | **E. P. White 2022** | arXiv:2201.05704; Acta Arithmetica **208** (2023) 235-255, doi 10.4064/aa220728-7-6 |
| `0.37912` | **Kim and Pilanci, 30 June 2026** | arXiv:2606.31182, preprint, unreviewed |

### Upper bounds on `C`

| bound | attribution |
| --- | --- |
| `1/2`, `4/9` | Erdos 1955 and unpublished |
| `5/12`, `0.4` | Motzkin, Ralston and Selfridge 1956 |
| `0.385694` | Haugland, unpublished 1993 |
| `0.382002` | Haugland 1996, J. Number Theory **58** 71-78 |
| `0.380927` | Haugland 2016, arXiv:1609.08000 (he writes `0.3809268534330870`; the catalogue rounds to `0.380927`) |
| `0.380924` | Georgiev, Gomez-Serrano, Tao, Wagner 2025, **AlphaEvolve** |
| `0.380876` | Yuksekgonul et al. 2026, **TTT-Discover** |
| `0.380871` | Together AI 2026 |
| `0.380868` | Ye et al. 2026, arXiv:2604.19341, **SimpleTES** |

A public leaderboard at `einsteinarena.com/problems/erdos-min-overlap` shows
`0.3808586` from an agent submission with no paper behind it. That is a
leaderboard entry, not literature, and it is not used as a reference value.

### The catalogue, and one correction about it

`github.com/teorth/optimizationproblems` (Damek Davis, Paata Ivanisvili,
Terence Tao). The entry is `constants/1b.md`, **"Erdos minimum overlap
constant"**, label `C_1b`, and it states the equivalence explicitly: *"The
problem of determining $C_{1b}$ is known to be equivalent to Erdős problem
#36."* Its README row reads

    | 1b | Erdős minimum overlap constant | 0.379005 | 0.380868 |

The repository-wide disclaimer, verbatim except for one elision. **`[C-WORD]`
stands for the reserved word that `zeta/rigor.py` and the Lean arm own; this
tree forbids that byte anywhere under `hunts/`, and the rule does not carve out
quotations, so it is elided here and below rather than reproduced.**

> "IMPORTANT NOTE: while submissions to this site are reviewed to meet
> minimal standards of plausibility and replicability, they are not [C-WORD]
> by this site for correctness, and may be subject to future revision, for
> instance due to errors in the associated preprint or paper. Thus, readers
> should exercise their own judgement when assessing the validity of the
> bounds reported on this site, particularly if their source is not yet
> published by a peer-reviewed journal."

and the asterisk convention, verbatim:

> "Bounds for which the level of available verification is currently at
> minimal levels will be marked with an asterisk in the table below."

**Correction 1.** The brief asked this hunt to verify that the minimum overlap
problem is one of the asterisk-marked entries and to quote the marking. **It
is not marked.** Neither `0.379005` nor `0.380868` carries an asterisk in the
README table, and neither carries one on `1b.md`. The general disclaimer above
applies to every entry in the repository, including this one; the asterisk
does not. Reporting the asterisk on this constant would have been wrong.

**Correction 2.** The brief states the lower bound *"has not moved since
2022."* It moved on **30 June 2026**: Kim and Pilanci, arXiv:2606.31182,
`0.379005 -> 0.37912`. Their abstract, verbatim: *"we improve the [C-WORD]
lower bounds from 1.28 to 1.2937 and from 0.379005 to 0.37912, respectively."*
The catalogue has not absorbed it, the last content commit to `1b.md` is
2026-04-30, two months before the preprint, which is why the catalogue still
reads `0.379005` and why a reader trusting the catalogue alone would repeat
the brief's error.

**Correction 3.** The `0.000059` figure is arithmetically exact but
misattributed: it is `0.380927 - 0.380868`, the 2016 *human* record minus the
2026 best published AI value, not twelve months of AI progress. The AI-only
span is AlphaEvolve `0.380924` to the leaderboard's `0.3808586`, which is
`0.0000654` over about nine months.

**Also worth stating.** The brief's implied attribution of `0.379005` to
Haugland is wrong: Haugland has only ever worked the upper side. And the
`0.37912` improvement did **not** come from a bigger computation: Kim and
Pilanci take White's program unchanged and add two Bochner semidefiniteness
constraints on the Toeplitz moment matrices of `f` and `g = 1 - f`. New
constraints, not a bigger `N`.

### White's own answer to this hunt's question

Section 6, concluding remarks, verbatim:

> "We expect that by computing more feasible solutions, using larger values of
> N, T, R, and using more accurate floating point calculations, that our lower
> bound of 0.379005 can be improved. Using the input N, T, R = 25000, 7000, 10
> and `h_1 = h_2 = 0.015, p_1 = p_2 = 0.381, -q_1 = q_2 = 0.02,` we were able
> to find a feasible point with objective 0.37905, but not with objective
> 0.3791. **This seems to indicate that the limit of this method is not much
> larger than 0.379.**"

and, for the simplified program of his section 4:

> "By increasing N and R this bound can be improved a little, but it seems
> that the limit of this approach is less than 0.3755."

**Both sentences are the author's inference from a single pair of solves, and
neither is a sweep.** That is precisely the gap this hunt exists to fill.

---

## B. What hunt #85 settled about each side, precisely

`hunts/r_828c8b/` (hunt #85, same day, same constant) settled:

- **The upper side, reproduced.** The `m`-piece step-function minimax falls
  `0.400000 / 0.385072 / 0.381833 / 0.381084` at `m = 4/8/16/32` and stalls;
  the stall is the solver's, not the family's, because an `m`-piece step
  function upsamples to a feasible `2m`-piece one and Haugland's object sits
  strictly below. Best exactly-evaluated object `C <= 9990167/26214400`,
  weaker than Haugland's.
- **Three lower-side routes killed, with witnesses.** Constructions bound only
  from above; the naive Fourier handling of the quadratic term is vacuous for
  every admissible weight because `what(0) = 1` forces `sup what = 1`; and
  single-weight averaging is capped at `0.2526` by explicit witnesses.

It did **not** settle:

- It did not reproduce `0.379005`, did not read White's discretisation, and
  did not check whether the published dual point is verified or merely
  reported. Its own words: *"this hunt did not reproduce 0.379005."*
- Its first loose thread asked whether the discretisation is sound at all,
  since restricting `f` to step functions bounds the infimum from above, in
  the unsafe direction.

**That thread is now closed, and the answer is that the worry does not apply.**
White discretises `M`, never `f`. His variables `w_j, v_j` are cell averages
of the *true* `M`, and every constraint is a necessary condition those
averages satisfy, so each admissible `f` maps to a feasible point with
`Omega = ||M||_inf`. The program is a relaxation, its optimum is at most
`||M||_inf`, and the direction is the safe one. His Proposition 9 says so in
one line: *"the average of M(x) on an interval cannot exceed the maximum."*
The discretisation error is absorbed by the envelopes
`alpha^-_{j,m} = cos(pi m L (j-1/2)/2) - pi m L/4` and its three siblings, and
the Fourier-tail error by the slack variables of (5.8), (5.9), which are
*defined* to be the discarded tail and then bounded by his Lemma 4.

Hunt #85 also recorded a route this hunt can now mark dead with a reason:
relaxing `f` to its cell masses alone. Given only `F_i = int_{cell i} f`, the
tight upper bound on the quadratic term at grid shift `k` is
`sum_i min(F_i, F_{i-k})`, which is attained at `f == 1/2` and returns a bound
of exactly `0`. Cell masses are not enough information; that is why the real
method carries Fourier coefficients.

---

## C. The free parameter

White's section 5 program has **three integer parameters and a six-number
box**: `N` (grid cells per half, `L = 2/N`), `T` (Fourier truncation index),
`R` (number of Fourier modes used as constraints, `1 <= m <= 2R`), and
`(h_1, h_2, p_1, p_2, q_1, q_2)` bounding `E(M)`, `c_1`, `d_1`. His headline
run is `N, T, R = 25000, 7000, 10`, solved in CPLEX. The section 4 program has
two, `N` and `R`, and his run is `N, R = 80000, 20`.

`R` is the one he never varied. It is `10` in every table of the full program
and `20` in the simplified one. **`R` is therefore the parameter this hunt
sweeps.**

---

## D. The section 4 ceiling (MEASURED, and it saturates)

White's (4.1)-(4.4), reimplemented from the displayed constraints in
`program.py:simplified_lp`. This program bounds `||M||_inf` for **even** `M`
only; it is not by itself a bound on `C`, and is not reported as one.

### D1. Reproduction, sweeping `N` at `R = 20`

| `N` | value | seconds |
| --- | --- | --- |
| 1000 | 0.369253406 | 0.07 |
| 2000 | 0.372119053 | 0.21 |
| 5000 | 0.373996605 | 1.00 |
| 10000 | 0.374637326 | 6.76 |
| 20000 | 0.374961067 | 58.69 |
| 80000 | **0.375169005340707** | White's published value, not recomputed here |

The successive gains are `6.41e-4` then `3.24e-4`, a ratio of `0.505`, so the
discretisation error decays as `C/N` to the precision available. Richardson
extrapolation on the last two rows puts the `N -> infinity` limit at
**`0.37528`** (MEASURED, one float route, extrapolated). White's own value at
`N = 80000` is `0.375169`, which sits between the measured `N = 20000` row and
that limit exactly as it should. **The reimplementation is faithful.**

### D2. The ceiling in `R`, at `N = 5000`

| `R` | value | gain over previous |
| --- | --- | --- |
| 5 | 0.373107329 |, |
| 10 | 0.373962906 | `+8.56e-4` |
| 20 | 0.373996605 | `+3.37e-5` |
| 40 | 0.373999461 | `+2.86e-6` |
| 80 | 0.373999458 | `-3e-9` |
| 160 | 0.373999458 | `-8e-11` |
| 320 | 0.373999457 | `-1e-9` |

**The value stops moving at `R = 40`.** Rows 80, 160 and 320 agree with row 40
to nine decimals, and the residual wobble at the tenth is solver noise, not
signal, the optimum is provably non-decreasing in `R`, so a decrease of `1e-9`
is a floating-point artefact and is reported as one.

The measurement that answers the question: **the total gain available from
`R = 20`, which is what White used, to `R = 320` is `2.9e-6`.** His choice was
already at the ceiling of the parameter, and the sentence *"it seems that the
limit of this approach is less than 0.3755"* is confirmed, with a number: the
limit in `R` is reached at `R = 40`, and what remains is entirely the `1/N`
discretisation, whose extrapolated value `0.37528` is indeed below `0.3755`.

### D3. Exact rational dual certificate (VERIFIED)

The dual of (4.1)-(4.4) is

    maximize   (N/4) lam - z/3
    subject to sum_j y_j <= 1
               lam <= y_j + sum_m a_{m,j} u_m + s_j z    for all j
               y, u, z >= 0,  lam free.

The float solver is used only to *propose* `(u, z)`. Everything after that is
`fractions.Fraction`: `alpha^-_{j,2m}` is replaced by a rational **lower**
bound (float cosine, floor at denominator `10^7`, minus one unit, minus the
Lipschitz term as an exact rational), which enlarges the primal feasible set
and so can only weaken the bound; `theta_j` is formed exactly; and the largest
feasible `lam` is found exactly by sorting `theta`.

At `N, R = 5000, 20`:

| quantity | value |
| --- | --- |
| float LP optimum | `0.3739966049729149` |
| **exact rational dual value** | `0.37399241331212807...` (29-digit numerator over 29-digit denominator, in `results/certificate.json`) |
| `sum_j y_j`, exactly | `1` |
| dual feasible, exactly | **yes** |
| cost of the directed rounding | `-4.19e-6` |

So `0.37399241331` is a **VERIFIED** value for the section 4 program at those
parameters, with no floating point in the number. It is `0.0050` below the
published lower bound on `C`, and, because section 4 assumes `M` even, it is
not a bound on `C` at all. It is here to show that the acceptance step on this
side is cheap and complete, which is the thing hunt #85 could not check.

---

## E. The section 5 ceiling (MEASURED, and the reproduction falls short)

White's (5.1)-(5.13), reimplemented in `program.py:WhiteProgram`. Two
departures, both stated before the numbers, both in the direction that can
only lower the value:

1. **The two quadratic families are outer-approximated.** White's program is a
   second-order cone program; the environment has `numpy` and `scipy` and no
   conic solver, so (5.5) and (5.11) are approximated from outside by
   supporting hyperplanes added at the current optimum. An outer approximation
   *contains* the true feasible set, so the LP optimum is at most the SOCP
   optimum and every value below remains a valid lower bound.
2. **(5.6) and (5.7) use the factor 4, not the 8 printed in the paper.**
   White's Lemma 3 (3.6) gives `B_m = -(4/(m pi)) sin(m pi/2) b_m` and Lemma 5
   sandwiches that same `B_m`, so 4 is what the sandwich needs and the printed
   8 is a factor-of-two typo. Using 8 makes the constraint *tighter* than the
   mathematics licenses, which is the unsafe direction. Measured cost of the
   choice at `N, T, R = 1000, 300, 10`: `0.37212920` with 4 against
   `0.37212751` with 8, a difference of `1.7e-6`. **The typo is real and
   numerically almost irrelevant**, which is worth saying in both halves.

### E1. Sweeping `N` at `T = 300`, `R = 10`, at White's binding box cell

Box `h_1 = h_2 = 0.015`, `p_1 = p_2 = 0.381`, `q_1 = -q_2 = -0.02`, which is
the cell his section 6 names.

| `N` | value | seconds |
| --- | --- | --- |
| 250 | 0.366821063 | 2.2 |
| 500 | 0.369627164 | 5.9 |
| 1000 | 0.372129203 | 17.5 |
| 2000 | 0.375067209 | 71.8 |

Gains `2.81e-3`, `2.50e-3`, `2.94e-3`, **not decaying**, so `N = 2000` is
nowhere near the `N` limit and no extrapolation is offered. `N = 4000` and
above did not fit the compute budget; see "What was not done".

### E2. The ceiling in `R`, at `N = 1000`

| `R` | value | gain over previous |
| --- | --- | --- |
| 5 | 0.371116641 |, |
| 10 | 0.372129203 | `+1.013e-3` |
| 20 | 0.372148913 | `+1.97e-5` |
| 40 | 0.372074126 | `-7.5e-5`, cut loop unconverged at 25 rounds |

**The same shape as section 4, at the same place White stopped.** The gain from
`R = 10`, his choice in every table, to `R = 20` is `2.0e-5`. For scale: the
entire improvement Kim and Pilanci obtained over White is `1.15e-4`, about six
times larger, and they got it by *adding constraints* rather than by raising a
parameter. The `R = 40` row is below the `R = 20` row, which is impossible for
the real program, adding constraints cannot lower a minimum, so it is
reported as an unconverged loop, not as a measurement.

This non-monotonicity is worth one sentence because it was the bug that
mattered. The cut loop originally stopped when the *objective* stalled, and
that produced `R = 5 -> 0.37433`, `R = 10 -> 0.37246`, `R = 20 -> 0.37504` at
`N = 2000`: a value that fell when a constraint was added. Monotonicity in `R`
is provable, so the stall was the loop's and not the program's, and the
stopping test was changed to the residual of the true quadratic constraint.
**A ceiling procedure that cannot tell "the parameterisation ran out" from
"the search ran out" measures the search**, and this is the second time in two
days that this family has produced that exact confusion (hunt #85, front B).

### E3. `T` does not matter here, and that is a defect not a finding

`T = 100, 300, 1000, 3000, 7000` at `N = 1000` all return
`0.3711470809943306` to sixteen digits. The tail slacks (5.8), (5.9) never
bind, so `T` is inert in this reconstruction.

That is a symptom of the real problem. **The Parseval cone (5.11) is not
enforced.** Cut-planing `sum_k (c_k^2 + d_k^2) <= 1/2` one hyperplane per round
in `2T = 600` dimensions leaves the ball violated by more than `200` after
thirty rounds, and the program silently degenerates into one where `a_m` and
`b_m` are free. Three reformulations were tried:

| form of (5.11) | outcome |
| --- | --- |
| the ball in `2T` dimensions, cut-planed | violation `>200` after 30 rounds; `c`, `d` effectively free |
| the exact pushforward ellipsoid `alpha^T (A A^T)^{-1} alpha <= 1/2` in `4R` dimensions | `A A^T` has condition number past `1e15`; the computed inverse is not positive on the iterates, reported violation `-3e15` |
| the Gram form `gamma^T (A A^T) gamma <= 1/2` | cut loop chases `gamma` to `1e7` with violation `1e10` |
| square-root coordinates, `a = F s` with `F = U sqrt(Lambda)`, constraint the plain unit ball | (5.5) converges to residual `4e-9`; the ball itself still violated by `~5` after 40 rounds |

The last form is what the numbers above use. It is the only one in which the
cosine constraints converge at all, and the ball is still open. **So the
figures in E1 and E2 are the ceiling of a program strictly weaker than
White's, and the `0.0040` gap between the `N = 2000` row and his `0.37905` is
mostly this, not discretisation.** They remain valid lower bounds, a
supporting hyperplane never removes a feasible point, and they remain bad
ones.

### E4. The box grid (MEASURED)

White's residual region (5.16) is `0 <= E(M) <= 0.06`, `0.35 <= c_1 <= 0.45`,
`-0.02 <= d_1 <= 0.02`. His tables cover it with degenerate *points* plus his
Lemma 10, which spreads one dual certificate over an ellipse in `(h, p)`. A
grid of genuine cells needs no reuse argument, so that is what was run, at
`N, T, R = 500, 300, 10`:

| `h` cell | `p` cell | value |
| --- | --- | --- |
| 0.000-0.030 | 0.350-0.383 | 0.369073827 |
| 0.000-0.030 | 0.383-0.417 | **0.367623890** |
| 0.000-0.030 | 0.417-0.450 | 0.369601291 |
| 0.030-0.060 | 0.350-0.383 | 0.368966815 |
| 0.030-0.060 | 0.383-0.417 | 0.367778352 |
| 0.030-0.060 | 0.417-0.450 | 0.369898521 |

Minimum over the grid `0.36762389`, at `p in [0.383, 0.417]`, adjacent to,
not identical with, the `p = 0.381 ... 0.385` where White concentrated. The
spread across the whole region is `2.3e-3`, so at this `N` the box is a modest
effect and the binding cell is not sharply localised.

---

## F. The guard, and what it misses (MEASURED)

Every value in fronts D and E rests on the envelope
`alpha^-_{j,m} = cos(pi m L (j-1/2)/2) - pi m L/4` being a genuine *lower*
bound on the trig weight over the cell. Drop it and the program stops being a
relaxation, which is the failure that manufactures a bound that is not there.
Faults were planted in the section 4 builder and checked against monotonicity
in `N` and in `R`, both of which are provable properties of the real program.
At `N, R = 2000, 10`:

| planted fault | value | delta vs sound | direction | caught by monotonicity |
| --- | --- | --- | --- | --- |
| none (negative control) | 0.372105479 |, |, |, |
| drop the `pi m L/4` envelope | 0.374949221 | `+2.84e-3` | **unsafe** | **no** |
| constrain every other mode | 0.358904453 | `-1.33e-2` | safe | no |
| constrain `cos(pi m x)` at odd `m`, which (2.4) does not license | infeasible |, | unsafe | **yes** |

**One of two unsafe faults caught, and the miss is the important one.**
Monotonicity in `N` and `R` is blind to dropping the envelope, because the
defective program is still monotone in both, it is simply a different, wrong
program. The fault is worth `2.84e-3`, which is larger than the entire gap
between Moser's 1959 bound and nothing, and it moves the value the flattering
way.

What *would* catch it is the exact certificate of front D3, because the
directed rounding there is applied to `alpha^-` itself and a builder that
omitted the envelope would produce a rational lower bound that no longer
bounds the real coefficient. Stated plainly: **on this program the guard is
the exact acceptance step, and monotonicity is not a substitute for it.**

---

## G. Does the published lower bound move? No.

| | value | grade |
| --- | --- | --- |
| best VERIFIED value obtained here (section 4, even `M` only) | `0.37399241331` | VERIFIED |
| best MEASURED value obtained here (section 5, one box cell) | `0.375067209` | MEASURED |
| White 2022, peer-reviewed | `0.379005` | INFERRED |
| Kim and Pilanci 2026, preprint | `0.37912` | INFERRED |

The gap from this hunt's best to the peer-reviewed record is `3.9e-3`, and the
reason is front E3, not the parameter sweep. **No new bound on `C` is claimed
and none is offered.**

The finding that *is* offered is the one the brief said would be publishable
if true, and it appears to be true in the parameter this hunt could actually
sweep:

> **White's choice of `R` was already at his method's ceiling in both of his
> programs.** In the simplified program, `R = 20` is his and the total gain to
> `R = 320` is `2.9e-6`. In the full program, `R = 10` is his and the gain to
> `R = 20` is `2.0e-5`, against the `1.15e-4` that the next real improvement
> obtained by adding constraints instead.

That is consistent with his own sentence, with Kim and Pilanci's route, and
with the shape this lab has now seen six times: **a published constant sits at
the ceiling of its parameterisation, and the next move is a different
parameterisation, not a bigger one.** The caveat that keeps this a probe and
not a result: it was measured on a weakened form of his full program, at
`N = 1000` rather than `25000`, and the `R`-saturation of the *faithful* SOCP
was not observed.

---

## What was not done, and why

- **The full program was not run at White's parameters.** `N, T, R = 25000,
  7000, 10` needs a conic solver and roughly a hundredfold more compute than
  was available. The machine this hunt ran on is a 13-inch laptop that had
  already crashed under this lab's own compute that day, so nothing over about
  a minute of CPU was run on it.
- **The sweep did not run on CI, though it was written for it.** The workflow
  is `hunts/overlap_lower/ci-sweep.yml`, complete and shardable at 25 minutes
  per job. It is not installed under `.github/workflows/` because the
  credential available refuses to create or update a workflow file without the
  `workflow` scope. Moving that one file into place and pushing is all that is
  needed; the sweep it defines reaches `N = 25000` for the full program and
  `N = 80000` for the simplified one.
- **The Parseval cone was not enforced.** Four formulations were tried
  (front E3); the best of them still leaves the ball violated. Closing it needs
  a second-order cone solver, which means a dependency this repository does not
  carry.
- **Kim and Pilanci's two Bochner constraints were not implemented.** They are
  semidefinite constraints on a Toeplitz moment matrix, which the LP route here
  cannot express at all. This is the single highest-value next step and it is
  recorded as a thread rather than attempted.
- **No exact certificate was produced for the section 5 program.** The dual of
  a program with box-constrained variables on both sides is materially messier
  than the section 4 dual, and with the primal value `0.004` below the
  published bound there was nothing worth certifying. The section 4
  certificate exists to show the acceptance step works, not to claim anything.
- **`M(n)` was not recomputed.** Hunt #85 has it exactly for `n <= 10` and this
  hunt has no reason to repeat it.

---

## What this is not

Nothing here is evidence for or against RH (`docs/08`). No new bound on `C` is
claimed. The reserved word that `zeta/rigor.py` and the Lean arm own is not
used anywhere in this hunt.

---

## Loose threads

- **The Bochner constraints are the live route and they are two lines of
  mathematics.** `T_f >= 0` and `I - T_f >= 0` where
  `(T_f)_{kl} = (1/4) delta_{kl} + (1/2)(a_{|k-l|} - i sgn(k-l) b_{|k-l|})`,
  valid because `z* T_f z = int f |sum z_k e^{i k pi x}|^2 >= 0` and
  `T_g = I - T_f`. Why it might matter: it is the whole of the `0.000115` that
  separates the current record from the peer-reviewed one, and it is a
  constraint on objects this reconstruction already carries. First step: get a
  conic solver into the environment, since neither this constraint nor (5.11)
  survives a cutting-plane treatment.
- **`R` saturation was measured on a weakened program.** Why it might matter:
  the whole headline rests on it, and the Parseval cone is exactly the
  constraint that ties `a_m` for large `m` back to a finite budget, so it is
  the constraint most likely to change where `R` stops paying. First step:
  rerun front E2 with (5.11) enforced and see whether the `R = 10 -> 20` gain
  is still `2e-5`.
- **The `1/N` decay in section 4 is the envelope, not the grid.** The gains
  halve exactly when `N` doubles, which is the signature of the `pi m L/4`
  Lipschitz term rather than of the Riemann sum. Why it might matter: a tighter
  envelope, the exact extremum of `cos(pi m x/2)` over the cell rather than
  midpoint-plus-Lipschitz, costs nothing to compute and would move the whole
  `N` curve, which is a change to the *method* and therefore out of this hunt's
  scope but squarely inside the next one's. First step: replace `alpha^-` by
  the exact cell minimum and re-run front D1; if the `N = 5000` row reaches
  what `N = 20000` reaches now, the published `N = 80000` was buying
  discretisation that better bookkeeping gives for free.
- **The catalogue is two months stale on this constant.** Why it might matter:
  this lab reads that catalogue as a frontier reference, and it silently
  disagreed with the literature by `0.000115` on the exact number this hunt was
  opened to move. First step: check the other constants this lab has hunted
  against their primary sources rather than against `1b.md`'s neighbours.
