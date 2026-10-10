# Results: the module that did not get the guard the tree already had

**2026-09-10. Grade: measured**, against an oracle the routine shares no code
with. Nothing here bears on RH (`docs/08`): it is a measurement of an
implementation.

**This page was rewritten after an independent adversarial audit.** Seventeen
attacks, eleven of which landed. `AUDIT.md` has them. The finding survived every
attack on the oracle, including a class-number-formula route that touches no
lattice at all. The first version's guard, its title and one of its instruments
did not.

**Landed on main 2026-10-10 as Hunt #129** (it was #120 on its branch,
`claude/repo-hunt-content-2smbid`), with its front door at `docs/41` (numbered
37 there). **The routine this page measures has since been changed.** Issue
#217, which this hunt opened, was closed by #291 on 2026-10-09: `epstein_zeta`
now raises its working precision by `ceil(0.6822 |t|)` digits, the leading term
of section 4, and `tests/test_epstein_zeta_height.py` pins it. Every number
below was re-measured on 2026-10-10 against the routine as it was, restored by
setting `zeta.epstein.EPSTEIN_DIGITS_PER_UNIT_HEIGHT` to zero (`epstein_completed`
itself is unchanged), and `test_epstein_height.py` pins them; what the current
routine returns at the same cells is noted where it matters. The 120-cell grid
and the 42 boundary cells came back identical to the artifacts in every field
but `digits_available`, which the artifacts carry as `dps + 10` from an earlier
probe (the audit's correction; the probe now writes `dps + 20`), and
`why_it_hangs.json` and `guard2_contract.json` came back exactly. Four stated
numbers did not reproduce and are marked where they are stated. Recorded text
is left as written.

## 1. The verdict

    zeta.epstein.epstein_zeta at dps 15, form (1,1,4), Re s = 5
      t = 40    15.6 correct digits
      t = 60     3.1 correct digits
      t = 80     0   correct digits, relative error 1.0
      t = 120    0   correct digits, relative error 2.3e+36

    the routine raises nothing, warns nothing, and its docstring says nothing

> **Since #291, 2026-10-09.** Still true that it raises and warns nothing; no
> longer true that its docstring is silent (it now states the loss and its
> limit at a zero of `zeta_Q`), and these four cells now read 16.1, 16.1, 16.3
> and 16.5. The block above is the routine before #291, reproduced exactly.

**The tree already has this guard, twice, in `zeta/`.** `zeta/heatflow.py` picks
a working precision from `_DIGITS_LOST_PER_Z` and deliberately over-provisions;
`zeta/core.py`'s `_eta_workload` solves Borwein's own error bound for the number
of terms and carries the matching guard digits. `hunts/gate5_p6_b/probe.py`
carries the Epstein constant as an executable `_dps_for`, and
`hunts/gate5_p6_c/probe.py` derives it in a comment. `hunts/dps_cap` (#113)
measured the cost at one point and stopped the interfaces clamping a caller's
`dps`.

So the first version of this page was wrong to call this a rule the core never
learned. The core learned the pattern twice. **`zeta/epstein.py` is the module
that did not get it**, which is a smaller claim and a more actionable one.

## 2. The oracle, which nothing moved

At `Re s = 5` the defining sum converges absolutely; grouping lattice points by
the value they represent turns the double sum into one sum over `q <= qmax`. The
audit attacked it four ways: a different counting algorithm, point-by-point
enumeration with no grouping, re-summing at `qmax = 400000`, and a class-number
formula route that uses no lattice at all. None of them moved it.

One correction stands: the truncation figure is **measured and extrapolated**,
not a bound. `K = N(qmax)/qmax` is measured at one point and used above it, and
`N(x) = Cx + O(sqrt x)` does not guarantee that. It held in every cell the audit
checked, by factors of 10 to 400.

> **Not reproduced as stated, 2026-10-10.** Re-summed at `qmax = 400000` on
> nine cells (three forms, `t = 10, 100, 160`), the actual truncation is
> `5.0e-20` to `1.8e-18` against stated figures of `1.02e-17` to `2.45e-17`,
> as the audit found, so the figure is honest everywhere; but it is
> conservative by factors of **13 to 214**, not "10 to 400".

## 3. The surface

Correct digits, form `(1,1,4)`, `Re s = 5`:

| t \ dps | 15 | 20 | 30 | 50 | 80 |
|---:|---:|---:|---:|---:|---:|
| 40 | 15.6 | 16.1 | 16.1 | 16.1 | 16.1 |
| 60 | **3.1** | 8.2 | 16.1 | 16.1 | 16.1 |
| 80 | **0** | **0** | 5.1 | 16.3 | 16.3 |
| 120 | **0** | **0** | **0** | **0** | 16.5 |
| 160 | **0** | **0** | **0** | **0** | 2.4 |

The ceiling near 16 to 17.6 digits is **float64 rounding in the comparison**,
not the oracle: `probe.py` computes the relative error outside a `workdps`
block, so the routine's answer is rounded to 53 bits first. The oracle at
`qmax = 20000` carries 18.3 to 19.5 digits. That matters because `law.py` used
that ceiling to select the cells that test it.

> **Note, 2026-10-10.** "18.3 to 19.5 digits" is the oracle's accuracy for
> `(1,1,4)` and `(1,0,1)`, re-measured against `qmax = 400000` at
> `t = 10, 100, 160`. For `(2,1,3)`, whose `|zeta_Q|` is about thirty times
> smaller at `Re s = 5`, it is 16.9 to 18.1.

> **What the current routine returns, 2026-10-10.** With #291's lift, every
> cell at `dps = 15, 20, 30` and `t = 40, 60, 80, 120, 160` reads 16.1 to 16.5
> correct digits, the float64 ceiling of this comparison, on both `(1,1,4)` and
> `(2,1,3)` (30 cells, `RUNS.md`, the landing manifest). The zeros and the 3.1,
> 5.1 and 8.2 in the table are the routine before #291.

## 4. The loss, and what it took to get right

**First model**, the constant already recorded in the tree plus a `sigma` term:

    L = 0.68219 t - (sigma - 1/2) log10 t - 0.399

Residual over the transition cells: mean `+0.13`, rms `0.86`. **The mean is an
artefact of cancellation.** Split by form it is `+0.93`, `+0.85`, `-0.75`: about
1.8 digits of deterministic form dependence in a law with no form term, and the
whole-sample mean is small only because the two largest biases have opposite
signs.

**Second model**, derived from what the routine actually forms. Since
`Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)` and the routine returns
`d^{s/2}` times a sum whose largest terms are about `1/|s|`,

    L(sigma, t, Q) = -log10|s| + sigma log10 pi - log10|Gamma(s)| - log10|zeta_Q(s)|

with no asymptotic and no fitted constant. The discriminant cancels. Substituting
Stirling recovers `0.68219 t` and shows what the first model dropped: a further
`-log10 t`, a `sigma log10 pi`, and the size of `zeta_Q` itself. `(1,1,4)`
represents 1 and `(2,1,3)` represents 2, so at `sigma = 5` their
`log10|zeta_Q|` differ by about 1.5, which is the gap that was in the residuals.

| model | residual mean by form | rms |
|---|---|---:|
| leading constant plus the `sigma` term | `+0.93 / +0.85 / -0.75` | 0.86 |
| derived | `+0.93 / +1.09 / +1.07` | 0.36 about one constant |

The per-form bias goes from 1.8 digits to 0.15. What is left is a single offset
of `+1.068`, and the audit identified it: mpmath's `dps_to_prec` rounds a decimal
request up to whole bits, which buys 0.87 to 1.15 digits. Not, as the first
version said, that "the largest quantity formed is a little smaller than `1/t`";
substituting the exact largest term for `1/t` moves the mean by 0.002.

> **Not reproduced, 2026-10-10 (three numbers in this section).** (a) The
> first model's residual by form, "`+0.93 / +0.85 / -0.75`", does not come back
> from `law.json`: over the 49 cells `law.py` itself selects it is
> `+0.91 / +0.83 / -0.68` for `(1,0,1)`, `(1,1,4)`, `(2,1,3)`, and over the
> audit's 46 cells (`1 < correct digits < 14`) it is `+1.16 / +0.85 / -0.67`,
> whose spread is the 1.82 that "1.8 digits" refers to. The derived row
> reproduces. (b) "0.87 to 1.15 digits" is 0.86 to 1.15 over every `dps` in the
> artifacts (`dps = 27`, a boundary cell, gives 0.864); 0.87 to 1.15 holds over
> the grid's five. (c) Replacing `1/t` by `|1/s|` moves the mean over the
> audit's 46 cells by 0.0008, not 0.002; the conclusion, that it is not the
> offset, is unchanged. A related point the page does not make: the formula
> above is written with `-log10|s|`, while `law2.py`, which produced `+1.068`,
> uses `-log10 t`; on these cells the two differ by at most 0.0034 digits.
> Pinned in `test_first_model_residual_and_its_split_by_form` and
> `test_the_offset_is_mpmaths_decimal_to_binary_rounding`.

**Both models were fitted and tested at `sigma = 5` only.** Every cell in
`surface.json` and `boundary.json` is on that line, so the `sigma` term, which is
precisely the part that decides whether a rule transfers between lines, was
asserted rather than tested. The audit tested it at `sigma = 1/2` against an
exact oracle and found the first model's residual there is `+4.66` digits.

> **Reproduced, 2026-10-10.** Re-run against the routine before #291 with the
> exact oracle `zeta_{(1,0,1)} = 4 zeta beta`: mean `+4.66`, rms `4.68`, range
> `+4.06` to `+5.36` over the audit's eight cells, and `+1.35` for the derived
> law with the precision correction (`test_the_critical_line_attack`, slow tier).

## 5. The guard, which the audit walked through

The first version shipped a rule with six planted faults, all passing, and
called it a guard that fires.

    guarded_epstein_zeta((2,1,3), 8 + 80i, dps=required_dps(8, 80, 4),
                         want_digits=4)

is allowed at `dps = 24` and returns **0.59 correct digits**. Reproduced here:
the form-blind rule puts the loss at `39.90` digits, the form-aware one at
`44.07`, a gap of `4.17` that is exactly the `-log10|zeta_Q|` term. **All six
rungs held the form fixed**, so the ladder tested the leading term, which was
already right, and never the term this hunt had just added.

`guard2.py` is the rebuild. It carries the form through the least value the form
represents, bounding `|zeta_Q|` below from integer counts where the series
converges and falling back to leading-term scaling with a declared margin inside
the strip, saying which regime it is in.

And the rung that matters is not another fault. **A guard is sound when every
call it allows delivers**, so the ladder now samples the calls the guard allows,
across three forms and five `(sigma, t)` points, evaluates each against the
oracle, and fails if any is short.

Its first run failed, on `(2,1,3)` at `sigma = 2.5`, by 0.3 digits. Raising the
precision did not move it, which is the signature of the oracle rather than the
routine: at `qmax = 20000` the lattice truncation carries 17 digits at
`sigma = 5` and about 6 at `sigma = 2.5`. **A contract rung that does not know
its own oracle's accuracy reports the oracle's limit as the guard's failure**, so
the rung now computes the oracle's digits per cell and excludes what it cannot
score. Current state: 12 of 12 scored calls deliver, 3 excluded and named.

> **Note, 2026-10-10.** Reproduced: with the model margin set to zero the
> `(2,1,3)` call at `2.5 + 60i` asks for `dps = 26` and delivers 7.71 of 8
> digits, 0.3 short. "17 digits at `sigma = 5`" is approximate: the contract's
> own record gives 15.7 to 17.2 there (lowest for `(2,1,3)`), and 5.7 to 6.3 at
> `sigma = 2.5`. On the current routine the contract run also passes, 12 of 12
> scored, and at `sigma = 5` its calls agree with the oracle to 17.7 to 19.3
> digits, past what the oracle is credited with, because #291 lifts the
> precision underneath the guard. `guard.py`'s own ladder now fails its second
> rung on the current routine: the call it calls wrong at `t = 120`,
> `dps = 15` is off by `2.9e-17`.

One fitted constant remains and is named as fitted: a `+1.0` model margin, set
from that first contract run's worst shortfall with a factor of three.

## 6. What `hunts/dps_cap/reach_check.py` left open

That file asks whether the cap costs a wrong answer or a refusal and records that
neither run returned, stopped at 30 and 25 minutes. It offers a hypothesis and
says it did not test it.

`_arg_variation` accepts a segment when the argument turns by less than `pi/3`
and otherwise bisects, to a depth limit of 45 at which **it returns the principal
value rather than raising**. So the branching factor is `2(1 - p)` and `p` costs
two evaluations per segment to measure. At height 120 on `(2,1,3)`, along the
edge and at the step the routine itself chooses:

| dps | segments accepted | p | branching | evaluations per segment |
|---:|---:|---:|---:|---:|
| 15 | 7 of 24 | 0.292 | 1.417 | 6.4e6 |
| 100 | **24 of 24** | 1.000 | 0 | 1 |

At sufficient precision the recursion stops on its first test every time. At
insufficient precision it accepts about as often as a uniform phase would, and
one segment costs about 148 days at two seconds an evaluation.

The answer does not depend on the measured `p`: because the depth limit returns
a value, **the cap cannot cost a refusal**. It costs a wrong count or a run that
does not finish, decided by the depth limit rather than by any check.

## 7. The doors

1. **Active constraint.** Working precision against height, binding above `t`
   about 40 at default precisions, at `0.682` digits per unit height. Its shadow
   price is exactly one digit of answer per digit of `dps`.
2. **Frozen-constant inventory.**
   - **`_GUARD = 10`, applied twice.** `epstein_zeta` opens `workdps(dps + 10)`
     and hands `mp.dps` to `epstein_completed`, which opens another, so a caller
     receives `dps + 20`. Undocumented and load-bearing in every number here.
     *(2026-10-10: since #291 a caller receives `dps + 20 + ceil(0.6822 |t|)`;
     measured at `t = 10`, a request for 15 or 30 reaches the cancelling step at
     42 or 57, against 35 or 50 before, and 80 reached it at 100.)*
   - **The Mellin split at `t = 1`.** Every cancelling term comes from that
     choice. Splitting at a `t` chosen per `s` is the one change that could
     reduce the cancellation rather than pay for it, and nothing has tried it.
     This is the door with real trade shape: it costs a derivation and buys back
     digits currently bought with precision.
   - **`sigma = 5`, the line everything here was measured on.** The audit's
     `sigma = 1/2` test is the only out-of-sample point and it found `+4.66`
     digits of error in the first model. A surface over `sigma` is the cheapest
     way to make any of this trustworthy on the line the tree actually works on.
   - **The depth limit 45 in `_arg_variation`**, which alone decides whether a
     bad contour miscounts or hangs.
3. **Information class.** Everything reads data the routine already forms. The
   guard is arithmetic on quantities in hand; the Mellin-split door is a
   re-derivation of an existing representation. That is the cheapest kind of
   door, and it is open because the pattern the tree uses twice in `zeta/` was
   never applied to this module.
