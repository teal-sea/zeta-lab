# 37. The rule the core never learned

**Hunt #120, `hunts/epstein_height/`.** Read `hunts/epstein_height/RESULTS.md`
for the measurements, the guard and the doors. This page is the front door:
what happened, why it is worth a page, and what a session picking it up should
know.

Grade: **measured**, throughout. Nothing on this page bears on RH (`docs/08`).

## 1. The situation

`zeta.epstein.epstein_zeta` computes the Epstein zeta function of a binary
quadratic form. Ask it for fifteen digits at height 120 and it returns a number
that is wrong by thirty-six orders of magnitude. It does not raise. It does not
warn. Its docstring is one line and says nothing about height.

This is not an unknown failure. On 2026-08-23 a session working on the fifth
gate wrote the mechanism into a comment inside its own probe, derived it from
first principles, and set a constant:

    GUARD_PER_UNIT_HEIGHT = 0.6822

Two weeks later `hunts/dps_cap` measured what ignoring it costs at one point,
`0.8 + 85.7i`, and found the routine returning `3.1e-33` against a converged
`1.6e-58`. That hunt landed a real fix: the interfaces had been silently
clamping a caller's requested precision, and `tests/test_interface_dps_is_honoured.py`
now stops them.

**But the function itself never learned.** The constant stayed in a probe
comment. The measurement stayed a single point. `epstein_zeta` and
`epstein_completed` still accept any precision at any height and return a
number.

## 2. What was measured

The failure is not a cliff, it is a slope, and it runs at about two thirds of a
decimal digit per unit of height. Correct digits for the form `(1,1,4)` at
`Re s = 5`, against a directly summed lattice oracle:

| t \ dps | 15 | 20 | 30 | 50 | 80 |
|---:|---:|---:|---:|---:|---:|
| 40 | 15.6 | 16.1 | 16.1 | 16.1 | 16.1 |
| 60 | **3.1** | 8.2 | 16.1 | 16.1 | 16.1 |
| 80 | **0** | **0** | 5.1 | 16.3 | 16.3 |
| 120 | **0** | **0** | **0** | **0** | 16.5 |
| 160 | **0** | **0** | **0** | **0** | 2.4 |

The bold zeros are answers, returned without complaint. At `t = 120`, `dps = 15`
the relative error is `2.3e+36`.

The oracle matters here. At `Re s = 5` the defining lattice sum converges
absolutely, so it can be summed directly with a stated truncation bound and used
as ground truth at any height. The routine reaches the same value through a
split Mellin transform and the incomplete gamma. They share the definition and
nothing else, which is what makes the disagreement informative rather than a
statement about one implementation compared with itself at more digits.

## 3. The part that is a small piece of mathematics

The first model this hunt fitted was the recorded constant plus the obvious
`sigma` correction. It predicted the correct-digit count to about `0.86` rms
over the 49 cells where a prediction can be tested, which sounds fine.

It was not fine, and the way it failed is the interesting part. The residuals
averaged `+0.85` for one form and `-0.75` for another. A model that is wrong by
a *constant that depends on the subject* is missing a term, not accumulating
noise, and no amount of refitting the constant would have said so.

Re-derived: the routine forms four quantities and returns `d^{s/2}` times their
sum. Two of them are about `1/t`. Since `Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)`,
the sum itself has size `pi^{-sigma} |Gamma(s)| |zeta_Q(s)|`, the discriminant
cancels, and the digits lost to cancellation are

    -log10 t + sigma log10 pi - log10|Gamma(s)| - log10|zeta_Q(s)|.

There is no fitted constant in that. Substituting Stirling recovers the
recorded `0.6822 t` and shows what the first model dropped, including the size
of `zeta_Q` itself. `(1,1,4)` represents 1 and `(2,1,3)` represents 2, so at
`sigma = 5` their `log10|zeta_Q|` differ by about 1.5, which is the 1.6-digit
gap that was sitting in the residuals.

With the derived law the per-form bias disappears (means `+0.93`, `+1.09`,
`+1.07`) and what is left is one uniform offset of `+1.068` digits with rms
`0.357` about it across three forms and heights 40 to 160. That is what a
correct derivation should leave: the model assumed the largest quantity formed
is exactly `1/t`, it is a little smaller, and the routine carries about one
digit more than the bound says.

## 4. Why the earlier hunt's runs never returned

`hunts/dps_cap/reach_check.py` asks a question and answers it honestly with
"unresolved": does the precision cap cost a wrong answer, or a refusal? Both
its runs were stopped, one after 30 minutes and one after 25. It offers a
hypothesis and says plainly that it did not test it.

The hypothesis is right, and it is testable without running the thing that does
not return. The winding-number routine accepts a segment when the argument
turns by less than `pi/3` along it and otherwise bisects, to a depth limit of
45 at which **it returns the principal value rather than raising**. So the
branching factor is `2(1 - p)` with `p` the acceptance probability, and `p`
costs two evaluations per segment to measure rather than an exponential
recursion to observe. When the samples carry no correct digits the phase is
noise, `p` falls to about `1/3`, the branching factor is `4/3`, and one segment
costs roughly `(4/3)^45` evaluations.

Measured at height 120, along the edge and at the step the routine itself would
choose: at `dps = 100` the rule accepts **24 segments out of 24**, so the
recursion stops on its first test every time and costs one evaluation per
segment. At `dps = 15`, where the samples have no correct digits, it accepts 7
of 24, `p = 0.292` against the `1/3` a uniform phase predicts, the branching
factor is `1.417`, and one segment costs about `6.4e6` evaluations. At two
seconds an evaluation that is 148 days, for one segment of one edge.

The consequence does not depend on the exact `p`, and it answers the open
question: because the depth limit returns a value instead of raising, **the cap
cannot cost a refusal.** It costs either a wrong count or a run that does not
finish, and which one you get is settled by the depth limit rather than by any
check.

## 5. What is proposed, and what is not

A guard, written as code with the planted faults that fire it, in
`hunts/epstein_height/guard.py`. It refuses `0.8 + 85.7i` at `dps 20`; it
refuses `t = 120` at `dps 15`; it does **not** refuse `t = 20` at `dps 30`, and
the value there is right to `2.5e-19`; it asks more of the critical line than
of `sigma = 5` at the same height; and when the cancellation constant is set to
zero it stops firing, which is what makes the other rungs mean anything.

A hunt may not write `zeta/`. So this is a proposal with its evidence attached,
not a landed change, and the decision is the tree's.

## 6. The general shape, which is why this is a page and not a line

A laboratory found a defect, derived its mechanism, wrote the mechanism down,
and put the note in the directory of the hunt that found it. The next hunt hit
the same defect from a different direction and measured its cost at one point.
The function kept its silence through both.

There is no villain in that story and no missing machinery. Both hunts did more
than they were asked to. What was missing is that neither of them was in a
position to write the rule where the code could read it, because a hunt may not
write the core, and nothing carried the finding across that line except a
person happening to read two directories.

That is a small, specific, fixable thing, and it is the reason this page names
the two earlier hunts before it names the measurement.
