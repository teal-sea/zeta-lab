# 37. The module that missed the guard the tree already had

**Hunt #120, `hunts/epstein_height/`.** Measurements, the guard and the doors in
`hunts/epstein_height/RESULTS.md`; the audit that rewrote this page's title in
`AUDIT.md`.

Grade: **measured**, throughout. Nothing here bears on RH (`docs/08`).

## 1. The situation

`zeta.epstein.epstein_zeta` computes the Epstein zeta function of a binary
quadratic form. Ask it for fifteen digits at height 120 and it returns a number
wrong by thirty-six orders of magnitude. It does not raise, does not warn, and
its docstring says nothing about height.

The failure is not a cliff but a slope, at about two thirds of a decimal digit
per unit of height. Correct digits for the form `(1,1,4)` at `Re s = 5`, against
a directly summed lattice oracle:

| t \ dps | 15 | 20 | 30 | 50 | 80 |
|---:|---:|---:|---:|---:|---:|
| 40 | 15.6 | 16.1 | 16.1 | 16.1 | 16.1 |
| 60 | **3.1** | 8.2 | 16.1 | 16.1 | 16.1 |
| 80 | **0** | **0** | 5.1 | 16.3 | 16.3 |
| 120 | **0** | **0** | **0** | **0** | 16.5 |

The bold zeros are answers, returned without complaint.

## 2. The first version of this page had the wrong title

It was called "The rule the core never learned", on the strength of the
constant `0.6822` sitting in a hunt's probe comment while the module carried no
guard.

An adversary checked, and the tree knows this rule perfectly well.
`zeta/heatflow.py` picks a working precision from its own
`_DIGITS_LOST_PER_Z` and deliberately over-provisions by six to eleven digits.
`zeta/core.py`'s `_eta_workload` solves Borwein's error bound for the term count
and carries the matching guard digits. `hunts/gate5_p6_b/probe.py` carries the
Epstein constant as an executable rule, not a comment.

**The core has this pattern twice. `zeta/epstein.py` is the module that did not
get it.** That is a smaller claim, and a more useful one, because it names a gap
rather than a culture.

## 3. The part that is a small piece of mathematics

The first model fitted here took the recorded constant plus the obvious `sigma`
correction, and predicted correct digits to about `0.86` rms. That sounds fine.

It was not, and the way it failed is the interesting part. The residuals
averaged `+0.93`, `+0.85` and `-0.75` for the three forms: about 1.8 digits of
deterministic form dependence in a law with no form term, and the small
whole-sample mean existed only because the two largest biases had opposite
signs. A model wrong by a constant that depends on the subject is missing a
term.

Re-derived: the routine returns `d^{s/2}` times a sum whose largest terms are
about `1/|s|`, and since
`Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)`, that sum has size
`pi^{-sigma}|Gamma(s)||zeta_Q(s)|`. The discriminant cancels, and the digits lost
are

    -log10|s| + sigma log10 pi - log10|Gamma(s)| - log10|zeta_Q(s)|

with no fitted constant. Substituting Stirling recovers the recorded `0.6822 t`
and shows what the first model dropped, including the size of `zeta_Q` itself.
`(1,1,4)` represents 1 and `(2,1,3)` represents 2, so at `sigma = 5` their
`log10|zeta_Q|` differ by about 1.5, which is the gap that was sitting in the
residuals.

With the derived law the per-form bias falls from 1.8 digits to 0.15. What is
left is one uniform offset of `+1.068`, and the audit identified that too: it is
mpmath rounding a decimal precision request up to whole bits, worth 0.87 to 1.15
digits.

## 4. Then the adversary walked through the guard

The first version shipped a rule with six planted faults, all passing, and
called it a guard that fires rather than another constant in a comment.

    guarded_epstein_zeta((2,1,3), 8 + 80i, dps=required_dps(8, 80, 4),
                         want_digits=4)

is allowed, and returns **0.59 correct digits**. The form-blind rule puts the
loss at 39.9 digits; the form-aware one puts it at 44.1. The gap is exactly the
`log10|zeta_Q|` term the hunt had just spent its own section deriving.

**All six rungs held the form fixed.** The ladder tested the leading term, which
was already right, and never the term the hunt had added. A guard that cannot
fire is the thing this hunt exists to name, and the hunt shipped one.

The rebuild carries the form. And the rung that matters is not another planted
fault: a guard is sound exactly when every call it allows delivers, so the
ladder now samples the calls the guard **allows**, across three forms and five
points, checks each against the oracle, and fails if any is short.

Its first run failed, by 0.3 digits, and raising the precision did not move it.
That is the signature of the oracle rather than the routine: the lattice
truncation carries 17 digits at `Re s = 5` and about 6 at `Re s = 2.5`. A
contract rung that does not know its own oracle's accuracy reports the oracle's
limit as the guard's failure. It now computes the oracle's digits per cell and
excludes what it cannot score.

## 5. Why the earlier hunt's runs never returned

`hunts/dps_cap/reach_check.py` asks whether the precision cap costs a wrong
answer or a refusal, and answers "unresolved": both its runs were stopped, at 30
and 25 minutes. It offers a hypothesis and says plainly it did not test it.

The hypothesis is right and it is testable without running the thing that does
not return. The winding routine accepts a segment when the argument turns by
less than `pi/3` and otherwise bisects, to a depth limit of 45 at which it
returns the principal value rather than raising. So the branching factor is
`2(1 - p)`, and `p` costs two evaluations to measure rather than an exponential
recursion to observe.

Measured at height 120: at `dps = 100` the rule accepts **24 segments out of
24**, so the recursion stops on its first test every time. At `dps = 15` it
accepts 7 of 24, close to the `1/3` a uniform phase predicts, and one segment
costs about `6.4e6` evaluations, or 148 days.

The answer does not depend on the exact `p`: because the depth limit returns a
value, **the cap cannot cost a refusal.** It costs a wrong count or a run that
does not finish, decided by the depth limit rather than by any check.

## 6. What this episode is

Two hunts derived a precision law and wrote it down. A third measured it as a
surface, derived it properly, built a guard, and shipped a guard with a hole in
exactly the term it had derived, protected by a fault ladder that could not see
the hole because every rung varied the wrong thing.

None of that was caught by anyone reading more carefully. It was caught by
something with no stake in the answer being told to break it, which then also
noticed that the page's title was wrong about the tree it was criticising.

The guard is still a proposal. A hunt may not write `zeta/`, and the disposition
is the tree's.
