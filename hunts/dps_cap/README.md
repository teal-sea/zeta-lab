<!-- provenance header added 2026-08-21 when this directory was landed -->

> **Landed 2026-08-21 from five branches that never merged.** Five runs
> worked this question concurrently on 2026-08-14 (`live-b4528bd7`,
> `live-aeb4e5de`, `live-f12f9441`, `live-e72925d1`, `support/e6241336`) and
> all five wrote to this same directory name. None of them landed, so the
> measurement below existed only on abandoned branches for a week.
>
> The directory is their union. Files only one run produced keep their name.
> Files several runs produced *differently* carry the run's short id, the
> convention `hunts/r_b9552d` already uses on main. Byte-identical copies
> were collapsed. Nothing was merged or reconciled: where two runs disagree,
> both are here and the disagreement is visible.
>
> Two lines were edited, and only two. `crosscheck.py` and
> `probe-e72925d1.py` each hardcoded an absolute path into the author's home
> directory to locate site-packages, which `tests/test_repo_hygiene.py`
> rejects and which would not run on any other machine. Both now derive the
> same directory from `ROOT`, which those files already compute. The edits
> are marked in place.
>
> So references below to `MISSION.md`, `probe.py` and `results.json` mean
> this run's copies: `MISSION-f12f9441.md`, `probe-f12f9441.py`,
> `results-f12f9441.json`. `FINDINGS.md` is `live-b4528bd7`'s independent
> write-up of the same question and agrees on the headline.
>
> This body text is `live-f12f9441`'s, verbatim.

# What the `min(dps, 20)` cap costs, measured at one point

**Status: probe, complete. At `0.8 + 85.7i` the capped precision does not
return a worse answer, it returns no answer: `3.1e-33` where the converged
value is `1.6e-58`, a factor of `1.9e25` and not one correct digit.**

Nothing here is a result and nothing here is evidence about ζ or RH. It is a
measurement of an implementation, taken at a single point. Read `MISSION.md`
first for scope; `probe.py` produces every number below, `results.json` holds
them at full width.

## The headline

The quantity is `abs(epstein_completed(0.8 + 85.7i, (2, 1, 3), dps=D))`.

| D | returned magnitude | correct significant digits |
| --- | --- | --- |
| 20 | `3.1063191101762650844e-33` | 0 |
| 60 | `1.6174526323779715467e-58` | ~15.8 |

Ratio `(D=20)/(D=60)` = `1.920501e+25`.

The D = 20 row is quoted for a point parsed at 20 digits, and reading #4 below
is the reason that qualification is needed: at the capped precision the
returned magnitude is not a property of the point at all, and writing the same
point a different way moves it by a factor of 64. The D = 60 row needs no such
qualification.

## Reading it

**1. The capped value is noise, not a rounded answer.** The two magnitudes do
not differ in their last digits, they differ by twenty-five orders of
magnitude. `epstein_completed` evaluates a lattice sum of incomplete gammas
whose terms are individually far larger than their total at this height, so
the routine carries an absolute error floor that has nothing to do with the
size of the answer. The full sweep shows the floor moving with precision while
the answer stands still:

| D | returned magnitude | seconds |
| --- | --- | --- |
| 20 | `3.1063191101762651e-33` | 0.93 |
| 30 | exactly `0.0` | 1.36 |
| 40 | `1.3136144537464079e-54` | 1.88 |
| 50 | `1.6174827233311586e-58` | 2.68 |
| 60 | `1.6174526323779715e-58` | 4.04 |
| 80 | `1.6174526323779713e-58` | 7.24 |

The floor sits near `1e-(D+13)`: `3.1e-33` at D = 20, `1.3e-54` at D = 40.
The true magnitude is `1.6e-58`, so nothing correct can appear below
D ≈ 46, which is where the sweep puts the crossover: D = 40 is still entirely
floor, D = 50 is the first row with correct digits, and it has about five.

**2. D = 60 buys ~16 digits, not 60.** The D = 60 and D = 80 rows agree to a
relative `1.5e-16`, so the cancellation at this point costs about 44 of the
requested digits. That is the convergence control, and it is the reason the
D = 60 row is quoted as the converged value rather than as one more sample.

**3. An independent size bound rejects the capped answer on its own.**
`epstein_completed`'s own definition is
`Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)` with `d = ac - b^2/4 = 5.75`.
The archimedean factor is computable without touching the lattice sum:

    abs((sqrt(5.75)/pi)^s Gamma(s)) = 2.64000157088e-58   at s = 0.8 + 85.7i

Dividing each returned magnitude by that envelope reports the
`abs(zeta_Q(0.8 + 85.7i))` it implies:

| D | implied `abs(zeta_Q)` |
| --- | --- |
| 20 | `1.1766353264e+25` |
| 40 | `4975.8` |
| 60 | `0.6126710871` |

`zeta_Q` is a Dirichlet series continued into the strip, so it grows
polynomially in `t` and `0.61` at `t = 85.7` is an ordinary value while `1e25`
is not one it takes. This check uses `mp.gamma` and nothing from the routine
under test, so it is the one line here that would survive the lattice code
being wrong. It is a size argument, not a computed bound: no explicit
convexity constant was evaluated.

**4. At D = 20 the returned magnitude is not a function of the point.** This
is the sharpest of the checks and it was not planned. `mp.mpc('0.8', '85.7')`
is a different bit pattern at every parse precision, and all of those bit
patterns denote the same complex number to far past any digit that matters. A
converged evaluation must return the same magnitude for all of them. This one
does not:

| how the same point was written | D = 20 | D = 60 |
| --- | --- | --- |
| parsed at dps 15 (mpmath's default) | `1.2115954820e-34` | `1.6174526324e-58` |
| parsed at dps 20 | `3.1063191102e-33` | `1.6174526324e-58` |
| parsed at dps 60 | `4.8463819280e-35` | `1.6174526324e-58` |
| Python floats `mp.mpc(0.8, 85.7)` | `1.2115954820e-34` | `1.6174526324e-58` |

Spread at D = 20: a factor of **64**. Spread at D = 60: none to twelve digits.
The capped output is a function of the bit pattern rather than of the
mathematics, which is what "noise" means stated as a measurement rather than
as an adjective.

It also reconciles this hunt with an earlier observation. The thread recorded
by run `d9ae5359` (`GATE5-P6-B`) reports `1.2e-34` at this same point and
precision, against this hunt's `3.1e-33`. Both are right: `1.2e-34` is the row
for a point parsed at mpmath's default precision, `3.1e-33` the row for one
parsed at 20. The two numbers were never in conflict, they are two samples of
the same floor.

**5. D = 30 returns exactly `0.0 + 0.0i`.** Not a small number, the zero
complex number, `re == 0 and im == 0` both `True`. That is the failure mode
worth flagging, because it is the one that does not look like a failure: a
caller that treats a vanishing `Lambda_Q` as a root of `Lambda_Q` would read a
root at a point where the function is `1.6e-58` and nonzero. **The mechanism
was not traced.** Exact cancellation in a fixed-point accumulator is the
obvious candidate and this run did not test it, so it stays a candidate.

## Where up the strip the cap actually fails

`0.8 + 85.7i` is one point, and the question that decides whether any earlier
verdict is suspect is *how far up* the cap still works. Measured by
`crossover.py` at `sigma = 0.8`, as the relative error of the whole complex
D = 20 value against D = 60 (the whole value, not the magnitude, because
`count_zeros_box` consumes the argument):

| t | `abs(Lambda_Q)` | relative error at D = 20 |
| --- | --- | --- |
| 5 | `9.53e-04` | `3.1e-22` |
| 10 | `9.23e-07` | `4.5e-22` |
| 20 | `1.04e-13` | `2.6e-19` |
| 25 | `3.27e-17` | `4.9e-16` |
| 30 | `2.69e-20` | `7.0e-14` |
| 35 | `1.10e-23` | `2.8e-10` |
| 40 | `1.34e-27` | `1.0e-06` |
| 45 | `5.54e-30` | `5.9e-05` |
| 50 | `6.47e-34` | `9.2` |
| 60 | `1.58e-40` | `3.9e+07` |
| 85.7 | `1.62e-58` | `3.0e+23` |

The capped path is accurate to `1e-6` through **t = 35**, degrades through
t = 40 to 45, and is **fully lost by t = 50**, where the relative error passes
1. Measured at `sigma = 0.8` only: a contour box spans a range of sigma and
this run did not sweep it.

## What this does not establish

The clamped call site is `count_zeros_box`, an argument-principle contour
integral, and it does not consume the magnitude measured here. It consumes the
**winding of the argument** around a box. Whether a floor of `1e-(D+13)`
against a true magnitude of `1e-58` corrupts that winding, and whether the
boxes the battery actually draws reach `t = 85.7`, are two separate questions
this run did not ask.

The routine is also not defenceless, which cuts against the alarming reading:
`count_zeros_box` requires the accumulated variation to come out within `1e-6`
of an integer and raises `ArithmeticError` otherwise (`zeta/epstein.py:628`).
A thoroughly corrupted phase would more likely trip that check than return a
quietly wrong count. Whether it always does is, again, not measured here. So:

- This is **not** a demonstrated defect in `zeta.epstein.battery`.
- This is **not** an argument for raising the clamp. The clamp is a speed
  decision, the sweep shows the cost of lifting it is small at this point
  (0.93 s to 4.04 s), and neither fact settles whether the winding needs it.
- No file outside `hunts/dps_cap/` was changed.

The next question, for whoever takes it: evaluate `count_zeros_box` on the
same form at `min(dps, 20)` and at `dps = 60` over a box that crosses t = 50,
and compare the counts rather than the magnitudes.

## Reproduce

    .venv/bin/python hunts/dps_cap/probe.py       # ~20 s, writes results.json
    .venv/bin/python hunts/dps_cap/crossover.py   # ~3 min, writes crossover.json

Backend at time of measurement: `python-flint`, both ball backends available
(neither probe uses them; the check is recorded because a green run in this
tree is not readable without it).

## Independent check

**The commissioned one did not arrive.** `fulcrum_support` refused to open a
child from this run four times with `no live parent
f12f9441-43e9-4b1f-92e1-e61d049be6cd`, while `fulcrum_status` listed this run
as `live: true`. A sibling run had already queued a child carrying the
identical request (`22d8a969`, `SUPPORT-22d8a969`); it was polled thirteen
times over about forty minutes and stayed `state: reserved`, never dispatched,
with no model and no tokens recorded. No outside verdict on the `D = 60` value
exists as of this handback, and none is invented here.

What does exist is a prior independent measurement of the same call by a
different run, the thread recorded by `d9ae5359` (`GATE5-P6-B`). This hunt
**accepts its load-bearing claim and rejects two of its numbers**; the verdict
and its reasoning are in `HANDBACK.json`.
