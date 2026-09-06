# RESULTS: gate-5 property 6 is VACUOUS

**Verdict: VACUOUS.** Two of the three preregistered boxes were decided for
all four functions, and in both of them all three RH-violating rivals satisfy
property 6 exactly as ζ does. Under gate #3's own rule a property that a rival
shares distinguishes nothing, so property 6 cannot be the load-bearing step of
an RH argument.

Grade: **measured**. One route, floating-point mpmath at stated precision with
a two-precision replication guard. Nothing here is evidence for or against RH
(`docs/08`); a hunt is a probe, not a result.

Parameters were fixed in `MISSION.md` and committed at `623e800` before any
zero count was computed. The probe ran afterwards. The commit order is the
evidence and it can be checked.

## The table

Counts are zeros in the closed rectangle, by the argument principle, with the
winding required to be within `1e-6` of an integer.

| box | `σ` | `t` | ζ (via ξ) | Davenport-Heilbronn | Epstein (2,1,3) | Epstein (1,1,6) | verdict |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **A** | `[0.70, 0.92]` | `[1.5, 11.5]` | 0 | 0 | 0 | 0 | **VACUOUS** |
| **B** | `[0.70, 0.92]` | `[85.2, 86.2]` | 0 | **1** | not decided | not decided | not decided |
| **C** | `[1.05, 1.60]` | `[1.5, 11.5]` | 0 | 0 | 0 | 0 | **VACUOUS** |

"Satisfies property 6" means a count of 0. In boxes A and C every rival
satisfies it, so `shared_with` is all three and the battery's rule returns
VACUOUS. Box B is reported not decided, honestly: its two Epstein cells were
never run, for the reason in the cost section below.

Every decided cell passed the preregistered adequacy guard by a wide margin.
The worst relative disagreement between `dps = D` and `dps = D + 15` at a box
corner, across all ten decided cells, was `3.5e-22` against a `1e-6`
threshold.

| cell | `dps` | forced segments | distinct evaluations | seconds |
| --- | --- | --- | --- | --- |
| A, ζ | 20 | 92 | 92 | 0.1 |
| A, Davenport-Heilbronn | 20 | 92 | 92 | 0.7 |
| A, Epstein (2,1,3) | 28 | 92 | 92 | 125.5 |
| A, Epstein (1,1,6) | 28 | 92 | 93 | 142.9 |
| B, ζ | 20 | 22 | 22 | 0.0 |
| B, Davenport-Heilbronn | 20 | 22 | 22 | 0.5 |
| C, ζ | 20 | 96 | 96 | 0.1 |
| C, Davenport-Heilbronn | 20 | 96 | 96 | 0.7 |
| C, Epstein (2,1,3) | 28 | 96 | 96 | 139.8 |
| C, Epstein (1,1,6) | 28 | 96 | 96 | 156.4 |

Whole probe: 641.6 seconds. No contour collision occurred, so the §5 nudge
rule never fired and no box was moved.

## The instrument checks out where it can be checked

Box B's Davenport-Heilbronn cell returns **1**, and the zero it is counting is
the one already pinned in `zeta/epstein.py`,

```
rho = 0.80851718245663738555335196060684... + 85.69934848537759217192926770894...i
```

which sits inside box B with `0.09` of clearance in `σ` and `0.5` in `t`, and
which matches Spira, *Math. Comp.* 1994. So the counting routine recovers a
known off-line zero at exactly the place the literature puts it, in the one
cell where an independent answer exists. That is the only positive control
available here and it passed.

## What was chosen, and why

The three boxes and the precision rule were picked on cost grounds and on one
measured numerical fact, before any count existed.

**The boxes.** Box A is the *a priori* box: the tallest strictly-off-line box
inside the critical strip that all four functions could be counted on at an
adequate precision within budget. Its height was set by what the Epstein
evaluation costs, not by where anybody's zeros are. Box B is the *witness*
box, chosen to be as favourable to DISTINGUISHES as any box can be: it
contains a rival's off-line zero that was known in advance, so one rival was
guaranteed to fail there. Box C sits in the half-plane `σ > 1`, where ζ is
zero-free by the Euler product and where the rivals are known to have zeros
somewhere, because that is where a well posed version of the property would
have to live.

**The precision.** A calibration run before `MISSION.md` was written measured
only timings and magnitudes, never a count. It found that

```
epstein_completed(0.8 + 85.7i, (2,1,3))  =  1.2e-34    at dps = 20
                                         =  1.617e-58  at dps = 60 and at dps = 90
```

against the analytic magnitude `|(√d/π)^s Γ(s)| = 2.64e-58`. The `dps = 20`
answer is round-off noise, wrong by twenty-four orders of magnitude, because
`Λ_Q` is exponentially small in `t` while the terms of its Mellin-split
representation are `O(10^-2)`. The digits lost are about
`π t / (2 ln 10) ≈ 0.6822 t`, which is the preregistered precision rule:
`dps = 20 + ceil(0.6822 · t_max)`, giving 28 for boxes A and C and 79 for box
B.

## What could not be settled, and what it would take

Box B's two Epstein cells are `NOT-DECIDED-BY-COST`, from arithmetic recorded
before either was attempted:

```
Epstein (2,1,3) at dps 79:  14.26 s/eval x 22 forced segments x 2 = 627 s
Epstein (1,1,6) at dps 79:  13.93 s/eval x 22 forced segments x 2 = 613 s
```

against a 480-second cell cap. Deciding them needs roughly 21 minutes of
mpmath at `dps = 79`, or a faster evaluator: ball arithmetic through
`python-flint`, or an Epstein routine that does not build an exponentially
small number out of `O(10^-2)` pieces. Neither was in scope here.

Their absence does not change the verdict. Boxes A and C are each decided for
all four functions, and either one alone returns VACUOUS.

## The trap the brief named, and what it actually costs

Property 6 is box-dependent by construction, and the run shows the dependence
rather than arguing about it: the Davenport-Heilbronn function **satisfies**
property 6 on box A and on box C, and **fails** it on box B. The same rival,
the same property, opposite truth values, decided by which rectangle you
picked. So "property 6" as written is not one claim. It is a family of claims
indexed by a box, and asking whether *it* is vacuous or distinguishing has no
answer until the box is named.

That does not rescue it, because the box-indexed claims are vacuous almost
everywhere and for a structural reason. For a fixed box `B` to distinguish, it
would have to contain an off-line zero of the Davenport-Heilbronn function
*and* an off-line zero of Epstein `(2,1,3)` *and* an off-line zero of Epstein
`(1,1,6)`, while containing no zero of ξ. Those three functions are unrelated
in their zero locations, so a rectangle catching all three at once is a
coincidence, not a construction. Box B is the demonstration: it was built
around the one off-line zero this laboratory has pinned, and it still leaves
two rivals with no reason to fail. Every box that misses any one rival's
off-line zeros returns VACUOUS, and boxes A and C are two such boxes decided
in full.

**A well posed version, and where it lands.** Quantify over boxes instead of
fixing one:

> for **every** box strictly off the critical line, the completed function has
> no zeros

This is well posed, and it does distinguish: it is false for all three rivals
by Davenport and Heilbronn's 1936 theorem, quoted and not recomputed here, and
it is expected true of ζ. But it is exactly the statement "the completed
function has no zeros off the critical line", which for ζ is RH. A gate-#3
property that turns out to be the conclusion is not a step toward the
conclusion, and a battery that returned DISTINGUISHES for it would be
reporting circularity rather than progress.

The nearest version that is both well posed and not circular is the half-plane
one:

> the completed function has no zeros with `Re s > 1`

true of ζ by the Euler product, false of all three rivals by the same 1936
theorem. That is a real discriminator, and it is also not new information: it
is the Euler product again, which is what property 4-5 already reported as
DISTINGUISHES. Property 6 has no discriminating power of its own to add.

## A defect in the battery, found on the way

`zeta.epstein.battery` cannot be used to answer any zero-counting question
above roughly `t = 25`, and it will not say so. Both rival interfaces cap the
working precision:

- `epstein_interface(...)["count_zeros_box"]` passes `dps=min(dps, 20)`
- `dh_interface(...)["count_zeros_box"]` passes `dps=min(dps, 20)`

For the completed Epstein function that cap is below the precision the
function needs: at `t = 85.7` a `dps = 20` evaluation is noise twenty-four
orders of magnitude too large, as measured above. An argument-principle count
built on those values is the winding number of round-off, and it will usually
still come out an integer, so `count_zeros_box`'s integrality check does not
catch it. A caller who asks `battery` a property-6 question at height gets a
number with no warning attached.

This hunt therefore called `count_zeros_box` directly with an explicit `fn`
and an explicit `dps`, reproducing `battery`'s verdict rule unchanged, and
declared the deviation in `MISSION.md` §1 before running. The defect is
reported rather than patched: `zeta/` is outside this hunt's write scope.

## Loose threads

- **Box B's Epstein cells.** Decidable, at roughly 21 minutes of mpmath at
  `dps = 79`, or much less through a ball-arithmetic backend. They would not
  change the verdict, but they would close box B and make the box-dependence
  demonstration complete on all four functions rather than two.
- **The capped precision in `battery`'s rival interfaces.** `min(dps, 20)`
  silently produces noise-driven counts above `t ≈ 25`. The fix is small: pass
  the caller's `dps`, or refuse a box whose height exceeds what the cap can
  support. Deserves an issue on this repository, and a test that a count at
  height disagrees with itself between two precisions.
- **A precision-adequacy guard as a reusable instrument.** The
  evaluate-at-`D`-and-`D+15` check in `probe.py` is four lines and it is the
  only reason this run knows its numbers are real. Nothing in `zeta/` offers
  it, and every hunt that evaluates a completed L-function at height needs it.
- **The Epstein evaluator's conditioning.** `epstein_completed` computes an
  exponentially small quantity as a sum of `O(10^-2)` terms, which is why it
  costs `0.6822 t` digits. An evaluator that factors out the `Γ(s)` decay
  before summing would make Epstein zero-counting at height affordable, and
  would retire the cost barrier this hunt hit.
- **Where the off-line zeros of the discriminant −23 forms actually are.**
  Davenport and Heilbronn prove they exist. This laboratory has never located
  one, and box B shows why it matters: without a pinned Epstein off-line zero,
  no box can be built that puts all three rivals under the same test at once.
- **The `prepare-commit-msg` hook is not installed in a fresh clone**, so the
  `Run-Id` trailer this run's telemetry expects does not appear on commits
  unless it is written by hand. Noted where it was noticed.
