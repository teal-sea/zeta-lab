# Hunt #13 (gate5_p6_a): is "no zeros in a box off the critical line" vacuous or distinguishing?

**Status at the time this file was committed: nothing has been computed.** The
parameters below were fixed first, on the reasoning recorded below, and the
commit order is the evidence. `probe.py`, `results.json` and `RESULTS.md` land
in later commits.

## The question

`docs/09` gate #3 says a claimed structural property of zeta is worth nothing
as evidence if a function that shares the structure and violates RH satisfies
it too. `zeta.epstein.battery` runs a claimed property against four functions:
zeta itself, the Davenport-Heilbronn function `f`, and the two Epstein zeta
functions of discriminant -23 attached to the forms (2,1,3) and (1,1,6).

Property 6, the open one:

> in a box strictly off the critical line, the completed function has no zeros

Does it **DISTINGUISH** (true of zeta, false on all three rivals) or is it
**VACUOUS** (some rival satisfies it too)?

## What is fixed in advance

### The operationalization

For a function with completed form `F`, and a rectangle `B` all of whose points
have `Re s > 1/2` strictly:

    P6(B, F)  is true  iff  count_zeros_box(corners of B, fn=F) == 0

using `zeta.epstein.count_zeros_box`, the argument-principle count already in
the module. All four completed functions are entire, so no pole dodging is
needed and the routine applies unchanged. This is exactly the `count_zeros_box`
entry of the interface dicts, so the four functions are compared through one
code path.

Note what `P6` is a property *of*: it is indexed by a box. That is stated here,
before any number exists, because it is the thing most likely to decide the
verdict.

### The boxes

**Box A, the adversarially favourable one.**

    sigma in [0.70, 0.92],  t in [85.55, 85.85]

Why this box and no other: it contains the Davenport-Heilbronn off-critical-line
zero pinned in `zeta.epstein.OFFLINE_ZERO_RE / OFFLINE_ZERO_IM`,

    rho = 0.80851718245663738555... + 85.69934848537759217192...i

and it is the *only* region anywhere in this repository where a rival is known
in advance to have an off-line zero. Box A is therefore the box that maximizes
property 6's chance of coming out DISTINGUISHES: one of the three rivals is
guaranteed to fail it here. Every other box we could afford has a strictly worse
chance. **If property 6 fails to distinguish even in the box hand-picked to
favour it, it fails in the cheap boxes too**, and that is the whole reason for
choosing adversarially rather than generically.

The box is strictly off the critical line (its left edge is at 0.70, well clear
of 1/2) and it is on one side only, so it contains `rho` and not the reflected
partner `1 - rho`. It is small: 0.22 wide, 0.30 tall.

**Box B, the generic control.**

    sigma in [0.70, 0.92],  t in [70.10, 70.40]

Same width and height, comparable ordinate so the sampling step is comparable,
and no relation to any pinned zero. Its job is not to settle the property. Its
job is to *measure the box dependence*: if box A and box B give different
verdicts, the property is not well posed as a single claim and the write-up has
to say so with numbers.

**Box C, the exploratory one, in the region `Re s > 1`.**

    sigma in [1.02, 1.60],  t in [0.50, 50.50]

Fixed now, run only if the cost measurement (below) says it fits. Reason for
having it at all: zeta's completed function is zero-free in `Re s > 1` and that
is a theorem rather than a computation, while the rivals are not obviously so.
A tall thin box in that half plane is the cheapest place where all three rivals
could in principle fail at once. The box is fixed here; the only thing decided
after measurement is whether it is affordable, which is a cost decision and not
a parameter chosen on a result.

### Precision and the counting route

- `dps = 20`. The interface wrappers cap the box count at `min(dps, 20)`
  regardless, so declaring 20 makes the cap explicit instead of accidental.
- `step`: the routine's own default (matched to the phase-turn rate of `f` at
  the box height). On `ArithmeticError` the step is halved and retried, at most
  3 times, and every retry is recorded in `results.json`.
- If the error persists and reads as a zero on the contour, the box is nudged
  by +0.005 in `t`, at most twice, and the nudge is recorded. A nudge changes
  the box, so it is reported next to the number it produced.
- Wall clock cap **420 s per (function, box)**. A cap hit is recorded as
  `timeout` and is **not** read as a truth value in either direction. The prior
  attempt on `0.6+80i` to `0.9+90i` died at 50 minutes; the caps here exist so
  that a miss costs a recorded gap rather than the run.

### Positive controls, run and reported before the verdict is read

1. `xi` over `sigma in [0.20, 0.80]`, `t in [13.60, 14.60]` must return **1**
   (gamma_1 = 14.134725141734694). This checks the contour machinery on a
   straddling box with a known answer.
2. The Davenport-Heilbronn entry for box A must return **at least 1**. Its value
   is known in advance from the pinned zero, so it is a machinery check and not
   part of the evidence. If it returns 0, the count is broken and this hunt
   reports `blocked` rather than a verdict.

Stating control 2 plainly also states where the verdict actually lives: the
Davenport-Heilbronn column of box A is known before the run, so **the verdict
hinges entirely on the two Epstein columns**.

### The preregistered prediction

Recorded so the outcome cannot be re-narrated afterwards: I expect box A to come
out **VACUOUS**, because the off-line zeros of the two discriminant -23 Epstein
functions have no reason to sit inside a 0.22 by 0.30 rectangle chosen around a
zero of an unrelated function. If that is what happens, the interesting part of
the result is not the verdict but the well-posedness question underneath it.

### What would count as DISTINGUISHES

All four counts complete, zeta's is 0, and all three rivals' counts are at least
1, in the same box. Nothing weaker. In particular a box in which two rivals fail
and one survives is VACUOUS, per `battery`'s own rule that the structure must be
ungrantable to every counterexample.

## Standing limits

Nothing here is evidence for or against RH (`docs/08`). This is about what
separates zeta from RH-violating look-alikes, and nothing more. Every number
below is a float-grade measurement on the ladder in `AGENTS.md`, and is called
one.

```huntspec
id: gate5_p6_a
question: Does "the completed function has no zeros in a box strictly off the critical line" distinguish zeta from the three RH-violating rivals of the gate #3 battery, or is it vacuous?
frontier: gate #3 battery properties 1-3 vacuous, 4-5 distinguishing, property 6 open; a prior attempt on the box 0.6+80i to 0.9+90i did not finish in 50 minutes
proposed_attack: instantiate the property on a box hand-picked to favour DISTINGUISHES (it contains the pinned Davenport-Heilbronn off-line zero), plus a same-sized generic box to measure box dependence
dead_routes:
  - the box 0.6+80i to 0.9+90i at working precision across four functions, which exceeded 50 minutes without finishing
required_oracles:
  - argument-principle winding count over a closed contour, with a non-integer residual raising rather than rounding
  - the Davenport-Heilbronn off-line zero pinned in zeta.epstein and re-verified by tests/test_epstein.py
  - the first ordinate of zeta, 14.134725141734694, as a straddling-box control
kill_conditions:
  - the straddling-box control on xi does not return 1
  - the Davenport-Heilbronn count on box A returns 0 despite the zero being pinned inside it
  - box A and box B disagree on the verdict, in which case the property is reported as not well posed rather than settled
  - any count fails to complete inside its wall-clock cap, in which case that cell is reported as a gap and not as a truth value
agents_may:
  - search
  - derive
  - code
  - attack
  - measure
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - read other agents' branches or hunt directories attacking this same question
```
