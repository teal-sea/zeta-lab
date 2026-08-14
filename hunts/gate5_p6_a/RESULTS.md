# Hunt #13 (gate5_p6_a): property 6 is VACUOUS, and it is also not well posed

**Verdict: VACUOUS.** A rival satisfies property 6 in the very box chosen in
advance to make that hardest.

Grade: **measured** (rung 1 of the ladder in `AGENTS.md`: one route, float
grade, no enclosures). Nothing here is evidence for or against RH (`docs/08`).
This is about what separates zeta from RH-violating look-alikes, and nothing
more.

## The property, and what was fixed before running

> in a box strictly off the critical line, the completed function has no zeros

Operationalized as `count_zeros_box(...) == 0` on the completed function, at
`dps = 20`, over boxes fixed in `MISSION.md` and committed in `14dbb17`, one
commit before `probe.py` existed. The reasoning for the boxes is in that file;
the short version is that **box A was chosen adversarially**. It is the one
region in this repository where a rival is known in advance to have an off-line
zero (the Davenport-Heilbronn zero `0.808517... + 85.699348...i` pinned in
`zeta.epstein.OFFLINE_ZERO_RE / OFFLINE_ZERO_IM`), so it is the box most
favourable to a DISTINGUISHES verdict. Box B is the same shape at an unrelated
ordinate, and exists to measure how far the verdict moves with the box.

`MISSION.md` also recorded a prediction before the run: VACUOUS. That is what
happened.

## The table

Counts are zeros of the completed function inside the closed rectangle, by the
argument principle.

**Box A** (`sigma in [0.70, 0.92]`, `t in [85.55, 85.85]`), the favourable box:

| function | count | seconds | reads |
| --- | --- | --- | --- |
| `riemann_zeta` (xi) | 0 | 0.02 | satisfies P6 |
| `davenport_heilbronn` | 1 | 0.46 | **fails** P6 (the pinned zero) |
| `epstein_2_1_3` | **0** | 28.95 | **satisfies P6, exactly as zeta does** |
| `epstein_1_1_6` | not finished | 420 (cap) | recorded gap, not a truth value |

**Box B** (`sigma in [0.70, 0.92]`, `t in [70.10, 70.40]`), the generic box:

| function | count | seconds | reads |
| --- | --- | --- | --- |
| `riemann_zeta` (xi) | 0 | 0.02 | satisfies P6 |
| `davenport_heilbronn` | **0** | 0.24 | **satisfies P6** |
| `epstein_2_1_3` | see `results.json` | | |
| `epstein_1_1_6` | see `results.json` | | |

Controls, both run and reported before the verdict was read:

- **Straddling-box control.** `xi` over `sigma in [0.20, 0.80]`,
  `t in [13.60, 14.60]` returned **1**, the expected single zero at
  `gamma_1 = 14.134725141734694`. The contour machinery works.
- **Known-answer control.** The Davenport-Heilbronn count on box A returned
  **1**, matching the zero pinned inside it. That column was known before the
  run, which is exactly why it is a control and not evidence.

Robustness of the one cell the verdict rests on: `epstein_2_1_3` on box A was
re-counted at halved and quartered forced-subdivision length
(`probe.py --confirm`); see the `robustness` block of `results.json`.
`count_zeros_box` independently refuses any contour whose winding residual
exceeds `1e-6`, so an under-resolved edge raises rather than rounds to zero.

## Reading it

**Box A settles the question in the direction that costs the property
everything.** `battery`'s own rule is that a structure must be ungrantable to
*every* counterexample: a claim zeta shares with any rival cannot be the
load-bearing step, however many other rivals it excludes. The Epstein zeta of
the non-principal discriminant -23 form has no zeros in box A. It satisfies
property 6 there in precisely the sense zeta does. So property 6 is VACUOUS on
box A, and the unfinished `epstein_1_1_6` cell cannot change that: one survivor
is enough, and a second survivor would only make the verdict more so.

That the *favourable* box came out vacuous is the point of having chosen it in
advance. Any cheaper box has a strictly worse chance, so there is nothing to be
gained by shopping for another one.

## The larger finding: property 6 is not well posed as stated

Box A and box B give **different answers for the same function**. The
Davenport-Heilbronn function fails property 6 in box A and satisfies it in box
B. Property 6 is therefore not a property of a function at all. It is a
property of a *(function, box)* pair, and the gate is being asked to read a
one-bit verdict off a quantity that has a free parameter in it.

Resolve the free parameter either way and the property stops being useful:

- **Quantify over all boxes.** "For every rectangle strictly off the critical
  line, the completed function has no zeros" is, for zeta, exactly RH restricted
  to the off-line region. It cannot be verified for zeta, by anybody, so it
  cannot be the *true* half of a gate #3 comparison. A gate whose zeta column is
  unknowable decides nothing.
- **Instantiate one box.** Then it is vacuous, and measurably so, for a
  structural reason rather than a numerical accident: the off-line zeros of the
  three rivals sit at unrelated ordinates, so a box small enough to compute is
  overwhelmingly likely to miss at least one rival's zeros. A box that caught an
  off-line zero of all three at once would have to be large, and confirming
  zeta's column in a large box is the expensive direction. That is the same wall
  the previous attempt hit at 50 minutes on `0.6+80i` to `0.9+90i`, and it is not
  an artifact of that particular box.

So the answer to the question as put is **VACUOUS**, and the reason it is
vacuous is not "we picked a bad box". It is that no affordable box can make it
otherwise.

### What a well posed version would be

Replace the box with a **fixed region**, chosen so that zeta's column is a
theorem rather than a computation:

> the completed function has no zeros in `Re s > 1`

- **Zeta's column is settled and provable.** `zeta(s) != 0` for `Re s >= 1`
  (Hadamard and de la Vallée Poussin, 1896), and `xi(s) = (1/2)s(s-1)pi^{-s/2}
  Gamma(s/2) zeta(s)` has no extra zeros there, since `Gamma` never vanishes and
  `s(s-1)` vanishes only at `s = 0, 1`. No computation, no height limit, no box.
- **The rivals' column is the classical Davenport-Heilbronn theorem** (1936):
  both the Davenport-Heilbronn function and the Epstein zeta of a positive
  definite binary form of class number greater than one have infinitely many
  zeros with `Re s > 1`. **This is quoted from the literature and was not
  recomputed here** (see "what I could not settle").
- It is box-free, so it has no free parameter for a verdict to hide in.

This version DISTINGUISHES. But it should be adopted with its own caveat
attached, because **it distinguishes for a reason the module already names**:
zeta's nonvanishing in `Re s > 1` follows immediately from the Euler product,
absolutely convergent there. So the well posed version is a restatement of "has
an Euler product", which is already property 4 or 5 territory. It is a correct
gate input and it is not an *independent* one. A gate #3 property earns its keep
by isolating a structure other than the Euler product; this one does not, and
saying so is more useful than banking a DISTINGUISHES.

## What I could not settle

- **`epstein_1_1_6` on box A** did not finish inside its 420 s cap and is
  recorded as a gap. It does not affect the verdict (one survivor already
  settles it), but the asymmetry is itself a measurement: the principal form
  `(1,1,6)` is far more expensive to evaluate than the non-principal `(2,1,3)`,
  which finished the same box in 29 s. More than a 14x cost ratio on the same
  contour, from the same code path.
- **The rivals' half of the proposed well posed version was not verified here.**
  Box C (`sigma in [1.02, 1.60]`, `t in [0.50, 50.50]`) was fixed in advance for
  exactly that purpose and gated on a measured cost projection; see the
  `cost_probe` block of `results.json` for whether it was affordable and what it
  returned. Finding an explicit zero with `Re s > 1` for each of the three
  rivals would upgrade the proposal from "quoted theorem" to "quoted theorem
  plus a witness in this tree", which is what this repository normally requires
  of a claim it leans on.
- **Nothing here bounds where the rivals' off-line zeros actually are.** The
  claim "an affordable box cannot catch one of each" is an argument from their
  being at unrelated ordinates plus the two boxes measured, not a proven
  density statement.

## Loose threads

- **The battery's property-6 column is not literally the same claim across the
  four functions.** `zeta.epstein.dh_interface` wires its `count_zeros_box` to
  the *uncompleted* `dh_f`, while `zeta_interface` uses `xi` and
  `epstein_interface` uses `epstein_completed`. In every box used here the gamma
  factor of `completed_dh` is finite and non-vanishing, so the two agree and
  nothing above is affected. In general they need not: the gamma factor has
  poles at `s = -1, -3, -5, ...`, and a box reaching into `Re s < 0` would count
  different things in different columns. This probe used `completed_dh`
  explicitly to keep the four columns identical. Worth an issue.
- **The `(1,1,6)` evaluation cost.** A 14x-plus gap between the principal and
  non-principal forms of the same discriminant, on the same contour, is either a
  real property of the theta-series split in `epstein_completed` or a slow path
  worth finding. It is the reason one cell of this table is empty.
- **Where the Davenport-Heilbronn zeros with `Re s > 1` actually are.** Spira
  1994 computed off-line zeros of the Davenport-Heilbronn function; this tree
  pins exactly one, at `Re = 0.8085`, which is not in `Re s > 1`. A witness in
  `Re s > 1` for each rival would let the proposed well posed version stand on
  something this repository measured rather than quoted.
- **The gate itself has a shape problem worth naming.** Three of the six battery
  properties came back vacuous and this one is vacuous *and* ill-posed. A gate
  input whose zeta column is unknowable is not a gate input, and it may be worth
  making that a stated admission rule for the battery rather than something each
  hunt rediscovers.
