# MISSION, gate-5 property 6: vacuous or distinguishing?

**Status when this file was committed: nothing has been computed.** No zero
count, for any function, in any box, had been evaluated when this file
landed. The commit order is the evidence, and it is the only reason the
verdict below is worth reading.

## The question

`docs/09` gate #3: a claimed structural property of ζ is worth nothing as
evidence if a function that shares the structure and violates RH satisfies it
too. `zeta.epstein.battery` runs a claim against ζ, the Davenport-Heilbronn
function `f`, and the two discriminant −23 Epstein zetas `(2,1,3)` and
`(1,1,6)`.

Property 6 is the open one:

> in a box strictly off the critical line, the completed function has no zeros

Does it **DISTINGUISH** (true of ζ, false of all three rivals) or is it
**VACUOUS** (some rival satisfies it too)?

## Scope of this hunt

Nothing here is evidence for or against RH (`docs/08`). This is only about
what separates ζ from RH-violating look-alikes. Nothing here is a result;
`hunts/` is a probe area.

## What is fixed before any truth value is computed

### 1. The instrument

`zeta.epstein.count_zeros_box(s0, s1, dps=…, fn=…)`: an argument-principle
winding count over a closed rectangle, which raises `ArithmeticError` when the
winding is not within `1e-6` of an integer (a zero on the contour, or an
undersampled edge). Errors are recorded, never swallowed; a box is nudged
only by the rule in §5.

**Declared deviation from `battery()`, with its reason.** `battery` is not
called directly. Its rival interfaces hard-cap the working precision at
`dps=min(dps, 20)` (`zeta/epstein.py`, `epstein_interface` and `dh_interface`).
A cost calibration run *before* this file was written, timings and magnitudes
only, no zero counts, measured that `epstein_completed(0.8 + 85.7i, (2,1,3))`
returns `1.2e-34` at `dps=20` but `1.617e-58` at both `dps=60` and `dps=90`,
against an analytic magnitude `|(√d/π)^s Γ(s)| = 2.64e-58`. The `dps=20` value
is round-off noise, wrong by twenty-four orders of magnitude. So the battery's
own instrument cannot count Epstein zeros above roughly `t ≈ 25`, and this
hunt therefore calls `count_zeros_box` directly with an explicit `fn` and an
explicit `dps`, while reproducing `battery`'s verdict rule exactly (§6). The
capped-precision defect is reported as a finding, not routed around silently.

Each function is counted through the completion the battery's own interface
uses:

| function | counted object | note |
| --- | --- | --- |
| ζ | `zeta.core.xi` | entire |
| Davenport-Heilbronn | `zeta.epstein.dh_f` | the battery's own choice; the completion factor `(π/5)^{-(s+1)/2} Γ((s+1)/2)` is zero-free and pole-free for `Re s > −1`, so on every box below it counts the same zeros as `completed_dh` |
| Epstein `(2,1,3)`, `(1,1,6)` | `zeta.epstein.epstein_completed` | has a simple pole at `s = 1`; every box below avoids it |

The contour evaluator is memoized on the sample point. This changes no
mathematics (the integrands are deterministic functions of `s`) and roughly
halves the evaluation count, because `_arg_variation` re-evaluates its segment
endpoints.

### 2. The boxes, and why these

All boxes are **strictly off the critical line**, `Re s ≥ 0.70 > 1/2`
throughout, and avoid `t = 0` and the Epstein pole at `s = 1`.

| box | `σ` range | `t` range | why this one |
| --- | --- | --- | --- |
| **A** | `[0.70, 0.92]` | `[1.5, 11.5]` | the *a priori* box: the tallest off-line box inside the critical strip that all four functions can be counted on at a precision the calibration showed adequate. Its height is set by cost and by the Epstein precision loss, not by where anything's zeros are. |
| **B** | `[0.70, 0.92]` | `[85.2, 86.2]` | the *witness* box: it contains the off-line Davenport-Heilbronn zero already pinned in `zeta/epstein.py`, `ρ = 0.80851718… + 85.69934848…i`. Chosen deliberately to be as favourable to DISTINGUISHES as any box can be, since one rival is known in advance to fail there. Same `σ` range as A, so A and B differ only in height. |
| **C** | `[1.05, 1.60]` | `[1.5, 11.5]` | supplementary, run only if the global cap in §4 leaves room. A box in the half-plane `σ > 1`, where ζ is zero-free by the Euler product and where Davenport and Heilbronn proved the rivals do have zeros, the region where a well-posed version of property 6 would have to live. |

Box B's `σ` range brackets `Re ρ = 0.8085` with `0.09` of clearance on each
side and its `t` range brackets `Im ρ = 85.6993` with `0.5` above and `0.5`
below, so no edge runs near the known zero.

### 3. The precision, and the adequacy guard

The completed Epstein function loses relative precision to the `Γ(s)` decay in
its Mellin-split representation: `Λ_Q` is exponentially small while the terms
that build it are `O(10^-2)`, so the digits lost are about
`π t / (2 ln 10) ≈ 0.6822 · t`. Preregistered working precision:

```
dps_epstein(t_max) = 20 + ceil(0.6822 * t_max)
dps_zeta = dps_dh   = 20
```

giving `dps = 28` for boxes A and C and `dps = 79` for box B. ζ's `xi` and the
Davenport-Heilbronn `dh_f` are evaluated as products and Hurwitz-zeta sums with
no comparable cancellation, so they keep `dps = 20`.

**Adequacy guard, and it runs before any count is read.** At each box's
top-right corner, evaluate the function at `dps = D` and at `dps = D + 15`. If
the two do not agree to a relative `1e-6`, the cell is recorded
`NOT-DECIDED-PRECISION` and no count from it is used. This is an empirical
check that does not depend on the analytic estimate above being right.

### 4. The cost caps

- **Per cell** (one function, one box): 8 minutes wall clock. On overrun the
  cell is `NOT-DECIDED-BY-COST`.
- **Predicted-infeasible cells are not run.** If (measured seconds per
  evaluation at the required `dps`) × (the box's forced-segment count) × 2
  exceeds the cell cap, the cell is recorded `NOT-DECIDED-BY-COST` from the
  arithmetic, and the arithmetic is reported. Burning the cap to confirm an
  arithmetic certainty buys nothing.
- **Global probe cap**: 20 minutes. Cells are executed in this fixed order,
  box A all four, box B ζ and DH, box B Epstein `(2,1,3)` then `(1,1,6)`, box
  C all four. Any cell not reached is `NOT-DECIDED-BY-BUDGET`.

**No substitution.** A cell that cannot be decided is reported undecided. An
easier box is never swapped in for a harder one, and no box is added after a
count has been seen.

### 5. Contour collisions

If `count_zeros_box` raises `ArithmeticError` on a box, the box is nudged
**once**, by the fixed rule `σ` range widened by `+0.005` on the right and `t`
range widened by `+0.005` at the top, and the error, the nudge and the retry
are all recorded. A second failure is `NOT-DECIDED-CONTOUR`.

### 6. The decision rule

For a fixed box `B`, the claim evaluated is

```
claim_B(F)  :=  (number of zeros of F in B) == 0
```

and `battery`'s own verdict rule is reproduced without change:

- **DISTINGUISHES on `B`** iff `claim_B` is true for ζ and false for *all three*
  rivals.
- **VACUOUS on `B`** iff `claim_B` is true for ζ and true for at least one rival.
- If `claim_B` is false for ζ, the claim is not a property of ζ on that box and
  the box is reported as such.

And for the question as asked, which is not indexed by a box:

- If every decided box gives the same verdict, that verdict is reported for
  property 6, with the boxes named.
- **If two decided boxes give different verdicts, property 6 is not well posed
  as stated**, it is a box-indexed family of claims, not one claim, and a
  single VACUOUS/DISTINGUISHES answer to it does not exist. In that case the
  finding is the ill-posedness, the per-box verdicts are reported as the
  evidence for it, and `RESULTS.md` states what a well-posed version would be.
- If the rival cells needed to separate the two are undecided, the answer is
  `not-settled` with the cost arithmetic that makes it undecidable at this
  budget. That is a real answer and it will be given rather than dressed up.

### 7. What would make this hunt's own answer worthless

Recorded here so it can be checked against the commit history: choosing a box
after seeing a count, widening a box until a rival's count changes, dropping a
cell because its answer was inconvenient, or reading a count from a cell that
failed the adequacy guard in §3.

## The huntspec

```huntspec
id: gate5_p6_b
question: Does gate-5 property 6, the completed function has no zeros in a box strictly off the critical line, distinguish zeta from the three RH-violating rivals of zeta.epstein.battery, or is it vacuous?
frontier: properties 1-3 of the battery returned VACUOUS and 4-5 DISTINGUISHES; property 6 is undecided, and one prior attempt on the box 0.6+80i to 0.9+90i at working precision did not finish inside fifty minutes
proposed_attack: fix two boxes and a precision rule in advance, count zeros of all four functions in each by the argument principle, and read the battery's own verdict rule off the counts
dead_routes:
  - the box 0.6+80i to 0.9+90i at working precision, which did not finish in fifty minutes
  - epstein_completed at dps 20 above t roughly 25, where the Gamma decay in the Mellin split leaves only round-off, measured 1.2e-34 against a true 1.617e-58 at t = 85.7
  - epstein_functional_equation_defect as a check of anything, since it is zero by construction
required_oracles:
  - argument-principle winding count over a closed rectangle, rejected unless the winding is within 1e-6 of an integer
  - replication of every boundary evaluation at fifteen additional digits, agreeing to a relative 1e-6
  - the off-line Davenport-Heilbronn zero pinned in zeta/epstein.py and cross-checked against Spira, Math. Comp. 1994
  - the Davenport-Heilbronn 1936 theorem as published, quoted and not recomputed
kill_conditions:
  - a count is read from a cell whose two precisions disagree
  - a box is chosen, moved or widened after any count on it has been seen
  - the verdict changes between the preregistered boxes, in which case the single-verdict question is withdrawn as ill posed rather than answered
  - the winding fails to be an integer twice on the same box
agents_may:
  - evaluate the four functions and count zeros in the preregistered boxes
  - record a cell as undecided on cost, precision or contour grounds
  - report the capped-precision defect in the battery interfaces as a finding
agents_may_not:
  - substitute an easier box for a preregistered one
  - add a box after seeing a count
  - claim novelty for anything here, or use the reserved word
  - grade any of this above measured
```
