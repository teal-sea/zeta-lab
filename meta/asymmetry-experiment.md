# Independent vs shared verification — an experiment design

*Pre-registration draft, 2026-08-10. Nothing here has been run. Predictions are
stated before any data exists, and the whole point of writing them down now is
that they can embarrass me later.*

## The observation that prompted it

Across this repository, checks sort cleanly by whether they were **independent of**
the artifact they check:

| check | independent | deterministic | cheap | caught real defects |
|---|---|---|---|---|
| Lean kernel | yes | yes | no | yes |
| `Fraction` mirror vs the rung-3 plan | yes | yes | yes | yes, decisively |
| Arb vs mpmath cross-check | yes | yes | no | yes |
| outside model reading the public repo | yes | **no** | yes | yes |
| integrity audit vs batteries | **no** | yes | yes | 2 of 6 |
| promotion gate vs claim reports | **no** | yes | yes | no — loses to its null control |

## Why the observation is not yet a result

**Three variables are confounded.** Independence, determinism and cheapness
co-vary across every row above, so the table cannot distinguish:

- *independence* doing the work (co-designed checkers share the author's blind
  spots);
- *determinism* doing the work (the kernel and the mirror cannot be talked into
  agreeing);
- *cheapness* doing the work (cheap checks get run before commitment, when
  disagreement is still free to act on).

There is also a fourth candidate nobody has controlled for: the co-designed
checks in this tree may simply be **weaker artifacts**, built later and with less
care, and the asymmetry may be about effort rather than architecture.

Until those are separated, "independent verification beats shared verification" is
a hunch with a suggestive table under it. This design separates them.

## Design

A factorial over three factors, with planted faults, blind authorship, and one
arena outside mathematics.

**Factor A — relationship to the artifact.** *Independent*: the checker's author
never saw the artifact or its author's reasoning. *Co-designed*: checker and
artifact authored by the same process, as `harness/integrity.py` was against the
batteries it audits.

**Factor B — decision procedure.** *Deterministic*: a program with no model in the
loop at check time (kernel, mirror, compile-and-run). *Probabilistic*: a model
asked to find the defect.

**Factor C — cost.** *Cheap*: runnable in seconds, before commitment.
*Expensive*: minutes to hours, run once at the end.

Eight cells; six are populatable now. (Independent + probabilistic + expensive and
co-designed + probabilistic + expensive can be dropped in round one.)

**Arenas.** Two, deliberately:

1. **Mathematics** — interval-arithmetic claims, where a cheap exact independent
   oracle is available (the `Fraction` mirror pattern) and an expensive one is too
   (the Lean kernel).
2. **Programs** — the `compiler/` department's LLVM IR rewrites, which already has
   an executable oracle (compile and run) and a foreign vocabulary. Chosen because
   it breaks any explanation that depends on the subject being mathematics.

**Faults.** Planted, from three sources so that no single author's imagination
bounds the fault space: the existing `SHAM_MODES` catalog, `compiler/FINDINGS.md`'s
recorded incidents, and faults authored by a party who sees no checker.

**Blinding, and how it is enforced rather than declared.** Fault authors and
checker authors exchange only SHA-256 digests of their bundles before reveal, per
the procedure already specified in the E1–E3 logistics. `harness/preregistration.py`
records the digests of evidence existing at freeze time, so independence is
*derived from artifacts* rather than asserted in a README. That mechanism is the
reason this experiment is worth running here rather than anywhere else.

## Measurements

Five, and the fifth is the one nobody currently takes.

1. **Defect detection rate** — planted faults found / planted.
2. **False confidence rate** — artifacts containing a planted fault that the
   checker grades sound. This is the quantity that matters for deployment, and it
   is not one minus detection: a checker may refuse everything and have zero false
   confidence while being useless.
3. **Specificity** — clean artifacts graded unsound. Without it, a checker that
   always says "no" scores perfectly on 1 and 2. This is the repo's own admission
   rule applied to the experiment.
4. **Cost** — wall-clock and tokens per artifact.
5. **Independence, measured as conditional detection lift.** For checkers A and B:
   does B catch A's misses at more than B's own base rate? If yes they are
   genuinely independent; if B misses precisely what A misses, they share a blind
   spot regardless of who authored them. **This repository currently asserts
   independence and has never measured it**, and this quantity is the closest
   thing to a definition.

## Pre-registered predictions

Frozen before any data. Ordered from the one I most expect to survive to the one
I expect to be wrong.

- **P1 (independence).** At matched cost and decision procedure, independent
  checkers have a lower *false confidence* rate than co-designed ones. Effect
  expected to be large — the blind-authoring result is 4 of 6 hollow batteries
  surviving a co-designed audit.
- **P2 (shared blind spots).** Conditional detection lift between two co-designed
  checkers is near zero, and between two independent checkers is clearly positive.
  This is P1's mechanism, and it is the more informative measurement.
- **P3 (determinism).** Within independent checkers, deterministic ones have lower
  *variance* in detection across runs, but **not necessarily higher mean
  detection**. The outside model that found the `rigor.py` cache defect was
  probabilistic and found what 2135 deterministic tests missed, so I expect
  probabilistic independent checkers to win on *coverage* and lose on
  *reproducibility*.
- **P4 (cheapness acts through frequency, not power).** This is the prediction I
  most want tested, because it corrects my own earlier claim. I asserted that
  *cheap* independent checks work better. The honest mechanism is probably that
  cheap checks get **invoked**, and invocation is what produces detections. The
  rung-3 case is the evidence: the generator's feasibility assert was cheap,
  correct, and present for the entire period during which the plan was described
  as nearly complete — because nobody ran it. Prediction: cost has **no
  significant direct effect** on detection rate at matched independence, and a
  large effect on how often the check is run in practice.
- **P5 (effort confound).** Co-designed checkers in this tree underperform partly
  because they are weaker artifacts, not only because they are co-designed. I
  expect this to account for some of the gap, and the design controls it by
  matching author effort per checker.

**If P1 fails** — co-designed checkers detect and mis-certify at the same rates as
independent ones — the asymmetry was an artifact of this repository's particular
audit being weak, hypothesis C on the futures map loses its evidence, and the
"instrument and benchmark" hypothesis loses its most interesting content. That is
the outcome to hope for in the sense that matters: it is the one that would teach
us the most about how wrong we were.

## Cost and cheapest first step

The full factorial is weeks. The cheapest informative slice is **days** and does
not need the factorial:

> Take the four hollow batteries that survive the current audit. Have an
> **independent** party — a model that has seen neither the audit nor the
> batteries' authors' reasoning — attempt to identify which of six batteries
> measure nothing. Compare its detection rate against the audit's 2 of 6.

One number, one afternoon, and it discriminates P1 immediately. If the
independent party also gets 2 of 6, independence is not the variable and this
whole design is premature.

## Relationship to the rest of the tree

This is meta-research, so it lives here rather than in `docs/`. It borrows the
zeta department's and compiler department's batteries as arenas; per
`harness/README.md`'s rule, borrowing another department's battery means this is
not a department and cannot become one by growing. Results, when they exist, get a
`docs/` number and a case-log-style disposition — including if the answer is that
the asymmetry does not exist.

---

## Addendum, 2026-08-20: a runner exists; nothing has been run

Added after the freeze above. **It changes no prediction and no design**; the
predictions P1 to P5 stand exactly as written, and this section is separated
because editing a preregistration's frozen content would destroy the only thing
that makes it worth having.

`meta/evals/asymmetry.py` implements E0, the "cheapest first step" named above,
as an Inspect (`inspect_ai`) task. What it supplies is the part this repository
did not have: a model in the loop at check time, per artifact cost accounting,
and a log a stranger can audit.

The dataset is real rather than illustrative. Each artifact is a live
department with one corruption planted by the matching mutator in
`harness/shams.py`, plus one clean control, and each artifact's ground truth is
read from `harness.integrity.SHAM_MODES` rather than restated. Nine of the
fifteen catalogued sham modes can currently be planted; three of those nine are
modes the audit declares itself blind to, which is what makes E0 informative at
all.

Two things worth recording because they were found rather than anticipated.
First, the artifact digests the design asks for as a blinding mechanism earned
their keep before any run: six of nine corrupted artifacts initially hashed
identical to the clean control, because the renderer showing the battery to a
checker truncated above the depth the payloads live at. That eval would have
measured nothing while reporting numbers, which is the precise hollowness this
experiment studies. Second, Inspect coerces a string score value to a float
before metrics see it, so a metric written the obvious way reads zero for every
sample. Both are pinned in `tests/test_meta_evals.py`.

Measurement 5, conditional detection lift, is not covered: it compares two
checkers and needs two arms, so it stays with E1.

**Status: not run.** Executing E0 requires choosing a model, recording the
sample digests, and writing the disposition up with a `docs/` number, including
if the answer is that the asymmetry does not exist.
