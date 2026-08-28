# Harness gate v4 — cheap binary screen

**Frozen before any run. 6 items, 12 runs. One question, yes or no.**

> Does the harness improve the correctness of research-claim evaluation?

Not how much, not which part. If this passes, characterization is worth paying
for. If it fails, it isn't.

## Why this department, measured

v1/v2 died on **no headroom**, v3 on **no positive class**. Both were properties
of `frozen_croniter`, not of the harness. Elimination over the six registered
departments:

- `zeta`, `finitefield`, `stateval` — `ModuleNotFoundError: numpy`. Cannot
  execute in this container at all.
- `croniter` — control scored 25/25 across v1+v2. Cheap oracle, measured dead.
- `referee` — its subject *is* the verification machinery. Circular.
- `compiler` — the remainder, and it passes the two tests the others failed.

The decisive measurement, both axes complete enumerations of all 65536 i8 points:

```
                                   concrete   refines
mul2->shl, +2 commutativity     65536/65536      True     <- positive class exists
shl nsw / add nuw / udiv exact  65536/65536     False     <- 32768, 32512, 49152 poison
sdiv2->ashr, udiv4->ashr          DISAGREES     False
```

**Six rewrites where the strongest concrete evidence obtainable — every one of
65536 inputs, two optimisation levels, byte-identical — is achieved and the
transformation is still invalid.** Running the artifact cannot settle it. That is
the headroom v1 and v2 never had, and it is measured.

Ground truth is `compiler.semantics.refinement`, exhaustive over the whole
domain. v3's key came from 21 mutation operators I thought of and all six of its
positive items were refuted; this cannot be too narrow by construction.

## Items

6 items, **3 VALID / 3 INVALID**, every one carrying identical perfect concrete
evidence — so the evidence text cannot predict the answer.

Digest of `items.json` + `key.json`:

```
29146596f23bd8320645fd9133260096372dd84b260cc3acc69e92f2c5af7b96
```

## Arms and scoring

Same model, same task, one difference: Arm A is barred from `harness/`; Arm B is
told to route through it. `compiler/` is the subject package and both arms have
identical access to it; neither is told what is in it.

`INVALID` requires a concrete `(x, y)` witness, verified mechanically against the
model — source defined there, target poison or UB. A missing or wrong witness
scores incorrect, so no arm can win by answering `INVALID` to everything. The
3/3 balance is the other half of that guard.

## Criterion

- **b** = items where Arm B is correct and Arm A is wrong
- **c** = items where Arm A is correct and Arm B is wrong

> ## PASS iff **b − c ≥ 2**. Anything else, including a ceiling, is a FAIL.

Threshold 2 rather than 3 because this is a 6-item screen, not a measurement of
size. A PASS means only "an effect exists, go measure it properly".

## Declared confound

`harness/departments/compiler_department.py` ships `model_detector`, which is the
adequate instrument. So Arm B is pointed at the right tool while Arm A must find
it. A PASS therefore cannot separate "the harness supplied the instrument" from
"the harness instilled the habit of asking whether the instrument is adequate".
Stated here, before the run, not in the results.

---

# RESULTS

Executed 2026-08-13 after the protocol above was committed at `0518847`.
`items.json` + `key.json` still hash to `29146596f23bd8320645fd9133260096372dd84b260cc3acc69e92f2c5af7b96`.
12 runs, 6 items × 2 arms, all completed, every verdict parseable.

```
paired items            : 6
Arm A correct (control) : 6/6
Arm B correct (harness) : 6/6
b (B right, A wrong)    : 0
c (A right, B wrong)    : 0
b - c                   : 0

CRITERION (frozen): b - c >= 2
OBSERVED         : b - c = 0
```

> ## GATE: **FAIL**

| | I1 | I2 | I3 | I4 | I5 | I6 |
|---|---|---|---|---|---|---|
| truth | VALID | VALID | VALID | INVALID | INVALID | INVALID |
| Arm A | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Arm B | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

Zero discordant pairs. Both arms produced identical witnesses on all three
invalid items: `f(-128,-128)`, `f(-127,-2)`, `f(1,0)`.

## This one is not a broken experiment

The venue passed both tests that killed the earlier attempts, measured before
the run: three rewrites are genuinely valid (positive class) and three achieve
byte-identical output on all 65536 inputs at two optimisation levels while being
invalid (headroom). Running the artifact provably cannot settle it.

**The control settled it anyway, on all three traps, unaided.** It identified the
poison class from the IR by reading the flags, and named the reason the supplied
evidence was worthless — one run: *"65536/65536 agreement at -O0 and -O2 is
exactly what an `nsw` violation looks like when observed by execution."* Two
control runs went further and found `compiler/semantics.py refinement()`
themselves. That module is the **subject** package, left open to both arms
deliberately so that ground truth was not something only the treatment could
reach; the control went and got it.

## Disclosed defect in the item set

**I3's source and target are byte-identical.** The intended commutativity edit
was a no-op because that fixture names the register `%m`, not `%d`. Both arms
scored it free, so it could never be discordant. Effective n = 5. The ceiling
holds on the other five, so the verdict does not depend on it. Recorded rather
than swapped, because the items were frozen before the run.

## Cost

| Resource | Arm A (control) | Arm B (harness) | ratio |
|---|---|---|---|
| tokens, total | 238,368 | 398,398 | 1.67× |
| tokens, median per run | 38,899 | 67,450 | 1.73× |
| wall-clock, median per run | 42 s | 165 s | **3.93×** |
| wall-clock, total | 263 s | 1,038 s | 3.95× |
| tool uses, median per run | 4 | 20 | **5.00×** |

Third independent replication of the same cost shape (v1 3.2×/3.4×, v2
2.7×/2.4× wall-clock and tool uses). For identical correctness the harness arm
costs roughly 3–4× the wall-clock and 5× the tool activity.

## What the harness did that the score cannot see

Recorded because it is true, not to soften the verdict — it changed no answer.

Every Arm B run surfaced the department's integrity grade
**`DETECTOR_INADEQUATE`** and carried it with the verdict, and every one reported
that `concrete_exhaustive_i8` has `has_power=False`,
`blind_to=('nsw_flag_on_a_wrapping_shift',)` — i.e. the arm was told, by
measurement, that the evidence in its prompt was the department's known blind
spot. On I5 the arm declined to stop at the model's verdict *because* of that
grade, embedded the rewrite in a consumer, and got independent confirmation from
real LLVM: `opt -passes=instcombine` folds the `nuw` version to `ret i1 false`
while the source version stays live; compiled and run, `g(-127,-2)` returns 0
with the flag and 1 without.

That is a second, independent line of evidence the control never produced. The
gate measures verdict correctness, and on verdict correctness it bought nothing.

## Verdict on the question

> Does the harness improve the correctness of research-claim evaluation?

**Not demonstrated, in any venue tested.** Four experiments, two subjects,
n = 12 + 13 + 12 + 6 scored runs. Control accuracy: 12/12, 13/13, 6/6 on
surviving items, 6/6. The unaided control has never once been wrong.

What this does and does not license:

- It **does not** show the harness is useless. It shows no *correctness*
  headroom was found in any domain that runs in this container, and its
  contributions here were to evidence quality and declared scope, which this
  gate does not score.
- It **does** stand as a fourth pre-registered FAIL, with the criterion held at
  the same shape throughout and never reinterpreted after the fact.
- The cost finding is now replicated three times and is the most robust thing
  these four experiments produced: **3–5× the effort for the same answers.**

Anyone arguing the harness earns its complexity needs an outcome variable other
than verdict correctness, and a domain where the control is not already at
ceiling. Neither has been found in four attempts.
