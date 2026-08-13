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
