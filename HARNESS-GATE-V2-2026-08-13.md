# Harness gate test v2 — frozen protocol

**Status at this commit: pre-registration. No arm has run. No result exists.**
Claims and key are held outside the repository during execution, as in v1; only
their digest is frozen here.

## Why there is a v2

v1 (`HARNESS-GATE-2026-08-13.md`) returned **FAIL on a ceiling**: the control arm
answered 12/12, which forces `b = 0` and makes the criterion unreachable by any
treatment performance. That was a defect of the claim set, not of the harness and
not of the criterion. v2 replaces the claim set and changes nothing else.

**The v1 result stands as recorded.** It is not retracted, reinterpreted, or
merged into this one. This is a second experiment with its own pre-registration,
because re-running a benchmark after seeing its result, against the same frozen
criterion, is only legitimate if the change is declared in advance and the prior
result is left standing.

## What is unchanged from v1

The question, the arms, the blinding, the output contract, the failure handling,
the scope limits, and — critically — **the criterion**:

- **b** = claims where Arm B (harness) is correct and Arm A (control) is wrong
- **c** = claims where Arm A is correct and Arm B is wrong

> ## GATE PASSES if and only if **b − c ≥ 3**.
> ## Any other outcome, including a ceiling, is a FAIL.

The threshold is held at 3 rather than rescaled to the larger claim set, so v2 is
not easier to pass than v1 was.

## What changed: the claim set

**14 claims** (v1 had 12), balance as enumerated **6 SOUND / 8 DEFECTIVE**, over
the same subject and the same 2024 window.

Claims were selected a priori from classes where **a plausible check confirms and
a boundary case refutes**:

| Trap class | Example behaviour it exploits |
|---|---|
| step values reset per field period | `*/7` in day-of-month gives a 3-day gap across a month boundary |
| the union default is suppressed by `#`/`W` | `0 0 15W * 5` is *not* the union of Fridays and 15W unless `day_or_union=True` |
| an alias that does not apply in every form | DOW `7 → 0` holds in 5-field cron and **not** in the 6-field seconds form |
| one form clamps where a neighbouring form does not | `31W` clamps to Feb 29; bare `31` simply does not fire |
| iterator endpoint conventions | `get_prev()` from exactly on a firing instant, `croniter_range` endpoint inclusivity |

**Difficulty was chosen from those classes in advance. Candidate claims were NOT
tried against the control arm and kept if it failed** — that would be selection
on outcome, and it would manufacture the effect the experiment is supposed to
measure. The consequence is accepted honestly: v2 may hit a ceiling again, and if
it does, that is another FAIL.

Ground truth remains exhaustive enumeration by a script frozen with the claims
(`gate2/build_claims.py`), never the harness's own `distinguishes` criterion.

**Frozen digest** of `claims.json` + `key.json`:

```
0cc1d5a0e3f6fc9146954717ac2332fa90d85e44c854e2bd276b51a1f3bb22bc
```

## Budget measurement, corrected

v1 §4.1 assumed token counts were unavailable. They are not: the subagent
completion record reports per-run tokens, and v1 used them. v2 records tokens,
wall-clock and tool uses per run from the outset. The gate criterion depends on
none of them.

## Execution order

Both arms run over all 14 claims; 28 runs. Arm A and Arm B are launched in mixed
batches so neither arm systematically runs under different system load.

---

**Freeze.** This commit contains this protocol and nothing else. Claims, key,
runner and results follow in a later commit and must hash to the digest above.
