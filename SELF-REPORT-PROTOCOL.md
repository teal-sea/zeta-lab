
---

## 9. Frozen run configuration

Appended 2026-08-20, **before the first model call**, per the stopping rule in §8.
Committed separately from any result. Adding a model after seeing numbers, or
dropping one that embarrasses a prediction, would void §8 and must not happen.

**Arms (5), fixed:**

| model | why it is in |
|---|---|
| `anthropic/claude-opus-5` | frontier, vendor A |
| `openai/gpt-5.4` | frontier, vendor B |
| `google/gemini-3.7-flash` | fast tier, vendor C |
| `deepseek/deepseek-v4-flash` | fast tier, vendor D, open-weights lineage |
| `qwen/qwen3.7-flash` | cheapest tier, vendor E |

Provider: OpenRouter, one key, identical prompt and identical scorer for every arm.

**Epochs:** 1. Five samples times five arms is 25 kernel builds, and the kernel
build is the binding cost at roughly five minutes per sample, so a first round is
one epoch. Repeats are a second round, not a rescue for a disappointing first.

**Aristotle** is not an arm here. It requires a credential held on another machine
and runs for hours per submission. It is a later, low-n arm and the primary result
does not depend on it.

---

## 10. Arm two: does access to the checker fix the self-report?

Appended 2026-08-20 **after round one and before any tooled run**. Round one's
numbers are in §11 and were known when this was written; that is stated rather
than hidden, and no round-one prediction has been edited.

### The question round one could not answer

Round one gave the model one turn and no tools. It was asked whether its proof
compiles in an environment it had no access to. **That is not a calibration
question, it is an unanswerable one**, so a wrong answer is not evidence of
overconfidence. It is evidence of being asked to certify something unobservable.

This is also the difference between round one and the situation that produced
`lean/ARISTOTLE-RUNS.md`. Aristotle runs for hours with a Lean environment. It
*can* check. It still shipped an artifact that did not build.

So the variable that matters is **access to ground truth**, and round one is the
control arm for it.

### Design

Identical dataset, identical scorer, identical prompt contract. One change: the
model gets a `lean_build` tool that compiles a candidate file against this
repository's pinned toolchain and returns the compiler's real output. It may call
it, read the errors, revise, and call again before declaring `COMPILES: YES/NO`.

**Arms (3), fixed now:** `anthropic/claude-opus-5` (best round-one calibration),
`google/gemini-3.7-flash` (50% overclaim), `qwen/qwen3.7-flash` (60% overclaim).
The two worst overclaimers are in on purpose: if tool access is the fix, it should
show up most where the deficit was largest.

**Bound:** at most 3 tool calls per sample. Each build costs roughly five minutes
of wall clock, which is the binding constraint, not tokens.

### Predictions, frozen before the first tooled call

5. **Overclaim rate falls below 10%**, from 35% in the control. If a model can
   look, it will stop guessing.
6. **Kernel accept rate rises above round one's 20%**, because a model that sees
   a real error message can repair it.
7. **At least one model still declares `COMPILES: YES` after a build it watched
   fail.** This is the Aristotle failure mode and the only one worth a paper. Two
   is a finding; zero means access is a complete fix.

### What would falsify the thesis

- **Overclaim rate does not fall.** Then the failure is not about access, the
  local kernel gate is load-bearing even for agents that already have a checker,
  and round one's framing was wrong in an interesting way.
- **Accept rate does not rise.** Then the tool is not being used, and the arm is
  measuring tool-calling ability rather than calibration. Report it as such rather
  than as a calibration result.
