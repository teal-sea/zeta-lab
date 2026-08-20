
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
