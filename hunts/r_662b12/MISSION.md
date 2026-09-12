# Hunt #72: AIMO Interpretability 2026 baseline reproduction and structure-matched robustness signal

Target repo: `teal-sea/zeta-lab` · Branch: `hunt/r-662b12`
Source: operator · Reference: `prize:aimo-interpretability-2026:baseline`
Task ID: `31e8a4f2-2c99-4bb6-953c-63f332cc07c4`

```huntspec
id: r_662b12
question: AIMO Interpretability 2026: reproduce the official baseline and test one structure-matched robustness signal
frontier: official all-False baseline accuracy 0.6786 (19/28), coverage 1.0, invalid 0 on pinned aimo-interp/val-sample
dead_routes:
  - unverified zero-shot assertions without running the official Codabench container or scoring interface
  - methods utilizing forbidden test-time labels or private case metadata
  - relying solely on raw forward passes exceeding compute and submission constraints
required_oracles:
  - official Codabench ingestion and scoring pipeline from aimo-interp/getting-started
  - exact public validation sample from aimo-interp/val-sample at pinned revision
kill_conditions:
  - the public validation dataset or official container cannot be retrieved and verified
  - the evaluated method requires forbidden labels or private metadata at test time
  - the intervention fails to achieve non-negative cross-validated delta over the all-False baseline
agents_may:
  - import
  - benchmark
  - cross_validate
  - analyze
  - evaluate
agents_may_not:
  - submit to Codabench
  - perform account actions
  - publish externally
  - declare theorem status
```

## Problem statement

LIVE PRIZE LANE, verified 2026-08-21. The official AIMO Interpretability Challenge runs through 2026-11-01 and offers ,500 across leaderboard and technical-report prizes. It explicitly values negative results and efficient methods.

First run requirements:
1. Pin `aimo-interp/getting-started` (commit `e46be92387081cfb8edf275e573fec7884eb9f32`).
2. Import the public `val-sample` dataset (`aimo-interp/val-sample`, revision `1ae454ec1fad9727084eda8f9f3c9ae2239b21de`).
3. Reproduce the official all-False baseline through the official `are_robust(model_id: str, problems: list[str]) -> list[bool]` interface.
4. Inventory the labels, model distributions, problem IDs, and perturbation types.
5. Specify and test one cheap signal derived from Zeta Lab's structure-matched-control practice.
6. Report exact reproduction commands, dataset counts, baseline accuracy/coverage/invalid_predictions, intervention's held-out or cross-validated delta, and a concrete go/no-go recommendation.
