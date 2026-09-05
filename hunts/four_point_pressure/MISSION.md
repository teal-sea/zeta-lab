# Four-point pressure tuning: closed exploratory record

This directory preserves the arithmetic and terminal verification status of
the 2026-09-05 experiment. Its generated Lean candidate remains on the
separate `codex/zeta-win-20260905` branch at
`d28df5f992479cd32751cb90c8c88551550582a3`. This publication does not import it
into the main proof development or change the registered constant.

```huntspec
id: four_point_pressure
question: Can joint pressure and floor tuning improve the four-point bound with a manageable exact proof tree?
frontier: registered Phi4 is 0.67284701976668882760; a stronger candidate was emitted but its complete Lean check was canceled
proposed_attack: preserve the exact arithmetic, emitted-source preflight, and canceled run as distinct stages
dead_routes:
  - treating a numerical infimum as a uniform lower bound
  - treating exact search-tree closure or source preflight as a completed Lean proof
required_oracles:
  - exact rational arithmetic for the parameter substitution
  - emitted-source arithmetic preflight
  - Lean 4 kernel for any claimed new theorem
kill_conditions:
  - the exact formula differs from the generic bridge after substitution
  - the preflight reports an uncovered or invalid interval cell
  - a claimed completed proof lacks a successful complete kernel build
agents_may:
  - reproduce the arithmetic and existing source preflight
  - record the completed and incomplete checks separately
agents_may_not:
  - promote the canceled candidate to theorem status
  - replace the registered constant
  - resume the expensive candidate build as part of this archival publication
```

The original exploratory contract and generated source are retained in the
[candidate commit](https://github.com/teal-sea/zeta-lab/commit/d28df5f992479cd32751cb90c8c88551550582a3).
The final outcome and reproduction commands are in [RUNS.md](RUNS.md).
