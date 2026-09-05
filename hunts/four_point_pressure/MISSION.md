# Four-point pressure tuning

The operator requested a stronger mathematical result on 2026-09-05. This hunt
reuses the exact interval machinery from `ainta_seven_point/four_point_gen.py`
and varies the pressure as well as the floor. It writes only in this isolated
worktree and this hunt until a candidate has passed the arithmetic preflight.
The upstream four-point development remains unchanged during exploration.

```huntspec
id: four_point_pressure
question: Can joint pressure and floor tuning improve the unconditional four-point bound with a comparable rational proof tree?
frontier: proved Phi4 = 0.67284701976668882760 at c=2310/1000000 and p=2500; measured n=4 envelope around 0.6728744
proposed_attack: enumerate rational pressure-floor pairs and exact proof trees, then emit and kernel-check the best affordable candidate
dead_routes:
  - merely raising c at p=2500 gives rapidly growing proof trees, already measured in FOUR-POINT.md
  - treating the numerical infimum as a global lower bound
required_oracles:
  - exact rational interval arithmetic matching the existing cell lemmas
  - the generated Lean arithmetic preflight
  - Lean 4 kernel on the complete generated proof with no sorry
kill_conditions:
  - the exact tree fails to cover every box below its pressure cutoff
  - an independent numerical evaluation contradicts any interval lower bound
  - the complete Lean build fails or retains a hypothesis for its finite certificate
agents_may:
  - tune the pressure and floor
  - measure proof tree size
  - generate a proof candidate in the isolated worktree
agents_may_not:
  - claim theorem status before the kernel build passes
  - claim novelty without a primary-source comparison
  - overwrite another session's work
```

Compute: first measurement is one exact tree on one VM core, limited to two
minutes. No new paid-service job is launched for this measurement. Subsequent
tree probes use the measured time as their estimate. The existing four-point
CI proof measured 3h18m30s; a stronger candidate is not promised that latency.
