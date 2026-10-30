# MISSION: exact_gram/, the exact-Gram rebuild of ΔT at 280 modes, N = 32

Opened 2026-10-26 on branch `hunt/c4-exact-gram` (off `origin/main` at
558eee037) as a resumption of the C4 line in `hunts/weil_propagation/c4_s2/`,
under the owner's compute sweep of 2026-10-26 (dispatched by the Orca
coordinator, task `task_324ab6194f66`). No new hunt number: this is a dated
update inside the existing `weil_propagation` case-log entry (coordinator's
ruling, 2026-10-26).

**This mission inherits `hunts/weil_propagation/MISSION.md` and
`c4_s2/MISSION.md` in full** (rules, kill-controls, the reserved word, no
claim about RH, the operator's grading ruling on exact inertia) and does not
restate them. Every recorded result in `c4_s2/` stays as written; this folder
only adds.

## The question

Does the negative count n_−(R_S) = 4, 10, 20 at c = 2.9, N = 8, 16, 32
(`c4_s2/RESULTS.md` line 2) survive an actual error bound on ΔT, in place of
the response band (8.2e−3 to 3.0e−2 at N = 32) it is graded by now?

## Why this, why now

C4 (semilocal Sonin positivity at S = {∞, 2}) is the one mechanism in the
record whose information class every rival fails: Davenport-Heilbronn, both
discriminant −23 Epstein forms and W_a are refused by its (U-S) gate
(`checker/` s3). Its bounded-rank prediction is open because ΔT is known
only as a band. Two steps block a bound (`delta_t_bound/RESULTS.md`):
bound_quad/'s E2 (the projection taken in the s-truncated inner product,
‖X‖ ≥ 9.2e9 at N = 32, Prop 3), closable by recomputing ΔT with the exact
Gram in ball arithmetic (DERIVATION s2.8, route (ii), never run); and
bound_trunc/'s statement O (the Sonin overlap on the prolate tail). The
record called E2 a cost wall (about 200 core-hours, measured on a loaded
laptop at 2.2e−7 s per ball product). This folder re-prices it on the box,
fixes the reading before any rebuilt row exists, and asks for the compute.

## Inputs and their grades

| input | where | grade |
|---|---|---|
| stored R_S rows, counts 4, 10, 20 | checker/ s7.8, s7.9; snapshot digest b2e7787b | exact inertia of stored matrices (hardened); measured as a statement about R_S |
| E1, E6, E7 bounds; E2 obstruction (Prop 3) | bound_quad/ DERIVATION s2 | ordinary arguments, unreviewed |
| Identity A, Lemmas 1 to 3, Prop 4 | bound_trunc/ DERIVATION s2 | ordinary arguments; Lemma 1 passed referee/'s internal review |
| the decision scale 1.18e−2 | delta_t_bound/ RESULTS s5 (post-hoc there, labelled) | measured on stored rows |
| exact Gram well conditioned (G_z = I, cond(G_b) ≤ 34) | two_adic/ s10.1 | ordinary argument |

## Rivals and the gate

The (U-S) gate is fixed from the record and must still refuse, on every
code path this folder adds: Epstein (1,1,6) (n = 6 composite atom; n = 8,
s₃(2) = 6), W_a (a = 1/4) at n = 2, and DH. The rebuild reads only ζ's
data; any path that returns a trace term for W_a or Epstein data is a
defect (c4_s2 kill-control 2). The rebuild module will call
`two_adic`'s gate before building and a test will check that it refuses.

## Kill conditions (the result, either way)

- Under a closed E2 and a ΔT bound ε, the rigorous lower bounds
  C_N(ε) = n_−(R_center + εI) at c = 2.9 rise from N = 16 to N = 32 by at
  least 2 (assembler/'s successor rule): evidence against the bounded-rank
  prediction that no float band can give. The brief calls this a
  refutation; the operator's ruling (`c4_s2/MISSION.md`, ΔT-bound
  follow-up) governs: C4 fixes no rank bound, so no finite N refutes it, and
  the result rules out any remainder of rank below C_32(ε). Which wording is
  recorded is the owner's decision, not this folder's.
- Or C_32(ε) ≤ C_16(ε) + 1: the growth does not survive the bound, and the
  prediction stays alive (unresolved) at S = {∞, 2}.
- The rebuild itself is killed if a block fails its key, if its ball radius
  is not finite, or if a rebuilt row disagrees with the stored row by more
  than the stored row's band plus the rebuilt radius (a defect in one of
  the two routes, to be found before anything is counted).

## What this folder may write

Only `hunts/weil_propagation/c4_s2/exact_gram/` and a dated paragraph in the
`weil_propagation` entry of `hunts/README.md`. It reads checker/, two_adic/,
kernel/, bound_quad/, bound_trunc/ and assembler/ and imports from them
read-only. It never edits `zeta/`, `ontology/`, `harness/`, `lean/`,
`scripts/`, another hunt or another c4_s2 folder.

## Compute rules

The box rules of the dispatch: at most 4 processes, `nice -n 10`, wait while
the first field of /proc/loadavg exceeds 64, stop the newest job below
20 GiB MemAvailable, no file over 100 MB, under 300 MB added, large outputs
outside git and recorded by SHA-256. Every estimate goes in `RUNS.md` before
the spend; anything over one core-hour is asked of the coordinator first.
Production runs only under the guard of `guard.py` (PREREG s3).

```huntspec
id: c4_s2_exact_gram
question: Does the c = 2.9 negative count 4, 10, 20 of R_S at N = 8, 16, 32 survive an error bound on Delta_T, with E2 closed by the exact-Gram ball rebuild at 280 modes?
frontier: counts exact on stored float64 rows; Delta_T graded by a response band 8.2e-3 at N = 32, c = 2.9; no bound closes (E2 obstruction norm at least 9.2e9; statement O open); the 20 survives a uniform bound only below 1.18e-2
proposed_attack: rebuild Delta_T at (280, N = 8, 16, 32) with exact Gram matrices in python-flint balls, block by block under a fail-closed key, then count below minus the bound by exact inertia
dead_routes:
  - perturbation bound through the Gram pencil (bound_quad/ Prop 3, norm of X at least 70 at the best build)
  - bounding the two infinite traces of the mode truncation separately (bound_trunc/ Lemma 1)
  - the response band as a bound (checker/ s7, delta_t_bound/ outcome 4)
required_oracles:
  - exact rational inertia of the rebuilt centre matrix shifted by the bound
  - an independent second route: the stored float64 rows, which the rebuilt rows must match within band plus radius
  - the exact (U-S) gate refusing Epstein (1,1,6), W_a and DH
kill_conditions:
  - a block fails its key or carries a non-finite radius
  - a rebuilt row disagrees with its stored row by more than band plus radius
  - under a closed bound the N = 32 count exceeds the N = 16 count by at least 2 (recorded against bounded rank, graded by the operator's ruling)
  - under a closed bound the N = 32 count exceeds the N = 16 count by at most 1 (the growth does not survive)
agents_may:
  - derive
  - code
  - measure
  - attack
  - ask the coordinator for compute
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - run production before the pre-registration is committed and the compute is approved
  - edit any folder outside exact_gram/
```
