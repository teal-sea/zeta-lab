# Hunt R-2AC05F — adjudicate the two conflicting kappa = 2 coefficient tables

Two directories in this laboratory carry a table of the same quantity and
disagree from `i = 2` onward, with conflicting diagnoses of why:

* `hunts/higher_xi/C2_EXACT.json` (on `main`) — `C_{2,i} = 1, -8, 24, -32, 64/3, ...`
  Diagnosis: Bian's published row is wrong from `i = 2` because the weights
  `M(v_l) M(w_k)` are dropped between thesis p. 71 and eq (8.1).
* `hunts/rogue_frontier/fkappa/` (branch `hunts(rogue_frontier)` checkpoints,
  commit `360c545`) — corrected `C_{2,i} = 1, -4, 4, -16, 52/3, ...`
  Diagnosis: Bian's published row is right through `i = 4` and wrong from
  `i = 5` because of three implementation defects (a truncated assembly loop,
  phantom zero slots evaluated as nonzero, and an `alpha!` overcount in (6.18)).

Both cannot be right. The lab's record on `main` currently carries only the
first. This is a mathematical question and must not be settled by a merge
order or by whichever branch lands first.

```huntspec
id: r_2ac05f
question: Which of the two recorded kappa=2 form-factor coefficient tables, hunts/higher_xi/C2_EXACT.json or hunts/rogue_frontier/fkappa/coefficients.json (corrected mode), is the correct C_2,i?
frontier: the two tables agree only at i=1 (both 1); higher_xi gives C_2,2=-8 and fkappa gives C_2,2=-4, and they differ at every index from 2 to 11
proposed_attack: recompute the row from the analytic identity R_kappa = xi'/xi + D log Q_kappa in a formal Dirichlet word algebra written for this adjudication, importing neither disputant, and calibrate the one borrowed ingredient on the externally published kappa=1 row
dead_routes:
  - deciding by merge order or by which branch lands first
  - trusting Bian's Lemma 12 that C_kappa,2 is universal, which is the disputed assertion itself
  - using the kappa=1 row alone as the validation, which fkappa's own RESULTS.md section 5(a) already records as the reason none of its three defects was visible from the literature side
required_oracles:
  - the Farmer-Gonek closed form for the kappa=1 row, arXiv:0803.0425, as published
  - exact rational arithmetic in Python fractions, no floating point anywhere
  - fault injection against the probe's own controls
kill_conditions:
  - the independently written probe fails to reproduce the Farmer-Gonek kappa=1 row exactly at all eleven indices
  - the probe reproduces neither disputed table
  - the planted-defect check shows the kappa=1 control is blind to every plant, leaving the calibration unanchored
agents_may:
  - derive the R_kappa expansion and implement it
  - compare against both recorded tables and against the published Bian figure row
  - plant faults in the probe's own machinery to measure control power
  - record the outcome in harness/departments/review_ledger.py
agents_may_not:
  - edit either disputant's directory or files
  - assign a certainty rung to their own output beyond what the oracles support
  - use the reserved word for anything in this hunt
  - claim novelty; no literature search beyond the two sources already named was run
```

## Scope

Writes only inside `hunts/r_2ac05f/`, plus the two sanctioned exceptions:
one case-log entry in `hunts/README.md` and one appended `AttackOutcome` in
`harness/departments/review_ledger.py`.

Nothing in this hunt is evidence for or against the Riemann hypothesis
(`docs/08`).
