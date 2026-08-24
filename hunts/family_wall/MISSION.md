# family_wall — where the n-point pressure family stops

The n-point pressure certificate family gives, for each n, the bound

    Phi_n(c, m, p) = (H - (n-1)(m-1)/(p m)) / (1 - c (m-(n-1))/m),
    H = 3/2 - (1/sqrt2) cot(1/sqrt2) = 0.6725007036794116,
    m capped at (n-1) + floor(1/c),

with c any uniform floor for F_{n-1} on nonnegative gap vectors. The formula is proved
for every n (`lean/bridge`, `n_point_bound`). The measured peaks climb: 0.6730297 at
n = 7, 0.6730537 at n = 8, 0.6730714 at n = 9. The configuration ceiling for anything
reading bandwidth-one data is 0.6818286874638.

This hunt asks, analytically, where that climb ends.

```huntspec
id: family_wall
question: Does the n-point pressure family converge to a limit strictly below the configuration ceiling 0.6818286874638, and to what value?
frontier: measured peaks 0.6730297 (n=7), 0.6730537 (n=8), 0.6730714 (n=9); configuration ceiling 0.6818286874638
proposed_attack: reduce Phi_n to H + H c - (n-1)/p, then bound c above by the value of the functional at explicit gap vectors of total length at most (n-1)/H, so that the pressure term cancels and the bound becomes H(1+W) with W an energy per point
dead_routes:
  - raising the pressure without limit; the floor decays and the bound returns to H
  - reading the peak off a fixed pressure grid; the true optimum sits between grid points, at a minimiser-family crossover
required_oracles:
  - direct multistart minimisation of the functional, run independently of the analytic prediction
  - the published n=7 arbitrary-precision floor 0.0038262312115073 at p=3000 as a control
  - exact Poisson-summation lattice sums, which terminate at a finite Fourier order
kill_conditions:
  - a gap vector is exhibited whose functional value at some pressure lies below the claimed floor by more than the stated numerical tolerance
  - the inequality chain fails on any row of the existing sweep
  - a direct minimisation returns a Phi_n above the barrier reported here
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```

## Files

- `RESULTS.md` — the bounded outcome, in one page.
- `FAMILY-LIMIT.md` — the analysis: the closed-form peak condition, the barrier, the limit.
- `modal_family_limit.py` — independent direct minimisation of the floor at larger n over
  a wide pressure range, on Modal.
- `chain_repair_check.py` — the case split that repairs the inequality chain, and the two
  counterexamples to the chain as originally written.
- `period37_check.py` — the period-37 all-n witness word, re-evaluated with this hunt's own
  `famlib` and at 60 digits.
- `f7_point_check.py` — where the 2.0e-13 in the n=7, p=3000 control comes from.
- `audit/` — an independent adversarial audit of the barrier claim by a different model,
  run in an isolated directory outside this repository. Brief, report, witnesses, scripts,
  and `PROVENANCE.md`.
- `artifacts/` — run output.

## A correction to the huntspec above

`required_oracles` names "the published n=7 arbitrary-precision floor `0.0038262312115073`
at p=3000". That figure is **not a floor**. As `hunts/ainta_seven_point/RESULTS.md` states
it correctly, it is the upper end of a bracket: an Arb evaluation of `F6` at an argmin
rounded to six decimals, hence an upper bound on the infimum. Two independent minimisations
— this hunt's Modal job and the audit's 80-digit Newton solve — come in `2.0e-13` below it,
which is the correct behaviour for a minimiser against an upper bound, not a discrepancy.
The huntspec block is left as pre-registered; `FAMILY-LIMIT.md` section 3 has the numbers.
