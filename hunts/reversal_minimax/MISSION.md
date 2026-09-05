# Reversal and finite adversaries for pressure certificates

Opened 2026-09-04 at repository commit
`6a9aa8fd4074ea23868c1c547168c0c773185781` following the operator's request
for a whole-laboratory structural research experiment.

Scope: this directory, one classification entry in `hunts/README.md`, and
regeneration of the generated context if needed. Other hunts are inputs only.
No publication, deployment, upstream messages, or promotion of a zeta bound.
The user authorized Modal execution for Lean checks. No other remote compute
is needed for this experiment.

```huntspec
id: reversal_minimax
question: Can reversal symmetry and a finite mixed adversary disprove the recorded pressure optimum and remove an unnecessary search dimension?
frontier: amtopa_ceiling reports epsilon star in [0.007916857810, 0.007916857812] at the fixed 17-term window and B = 93/23000
proposed_attack: close the saved cut pool under reversal, extract a rational probability measure, and verify its universal upper bound with ball arithmetic independently of the optimizer
dead_routes:
  - the uncapped total-energy Gram profile is already in the competitor record
  - a multistart minimum is not a global lower bound
  - changing the fundamental frequency cannot improve the already sharp ambient Montgomery-Taylor Rayleigh quotient
required_oracles:
  - exact rational probability and budget arithmetic
  - independent direct quadrature of the window transform
  - Arb evaluation of the finite adversary with outward bounds
  - Lean kernel for the abstract symmetry and finite-adversary deductions
kill_conditions:
  - reversal changes the feasible coefficient polytope or the gap domain
  - the interval upper bound fails to lie below the reported lower endpoint
  - independent quadrature disagrees with the closed-form evaluator
  - any claimed new theorem is already a standard averaging argument
agents_may:
  - inspect repository mathematics and primary literature
  - derive and attack inequalities
  - run small local numerical probes
  - prepare and remotely check Lean proofs
  - record a negative result with its exact scope
agents_may_not:
  - claim a new lower bound for the proportion of simple zeros
  - claim novelty for group averaging or linear programming duality
  - alter the historical evidence in another hunt
  - publish or deploy
```

The last kill condition applies to novelty, not to the usefulness of a concrete
countercertificate. A previously unrecorded refutation can survive even when
the argument that finds it is classical.
