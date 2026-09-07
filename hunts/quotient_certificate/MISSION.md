# Mission: positivity on attainable quotient cells

Continue the factorial-certificate investigation from main `d393e1a`.
The previous LP imposes positivity at every integer cell through N, although
its prime sum evaluates the certificate only at floor(N/d). Test the smaller
constraint set of all attainable integer quotients, without using prime
locations to choose the constraints. Audit the claimed asymptotic barriers
separately from these finite measurements.

Scope: this directory, its regression test, its hunts/README.md case-log
entry, regenerated CONTEXT.md, and a dated correction pointer at the top of
the earlier LP results. Earlier recorded text remains intact. No
core-package changes.
Every numerical optimization is a measured finite result. No claim about RH
or novelty follows from a successful finite optimization.

```huntspec
id: quotient_certificate
question: How much excess does positivity on unattainable cells force in the finite factorial-certificate LP?
frontier: The all-cell LP has measured excess 62.923 at N=1000,y=31 and 323.65 at N=10000,y=100; its proposed N/sqrt(y) lower bound is unproved
proposed_attack: Impose positivity at every attainable quotient floor(N/d), derive validity without prime locations, and compare with the all-cell and prime-cell LPs
dead_routes:
  - treating three fitted cutoff values or a Gaussian heuristic as an asymptotic obstruction
  - treating exact evaluation through prime-counting data as an independent estimate
required_oracles:
  - direct enumeration of all integer quotients
  - exact rational evaluation of candidate floor-sum inequalities
  - independently factored von Mangoldt sums and high-precision logarithms
  - primary literature for statements about RH and approximation rates
kill_conditions:
  - any attained quotient violates the proposed ceiling
  - direct weighted excess disagrees with the factorial objective
  - a claimed improvement disappears after exact feasibility repair
agents_may:
  - derive
  - measure
  - search
  - attack
agents_may_not:
  - declare novelty
  - promote an asymptotic conclusion from finite fits
  - modify earlier research records
```
