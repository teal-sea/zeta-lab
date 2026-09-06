# Hunt R-6F0F63: the ceiling of the Delsarte LP for kissing numbers

Fourth instance of the lab's ceiling procedure (issue
[#110](https://github.com/teal-sea/zeta-lab/issues/110)): reproduce a published
certificate, read its verifier for soundness, measure where the method's own
ceiling is, then push the method to that ceiling. The first three instances were
simple zeros (Hunt #79), the Davenport-Heilbronn line, and Bloch's constant.

The object here is the **Delsarte / Odlyzko-Sloane linear programming bound for
kissing numbers**, the LP half of the LP/SDP family the issue names. The
certificate is one univariate polynomial

    f(t) = sum_{k=0}^{d} f_k G_k^{(n)}(t),   G_k^{(n)}(1) = 1

satisfying (P1) f_0 > 0, (P2) f_k >= 0 for k >= 1, (P3) f(t) <= 0 on
[-1, 1/2]; the conclusion is tau_n <= f(1)/f_0.

**Scope.** The LP half only. The Cohn-Elkies semidefinite side (sphere packing
density in R^n) was not attempted at this budget, and this hunt makes no claim
about it. Nothing here proves any new packing or kissing bound, and no claim of
novelty is made for anything in the family: the values reproduced are
literature. The deliverable is the ceiling of the parameterisation and the
soundness read of the acceptance step. Everything is float grade.

Nothing in this hunt is evidence for or against RH (`docs/08`).

```huntspec
id: r_6f0f63
question: Where is the ceiling of the Delsarte LP parameterisation for kissing numbers, and is the acceptance step of the standard node-discretised implementation sound?
frontier: tau_8 = 240 and tau_24 = 196560 are exactly attained by the LP (degree 6 and degree 10 certificates); for other n the LP value is strictly above the best known configuration and the free parameters are the degree d and the node count m
proposed_attack: rebuild the two exact certificates from their contact structure, then sweep d and m independently while checking (P2) and (P3) on the interval rather than on the LP's own node set
dead_routes:
  - trusting the LP optimum on a node grid as a bound; the discretisation is a relaxation and the optimum sits below the truth at every node count tested up to 40000
  - reading the sup of f from the LP node set itself; the node set cannot audit the discretisation that produced it
required_oracles:
  - the exact kissing numbers of E8 and the Leech lattice, 240 and 196560, which the LP attains with equality
  - Chebyshev interpolation plus companion-matrix root finding of f', independent of the LP node set
  - a planted-fault ladder that must fire before any no-violation verdict is reported
kill_conditions:
  - the planted-fault ladder fails to fire, in which case no number in results.json is reported as verified
  - the rebuilt certificates do not reproduce 240 and 196560, in which case the reproduction step failed and the ceiling sweep is not run
  - the repaired value falls below the exact kissing number in dimension 8 or 24, which would mean the repair is unsound
agents_may:
  - solve the linear programs and sweep their free parameters
  - rebuild published certificates from their stated contact structure
  - verify sign conditions off the LP node set and report the repaired value
agents_may_not:
  - report a node-set LP optimum as a bound
  - claim any value here is new, or that any of it bears on RH
  - use the reserved word that belongs to zeta/rigor.py and the Lean arm
```
