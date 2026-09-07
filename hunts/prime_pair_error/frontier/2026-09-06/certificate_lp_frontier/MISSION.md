# Mission: the exact LP floor of the factorial-certificate route

**Question.** For support bound y and cutoff N, what is the smallest excess
B(N) - psi(N) any factorial certificate can have?  Every seed, lift, carry,
mask and repair construction in this hunt is a feasible point of one linear
program, so its optimum V*(y,N) is a hard floor for the whole family at that
(y,N).  We compute the floor and its scaling in y and N, and read the dual
solution to see where the freedom the constructions cannot use actually sits.

**May write:** this directory only.  **May not touch:** `zeta/`, `ontology/`,
`harness/`, or any earlier package in `frontier/2026-09-06/`.

**Grade of everything here:** measured (floating LP), with the primal
certificate re-verified cell by cell.  No enclosure, no asymptotic claim.
