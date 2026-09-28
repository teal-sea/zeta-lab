# Mission: exact finite paid-surplus feasibility

Base: `fd04f1fac9d48a4d769048817e678acdea3b4bdb`.
Read-only predecessor: `af13799d3034b4d6a07e76c0d6a409dc7421f056`.
This mission implements the coordinator's focused selection packet, after
acceptance of the claims map and independent review of paid-cap saturation.

At the single cutoff `N=144`, allow rational coefficients `c_1,...,c_12`,
zero outside that support, satisfying

- harmonic balance: `sum_{j=1}^{12} c_j/j = 0`;
- exact prefix coverage: `sum_{j=1}^{12} c_j floor(q/j) = 1` for `1<=q<=5`;
- coefficient mass: `sum_{j=1}^{12}|c_j| <= 23`.

There are no further sign conditions. In particular coverage forces `c_1=1`.
This rational polytope contains every balanced Mobius prefix of cutoff
`6<=h<=12`, and allows choices outside their convex hull. The coverage range
and mass ceiling are inherited from the existing prefix construction.

The one question is whether this class contains a vector satisfying
`W_d=sum_j c_j floor(144/(dj))<=1` for every prime power `2<=d<=144`.
If yes, exhibit exact coefficients and price `B-144`, `P_Lambda`, and
`C-144` separately, where `B=sum_d Lambda(d)W_d`,
`P_Lambda=sum_d Lambda(d)(1-W_d)_+`, and
`C=B+P_Lambda=psi(144)+sum_d Lambda(d)(W_d-1)_+`.
If no, exhibit exact nonnegative dual multipliers or an equivalent finite
linear contradiction, with all hypotheses shown. An optimizer status is
only a discovery aid, never the conclusion.

The complete research target remains a uniform upper estimate for the full
paid cost. Zero surplus at this one cutoff would yield only `C=psi(144)`.
The first uncertain step is finite feasibility in the declared class;
after it, any scale-dependent construction and uniform complete-cost
estimate remain separate obligations.

Ownership is this new hunt, `tests/test_paid_surplus_obstruction.py`, a short
entry in `hunts/README.md`, and generated `CONTEXT.md`. Do not edit core,
ontology, harness, another hunt, or private operating repositories. No paid
services, new campaign, or sub-workers. Produce a local commit, without push,
PR, or merge, for independent challenge.

Stop after one exact feasible construction or one exact finite obstruction
and its controls. If rational verification fails, report the failed check
and the precise unresolved statement. Do not extend to larger cutoffs merely
to accumulate examples. Retain finite scope, original versus novel, actual
arithmetic grade, zero outcomes, failures, runtime and available usage data.

```huntspec
id: paid_surplus_obstruction
question: Can balanced rational coefficients supported through 12 and covering q through 5 eliminate paid surplus at N=144?
frontier: Exact cap saturation leaves positive surplus for the existing selected coefficients
proposed_attack: Solve one finite rational feasibility problem and verify an exact primal or dual witness
dead_routes:
  - treating a floating optimizer status as an exact obstruction
  - inferring a uniform complete bound from finitely many zero surpluses
required_oracles:
  - exact rational matrix arithmetic with an independent floor-sum implementation
  - explicit prime-power enumeration through 144 by independent factorization
  - independent logarithm enclosures for any reported costs
kill_conditions:
  - the candidate violates balance coverage mass or a prime-power constraint
  - a dual multiplier has the wrong sign or its exact cancellation fails
  - the complete cost omits the positive surplus or the repair bill
agents_may:
  - construct or refute the specified finite feasibility statement
  - run bounded exact checks and report a local commit
agents_may_not:
  - promote their own finding or declare novelty
  - infer a uniform result or close the general factorial route
  - spend on external services or edit other workers
```
