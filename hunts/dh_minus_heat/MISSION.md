# Second Davenport-Heilbronn heat flow

Base commit: `85efdcb2b4f8255caed8dbac0961c28361abd413`.
Status: bounded construction, not an established heat-flow comparison.

## Question and scope

Derive the heat deformation for the second real conductor-five combination,
with coefficients `(1, tau_minus, -tau_minus, -1, 0)` and
`tau_minus = -phi - sqrt(1+phi^2)`, `phi=(1+sqrt(5))/2`.
Use the narrow coordinate `s=1/2+iz` throughout.

The first target is a non-real zero at a rational positive heat time exceeding
the first function's recorded upper bound
`0.19242481458026887663805`. If it exists, construct an explicit local
zero-existence inequality with all numerical errors retained. A comparison of
heat constants also requires a written verification of the analytic hypotheses.
An unsuccessful search is not an obstruction to this target.

The functional equation must be derived before a sine or cosine transform is
chosen. The coefficient bound of the first DH instrument does not transfer:
`abs(tau_minus)>1`. All tail bounds must retain this factor.

## Alternatives inspected

The balanced Mobius-prefix floor targets a restricted coefficient class, not a
new constructive prime-counting bound. The higher-correlation simple-zero target
requires a new arithmetic correlation estimate before its proposed gain can be
used. Both remain live research questions; neither is ruled out here. The
second heat-flow construction is selected for this bounded pass because its
normalization and low-height zeros admit direct independent checks.

## Resource boundary

Only short serial pilot computations and targeted tests run locally. No Lean
build, large contour census, paid compute, public submission, commit or push
is authorized by this mission. Stop a pilot at its explicit evaluation budget.
Write scientific artifacts only in this hunt; a case-log entry and generated
index update may be added after the result is checked.

```huntspec
id: dh_minus_heat
question: Does the second DH heat flow have a non-real zero after the first DH upper bound?
frontier: First DH narrow upper bound 0.19242481458026887663805; no second-function comparison checked in this pass
proposed_attack: Derive the odd theta kernel, locate a low-height zero, and enclose a local Rouche inequality
dead_routes:
  - Reusing the first DH cosine transform without checking the functional equation
required_oracles:
  - Hurwitz-zeta evaluation independent of theta quadrature
  - Arb enclosures with explicit series and integration tails
  - Exact rational input checks and planted normalization faults
kill_conditions:
  - The zero-time heat transform disagrees with the completed Dirichlet series
  - A tail bound omits the magnitude of tau_minus
  - A measured non-real zero survives beyond an applicable de Bruijn strip-collapse bound
  - The local zero-existence inequality fails its enclosure checks
agents_may:
  - derive
  - run bounded numerical pilots
  - implement local instruments and tests
  - obtain independent mathematical criticism
agents_may_not:
  - claim novelty from an empty search
  - promote their own claim
  - alter shared mathematical implementations
  - launch heavy local work or external publications
```
