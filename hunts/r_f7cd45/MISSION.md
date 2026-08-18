# Hunt r_f7cd45 — which structural properties of ζ actually discriminate

Publishes the artifact queued by
[issue #21](https://github.com/teal-sea/zeta-lab/issues/21): a partial
computation established that three commonly-cited structural properties of ζ
are satisfied by every RH-violating look-alike in `zeta.epstein.battery`, and
it was recorded as an observation without the probe, the data or the writeup.
This hunt runs it end to end and lands those three files.

## The question

For each of six claimed structural properties of ζ, does the property
**distinguish** ζ from functions that share its analytic structure and violate
RH? Gate #3 of `docs/09-new-ontologies.md`: a property the
Davenport–Heilbronn function and the discriminant −23 Epstein zetas also
satisfy cannot be the load-bearing step of an RH proof, because it is
ungrantable to nothing.

Five of the six were reported in issue #21. The sixth — "in a box strictly off
the critical line the completed function has no zeros" — ran to a 50-minute
timeout there and is the open part.

## Scope

- Writes only inside `hunts/r_f7cd45/`, plus one case-log line in
  `hunts/README.md`.
- Nothing here is evidence for or against RH (`docs/08-why-it-is-hard.md`).
  The subject is which properties *discriminate*, not where the zeros are.
- Gate #3 is eliminative, never probative. "Distinguishes" means "not yet
  eliminated", not "proves anything".

## Preregistration for the sixth property

Issue #21 warns that the box parameters must be chosen **before** any truth
value is seen, because choosing after is choosing the answer. These were
fixed, and this file committed, before the first box was counted.

The property "the completed function has no zeros in box B" is not scale-free:
its verdict is a function of B. A single box would let the choice of B decide
the gate verdict, so two boxes are run and both are reported:

| box | Re | Im | why this box, stated in advance |
| --- | --- | --- | --- |
| B1 | [0.6, 0.9] | [80.0, 81.0] | the first unit slice of issue #21's window, no rival zero known to this laboratory inside it |
| B2 | [0.6, 0.9] | [85.0, 86.0] | the unit slice holding the Davenport–Heilbronn off-line zero this repository already pins, 0.8085171824… + 85.6993484853…i |

The real extent is issue #21's, unchanged. Only the imaginary extent is
narrowed, 10 → 1, and the working precision is dropped to `dps = 15`. Both
changes are the ones issue #21 names ("narrow the box or lower `dps`"). Cost
drove the size: one `epstein_completed` evaluation was measured at ~1.0 s
before the boxes were chosen, and the issue's 10-unit box needs of order
10³ of them per rival.

The wall-clock cap is 600 s per (function, box). A box that exceeds it is
reported as `timeout`, not guessed.

```huntspec
id: r_f7cd45
question: For each of six claimed structural properties of zeta, does the property distinguish zeta from the RH-violating look-alikes of gate #3, or is it shared with them?
frontier: five properties reported unpublished in issue #21 (3 vacuous, 2 discriminating); the sixth, a box zero count over Re in [0.6,0.9] Im in [80,90], unfinished at a 50-minute timeout
proposed_attack: run all six through zeta.epstein.battery against Davenport-Heilbronn and both discriminant -23 Epstein forms, with the sixth narrowed to two preregistered unit-height boxes at dps 15
dead_routes:
  - the sixth property at Im in [80,90] and default precision - it exhausted 50 minutes without finishing in issue #21
  - reading a passing property as evidence about RH - gate #3 is eliminative, never probative (docs/09 section 5.1)
required_oracles:
  - argument-principle winding number over the box boundary, required to come out an integer to within 1e-6
  - exact integer representation counts of the binary quadratic forms
  - the published Davenport-Heilbronn off-line zero 0.8085171824566373855 + 85.6993484853775921719i, pinned in zeta/epstein.py against its literature digits
  - sign changes of the real Hardy-style Z on the critical line
kill_conditions:
  - a winding number fails to be an integer to 1e-6, making that box count ill-posed
  - the property verdict for a rival flips under a change of box, precision or tolerance that was not preregistered
  - zeta itself fails a property it is supposed to have, indicating a defect in the probe rather than a result
agents_may:
  - run the battery and record its verdicts
  - narrow the sixth property's box within the preregistered parameters
  - report a property as unsettled at this cost
agents_may_not:
  - choose box parameters after seeing a truth value
  - read a vacuous verdict as evidence for or against RH
  - claim the reserved word that belongs to zeta/rigor.py and the Lean arm
  - widen the gate verdict beyond the four functions actually run
```

## Kill conditions, in prose

Stop and report if the winding number is not an integer (a zero on the
contour makes the count ill-posed), if ζ fails a property it demonstrably has
(the probe is wrong, not the mathematics), or if the sixth property exceeds
600 s per box per function. "Not settled at this cost" is the result in that
case.
