# MISSION — `dps_cap`: what the precision cap in the rival interfaces costs

A bounded measurement run. One quantity, two precisions.

## Scope

`zeta/epstein.py` hands the counterexample battery three rival interfaces, and
each one silently caps the precision it was asked for:

| line | caller | cap |
| --- | --- | --- |
| 1073 | `epstein_interface.zeros_on_line` | `Z_epstein(..., dps=min(dps, 15))` |
| 1092 | `epstein_interface.count_zeros_box` | `count_zeros_box(..., dps=min(dps, 20))` and `epstein_completed(..., dps=min(dps, 20))` |
| 1126 | `zeta_interface.count_zeros_box` | `dps=min(dps, 20)`, `xi(..., dps=min(dps, 20))` |
| 1142 | `dh_interface.count_zeros_box` | `dps=min(dps, 20)` |

The caller's `dps` is accepted and then discarded. Nothing in the returned
dict records that it was. This run measures the size of that discard at one
point, and does not touch `zeta/`.

## The measurement

`abs(epstein_completed(mpc('0.8','85.7'), (2,1,3), dps=D))` at `D = 20` (what
the cap delivers) and `D = 60` (what the caller asked for), plus a convergence
ladder to establish which of the two is the number and which is noise.

## What this run does not establish

One point, one form, one function. It bounds nothing about the heights at
which the battery actually calls `count_zeros_box`, and it is not a claim that
any published battery verdict is wrong. It measures a cost, not a defect in a
result.

```huntspec
id: dps_cap
question: What does the min(dps, 20) cap in epstein.py's rival interfaces cost on a completed-Epstein evaluation high on the strip?
frontier: uncharacterised — the caps are undocumented at their call sites and no test pins the accuracy the capped path delivers
proposed_attack: evaluate the same quantity at the capped precision and at the requested precision, and separate signal from roundoff with a convergence ladder
dead_routes:
  - reading the returned dict for a precision warning — the interfaces record no provenance for the discarded dps
required_oracles:
  - internal convergence of the same routine at dps 80 and 100, agreeing to all digits printed
  - an independent recomputation by a separate process, reported as agreement or disagreement in order of magnitude
kill_conditions:
  - the two precisions agree to within an order of magnitude, making the cap free at this point
  - the dps=60 value fails to stabilise against dps=80 and dps=100, making it noise too
  - the quantity is shown to be outside any range the battery evaluates, making the cost unreachable
agents_may:
  - measure
  - code
  - attack
  - report a candidate for the ledger
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - edit zeta/epstein.py
```

```runmanifest
id: dps_cap-2026-08-14-run1
hunt: dps_cap
started: 2026-08-14T00:00-05:00
finished: 2026-08-14T00:00-05:00
ran:
  - python hunts/dps_cap/measure.py
  - python -c convergence ladder at dps 30, 40, 80, 100
outcome: the capped precision returns a magnitude 24 orders too large at this point, with no correct digits; the requested precision converges
artifacts:
  - hunts/dps_cap/results.json
  - hunts/dps_cap/HANDBACK.json
```
