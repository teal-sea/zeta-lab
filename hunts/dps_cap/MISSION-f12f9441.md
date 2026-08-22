# MISSION: what the `min(dps, 20)` cap costs (`hunts/dps_cap/`)

A bounded measurement run, opened 2026-08-14 by the operator. One number, at
two precisions, plus the sweep needed to read those two numbers against a
scale.

## Why this hunt exists

`zeta/epstein.py` builds the rival interfaces that `zeta.epstein.battery`
compares against ζ. Two of the entries in `epstein_interface` clamp the
precision they were handed:

```python
"zeros_on_line":    Z_epstein(t, _f, dps=min(_d, 15))          # line 1073
"count_zeros_box":  count_zeros_box(..., dps=min(_d, 20),
                        fn=lambda z: epstein_completed(z, _f, dps=min(_d, 20)))
                                                                # line 1092
```

The clamps are a speed decision, and the question this hunt answers is what
they buy and what they cost, on one concrete value rather than in principle.

The value chosen is `abs(epstein_completed(0.8 + 85.7i, (2, 1, 3)))`. It is a
fair stress point rather than a hostile one: `count_zeros_box` is an
argument-principle contour integral, so it evaluates `epstein_completed` at
whatever height its box reaches, and t = 85.7 is an ordinary height for a
zero-counting box. The archimedean factor `Gamma(s)` decays like
`e^{-pi t / 2}` there, which puts the true magnitude far below anything a
20-digit evaluation of a cancelling lattice sum can resolve.

## Scope

This hunt measures. It does not change `zeta/epstein.py`, does not file the
result as a defect, and does not decide whether the clamps should be raised:
`count_zeros_box` only needs the *sign of the winding*, and whether the noise
this hunt measures can flip that sign is a separate question this run did not
ask. See `README.md` for what was and was not established.

```huntspec
id: dps_cap
question: What does the min(dps, 20) precision clamp in zeta/epstein.py's rival interfaces cost, measured on one value of the completed Epstein zeta at an ordinary zero-counting height?
frontier: at dps = 60 the value is 1.6174526323779715e-58; the clamped path evaluates the same object at dps = 20, where the routine returns 3.1063191101762651e-33
proposed_attack: evaluate the same point across a precision sweep and locate the precision below which no digit of the answer is correct
dead_routes:
  - reading a small returned magnitude as a zero of Lambda_Q without first checking it against the routine's precision floor at that height
required_oracles:
  - re-evaluation of the same quantity at higher working precision, converged when two adjacent precisions agree
  - the archimedean envelope abs((sqrt(d)/pi)^s Gamma(s)) computed independently of the lattice sum, as a size bound the answer must respect
  - an outside independent recomputation of the same number
kill_conditions:
  - the dps = 20 and dps = 60 magnitudes agree to within an order of magnitude, so the clamp costs nothing at this point
  - the dps = 60 value moves under further precision, so it is not the converged answer either
  - the outside recomputation disagrees with the dps = 60 value by more than an order of magnitude
agents_may:
  - measure
  - sweep precision
  - record raw magnitudes and timings
agents_may_not:
  - edit zeta/epstein.py or any other file outside this directory
  - promote this measurement into a defect report or a battery change
  - declare novelty
  - declare theorem status
```

```runmanifest
id: dps_cap-2026-08-14-bounded-run
hunt: dps_cap
started: 2026-08-14T00:00-05:00
finished: 2026-08-14T00:00-05:00
ran:
  - .venv/bin/python hunts/dps_cap/probe.py
outcome: the clamped precision returns 3.1e-33 where the converged value is 1.6e-58, a factor of 1.9e25 and no correct digit; dps = 30 returns exactly zero at the same point
artifacts:
  - hunts/dps_cap/results.json
  - hunts/dps_cap/README.md
```
