# hunts/dps_cap — what the precision cap in the rival interfaces costs

Opened 2026-08-14. A bounded measurement, not a claim about zeta and not a
result. Nothing here has been through a control.

`zeta/epstein.py:1091` caps precision inside the rival interface:

```python
"count_zeros_box": lambda s0, s1, _f=(a, b, c), _d=dps: count_zeros_box(
    s0, s1, dps=min(_d, 20), fn=lambda z: epstein_completed(z, _f, dps=min(_d, 20))
),
```

so a caller who asks `epstein_interface(form, dps=60)` for a box count gets
`epstein_completed` evaluated at dps = 20 regardless. (`Z_epstein` in the same
interface carries a tighter cap, `min(_d, 15)`, at line 1073.) This hunt
measures one number at two precisions to see what that substitution costs.

## Scope

- One point, `s = 0.8 + 85.7i`, one form, `Q = (2, 1, 3)` (discriminant -23).
- Two precisions, `dps = 20` (the cap) and `dps = 60`, plus one `dps = 100`
  run used only to say which of the two is the reliable one.
- It measures the **evaluation**, not the box count. Whether the winding
  number `count_zeros_box` returns is actually wrong at the cap is a
  different and larger question, left open below.

## What was run

```bash
.venv/bin/python hunts/dps_cap/probe.py       # writes hunts/dps_cap/results.json
```

(The worktree this ran in had no `.venv`; see the note at the top of
`probe.py`.)

## Measured

| dps | `abs(epstein_completed(0.8 + 85.7i, (2,1,3), dps=D))` | seconds |
| --- | --- | --- |
| 20 (the cap) | 4.8463819279571518346e-35 | 1.8 |
| 60 | 1.617452632377971461454064e-58 | 7.7 |
| 100 (scope check) | 1.617452632377971296327251e-58 | 19.6 |

Three things the table says, in order of how load-bearing they are:

1. **The capped value is not a coarser version of the right answer; it is a
   different number by 23 orders of magnitude.** 4.8e-35 against 1.6e-58.
   The imaginary part even changes sign (+2.1e-35 at the cap, -4.0e-59 at
   dps = 60), so no digit of the capped output is a digit of the answer.
2. **The mechanism is cancellation, and it is structural, not incidental.**
   The Mellin split in `epstein_completed` adds pole terms of size
   `1/(sqrt(d)(s-1)) - 1/s` ~ 1e-2 to lattice sums of the same order, and
   the completed function at `t = 85.7` is ~1e-58 because of the Gamma
   factor's `exp(-pi t / 2)` decay. That is ~56 digits of cancellation. The
   internal guard is `_GUARD = 10`, so dps = 20 works at 30 digits and the
   answer sits 28 orders of magnitude below the noise floor. 4.8e-35 is that
   floor, measured.
3. **dps = 60 does not buy 60 digits either.** It agrees with dps = 100 to
   16 significant figures and no further, which is what 70 working digits
   minus ~56 cancelled digits predicts. The cost of the cancellation is paid
   at every precision; the cap is just where it eats the whole number.

## The independent route

`fulcrum_support` refused three times with `no live parent
e72925d1-a292-4b7a-b3ee-caeba70502bf`, so the requested outside check could
not be started from this run. A sibling support run asking the identical
question (`22d8a969`, spawned by run `b4528bd7`) was already working and was
polled instead; see `HANDBACK.json` for what it returned by the end of this
run.

Independently of that, the number was checked here against a formula that
uses no code from `zeta/epstein.py` on its right-hand side
(`hunts/dps_cap/crosscheck.py`). For a negative fundamental discriminant the
class forms partition the representation counts, so with `h(-23) = 3`,
`w = 2` units and `d = |D|/4` shared across classes:

    sum_{Q in Cl(-23)} Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) * 2 * zeta(s) L(s, chi_{-23})

with the right side built from mpmath's `zeta` and Hurwitz zeta alone.
Measured at the same `s = 0.8 + 85.7i`:

| dps | `sum_Q Lambda_Q` | independent right-hand side | relative defect |
| --- | --- | --- | --- |
| 20 | 1.45391457839e-34 | 8.90368899839e-58 | 1.63e+23 |
| 60 | 8.90368899839e-58 | 8.90368899839e-58 | 5.36e-17 |

That is the same story from outside the module: at dps = 60 the completed
values satisfy an identity they were not built from, to the ~16 digits the
cancellation leaves; at dps = 20 they miss it by 23 orders of magnitude.

## Left open, deliberately

`count_zeros_box` reads only the *change in argument* along a contour, so a
uniform scale error would not disturb it, and the routine already refuses a
winding that misses an integer by more than 1e-6. Whether the capped
evaluation makes that routine return a wrong count, raise, or survive is not
measured here and is not asserted either way. What is measured is that at
this height the values it would be reading are roundoff.

```huntspec
id: dps_cap
question: What does the dps=min(dps, 20) cap in zeta/epstein.py's rival interfaces cost, measured on one evaluation?
frontier: unmeasured before this hunt; the cap has been in epstein_interface since the Epstein half was added
proposed_attack: evaluate the same completed Epstein zeta at the cap and well above it, at one point where the Gamma factor forces heavy cancellation
dead_routes:
  - reading the capped output as a low-precision approximation of the true value
required_oracles:
  - the same computation at a third, higher precision (dps = 100)
  - an independent second evaluation by a separate implementation
kill_conditions:
  - the dps = 60 and dps = 100 values disagree beyond their stated 16 figures
  - an independent evaluation at dps = 60 disagrees with 1.6e-58 by more than an order of magnitude
  - the gap shrinks to nothing at points where the Gamma factor is not decaying, showing the effect is the point and not the cap
agents_may:
  - measure
  - report both magnitudes
  - name the cancellation mechanism
agents_may_not:
  - declare the box count wrong without measuring it
  - edit zeta/epstein.py
  - promote this to a result
```

```runmanifest
id: dps_cap-2026-08-14-bounded
hunt: dps_cap
started: 2026-08-14T00:00-05:00
finished: 2026-08-14T00:00-05:00
ran:
  - .venv/bin/python hunts/dps_cap/probe.py
  - .venv/bin/python hunts/dps_cap/crosscheck.py
outcome: the capped evaluation returns 4.8e-35 where the answer is 1.6e-58, a 23-order-of-magnitude error from ~56 digits of cancellation against 30 working digits; the class-number identity confirms the dps = 60 values to 5.4e-17 relative and the dps = 20 values not at all
artifacts:
  - hunts/dps_cap/probe.py
  - hunts/dps_cap/results.json
  - hunts/dps_cap/crosscheck.py
  - hunts/dps_cap/crosscheck.json
```
