# Hunt: what the `dps=min(dps, 20)` cap costs (`hunts/dps_cap/`)

`zeta/epstein.py` caps working precision in one place inside the rival
interface it hands the battery: `epstein_interface(...)["count_zeros_box"]`
passes `dps=min(_d, 20)` both to `count_zeros_box` and to the
`epstein_completed` closure it winds (`zeta/epstein.py:1091-1093`). Every
other entry in that dict passes the caller's `dps` through untouched.

This hunt measures one number at two precisions and reports both magnitudes.
It changes nothing in `zeta/`.

The quantity:

    abs(epstein_completed(mpc('0.8','85.7'), (2, 1, 3), dps=D))   for D in {20, 60}

It is deliberately off the critical line and high up the strip, which is
where the incomplete-gamma split in `epstein_completed` is at its most
cancellation-prone: `Lambda_Q` decays like a gamma factor in `|t|`, so the
true magnitude at `t = 85.7` sits far below anything 20 digits of working
precision can resolve against the `O(1)` terms that build it.

**Scope.** One number, two precisions, one comparison. Not a study of the
cap's effect on `count_zeros_box` verdicts, not a fix, not a claim about
whether the cap is wrong for the job it was written for. Those are threads,
recorded as such in `HANDBACK.json`, not pursued here.

```huntspec
id: dps_cap
question: What magnitude does abs(epstein_completed(0.8+85.7i, (2,1,3))) take at dps=20 versus dps=60, and does the dps=20 value carry any correct digits?
frontier: unmeasured; the cap at zeta/epstein.py:1091-1093 has no recorded cost
proposed_attack: evaluate the same quantity at both precisions and compare magnitudes
dead_routes:
  - reading the cap's cost off the docstrings, which record defects only at dps 30-70 and never above t = 20
required_oracles:
  - independent evaluation at higher working precision
  - self-consistency of the value under further precision increase
kill_conditions:
  - the two magnitudes agree to within an order of magnitude, so the cap costs nothing here
  - the dps=60 value fails to stabilise under a further precision increase, so the reference itself is noise
agents_may:
  - measure
  - code
  - report both magnitudes with their working precisions named
agents_may_not:
  - edit zeta/epstein.py
  - generalise from one point to the cap's effect on any battery verdict
  - promote their own claim
```
