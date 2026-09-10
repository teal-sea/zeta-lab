# MISSION: `epstein_height` — the rule the core never learned

Two hunts in this tree have already met this. `hunts/gate5_p6_c/probe.py`
derives the mechanism in a comment and writes the constant down:

    GUARD_PER_UNIT_HEIGHT = 0.6822

`hunts/dps_cap` (#113) measured what ignoring it costs at one point,
`0.8 + 85.7i` on the form `(2,1,3)`: `epstein_completed` returns `3.1e-33`
against a converged `1.6e-58`, and not one correct digit. The fix that landed
from that hunt was to stop the interfaces silently clamping a caller's `dps`,
and `tests/test_interface_dps_is_honoured.py` guards it.

None of that reached `zeta/epstein.py`. `epstein_completed` and
`epstein_zeta` still accept any `dps`, return a value for any `s`, and say
nothing about the height above which that value has no correct digits. A
caller who asks for `dps = 15` at height 120 is handed a number, and the
number is wrong by thirty-six orders of magnitude.

## What this hunt adds

A point is not a surface, and a constant in a comment is not a guard.

1. **The surface.** Correct digits as a function of `(form, height, dps)`,
   measured against an oracle the routine shares no code with: at `Re s = 5`
   the defining lattice sum converges absolutely, so it can be summed to a
   stated truncation bound and used as ground truth at any height.
2. **The law with its `sigma` term.** The recorded constant is the leading
   term of `L(sigma, t) = 0.68219 t - (sigma - 1/2) log10 t - 0.399`. The
   second term decides whether a rule fitted on one vertical line transfers to
   another, and it says the critical line is the worst case, which is the line
   `Z_epstein` and `count_zeros_box` actually work on.
3. **A guard that fires.** A rule stated as code, with the planted faults that
   make it fire, so it is not another constant in a comment.
4. **The reach.** Which evaluations recorded in this tree sit inside the
   region where the routine has no correct digits.

Nothing here is evidence about RH (`docs/08`). It is a measurement of an
implementation, and the mathematics it touches is classical.

```huntspec
id: epstein_height
question: Above what height does zeta.epstein's Epstein evaluator stop having correct digits at a given dps, and does the constant already recorded in one hunt describe the whole surface?
frontier: hunts/gate5_p6_c records 0.6822 digits lost per unit height as a comment constant; hunts/dps_cap measured one point at 0.8 + 85.7i; zeta/epstein.py carries no guard and no docstring caveat
proposed_attack: measure correct digits against a directly summed lattice oracle at Re s = 5 over a grid of heights and precisions and three forms, then fit the derived law including its sigma term and check the residual on the cells that are neither saturated nor zero
dead_routes:
  - using the routine at higher precision as its own oracle, which cannot separate a converged answer from two agreeing wrong ones
  - reading the constant off hunts/gate5_p6_c instead of re-deriving it, which would inherit its scope silently
required_oracles:
  - the defining lattice sum at Re s = 5, summed directly with a stated truncation bound
  - exact integer enumeration of the lattice points each form represents
  - the asymptotic |Gamma(sigma + it)| = sqrt(2 pi) t^{sigma - 1/2} exp(-pi t / 2), checked numerically against mpmath
kill_conditions:
  - the routine agrees with the oracle everywhere, in which case there is nothing here
  - the fitted law's residual exceeds a decimal digit on the cells that test it, in which case the mechanism is not the one claimed
agents_may:
  - measure, fit, and propose a guard inside hunts/epstein_height/
  - audit which recorded evaluations in the tree sit in the unsafe region
agents_may_not:
  - edit zeta/epstein.py or any test outside this hunt
  - describe a recorded number as wrong without recomputing it
```
