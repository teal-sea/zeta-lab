# MISSION: `euler_defect_axis` — the axis the Epstein family actually supplies

Issue #93 records a measured observation and one open question. The
observation: a nonzero log-derivative coefficient at a composite is a failure
of multiplicativity read off the zeros, and the Epstein zeta functions of
binary quadratic forms supply a family where that failure is tunable. The
open question: does the size of that failure *bound* how far zeros may leave
the critical line?

The issue proposes the experiment and prices it: "The Epstein family supplies
a defect axis from 0 to 36 with class number as the knob... Testing it needs
the off-line zeros, and `zeta.epstein.epstein_zeta` costs about 2.2 s per
evaluation at dps 15, so it is a compute job."

This hunt does the cheap thing first: check the axis before buying the compute.

## The check

The discriminator is defined for a Dirichlet series `f = sum a(n) n^-s` with
`a(1) = 1`. It solves

    a(n) log n = sum_{d | n} c(d) a(n/d)

for `c` by recursion, isolating the `d = n` term as `c(n) a(1)`.

A binary quadratic form represents 1 if and only if it is the principal form
of its class group. So the recursion's normalisation is a statement about
which forms are admissible inputs, and it is checkable in one line per form.

## What this hunt may conclude

The identity above is the whole content of the recursion, so its residual at
the returned `c` decides whether the recursion was entitled to run. That is a
measurement, not a reading of the source.

If the axis survives, the hunt says so and the compute job proceeds on a sound
footing. If it does not, the hunt reports the corrected axis and what it costs
the proposed experiment, which is cheaper than discovering it afterwards.

Nothing here is evidence about RH (`docs/08`).

```huntspec
id: euler_defect_axis
question: Is the Epstein family's composite-defect axis, reported as running from 0 to 36 with class number as the knob, what the discriminator's own normalisation entitles it to report?
frontier: docs/34 table E7 and issue #93 report per-form composite defects for 44 reduced forms of 14 discriminants, headline 36.0644 at d = -15; tests/test_zeta_temperament.py pins that row above 30
proposed_attack: compute the residual of the defining identity at the returned coefficients for every form, then rebuild the axis from the forms whose residual is zero and check those against the class-number-one prediction c(n) = Lambda(n)(1 + chi_d(n)), which uses no recursion
dead_routes:
  - reading the normalisation off the source instead of measuring the residual it implies
  - repairing a form with a(1) = 0 by rescaling n to n/m, which needs every represented value to be a multiple of the least one
required_oracles:
  - the residual of a(n) log n = sum_{d|n} c(d) a(n/d), computed by an independently written function
  - the class-number-one factorisation zeta_Q = w zeta L(chi_d), giving c(n) = Lambda(n)(1 + chi_d(n)) with the Kronecker symbol computed from its definition
  - exact integer enumeration of the values each form represents
kill_conditions:
  - the residual is zero for every form, in which case the published axis stands and this hunt has found nothing
  - the class-number-one prediction disagrees with the recursion on the forms the recursion is entitled to, which would put the fault in this hunt rather than in the axis
agents_may:
  - recompute the published table and report the residual alongside every row
  - report a corrected axis and what it does to the experiment issue #93 proposes
agents_may_not:
  - edit zeta/, tests/ or docs/ from inside this hunt
  - describe the qualitative conclusion of docs/34 section 6 as withdrawn when only some of its rows are
```
