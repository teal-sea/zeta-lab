# DIAGNOSIS: the saved defect-vs-position correlation is a scanning artifact

> Written 2026-10-24 on `swarm-trial-b2-120` by Vizier, on Thomas's instruction to
> work on new ontologies. This hunt has data (`results.json`, `results2.json`) and
> no written outcome. This file is the missing outcome: the lead does not survive.
> Grade: **measured**, one route, float/mpmath values, no enclosure. It is a
> kill, so the usual ladder does not apply: a negative result does not need a
> certificate to be worth recording, only a reproduction.

## What was claimed

`run_experiment.py` sweeps a one-parameter family `F_kappa`, kappa from 0 to 1,
and records a `factorization_defect` together with a `max_position_residue`. The
saved rows rise together: defect 1.58 to 105.95, residue 3.66 to 4.99. Read
straight, that is a quantitative relation between failure to factor and failure
to sit on the line, which is the MISSION's hypothesis.

## What is actually there

Re-run on 2026-10-24 with the hunt's own modules (`detector.py`, `family.py`),
same parameters, c grid 20, 40, 60, 80, 86, 90, 95, t_max 110, n_max 2000:

```
kappa = 0.0   defect = 1.5823   online zeros = 59
    c        arith     zeroside      residue
   20       2.9587       2.7761       0.1826
   40       4.0783       4.3832      -0.3049
   60       4.3375       4.3640      -0.0265
   80       4.5441       4.5661      -0.0220
   86       5.0705       1.4059       3.6645
   90       4.9870       4.7697       0.2173
   95       5.0495       5.1623      -0.1128

kappa = 1.0   defect = 105.9511  online zeros = 59
    c        arith     zeroside      residue
   20       2.2710       2.7761      -0.5051
   40       5.2349       4.3832       0.8516
   60       4.4007       4.3640       0.0367
   80       4.5666       4.5661       0.0004
   86       6.3965       1.4059       4.9906
   90       4.4010       4.7697      -0.3687
   95       5.4911       5.1623       0.3289
```

Three defects, in order of severity.

### 1. The zero list does not depend on kappa

`zeroside` is identical at every c for the two ends of the family:
2.7761, 4.3832, 4.3640, 4.5661, 1.4059, 4.7697, 5.1623 in both runs, and
`online_zero_count` is 59 in every one of the nine saved rows. The on-line zero
side is a functional of one list of zeros, so an unchanged zero side means the
same zeros were found for every member.

`family.Z_kappa` rotates by `expjpi(dh_theta(t)/pi)`, the Davenport-Heilbronn
root number, for every kappa. That rotation makes `Z` real only at the DH
parameter. At kappa = 0 and kappa = 1 the quantity is complex, and
`float(mp.re(val))` takes the real part of a complex value, so sign changes of
that real part are not zeros of `F_kappa`. The sweep is reading one fixed zero
set, not nine.

### 2. The extremum is therefore fixed by construction

`argmax_c = 86.0` in all nine rows because the residue at c = 86 is dominated by
`zeroside` collapsing to 1.4059 there, in both runs above. That collapse is a
property of the shared zero list, not of the family. Any sweep over this c grid
will return 86 regardless of the defect, which is what an artifact looks like:
an extremum location invariant under a 67x change in the independent variable.

### 3. kappa = 0 is not zeta, and is not an Euler product

Coefficients from `f_kappa_coefficients`, n = 1..12, kappa = 0:

```
n        1  2  3  4  5  6  7  8  9 10 11 12
f_0(n)  +1  0  0 -1  0 +1  0  0 -1  0 +1  0
```

Nonzero at 1, 4, 6, 9, 11 with signs +, -, +, -, +. This is not a Dirichlet
character and not zeta: it is a theta-series style object. Its
`factorization_defect` of 1.58 is therefore not a deviation from an Euler
product it was supposed to have. The family never interpolates zeta to DH; both
ends lack the property the x-axis is supposed to be measuring.

The independent control in `results2.json` supports this reading rather than
contradicting it: zeta there has defect 0.0 and residue 0.0037, roughly a
thousandth of the family's smallest residue. Whatever `results.json` is
measuring, it is not a smooth departure from the zeta point, because zeta is not
on that axis.

## Verdict

The saved correlation is withdrawn. It is not a weak lead, it is three separate
measurement errors composing into a monotone-looking table. Nothing about
factorization defect versus zero position is established here, in either
direction.

Reproduce with `../.venv/bin/python` (backend `python-flint`) and the diagnostic
kept at the path named in the commit message; the numbers above are printed by a
script that imports `detector.py` and `family.py` unchanged.

## What a working frame would need

If the defect-versus-position question is worth keeping, it needs three things
this hunt did not have:

1. **An axis with a real zero.** Start at zeta, stay inside Dirichlet
   L-functions where the Euler product is a theorem for principal and primitive
   characters, and ablate a named axiom (multiplicativity of the coefficient
   sequence) by a controlled amount. kappa on a theta series is not an ablation.
2. **Zeros computed from the member's own function**, with the correct root
   number and gamma factor per member, and a stated completeness interval.
   A Hardy Z built with another function's rotation is not a zero finder.
3. **No scan over a free parameter as the response.** A maximum over c is a
   maximum over a choice the analyst made. Measure the position defect at a
   matched point, or over a range proved to contain the extremum.

The doors, such as they are: a corrected family is cheap to build on this host;
the completeness question for off-line zeros needs `count_zeros_box` rather than
a sign scan; and the whole frame still fails the standing test unless a
Davenport-Heilbronn rival can be distinguished from zeta by it.
