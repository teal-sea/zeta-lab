# DIAGNOSIS: the saved defect-vs-position correlation is a scanning artifact

> Written 2026-10-24, corrected 2026-10-27. Grade: **measured**, one route,
> float/mpmath values, no enclosure. It is a kill, so the usual ladder does
> not apply: a negative result does not need a certificate to be worth
> recording, only a reproduction.
>
> This is not the missing outcome of the hunt. `hunts/README.md` Hunt #2
> already withdraws the recorded correlation, on three defects checked in
> tree: the completeness gate was never called, a lesion shows an incomplete
> on-line list forges the off-line signal at zero factorization defect, and
> the test set is the rival set. This file is an additional, independent
> defect in the same scanner. It does not replace that withdrawal.

## What was claimed

`run_experiment.py` sweeps a one-parameter family `F_kappa`, kappa from 0 to 1,
and records a `factorization_defect` together with a `max_position_residue`. The
saved rows rise together: defect 1.58 to 105.95, residue 3.66 to 4.99. Read
straight, that is a quantitative relation between failure to factor and failure
to sit on the line, which is the MISSION's hypothesis.

## What is actually there

Re-run on 2026-10-24 with the hunt's own modules (`detector.py`, `family.py`),
same parameters, c grid 20, 40, 60, 80, 86, 90, 95, t_max 110, n_max 2000.
The script that prints these numbers is
`hunts/factorization_vs_position/diagnose_kappa_scan.py`. It imports
`detector.py` and `family.py` unchanged.

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

Three defects, in order of severity. Defect 1 is the one this file adds.
Defects of completeness, the lesion, and the rival set are Hunt #2's, already
withdrawn there.

### 1. The scanner's output does not depend on kappa

`zeroside` is identical at every c for the two ends of the family:
2.7761, 4.3832, 4.3640, 4.5661, 1.4059, 4.7697, 5.1623 in both runs, and
`online_zero_count` is 59 in every one of the nine saved rows. The on-line zero
side is a functional of one list of zeros, so an unchanged zero side means the
same zeros were found for every member.

The mechanism is exact proportionality, not a shared sample. `family.Z_kappa`
returns the real part of one fixed rotation, `expjpi(dh_theta(t)/pi)`, times
`f_kappa`. That real part is `(1 + 0.284079*kappa)` times one fixed function
of t. `0.284079` is the leading digits of `zeta.epstein.KAPPA_REF`. The ratio
`Z_kappa(t, 1) / Z_kappa(t, 0)` equals `1 + KAPPA_REF` to 20 digits at
t = 4, 12.3, 30.3, 50 and 77.7, with a zero residual at that precision
(`test_kappa_proportionality.py`). The factor is positive for kappa in [0, 1],
so sign changes of the scanner's output cannot depend on kappa. The sweep is
reading one fixed zero set, not nine.

The rotation is the Davenport-Heilbronn root number for every kappa, so the
quantity is real only at the DH parameter. At kappa = 0 and kappa = 1,
`float(mp.re(val))` takes the real part of a complex value. Those sign changes
are not zeros of `F_kappa`. Proportionality is why the list cannot move even
before that point is reached: a positive scalar does not move a sign change.

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
character and not zeta. `f_0 = (L(chi) + L(chibar))/2` is a linear combination
of `L(chi)` and `L(chibar)` without a scalar Euler product. Its
`factorization_defect` of 1.58 is therefore not a deviation from an Euler
product it was supposed to have. The family never interpolates zeta to DH; both
ends lack the property the x-axis is supposed to be measuring.

The independent control in `results2.json` supports this reading rather than
contradicting it: zeta there has defect 0.0 and residue 0.0037, roughly a
thousandth of the family's smallest residue. Whatever `results.json` is
measuring, it is not a smooth departure from the zeta point, because zeta is not
on that axis.

## Verdict

The saved correlation is withdrawn. Hunt #2 already withdrew it on completeness,
the lesion, and the rival set. This file adds an independent defect: the
scanner's output is a positive multiple of one fixed function, so the zero list
cannot depend on kappa. Nothing about factorization defect versus zero position
is established here, in either direction.

Reproduce with the repository interpreter (backend `python-flint`) and:

```bash
python hunts/factorization_vs_position/diagnose_kappa_scan.py
python -m pytest hunts/factorization_vs_position/test_kappa_proportionality.py -q
```
