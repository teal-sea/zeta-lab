# Hunt #76: the Riemann zeros in tuning units

Hunt #75 (`chroma_hue/`) closed the note-to-colour question and, in its
aftermath, the operator asked for something bolder. The substitution
t = 2 pi x / ln 2 turns the critical line into a tuning-quality score for the
x-note equal temperament (Gene Ward Smith; Xenharmonic Wiki, "The Riemann
zeta function and tuning"), and that community studies the *peaks*. This
laboratory's subject is the *zeros*. Nobody seems to have asked what the
zeros say in those units. Landau's formula answers it, and this hunt tests
the answer on Odlyzko's tables. Write-up: `docs/34-zeros-in-tuning-units.md`.

```huntspec
id: zeta_temperament
question: In tuning units theta = gamma ln2 / 2pi, do the Riemann zeros avoid the equal temperaments that tune prime-power harmonics, with the deficit Landau's formula predicts, and ignore composite harmonics?
frontier: the Xenharmonic literature ranks equal temperaments by peaks of |zeta(1/2+it)| (OEIS A117536) and does not treat the zeros; Landau 1912 gives sum over zeros of n^{i gamma} = -(T/2pi) Lambda(n)/sqrt(n) + O(log T), which in these units is the Fourier coefficient of the zeros mod 1 at frequency log2 n
proposed_attack: compute the mod-1 Fourier coefficients of Odlyzko's first 100,000 zeros at every frequency log2 n for n up to 32, compare with -Lambda(n)/sqrt(n)/<log(gamma/2pi)>, and measure the smoothed zero density at integer, half-integer and fifths-perfect x against the prediction
dead_routes:
  - reading the peaks of |Z| as new (they are A117536 and the Xenharmonic Wiki, reproduced here only as calibration)
  - pair correlation of zeros mod 1 in tuning units at the 100,000-zero scale (signal below 0.01, not resolved)
required_oracles:
  - Odlyzko's zeros1 table under its pinned sha256, loaded through zeta.moments.load_odlyzko_zeros
  - the 2000 cached zeros in data/explicit_zeros.npz as an always-available second table
  - composite n as the built-in control (Lambda(n) = 0 must give a vanishing coefficient)
  - uniformly random points as the null for the size of each coefficient
kill_conditions:
  - a composite n shows a coefficient of the size a prime power shows
  - the deficit at integers fails to track 1/log(gamma/2pi) across height bands
  - the Odlyzko table fails its checksum or its declared row count
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```

## Files

| file | what it does |
| --- | --- |
| `probe_landau_edo.py` | Landau's formula in tuning units on the 100,000-zero table and on the cached 2000; the density table; writes `results_landau.json` |
| `probe_peaks_edo.py` | calibration against the Xenharmonic result (peaks of |Z| at integer x against an independent tuning error) and the Riemann-Siegel harmonic horizon per temperament; writes `results_peaks.json` |
| `make_figures.py` | `figures/zeta_temperament_*.png` |

Tests: `tests/test_zeta_temperament.py`. The Odlyzko table is fetched into
`data/odlyzko/zeros1` (gitignored) by the probe if absent, and refused if its
sha256 is not `3436c916a7878261ac183fd7b9448c9a4736b8bbccf1356874a6ce1788541632`.

## Scope

Nothing here is evidence for RH (`docs/08`). Landau's formula is
unconditional in the form used (the zeros are on the line in Odlyzko's
range by verification, not by assumption). The hunt touches no core module.

## Run manifest

```runmanifest
id: zeta_temperament-2026-08-22-first
hunt: zeta_temperament
started: 2026-08-22T19:45-05:00
finished: 2026-08-22T20:40-05:00
ran:
  - .venv/bin/python hunts/zeta_temperament/probe_landau_edo.py
  - .venv/bin/python hunts/zeta_temperament/probe_peaks_edo.py
  - .venv/bin/python hunts/zeta_temperament/make_figures.py
  - .venv/bin/python -m pytest -q tests/test_zeta_temperament.py
outcome: on 100,000 zeros every prime-power frequency log2 n carries the coefficient Landau predicts to within 0.0012, every composite gives 0.0000, and the smoothed zero density at integer temperaments is 0.801 against 0.800 predicted
artifacts:
  - hunts/zeta_temperament/results_landau.json
  - hunts/zeta_temperament/results_peaks.json
  - figures/zeta_temperament_landau.png
  - figures/zeta_temperament_density.png
  - docs/34-zeros-in-tuning-units.md
```
