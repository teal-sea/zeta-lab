# 34. The Riemann zeros in tuning units

**Hunt #76 (`hunts/zeta_temperament/`). Verdict: INTERESTING STRUCTURE,
classical in substance.** Measured in steps-per-octave, the Riemann zeros
avoid the equal temperaments that tune prime-power harmonics and ignore the
ones that tune composites, with the exact deficit Landau's formula
prescribes. On Odlyzko's first 100,000 zeros every prime power lands within
0.0012 of the prediction and every composite gives 0.0000. The mathematics
is Landau (1912); the reading, and the composite control that makes it
vivid, are this laboratory's. Nothing here is evidence about RH (`docs/08`).

## 1. Definitions

* **Tuning units.** For a zero 1/2 + i gamma put theta = gamma ln 2 / 2 pi.
  Then ζ(1/2 + it) at t = 2 pi x / ln 2 is sum_n n^{-1/2} e^{-2 pi i x log2 n},
  which is large when x log2 n is near an integer for many small n, i.e. when
  the x-note equal temperament approximates the harmonic series. So x is a
  number of steps per octave and theta is a zero's ordinate in those units.
  This substitution is Gene Ward Smith's; the Xenharmonic Wiki ("The
  Riemann zeta function and tuning") and OEIS A117536 carry the peaks.
* **Landau's formula.** For n > 1, sum over 0 < gamma < T of n^{i gamma} =
  -(T / 2 pi) Lambda(n) / sqrt n + O(log T), Lambda the von Mangoldt
  function. Since n^{i gamma} = e^{2 pi i theta log2 n}, dividing by the
  zero count N(T) ~ (T/2 pi) log(T/2 pi e) gives

      mean over zeros of e^{2 pi i theta log2 n}  ~  -Lambda(n) / (sqrt n · <log(gamma/2 pi)>).

  At n = 2^k the left side is the k-th Fourier coefficient of the
  distribution of theta mod 1, so the octave tower 2, 4, 8, ... fixes the
  density of zeros mod 1 in tuning units. At other prime powers it says the
  zeros avoid the x for which x log2 p is near an integer, the temperaments
  that tune the harmonic p. At composites Lambda(n) = 0 and the coefficient
  must vanish, which is the built-in control.
* **Smoothed density.** A box window of half-width w = 0.1 steps damps the
  k-th coefficient by sinc(2 pi k w), and the predicted density at theta is
  1 + 2 sum_k c_k sinc(2 pi k w) cos(2 pi k theta).

## 2. Derivable facts

**F1.** Landau's formula in these units is exactly the statement above; no
new mathematics, a change of variable.

**F2.** Since Lambda(2^k) = ln 2 for every k, the density of zeros at
integer x is depleted, to first order, by 2 ln 2 (sum_k 2^{-k/2}) / L =
2 ln 2 (1 + sqrt 2) / L ≈ 3.35 / L with L = <log(gamma / 2 pi)>, and
enhanced at half-integers by 2 ln 2 / ((1 + sqrt 2) L) ≈ 0.57 / L. The
deficit decays like 1 / log t: the zeros become uniform in tuning units,
slowly (Hlawka's theorem), and at any finite height they are not.

**F3. Harmonic horizon.** The Riemann-Siegel main sum runs over n <=
sqrt(t / 2 pi) = sqrt(x / ln 2) ≈ 1.2 sqrt x, with a remainder of size
x^{-1/4} that depends on the fractional part of sqrt(x / ln 2) and not on
how any higher harmonic is tuned. So the zeta score of the x-EDO is decided
by the harmonics up to 1.2 sqrt x. For 12-EDO that is harmonics 1 to 4: the
main sum gives 5.385 against Z = 5.084, and the major third (harmonic 5)
enters only through the universal remainder. For 53-EDO the horizon is 8.7;
for 311-EDO, 21.

## 3. Empirical results

**E1. The harmonic spectrum of the zeros** (`probe_landau_edo.py`,
Odlyzko zeros1, 100,000 zeros, gamma <= 74,921, L = 8.505, checksum
pinned, loaded through `zeta.moments.load_odlyzko_zeros`):

| n | log2 n | measured | Landau | |
| --- | --- | --- | --- | --- |
| 2 | 1.000 | -0.0584 | -0.0576 | prime power |
| 3 | 1.585 | -0.0756 | -0.0746 | prime power |
| 4 | 2.000 | -0.0413 | -0.0407 | prime power |
| 5 | 2.322 | -0.0858 | -0.0846 | prime power |
| 6 | 2.585 | +0.0000 | 0 | composite |
| 7 | 2.807 | -0.0877 | -0.0865 | prime power |
| 8 | 3.000 | -0.0292 | -0.0288 | prime power |
| 9 | 3.170 | -0.0436 | -0.0431 | prime power |
| 10 | 3.322 | +0.0000 | 0 | composite |
| 11 | 3.459 | -0.0862 | -0.0850 | prime power |
| 12 | 3.585 | +0.0000 | 0 | composite |
| 13 | 3.700 | -0.0848 | -0.0836 | prime power |
| 16 | 4.000 | -0.0206 | -0.0204 | prime power |
| 25 | 4.644 | -0.0384 | -0.0378 | prime power |
| 27 | 4.755 | -0.0252 | -0.0249 | prime power |
| 32 | 5.000 | -0.0146 | -0.0144 | prime power |

For 100,000 uniformly random points the standard error of each coefficient
would be 0.0022. The composites are zero to four decimals, which is tighter
than random points would allow: Landau's O(log T) remainder divided by
100,000 is 10^{-4}. The zeros are not random and they know which harmonics
are prime. `figures/zeta_temperament_landau.png`.

**E2. Density in tuning units** (box window ±0.1 step, uniform = 1):

| where | measured | predicted |
| --- | --- | --- |
| integer x (pure-octave temperaments) | 0.801 | 0.800 |
| half-integer x | 1.069 | 1.067 |
| x log2 3 near an integer (53, 665, ... territory) | 0.762 | 0.767 |
| x log2 6 near an integer (composite control) | 0.997 | 1.000 |

By height band at integers: (0, 1000] 0.570 vs 0.605; (1000, 5000] 0.730
vs 0.722; (5000, 20000] 0.780 vs 0.775; (20000, 75000] 0.811 vs 0.809. The
deficit shrinks like 1 / log t as F2 says. `figures/zeta_temperament_density.png`.

**E3. Second table.** The laboratory's own 2000 cached zeros
(`zeta.explicit.first_zeros`, computed here, independent of Odlyzko) give
the same picture at lower height: prime powers within 3 percent of
Landau, composites within 0.0012, density at integers 0.655 against 0.672
predicted, and only 4.9 percent of zeros within 0.05 of an integer against
10 percent for uniform.

**E4. Calibration against the known result** (`probe_peaks_edo.py`). At
integer x in [5, 400], |Z| against a tuning error that never mentions
zeta (RMS deviation of x log2 p from integers, weighted 1/sqrt p): Spearman
-0.59 for p = 3 alone, -0.72 for p <= 7, -0.78 for p <= 13; null 99.9th
percentile 0.22; no shared trend with x (Spearman(x, error) = 0.003).
Detrended by the local RMS of |Z|, the top of the ranking is 311, 270, 342,
224, 171, 118, 53, which is the list microtonal practice arrived at on its
own; 7 of 15 classic temperaments sit in the top 24 of 396 (chance 0.9).
Reproduced, not claimed: Gene Ward Smith, OEIS A117536.

**E5. Tried and dropped.** The pair correlation of zeros mod 1 in tuning
units (Bogomolny-Keating would put an arithmetic correction at integer
separations): at 100,000 zeros the first coefficient is +0.010, below what
this hunt can resolve from a box-window artefact.

## 4. What this is and is not

It is Landau's formula read in a coordinate that a different community
uses for a different purpose, and that reading makes the explicit formula
audible: **the zeros avoid the temperaments that tune primes**, harmonic n
pushing with weight Lambda(n) / sqrt n, and composites pushing not at all.
The numbers are four-decimal confirmations of a 1912 theorem on
verified zeros, so the grade is *measured* on the table and *theorem* on the
statement. What is original here is the framing, the composite control and
the harmonic-horizon remark (F3), which is a concrete caveat for the
Xenharmonic use of |zeta| as a tuning metric at small x. Nothing here bears
on RH: Landau's formula is unconditional, and the zeros used are on the
line by Odlyzko's verification, not by hypothesis.

## 5. Follow-ups

* A note for the Xenharmonic Wiki: the zeros as "anti-temperaments", with
  E1 and E2, and the horizon caveat for x < 25.
* Enclosure-carrying peak locations (`zeta/rigor.py`) for the A117536
  record temperaments; the published tables are floating point.
* The Fyodorov-Hiary-Keating question restated: how good can the best
  temperament near size x be? The record peaks at integer x are a sparse
  subsequence of the large values of |zeta|, and their growth against the
  conjectured exp(sqrt(½ log t log log t)) has not been measured.

## 6. What was searched

The Xenharmonic Wiki pages "The Riemann zeta function and tuning", "Zeta
peak index" and "Table of zeta-stretched edos", OEIS A117536, and Belmans'
2012 note were read; they treat the peaks and the Gram points and not the
distribution of zeros mod 1. One web search for the zeros in this framing
found nothing. That is weak evidence of absence and is reported as such.

## Reproduce

```bash
.venv/bin/python hunts/zeta_temperament/probe_landau_edo.py   # fetches data/odlyzko/zeros1 if absent
.venv/bin/python hunts/zeta_temperament/probe_peaks_edo.py
.venv/bin/python hunts/zeta_temperament/make_figures.py
.venv/bin/python -m pytest -q tests/test_zeta_temperament.py
```
