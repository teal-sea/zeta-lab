# Hunt #7: the quasicrystal that is a theorem (`golden_control/`)

**Question.** The sharpest gate in this repository is the quasicrystal gate
(`zeta/quasicrystal.py`, `docs/18` §4): the zero measure's Fourier transform
is atomic, and the atom pattern detects the Euler product. But that
instrument has never been pointed at the one kind of aperiodic point set
whose atomic diffraction is a **theorem**: a regular model set (cut-and-
project). The golden-ratio chain is the canonical one. This hunt gives the
quasicrystal lane what `zeta/finitefield.py` gives the RH lane, a universe
where the answer is proved, and asks whether the lane's instrument
reproduces the proved answer.

**The golden thread, stated precisely and then pinned by computation.** The
Davenport–Heilbronn rival is built on the quartic character mod 5, whose
square is the quadratic character χ₅, the character of ℚ(√5), the golden
field. Fibonacci arithmetic mod p is governed by that same χ₅: the Pisano
period π(p) divides p − χ₅(p). So the lab's standing counterexample and the
golden quasicrystal sit over the same conductor-5 arithmetic, one step
apart. This hunt does not claim that connection *does* anything; it pins it
exactly and uses the golden chain as ground truth for the instrument.

House rule applied to the author: **derive, never remember.** No diffraction
formula is quoted from memory. The probe calibrates its tapered transform on
ℤ itself, where the answer is Poisson summation, elementary and exact,
and then derives the golden chain's predicted peak set and intensity law
from the cut-and-project data (lattice matrix, dual, window Fourier
transform) inside the probe, as code that can be read and checked.

## Pre-registered predictions

- **P1 (calibration on ℤ).** The tapered transform of ℤ matches the Poisson-
  summation prediction at k ∈ 2πℤ to better than 0.5%, and the calibration
  constant transfers unchanged to the aperiodic runs.
- **P2 (the theorem reproduced).** For the golden model set (window [0, 1)),
  the twelve strongest predicted peaks appear within 10⁻³ of their predicted
  positions in the projected dual module, and the measured amplitude ratios
  match the derived window-transform law to a few percent (finite-size
  limited).
- **P3 (silence off the module).** At 200 random frequencies away from the
  predicted module, the median response is at least 30× below the weakest
  tested peak, the analog of the 26.8× prime-power/composite separation the
  gate measured on ζ.
- **P4 (lesions).** Gaussian jitter of size σ suppresses each peak by the
  factor e^{−σ²k²/2} (measured log-slope within 10%); a Poisson set of equal
  density shows no peaks above background.
- **P5 (the golden thread, exact).** In exact integer arithmetic: the square
  of the DH quartic character equals χ₅ pointwise mod 5, and for every prime
  p < 500, p ≠ 5, the Pisano period π(p) divides p − χ₅(p).
- **P6 (precision response).** Doubling the point-set extent and the taper
  width moves every measured peak intensity *toward* the derived law, the
  defect shrinks, as a real quantity must.

## Scope

May touch: `hunts/golden_control/` only. Reads `zeta.epstein.chi5` and
nothing else from the package's subject-matter modules; the transform is
probe-local (the packaged one is specialized to one-sided ordinate lists).
No ledger entry unless something survives `hunts/README.md`'s checklist.
Everything here is the accurate regime, numpy floats and exact integer
checks; the strongest words used are *measured* and *observed*. Nothing in
this hunt is about ζ's zeros, and nothing in it is evidence about RH; it is
an instrument-validation study against a proved ground truth, plus one
exactly pinned piece of conductor-5 arithmetic.
