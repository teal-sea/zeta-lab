# Results — the quasicrystal that is a theorem

**Status: probe, complete. The quasicrystal lane now has its ground-truth
universe: the tapered-transform instrument, pointed at a golden cut-and-
project set whose atomic diffraction is proved, reproduces the derived law
to 2.5e-8 — and the exact-arithmetic stage caught the author mis-remembering
a classical theorem, which is the house rule doing its job.**

Everything is the accurate regime (numpy float64; exact integers for the
Pisano stage). Raw numbers in `results.json`; predictions pre-registered in
`MISSION.md`. Nothing here is about ζ's zeros and nothing is evidence about
RH; this is instrument validation against a proved answer, in the same
spirit as `zeta/finitefield.py` for the RH lane.

## What was measured

- **P1 (calibration on ℤ): holds, at machine precision.** The tapered
  transform of the integer lattice matches Poisson summation at 2π, 4π, 6π
  to 6.4e-14, off-peak response 4e-16 of scale. The one constant of the
  instrument (taper mass T√(2π)) is thereby fixed by an elementary identity
  and transfers unchanged.
- **P2 (the theorem reproduced): holds, far past the registered bar.** The
  golden model set (window [0,1), density measured 0.44722 vs derived
  1/√5 = 0.44721, defect 9.5e-6): the twelve strongest predicted peaks sit
  within **8.7e-9** of the numerically derived dual-module positions
  (registered: 1e-3) and the measured amplitudes match the window-transform
  law |W|/covol·|sinc(k\*|W|/2)| within **2.5e-8** relative (registered: a
  few percent). The Fourier module and the intensity law were derived in
  code from the embedding lattice, not quoted.
- **P3 (silence off the module): holds, 300× past the bar.** 200 random
  frequencies away from every visible module point: median response
  1.0e-5 of scale, versus the weakest tested peak at 9.7e-2 — a
  **9717×** separation (registered: ≥ 30×; ζ's prime-power gate measured
  26.8× with 1000 zeros, so the theorem-universe instrument has headroom of
  two orders over the arithmetic one, as it should: nothing here is
  truncated by a finite zero list).
- **P4 (lesions): hold.** Gaussian jitter suppresses each peak by the
  Debye–Waller factor: fitted log-slope vs −σ²/2 within 1.0% (σ = 0.05) and
  0.8% (σ = 0.10). A Poisson set of matched density and extent shows max
  response 7.1e-3 at the peak set — 14× below the weakest true peak.
- **P5 (the golden thread): one exact identity holds, one registered claim
  was wrong and the computation caught it.** χ_DH² = χ₅ pointwise mod 5 —
  the rival's quartic character squares to the ℚ(√5) character, exactly.
  But the registered Pisano statement π(p) | p − χ₅(p) is **false**, first
  counterexample p = 3 (π = 8 ∤ 4): the author remembered the split case
  and half of the inert case. The statement that holds, checked for every
  prime p < 500, p ≠ 5: π(p) | p − 1 when χ₅(p) = 1 and π(p) | 2(p + 1)
  when χ₅(p) = −1. The miss stays on the books — it is precisely the
  failure mode the derive-never-remember rule exists for, and the exact
  stage caught it on first contact.
- **P6 (precision response): holds, monotone.** Doubling extent and taper
  twice: max amplitude defect 8.6e-9 → 1.8e-9 → 1.0e-10.

## What this buys the tree

The quasicrystal gate's headline on ζ (atoms at log prime powers, 26.8×
separation) was measured with an instrument that had never been run against
an aperiodic set with a *proved* atomic spectrum. Now it has been: the same
transform architecture reproduces a theorem to eight digits, its silence is
real silence, its lesion response is quantitative, and its one constant is
pinned by Poisson summation. A future session pointing this machinery at a
zero measure inherits a control that cannot be argued with.

## Disposition

Instrument kept; no claim promoted; no ledger entry. The conductor-5
observation (the rival's character squares to the golden field's) is pinned
arithmetic, not a lead. One registered prediction failed and is recorded
above with its counterexample.
