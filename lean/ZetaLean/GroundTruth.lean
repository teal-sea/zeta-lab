import Mathlib

/-!
# Ground truth, certified

Rung 1 of the formalization ladder: wire the laboratory's ground-truth
assertions (AGENTS.md, "Ground truth for quick assertions") to their
kernel-checked counterparts in Mathlib.  Every statement here is also
pinned numerically by `tests/` on the Python side; here the same facts
carry proofs instead of measurements.

House rule carried over: nothing counts until it compiles with zero
`sorry`s.  A `sorry` is an uncertified step.
-/

open Real

/-- ζ(2) = π²/6 — the Basel problem, certified.  The lab measures
`zeta.core` against `1.6449340668482264…`; the kernel proves the
closed form. -/
theorem zeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := riemannZeta_two

/-- ζ(0) = −1/2 — the analytic continuation's value at zero. -/
theorem zeta_zero : riemannZeta 0 = -1 / 2 := riemannZeta_zero

/-- ζ(4) = π⁴/90, for good measure. -/
theorem zeta_four : riemannZeta 4 = (π : ℂ) ^ 4 / 90 := riemannZeta_four

/-- ζ has no zeros on the half-plane Re s ≥ 1 — the zero-free region
that makes the Prime Number Theorem true, and the outer wall the
critical strip lives inside. -/
theorem zeta_ne_zero_of_one_le_re (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs
