# Handoff: Hardy's Z Function (Mathlib4 Port)

**Target:** `hardyZ`
**Status:** Ready to draft Lean code
**Workspace:** `/Users/thomas/zeta-lab/lean/ZetaLean/`
**Target Host:** `leanprover-community/mathlib4`

## Goal
Formalize Hardy's Z function in Lean 4 to pave the way for proving the Critical Line Theorem.

## The Strategy
Instead of wrestling with continuous branches of `log Γ` for the Riemann-Siegel `ϑ`, we are directly defining `Z t` using the completed Riemann zeta function `Λ` (which is `completedRiemannZeta` in Mathlib). Since `Λ(1/2 + it)` is known to be real, this lets us sidestep the logarithm branching issues entirely.

## Definition Stubs
I've placed a stub file at `ZetaLean/HardyZ.lean`. It includes the basic definition shape and outlines the lemmas for the first PR:

1. **Definition:** `hardyZ (t : ℝ) : ℂ := completedRiemannZeta (1/2 + t*I) / (...)`
2. **Realness:** Prove `∃ r : ℝ, hardyZ t = r` using `riemannZeta_conj` and `completedRiemannZeta_one_sub`.
3. **Absolute Value:** Prove `‖hardyZ t‖ = ‖riemannZeta (1/2 + I*t)‖` (requires showing `Γ(1/4 + I*t/2) ≠ 0`).
4. **Evenness:** Prove `hardyZ (-t) = hardyZ t`.
5. **Zero Equivalency:** Prove `hardyZ t = 0 ↔ riemannZeta (1/2 + I*t) = 0`.
6. **Continuity:** Prove `Continuous hardyZ`.

## Notes on the First PR
- **No `sorry`**: The `contrib-lab` hooks will complain if you try to commit with `sorry` or `snake_case` anywhere, so keep them commented out (as I did in the stub) or use `sorry` only during local iterative building.
- **Type Signature Debate**: The Zulip post asks whether `Z` should be `ℝ → ℝ` or `ℝ → ℂ`. The stub currently returns `ℂ` for algebraic convenience, but you can change this to output exactly `ℝ` if that's what the community prefers.
- **No Math in `contrib-lab`**: Remember that `contrib-lab` is just the tracking system. Keep your Lean work inside `zeta-lab/lean/ZetaLean` until it's ready to be transplanted into a `mathlib4` fork.
