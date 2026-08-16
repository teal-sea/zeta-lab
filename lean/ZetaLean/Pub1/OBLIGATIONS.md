# Pub 1 strong closure — what is proved and what is not

Formalization of `hunts/wide_search/RESULTS-xiprime-admissible-closure.md`
(Zeta Lab PR #45).  Toolchain `leanprover/lean4:v4.33.0-rc2`, Mathlib
`v4.33.0-rc2` (`51e6992efd06126df61a496bebf8f49482a4e129`).

`lake build` succeeds; no `sorry`, no `admit`, no `axiom` declaration, no
`native_decide`; every audited theorem depends only on `propext`,
`Classical.choice`, `Quot.sound` (`PrintPub1Axioms.lean`).

**The principal theorem `pub1_strong_closure` is still conditional.**  This file
says exactly on what.  Nothing is weakened: the open facts are the true
statements from the evidence document, carried as explicit named hypotheses
rather than assumed as axioms.

## The principal theorem

`ZetaLean.Pub1.pub1_strong_closure` : `IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w)`
`ZetaLean.Pub1.pub1_strong_closure_reciprocal` : `IsGLB (recipQuot '' …) (cStar w)⁻¹`

`strongClosureData_of_member` discharges every input except membership of the
constructed sequence in the class; `sourceWindow_taper` reduces that to the four
obligations below.

## Obligation A — `F₁'' = 2δ₀ + q` and `C²` regularity

**The identity is PROVED**, for the true Pub 1 kernel, unconditionally:

```
ZetaLean.Pub1.pub1_kernel_second_deriv :
  (T v)''(s) = 2 · v s + ∫_I fKer''(|s-t|) · v t dt      (|s| ≤ 1/2, v continuous)
```

No distribution theory was built or needed.  Splitting `∫_I F₁(s-t)v(t)dt` at
`t = s` and differentiating twice makes the two moving-endpoint boundary terms
*add* rather than cancel, each contributing `fKer'(0)·v(s)`; `Aristotle/S` proves
`fKer'(0) = 1`, so the coefficient is exactly `2`.  That is the delta mass, and
dropping it is the lesion the evidence document records.

Supporting, all kernel-checked: `Aristotle/N` (the two differentiations),
`Aristotle/S` (`fKer` entire, `fKer 0 = 0`, `fKer'(0) = 1`, `fKer'' = q`),
`F1_eq_fKer`, `F1_conv_eq_split`, `fKer_second_deriv_continuous`.

**Still open — the smallest missing statement:**

```lean
theorem w_contDiffOn :
    ContDiffOn ℝ 2 wExt (Set.Ioo (-(3/5) : ℝ) (3/5))
```

where `wExt s = 1 - ∫_I F₁(s-t) · w t dt` is the natural extension of `w` off
`I`.  Two steps remain, neither blocked by Mathlib:

1. apply `pub1_kernel_second_deriv` with `v = w` to get `w'' = -(2w + q*w)` on
   the interior of `I`, and conclude `ContDiffOn` there from continuity of the
   right-hand side;
2. cross `|s| = 1/2`.  The `w` produced by `exists_profile` solves the equation
   for the *clamped* kernel, so it is constant outside `I` and is not `C²`
   across the endpoints.  `wExt` is, because `F₁` is entire and `s - t` never
   vanishes for `|s| > 1/2`, `|t| ≤ 1/2`, so no kink arises there.

## Obligation B — the exact residual certificate

**The core computation is PROVED.**

```
ZetaLean.Pub1.r0_identity :
  u x + ∫_I F₁^(M)(x-t) · u t dt + r₀ x = 1        (|x| ≤ 1/2, M = 20)
```

with `u` the exact rational trial polynomial and `r₀` the transcribed degree-52
residual (27 nonzero coefficients, up to 65-digit numerators).  This is what
`admissible_closure.py` computes in `fractions.Fraction`, redone in the kernel:
`Aristotle/O` gives the atomic integral `∫_I |x-t|^m t^n dt` in closed form,
`CertAtoms` evaluates the 132 atoms `A₀` needs, and `Certificate` assembles.

Also proved, as exact rationals:

| quantity | theorem | value |
| --- | --- | --- |
| `‖r₀‖_∞` | `r0Sum_lt_decimal` | `< 2.1710808e-5` |
| `‖r₀''‖_∞` | `r0Sum2_lt_decimal` | `< 0.005982627` |
| `r₀''` is the second derivative | `deriv_deriv_r0Sum` | — |
| `‖z‖_∞ ≤ (9/5)‖g‖_∞` | `AristotleR.resolvent_linf_bound` | — |
| `‖z‖₂ ≤ (9/5)‖g‖₂` | `AristotleR.resolvent_l2_bound` | — |

`‖r₀''‖_∞` is the dominant term: it consumes `5.98e-3` of the `6.06e-3` budget.

**Still open**, in dependency order:

```lean
theorem r0_l2  : (∫ x in (-(1:ℝ)/2)..(1/2), r0Sum x ^ 2) ≤ <exact rational>
theorem u_l2   : (∫ x in (-(1:ℝ)/2)..(1/2), uPoly x ^ 2) ≤ <exact rational>
theorem rho_tail        : ∑' k, aCoef (k + 21) ≤ 45088768/2828846926917599723269509375
theorem second_tail     : ∑' k, dCoef (k + 21) ≤ 666953056256/23065890935073171953452059375
theorem q_abs           : 8 + ∑' k, dCoef (k+1) ≤ <exact rational>   -- < 80.963
theorem zpp_identity    : z'' = r₀'' - (Eu)'' - 2z - q*z
theorem zpp_bound       : ∀ s, |s| ≤ 1/2 → |z'' s| < 6060899845/10^12
```

`r0_l2` is the one with real cost: `‖r₀‖₂ ≈ 7.9e-10` is 27 000× smaller than
`‖r₀‖_∞`, so the crude bound `‖r₀‖₂ ≤ ‖r₀‖_∞` is not usable — it would blow the
budget by a factor of 1.5 — and the exact degree-104 integral `∫ r₀²` is needed.
`zpp_identity` is `pub1_kernel_second_deriv` applied to `z`, so obligation A's
proved identity is what it rests on.

## Obligation C — positivity

**DISCHARGED.**  `ZetaLean.Pub1.profile_pos : ∀ s, 0 < w s`.  The row-bound
argument already gives `1/5 ≤ w` at every real `s`, not merely on `I`, because
the clamped kernel makes `w` constant outside `I`.  Nothing stronger than the
square-root taper needs is assumed.

## Obligation D — uniform `L¹` derivative bounds

**Half PROVED.**

```
AristotleT.taper_second_deriv_L1_bound :
  ‖φ_L''‖₁ ≤ B₂/L + 4B₁/L + (35/4)B₀        uniformly for L ≥ 8
```

The `η`-side constants it rests on are all proved: `∫₀¹ η'² = 700/429`,
`∫₀¹|η''| = 35/8` (`AristotleD`), `‖(η²)''‖₁ ≤ 20615/1716`
(`ramp_sq_second_deriv_bound`).

**Still open:** the same bound for the square,

```lean
theorem taper_sq_second_deriv_L1_bound :
    (∫ u : ℝ, |iteratedDeriv 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|) ^ 2) u|)
      ≤ B2 / L + 4 * B1 / L + (20615 / 858) * B0
```

plus the instantiation of both with `P = √w` and `P = w`, which needs the
`‖w'‖_∞`, `‖w''‖_∞` bounds from obligation A.

## The lesion test

`Pub1LesionTest.lean.expected-fail` **must not compile**, and does not: with the
residual bound inflated by the factor 101 the arithmetic step reduces to `False`.
Its kernel-checked positive counterpart is `concavity_margin_lesioned`.

```bash
cd lean && lake env lean Pub1LesionTest.lean.expected-fail
```

## Provenance

Files under `ZetaLean/Pub1/Aristotle/` came from Harmonic's Aristotle (project
ids in `lean/ARISTOTLE-RUNS.md`).  Per `lean/proof_adapter.py` the service's own
verification claim is input, not evidence: each passed the static refusal scan
and `lake build` on this repository's toolchain before use.
