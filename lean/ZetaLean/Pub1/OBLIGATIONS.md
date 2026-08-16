# Pub 1 strong closure — status: CLOSED

Toolchain `leanprover/lean4:v4.33.0-rc2`, Mathlib `v4.33.0-rc2`
(`51e6992efd06126df61a496bebf8f49482a4e129`).

**Both headline theorems are unconditional.**

```
pub1_strong_closure :
  IsProfile w → ∃ C₁ C₂, IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w)

pub1_strong_closure_reciprocal :
  IsProfile w → ∃ C₁ C₂, IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹

pub1_strong_closure_exists :
  ∃ w C₁ C₂, IsProfile w ∧ IsLUB … ∧ IsGLB …
```

The only hypothesis is `IsProfile w`, which *is* the setting: it says `w` solves
`Aw = 1`, the profile the statement is about.  `exists_profile` proves such a `w`
exists and `pub1_strong_closure_exists` carries no hypothesis at all, so nothing
is vacuous.

`lake build` succeeds; no `sorry`, no `admit`, no `axiom` declaration, no
`native_decide`; all audited theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`.

## How the four obligations closed

**A — `F₁'' = 2δ₀ + q` and interior `C²` of `w`.**
`pub1_kernel_second_deriv : (Tv)''(s) = 2·v s + ∫_I q(|s-t|)·v t dt`, with the
delta mass obtained as the two moving-endpoint terms of the integral split at
`t = s`, each contributing `fKer'(0)·v(s) = v(s)`.  No distribution theory was
built.  Then `w_contDiffOn : ContDiffOn ℝ 2 w (Ioo (-1/2) (1/2))`,
`|w''| ≤ 2 + 80.963…`, `|w'| ≤ B₂/2`.  Claimed on the open interval only: `w''`
genuinely jumps by `2w(±1/2) ≥ 2/5` at the endpoints.

**B — the exact residual certificate.**
`r0_identity : u + T₀u + r₀ = 1` on `I` (`M = 20`, degree-52 rational residual,
132 atomic integrals), the exact `∫_I r₀²`, both series tails, `‖q‖_∞ ≤ 80.963`,
`‖q - q_M‖_∞ ≤ 2.90e-17`, the two resolvent estimates, and finally

```
zpp_bound : |w''(s) - u''(s)| < 6060899845/10^12      (s in the interior)
```

via the certificate identity `z'' = r₀'' - 2z - q*z - (q - q_M)*u`, which is the
difference of `w'' = -(2w + q*w)` and `u'' = -r₀'' - (2u + q_M*u)`.  The final
arithmetic closes with margin `3.6e-13`.

**C — positivity.** `profile_pos : ∀ s, 0 < w s`.

**D — uniform `L¹` bounds.** `taper_secondDeriv_L1_of_profile` and
`taper_sq_secondDeriv_L1_of_profile`, uniform for `L ≥ 8`.

**Strict concavity and radial monotonicity.**
`w_second_deriv_lt : w'' < -0.59326318` on the interior, hence
`w_deriv_neg`, `w_antitoneOn`, and `w_radial : |s₁| ≤ |s₂| ≤ 1/2 → w s₂ ≤ w s₁`.

`w_radial` supersedes `Concavity.radial_antitone`, which assumed
`Differentiable ℝ w` on all of `ℝ`.  `w` does not satisfy that at `±1/2`, so that
form was uninstantiable; the replacement needs only interior differentiability
plus continuity on the closed interval, via `antitoneOn_of_deriv_nonpos`.
`Concavity.lean` is retained for its abstract even/concave lemmas.

## The lesion

`Pub1LesionTest.lean.expected-fail` must not compile, and does not: with the
residual bound inflated by 101 the arithmetic step reduces to `False`.  Its
kernel-checked counterparts are `concavity_margin_lesioned` and, on the final
assembly, `zpp_arith_lesioned` / `concavity_lesioned_final`.

## Provenance

`ZetaLean/Pub1/Aristotle/` came from Harmonic's Aristotle (ids in
`lean/ARISTOTLE-RUNS.md`).  Per `lean/proof_adapter.py` the service's own claim
is input, not evidence: each passed the static refusal scan and `lake build`
here before use.
