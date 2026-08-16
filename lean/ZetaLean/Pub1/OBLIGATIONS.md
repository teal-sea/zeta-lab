# Pub 1 strong closure — what is proved and what is not

Toolchain `leanprover/lean4:v4.33.0-rc2`, Mathlib `v4.33.0-rc2`
(`51e6992efd06126df61a496bebf8f49482a4e129`).  `lake build` succeeds; no
`sorry`, no `admit`, no `axiom` declaration, no `native_decide`; every audited
theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

**`pub1_strong_closure` is still conditional.**  Exactly one gap remains, and it
is named below.

## Obligation A — `F₁'' = 2δ₀ + q` and interior `C²` of `w`: **CLOSED**

```
pub1_kernel_second_deriv : (T v)''(s) = 2·v s + ∫_I fKer''(|s-t|)·v t dt
w_contDiffOn             : ContDiffOn ℝ 2 w (Ioo (-1/2) (1/2))
w_second_deriv_bound     : |w''| ≤ wB2 = 2 + 80.963…
w_deriv_bound            : |w'|  ≤ wB2/2
deriv_w_zero             : w'(0) = 0
```

No distribution theory.  Splitting at `t = s` and differentiating twice makes
the two moving-endpoint terms add, each contributing `fKer'(0)·v(s) = v(s)`.

Only the **open** interval is claimed.  Across `|s| = 1/2` the second derivative
genuinely jumps — the delta mass gives `2w(s) ≥ 2/5` inside and nothing outside —
so `C²` there is false and is not asserted.  Two economies kept this small:
`|w'| ≤ B₂/2` comes from `w'(0) = 0` plus the mean value inequality, needing no
bound on `‖fKer'‖_∞`; and `|w''| ≤ 2‖w‖_∞ + ‖q‖_∞‖w‖₁` needs only `w ≤ 1`.

## Obligation C — positivity: **CLOSED**

`profile_pos : ∀ s, 0 < w s`.

## Obligation D — uniform `L¹` derivative bounds: **CLOSED**

```
taper_contDiff_of_profile      : ContDiff ℝ 2 (taper w L)          (L ≥ 8)
taper_secondDeriv_L1_of_profile: ∃ C₁, ∀ L ≥ 8, ‖φ_L''‖₁ ≤ C₁
AristotleTU2.taper_sq_second_deriv_L1_bound_open : the `(φ_L²)''` analogue
```

The earlier `T`/`U`/`J` versions asked for `C²` on a neighbourhood of the closed
interval, which nothing satisfies; `J2`/`TU2` re-prove them with `C²` on the open
interval plus bounded derivatives, which is what `w` and `√w` actually have.

## Obligation B — the exact residual certificate: **all ingredients proved, assembly open**

Proved, all exact and kernel-checked:

| fact | theorem |
| --- | --- |
| `A₀u + r₀ = 1` on `I`, `M = 20` | `r0_identity` |
| `‖r₀‖_∞ < 2.1710808e-5` | `r0Sum_lt_decimal` |
| `‖r₀''‖_∞ < 0.005982627` | `r0Sum2_lt_decimal` |
| `∫_I r₀²` exactly; `‖r₀‖₂ ≤ 7.8749770e-10` | `integral_r0_sq`, `r0_l2_le` |
| `∑_{k≥20} a_k`, `∑_{k≥20} d_k` geometric tails | `AristotleV.aCoef_tail_le`, `dCoef_tail_le` |
| `‖q‖_∞ ≤ 80.963` on `[-1,1]` | `q_abs_le` |
| `‖z‖_∞ ≤ (9/5)‖g‖_∞`, `‖z‖₂ ≤ (9/5)‖g‖₂` | `AristotleR.resolvent_*` |
| truncated kernel is a half-line polynomial | `TruncKernel.*` |
| the whole certificate arithmetic, margin `4.4e-13` | `CertArith.zpp_arith` |
| that arithmetic implies `w'' < -0.59326318` | `CertArith.concavity_closes` |

**The remaining gap** is the analytic assembly that ties them together.
`z_resolvent_eq` is now proved (`ZetaLean/Pub1/ZResolvent.lean`) — pure algebra
from `IsProfile.eq_on_I` and `r0_identity` — leaving four signatures:

```lean
-- z := w - uPoly,  Eu s := ∫_I (F₁ - truncKernel)(s-t) · uPoly t dt
theorem Eu_bounds : ‖Eu‖_∞ ≤ rhoC * usupC ∧ ‖Eu‖₂ ≤ rhoC * usupC
theorem Eupp_bound : ‖(Eu)''‖_∞ ≤ stC * usupC          -- = ‖(q - q_M) * u‖_∞
theorem zpp_identity : z'' = r₀'' - (Eu)'' - 2z - q*z
theorem zpp_bound (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    |deriv (deriv w) s - deriv (deriv uPoly) s| < 6060899845 / 10 ^ 12
```

`Eupp_bound` needs no new analysis: `(Eu)'' = (q - q_M) * u` is the difference of
`pub1_kernel_second_deriv` and `TruncKernel.truncKernel_second_deriv`, and the
`2u` delta terms cancel because `fKerM'(0) = fKer'(0) = 1`.  What is genuinely
unwritten is the `Eu` sup/`L²` bounds (a `tsum` split like `QBound`'s) and the
application of the resolvent estimates, whose `Aristotle/R` form asks for a
*minimal* `Bz` and so needs the sup constructed as an `sInf`.

Downstream of `zpp_bound`, still to do: weaken `Concavity.lean`'s
`strictAntiOn_w` / `radial_antitone` from `Differentiable ℝ w` on all of `ℝ` to
the interior (`w` is not differentiable at `±1/2`), then the radial-monotonicity
field of `sourceWindow_taper`, then `member`, then the two principal theorems.

## The lesion test

`Pub1LesionTest.lean.expected-fail` must not compile, and does not: with the
residual bound inflated by 101 the arithmetic step reduces to `False`.

## Provenance

`ZetaLean/Pub1/Aristotle/` came from Harmonic's Aristotle (ids in
`lean/ARISTOTLE-RUNS.md`).  Per `lean/proof_adapter.py` the service's own claim
is input, not evidence: each passed the static refusal scan and `lake build`
here first.
