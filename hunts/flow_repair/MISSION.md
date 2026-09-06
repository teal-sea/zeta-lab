# MISSION: Repairing the counterexample, the heat flow clock on Davenport–Heilbronn

**Agent Persona:** The Hunter (unsupervised-fun edition, second outing)
**Scope:** `hunts/flow_repair/` only. Nothing outside this directory is
modified except the case-log entry in `hunts/README.md`.

## Objective

The lab's two showpiece arms have never met. `zeta/heatflow.py` runs the
de Bruijn–Newman flow H_t = exp(−t∂²)H₀ on the Riemann Ξ, where increasing
t pulls complex zero pairs onto the real axis, Λ is the last landing time,
and RH ⟺ Λ = 0. `zeta/epstein.py` owns the Davenport–Heilbronn function,
zeta's functional equation, real coefficients, a real Hardy Z, **and zeros
off the critical line**. The flow has only ever been pointed at the function
that (as far as anyone knows) needs no repair.

Point it at the one that provably does. The hunt asks one question:

> **How long does the backward-heat flow take to repair the
> Davenport–Heilbronn counterexample, pair by pair, measured, with the
> collision times read off a quantity that is analytic through the
> collision?**

Each off-line quadruple ±(γ ∓ iy₀) of the DH Ξ-analogue lands on the real
axis at some t\*. Every measured t\* is a lower bound for the DH analogue of
the de Bruijn–Newman constant, Λ_DH := inf{t : H_t^{DH} real-rooted}.
Rodgers–Tao proved Λ_ζ ≥ 0 ("RH, if true, is barely true"); the flow-repair
times measured here put a number on the other side of the same coin: DH
fails RH, and *in flow time* it fails it barely.

## The construction (derived in the probe, not recalled)

F(s) = (π/5)^{−(s+1)/2} Γ((s+1)/2) f(s) is entire with F(s) = F(1−s) and no
pole terms (unlike ζ, the counterexample is *cleaner* here). The Mellin
split of Σ n aₙ e^{−πn²x/5} at x = 1 should give

    Ξ_DH(z) := F(1/2 + iz) = ∫₀^∞ Φ_DH(u) cos(zu) du,
    Φ_DH(u) = 4 e^{3u/2} Σ_{n≥1} n aₙ exp(−π n² e^{2u} / 5),

with Φ_DH even exactly when ω(1/x) = x^{3/2}ω(x), i.e. exactly when the
functional equation holds. **The probe does not trust this derivation**: the
constants (c, a) in H₀^{DH}(z) = c·Ξ_DH(a·z) are *measured* from the data,
`H0_vs_Xi`-style, and the evenness of Φ_DH is measured as a defect of the
raw unfolded series. Off-line zeros map to z = γ − i(β−1/2): complex zeros
of H₀^{DH} at distance y₀ = β − 1/2 from the axis.

## Instruments

`probe.py` → `results.json` + `flow_repair.png`. Vocabulary: *measured,
observed, decided*; the reserved enclosure word appears nowhere in this
directory (everything here is the accurate/float-of-mpmath regime, this
hunt makes no enclosure claims at all).

1. **Route agreement at t = 0.** H^{DH}(z, 0) by quadrature vs
   `zeta.epstein.completed_dh(1/2 + iz)` by Hurwitz zeta, two code paths
   sharing nothing. Constants (c, a) fitted and snapped to rationals.
2. **Contour moments through the collision.** For a circle around a pair,
   p_k = (1/2πi)∮ z^k H'/H dz gives N = p₀ (must be an integer, must be 2),
   e₁ = p₁, and the discriminant Δ = 2p₂ − p₁². For a conjugate pair
   Δ = −4y² < 0; after landing, Δ = gap² > 0; **Δ(t) is analytic through
   the collision** even though the individual zeros have a square-root
   branch point there. t\* = the root of Δ(t). No root-chasing near a
   double zero, ever.
3. **The survey.** t\* for the off-line quadruples the literature names
   (Spira 1994: heights 85.70, 114.16, 166.48, 176.70; Balanzario–
   Sánchez-Ortiz 2007: 240.40, 320.88, 331.05, 366.64, 411.80), each
   re-polished in-tree by `mp.findroot` on `dh_f` from the literature seed
   before use, with a winding-number identity check.
4. **Null control (the surrogate).** The N-body zero dynamics
   ż_k = 2Σ_{j≠k} 1/(z_k − z_j), no arithmetic in it, just the measured
   t = 0 zero configuration, integrated in the collision-safe variable
   Q = Δ_pair/4 (dQ/dt = 2 − 4Q Σ_w 1/((x−w)² − Q), analytic through
   Q = 0). If this predicts the PDE's t\* to ~1%, the repair time is
   generic zero-geometry, not arithmetic.
5. **Rival = instrument validation on ζ.** The same generic-Φ evaluator fed
   `zeta.heatflow.Phi` must reproduce `zeta.heatflow.H_t` to quadrature
   accuracy, and the moment machinery around two *real* ζ-flow zeros must
   return integer N = 2 and Δ > 0 matching `zeros_of_H_t` positions.
6. **Lesions.** (a) A contour deliberately clipping one pair member: the
   integer-winding check must refuse, loudly. (b) After landing, the two
   newborn real zeros form a close pair invisible to a default
   mean-spacing/20 sign scan, measure how long past t\* the standard
   instrument stays blind (hunt #3's blind spot, now with a clock on it).
7. **Precision response.** t\* re-measured at three working precisions and
   two contour node counts; Δ(0) against −4y₀² from the 50-digit pinned
   zero. A real quantity pins; an artifact wanders.

## Pre-registered predictions (written before any flow was run)

From the pinned/literature zeros, y₀ = β − 1/2, naive isolated-pair model
t\*₀ = y₀²/2 (from ẏ = −1/y, the mirror's pull alone):

| # | height γ | β (lit.) | y₀ | t\*₀ = y₀²/2 |
|---|----------|----------|------|--------------|
| 1 | 85.6993 | 0.808517 | 0.308517 | **0.047594** |
| 2 | 114.1633 | 0.650830 | 0.150830 | 0.011375 |
| 3 | 166.4793 | 0.574356 | 0.074356 | 0.002764 |
| 4 | 176.7025 | 0.724258 | 0.224258 | 0.025146 |
| 5 | 240.4046 | 0.86953 | 0.36953 | **0.068276** |
| 6 | 320.8764 | 0.81955 | 0.31955 | 0.051056 |
| 7 | 331.0502 | 0.76822 | 0.26822 | 0.035971 |
| 8 | 366.6409 | 0.62850 | 0.12850 | 0.008256 |
| 9 | 411.7967 | 0.81587 | 0.31587 | 0.049886 |

Predictions this hunt can lose on:

- **P1.** Every measured t\* lands strictly *below* its t\*₀: every zeta-like
  zero of the configuration (mirror, real neighbours, mirror quadruple)
  pushes the pair toward the axis, so crowding only accelerates. Expected
  shave: ~5–15%, growing with height as the real-zero density log-grows.
- **P2.** dΔ/dt at t = 0 is ≈ 8 for an isolated pair; measured slope is
  8 + 16y₀²Σ_w 1/((x−w)²+y₀²) + (mirror terms) ≈ 9–10 for pair 1.
- **P3.** The ODE null control reproduces each PDE t\* to ~1%: the repair
  clock reads *zero geometry*, not arithmetic.
- **P4.** The survey's max, the measured lower bound for Λ_DH, comes from
  **pair 5** (height 240.4), not the famous pair 1, at t\* ≈ 0.06 ± 0.005.
- **P5.** Λ_DH ≥ max t\* ≈ 0.06, which sits *inside* [0, 0.2], the interval
  that bounded Λ_ζ before and after Rodgers–Tao. In flow time, the
  counterexample is closer to satisfying RH than ζ was known to be to
  either side of it for most of a century. Gate-#3 moral, quantified: "Λ is
  small" is not a property that separates ζ from a function where RH is
  false.

## Rules of engagement

Repo-wide rules (`.venv` python, `mp.workdps`, Agg before pyplot, honest
scope). Λ_DH here is a *defined quantity for a rival function*; measuring
it neither supports nor threatens RH (Littlewood, `docs/08`), and a
measured collision time is a lower bound for a sup over infinitely many
quadruples, the probe measures nine and claims nothing about the tail.
All numbers are the accurate regime: mpmath floats with measured
cross-route defects, no enclosures. If a computation here appears to settle
anything open, the correct inference is a bug.
