# LEMMA: the Sonin-overlap truncation lemma, first pass (2026-10-26)

Bounded attempt (allowance: five agent-days) at the bound the brief asks
for: ‖ΔT_exact − ΔT^(n)‖₂ as a function of the mode count n, below 1.18e−2
at n = 280 on c = 2.9, or a recorded obstruction naming the step. Lineage:
bound_trunc/ (Identity A, Lemmas 1 to 3, statement O, Proposition 4). Every
statement here is an ordinary argument or a reading of the record,
**unreviewed**, and nothing in this file is pinned by a new computation
except where a test is named. Nothing here is a claim about RH.

## 1. What the record already fixes

1. The truncation error is E_n = τ_f(R_n − Π′_n) (bound_trunc/ Identity A),
   and both traces are +∞ for every n (Lemma 1), so a bound must pair them;
   it cannot bound them separately.
2. The pairing splits into mechanism 1 (controlled by Lemma 2, 2′ up to
   λ-sized terms) and mechanism 2, the operator S_∞F(1 − P)D on the prolate
   tail, whose norm does not decay in n. Statement O is the missing bound on
   its τ_f-weighted size (DERIVATION s2.5).
3. **The size any bound of mechanism 2's shape has** (Proposition 4, a
   lower bound on the window weight above the heuristic frequency
   σ_n = 2n/√3): at c = 2.9, N = 32 and n = 280, W(σ_n) = **0.1313** on the
   full window space, 11 times the decision scale 1.18e−2; on the continuous
   windows H = {Σ v_k = 0}, W₀(σ_n) = **0.0063** (bound_trunc/
   `eps_trunc.json`, `size_if_closed`; measured, mpmath and numpy).

## 2. The verdict of this pass on the target as stated

- **On the full window space the target is out of reach along this route.**
  By item 3, a bound of mechanism 2's shape is at least of the size
  W(σ_n) ≈ 0.13 at 280 modes; the edge jump of the window (Prop 4(b), the
  window v_1 with the largest |f(0)|) carries it. Closing O on the full
  space would give a number above the scale, so row D3 of PREREG s3 could
  not be reached there at 280 modes. **Status (ALIGNMENT s5): obstructed in
  a restricted class**: the class is bounds of mechanism 2's shape on the
  full space, and the step that fails is Proposition 4(b)'s edge-jump
  weight, conditional on Proposition 4 (ordinary argument, unreviewed).
  It does not show that ΔT^(n) fails to converge, or that a bound of another
  shape fails.
- **On H the target is open, with room.** W₀(σ_n) = 0.0063 at 280 modes,
  below the stored H-context of PREREG s2.4 (λ_20 = −9.7e−3 on H at the
  280-mode row). A bound of the form ε_t ≤ a·W₀(σ) + leak(σ) with a ≤ 1
  would leave about 3e−3 for ε_q + leak at 280 modes; E1 at the registered
  S' is 7.0e−4 of it. Counting on H costs at most one eigenvalue
  (interlacing), which PREREG s2.3 already reads. **Status: unresolved.**

## 3. The missing step, named, and the route this pass proposes

Statement O on H reduces (bound_trunc/ s2.5) to a **Mellin-frequency
localization** of F(1 − P)D U_n^⊥: the Mellin mass of F(1 − P)Du at
|s| < σ must be small for u orthogonal to the first n modes. Two
ingredients, each classical in form, with explicit constants still to be
derived:

- **(L1) Turning point.** For u ⊥ L_n (even Legendre degree < 2n),
  Fu(w) = Σ_{k ≥ 2n} c_k 2(−1)^{k/2} j_k(2πw). Kapteyn's inequality
  |J_ν(νt)| ≤ t^ν e^{ν√(1−t²)}/(1 + √(1−t²))^ν (0 < t ≤ 1) makes every
  term exponentially small in n where 2πw ≤ θ·2n, θ < 1, so Fu is
  exponentially small on w < θn/π, uniformly in u up to ‖u‖ and the
  Legendre-to-prolate leak sin θ_n of Lemma 2′ (not computed in the record).
- **(L2) Non-stationary phase.** For h supported on w ≥ w₀ whose oscillation
  is e^{±2πiw} times a symbol (the exact finite IBP form of ta_mellin's
  docstring for polynomial modes), ĥ(s) = ∫ h(w) w^{−1/2−is} dw has no
  stationary point when |s| < 2πw₀(1 − δ); integration by parts gives an
  explicit decay. Together with (L1), the Mellin mass of the tail modes
  below σ ≈ 2θn is exponentially small, with constants from the IBP.

Pairing (L1, L2) with Proposition 4(c) at σ = 2θn gives a candidate
ε_t(n) = a·W₀(2θn) + leak(n, θ). **Not done in this pass:** the constants in
(L1) for the computed modes (which needs Lemma 2′'s sin θ_n from kernel/'s
coefficients), the symbol bounds in (L2), and the choice of θ; the
heuristic σ_n = 2n/√3 corresponds to θ = 1/√3 and is not derived. The
rigorous W₀ also needs replacing Prop 4(c)'s closed-form upper bound, which
is about 20 times the measured λ_max at n = 280 (4K₂/(3πL(σ − κ_N)³) = 0.13
at σ = 323), by a ball enclosure of λ_max(M_σ) on H, which is computable
(M_σ's entries are closed forms in Si and Ci).

## 4. Status and allowance

First pass only: about two agent-hours of the five agent-days, spent on
reading the record and fixing what it already decides (s2) and on naming
the step and its route (s3). **ALIGNMENT s5: obstructed in a restricted
class on the full space (s2, first item); unresolved on H; paused by
allocation at the end of this dispatch**, not abandoned. The next unit, if
funded: the ball enclosure of W₀(σ) on H at n = 280 (minutes of compute),
then the constants of (L1) and (L2), which decide whether a·W₀ + leak can
fall below about 6e−3.

## 5. The tail-mass lemma, first pass (2026-10-26, second unit)

Asked for by the coordinator (RUNS.md s6, (B)): a bound on the Mellin tail
mass m(S) = (1/2π)∫_{|s|>S} ρ_Q, which enters E1 as κ(S)·m(S). bound_quad/'s
Prop 2 used m ≤ nvec.

**Outcome: the step closes as an identity, not a lemma, for the trapezoid
rule of amendment 1.** By Poisson summation (BOUNDS.md s3.2), the sum over
all nodes is exact up to aliasing: (Δ/2π) Σ_{k∈ℤ} ρ_Q(kΔ) = nvec +
Σ_ij G^{−1}_ij alias_ij. Since ρ_Q ≥ 0 pointwise, the omitted part is

    (Δ/2π) Σ_{|kΔ|>S'} ρ_Q(kΔ) = nvec + alias − (Δ/2π) Σ_{|kΔ|≤S'} ρ_Q(kΔ),

and the inner sum is computed in balls by the run itself (`rebuild.py`
accumulates it per family, `assemble` forms the tail). So E1 becomes
a posteriori: κ(S') times the tail mass the run actually leaves, with no
estimate of the modes' decay at all. **Grade: derived (Poisson summation
plus positivity), unreviewed; implemented and exercised on the toy
(`test_rebuild.py::test_inner_mass_and_eps_q`).** It needs only what P3
already needs: G exactly, so it inherits P4's open step for the b family.

**How large it is, measured** (`tailmass.py`, `tailmass.json`). The ζ hats
have a closed form (Tate's local functional equation for the [0, ∞) part,
the power series of Fξ for the [0, 1] part), checked against the ball hats
of `rebuild.ModeTable` to about 1e−12 on the toy modes. At 280 modes the ζ
family's tail mass is **m_z = 40.1, 21.8, 8.3, 5.0 at S = 1200, 2266.1, 6000,
10^4**, below Σ_n (4n + 1)/(πS) at every S, by 3.3 percent at S = 1200 and by at most 1 percent from 2266 up, against the crude 280. Per
mode, τ_n(S) ≈ (4n + 1)/(πS): the oscillation tail of A_n sin(2πv)/v with
A_n² = 4n + 1. **Grade: measured (float64, one route for the masses, two
routes agreeing on the hats).** The b family's tail mass is not measured
(b̂ has no closed form). The re-pricing assumes it follows the same model,
and the run's own sums replace the assumption.

**What it buys.** At the record's E1 target 7.0e−4, S' falls from 10^4 to
2,700 for the 280-mode rebuild, and the estimate from about 155 to about
28 core-hours. The sweep re-prices from 341 / 869 / 2,398 / 3,636 to
**72 / 209 / 658 / 844** core-hours (RUNS.md s8). **ALIGNMENT s5 status:
the tail-mass step is closed as an identity (conditional on P4 for the b
family). The 3-agent-day allowance was not needed beyond this pass.**
