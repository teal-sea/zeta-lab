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
