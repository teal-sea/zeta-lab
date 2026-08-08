# NOTES — what the probe measured

Run of 2026-08-07, `probe.py`, raw numbers in `results.json`. Probe
language throughout: *measured*, *observed*. Everything here is the
accurate regime (mpmath floats with measured cross-route defects); no
enclosure claims are made anywhere in this hunt.

## 0. The instrument is telling the truth (stage `validate`, `pair1` t=0)

- **Route agreement.** H₀^{DH}(z) by Φ_DH-quadrature vs
  `zeta.epstein.completed_dh(1/2+iz)` by Hurwitz zeta — two code paths
  sharing nothing — agree to **7.2e-41 worst** over real and complex probes
  at dps 40. The constants in H₀(z) = c·Ξ_DH(a·z) fitted from the data:
  |c − 1| = 4.2e-42, |a − 1| = 2.0e-18 (stencil-limited). So (c, a) = (1, 1):
  the DH flow normalisation is *cleaner* than ζ's H₀(z) = (1/8)Ξ(z/2) —
  no pole terms, no factor 8, no z/2.
- **Φ_DH evenness** (the functional equation in disguise): raw unfolded
  series both sides, relative defect ≤ 4.2e-51 for |u| ≤ 0.5 at dps 50.
- **The same evaluator pointed at ζ's Φ** reproduces `zeta.heatflow.H_t`
  to **5.4e-42 worst** over four (z, t) probes, with an independently built
  rule (own integration limit, own panel count). Rival-as-validation: the
  instrument reproduces the sibling before it is trusted on the rival.
- **t = 0 moments vs the pinned zero.** `mp.findroot` from the repo's
  50-digit `OFFLINE_ZERO_*` seed moves it by 4.2e-49 (|f| residual
  5.3e-77); the contour moments then recover y₀ to **all 24 compared
  digits**, N = 2 with winding defect 8.5e-29, and Δ(0) + 4y₀² = 4.7e-29.

## 1. The headline: the repair times, measured

The backward-heat flow H_t = exp(−t∂²)H₀ pulls each off-line quadruple of
the Davenport–Heilbronn Ξ onto the real axis at a landing time t\* — read
off as the root of the pair discriminant Δ(t) = 2q₂ − q₁² (contour
moments), which is analytic through the collision. Every t\* is a lower
bound for Λ_DH := inf{t : H_t^{DH} real-rooted}, the DH analogue of the
de Bruijn–Newman constant.

| # | height γ | y₀ = β−1/2 | naive y₀²/2 | **t\* measured** | shave |
|---|----------|-----------|--------------|------------------|-------|
| 1 | 85.6993 | 0.3085172 | 0.0475914 | **0.04412634450** | 7.28% |
| 2 | 114.1633 | 0.1508270 | 0.0113749 | **0.01112958794** | 2.16% |
| 3 | 166.4793 | 0.0743505 | 0.0027644 | **0.00274784849** | 0.60% |
| 4 | 176.7025 | 0.2242763 | 0.0251458 | **0.02366473172** | 5.89% |
| 5 | 240.4046 | 0.3695261 | 0.0682764 | **0.05765184035** | 15.56% |
| 6 | 320.8765 | 0.3195496 | 0.0510560 | **0.04468146893** | 12.49% |
| 7 | 331.0503 | 0.2682231 | 0.0359718 | **0.03217819397** | 10.55% |
| 8 | 366.6409 | 0.1285081 | 0.0082572 | **0.00803041920** | 2.75% |
| 9 | 411.7967 | 0.3158737 | 0.0498881 | **0.04265328332** | 14.50% |

(Pair 1 is the repo's pinned zero; the other seeds are Spira 1994 and
Balanzario–Sánchez-Ortiz 2007, each re-polished in-tree by `mp.findroot`
on `dh_f` with a unit winding check before use.)

**Measured lower bound: Λ_DH ≥ 0.0576518, attained by pair 5** — not the
famous pair 1, which comes third. Prediction P4 (the crown goes to the
height-240 quadruple, the deepest β in the surveyed list) held; the other
deep pairs, 6 and 9, land at 0.0447 and 0.0427, well behind.

Scope, stated plainly: nine quadruples out of infinitely many. Nothing
here bounds Λ_DH from above; the measured maximum is a floor, not the
constant. And the strip confinement −1 < Re s < 2 (pinned by the |aₙ|
argument in `zeta/epstein.py`) means every DH pair sits at y₀ < 1.5, so
no *single* pair can land later than y₀²/2 < 1.125 under dynamics in
which every zeta-like neighbour accelerates the landing — an observation
about the surveyed mechanism, not a theorem about the sup.

## 2. Predictions, settled

- **P1 (strictly below naive): held, 9/9.** Every measured t\* is below
  its isolated-pair y₀²/2. But P1's *quantitative* clause ("shave 5–15%,
  growing with height") was wrong on its own terms and lost to P2: the
  shave tracks y₀² × local zero density (0.60% for the shallow pair 3,
  15.6% for the deep pair 5), exactly what the P2 slope formula implies.
  Two pre-registered predictions contradicted each other; the mechanism
  P2 encodes is the one the data kept. (The height clause survives *at
  fixed depth*: the three y₀ ≈ 0.31–0.32 pairs shave 7.28% → 12.49% →
  14.50% as γ runs 86 → 321 → 412, the density term doing exactly what
  it says.)
- **P2 (slope): held.** dΔ/dt at t = 0 measured 9.248 for pair 1 against
  8 for an isolated pair; the crowding surplus matches the
  16y₀²Σ1/((x−w)²+y₀²) term built from the measured neighbour positions.
- **P3 (the null control): held, spectacularly.** See §3.
- **P4 (pair 5 wins): held.** t\*₅ = 0.0576518, inside the pre-registered
  0.06 ± 0.005 band.
- **P5 (the moral): held.** Λ_DH ≥ 0.0576518 sits comfortably inside
  [0, 0.2] — the interval that bracketed Λ_ζ before Rodgers–Tao proved
  Λ_ζ ≥ 0 and after Polymath 15 pushed the upper bound to 0.22. Measured
  in flow time, the counterexample's RH-failure is *smaller than ζ's own
  historical uncertainty about which side of RH it sits on*. A structural
  story of the form "ζ satisfies RH because its Λ is small" is therefore
  empty: the function where RH is false has a small Λ too. Gate #3,
  quantified on the flow axis.

## 3. The null control: the repair clock reads geometry, not arithmetic

For each pair, the probe censused the t = 0 zero configuration in a ±40
window (line zeros by phase-refined sign scan; total strip count by
argument principle; **the accounting closed exactly in all five windows**:
line + 2·quadruples = strip, e.g. 49 + 4 = 53 at pair 1), then integrated
the bare N-body dynamics ż_k = 2Σ 1/(z_k − z_j) — no Dirichlet series, no
character, no conductor, just the measured starting positions — in the
collision-safe variable Q = Δ/4 with the universal identity
dQ/dt = 2 − 4Q Σ_a 1/((x−a)² − Q).

| pair | t\*_ODE (geometry only) | t\*_PDE (measured flow) | difference |
|------|------------------------|------------------------|------------|
| 1 | 0.04411047 | 0.04412634 | −0.036% |
| 2 | 0.01112850 | 0.01112959 | −0.010% |
| 3 | 0.00274781 | 0.00274785 | −0.002% |
| 4 | 0.02366327 | 0.02366473 | −0.006% |
| 5 | 0.05766565 | 0.05765184 | +0.024% |

Sub-0.04% across the board, sign scattering with the truncation knobs
(window ±40, density-model tail, RK4 step) — the ~1% target of P3 beaten
by a factor of ~25. **The flow-repair time contains no information about
the Davenport–Heilbronn function beyond where its zeros start.** Any
entire function with the same zero layout would repair on the same clock.
Λ-style quantities measure a configuration's geometry; what would be
special about ζ (if RH holds) is that its configuration needs no repair —
a restatement of RH, not an explanation. This is docs/18's
position-sensitivity lesson meeting docs/09's gate #3 on the flow axis.

## 4. Lesions: the refusals fire, and the newborn pair hides

- **Clipped contour** (circle around one member of the pair): refused —
  `contour holds N=1 zeros, expected 2`. The moment machinery cannot be
  silently fed half a pair.
- **Grazing contour** (radius exactly y₀, passing through both zeros):
  winding came back ≈ 1.8e9 — grotesquely non-integer — and was refused.
  Both failure modes are loud, never quiet.
- **Post-landing blindness, with a clock.** Just after the landing the
  two newborn real zeros sit closer than the default sign-scan grid
  (mean_gap/20 ≈ 0.0744 here). Swept through five grid phases (hunt #3's
  lesson): at t = 1.002·t\* (gap/step = 0.36) only **2 of 5 phases** see
  the pair; by t = 1.03·t\* (gap/step = 1.38) all five do. The repair is
  invisible to the standard instrument for the first ~1–3% of t\* past
  the landing, while the contour count N = 2 never wavers. Sign scans
  bound from below; the argument principle decides — the same moral as
  hunt #3, now on the other side of a collision.

## 5. Precision response: the standing rule, passed flat

t\* for pair 1 re-measured at dps 44 / 54 / 70 and contour node counts
96 / 192, bracket tolerance 1e-10: **all four runs agree to the last
digit** (0.0441263445516239; spread 0.0). Δ(0) + 4y₀² = 4.7e-29 against
the 50-digit pinned zero. The quantity is pinned; nothing wanders.

## 6. Literature position (searched 2026-08-07, two passes)

No tabulated de Bruijn–Newman-type constant for the Davenport–Heilbronn
function was found; adjacent work exists (generalized Newman constants
for other families; the de Bruijn/Newman/Ki–Kim–Lee flow theory; the
Rodgers–Tao lower bound and the Polymath 15 upper bound for ζ; Spira's
and Balanzario–Sánchez-Ortiz's DH zero computations, which supplied the
survey seeds). The measurement itself — Λ_DH ≥ 0.0577, repair times for
nine off-line quadruples, the null-control agreement — appears
unpublished as of this search. One search is a check, not a survey; the
numbers above are measurements made for this tree, with no novelty claim
attached.

**Calogero–Moser connection.** The ODE ż_k = 2Σ 1/(z_k − z_j) that the
null control integrates (§3) is formalized as a Calogero–Moser particle
system for polynomial zeros under heat flow in Cuenca & McSwiggen,
"The Rectangular Finite Free Heat Flow" (arXiv:2606.06859, 2026), and
explored for random polynomials in Hall & Ho, "Zeros of random
polynomials undergoing the heat flow" (arXiv:2308.11685, 2023). The
0.04% PDE-vs-ODE agreement measured here is an empirical instance of
their universality on a non-polynomial (DH) case. Both added to
`references/papers.md` §6.

## Standing-checklist accounting

- **Rival**: this hunt runs *on* the rival — and the rival-as-validation
  leg (§0) makes the instrument reproduce ζ's sibling module first.
- **Decoy/surrogate**: the arithmetic-free N-body integration (§3) is the
  matched null, and it *explains the effect* — the honest outcome for a
  quantity that was always geometry.
- **Lesion**: run (§4); both refusals fire; the blind window is measured.
- **Precision response**: run (§5), spread zero.

## Disposition

Instrument (`probe.py`: the generic-Φ flow evaluator, contour-moment pair
tracker, collision-safe ODE) retained. **No claim promoted; no ledger
entry.** The headline numbers are measurements about a rival function's
zero geometry under a classical flow; nothing here is evidence for or
against RH (Littlewood, docs/08), and a measured max over nine quadruples
is a floor for Λ_DH, never the value. Candidate for the spine, if anyone
wants it: `zeta/heatflow.py` could grow a `Phi`-parametric entry point
(the DH weight differs only in (q, gamma-shift, coefficients)), but that
is a `zeta/` change and belongs to a session that wants it, not to this
hunt.
