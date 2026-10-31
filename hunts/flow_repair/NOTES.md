# NOTES: what the probe measured

Run of 2026-08-07, `probe.py`, raw numbers in `results.json`. Probe
language throughout: *measured*, *observed*. Everything here is the
accurate regime (mpmath floats with measured cross-route defects); no
enclosure claims are made anywhere in this hunt.

## Correction (2026-10-19): an absolute floor in the DH weight

Added after the original record. Every section after this one is the
original text, unchanged; where a number in it is affected, this section
says so.

**The defect.** `omega_dh` dropped every term n·e^(−πn²x/5) below an
absolute floor 10^-(P+8), P the ambient precision, so Φ_DH was exactly 0
wherever e^(−πx/5) fell below that floor: for u > ½·log(5(P+8)·ln 10/π),
x = e^(2u). The same construction as `hunts/jensen_clock`'s, where hunt
#135's Davenport-Heilbronn gate found it (`hunts/jensen_wedge/DH_GATE.md`
section 1) and its own correction fixed it (PR #315).

**The fix.** `omega_dh` now factors out the leading term and stops at
2^-(prec+20) of it, jensen_clock's corrected logic, reimplemented. The
original is kept as `omega_dh_absolute_floor`, for the record and as a
planted fault. `test_flow_repair.py` checks the fixed weight against a
cutoff-free 30-term sum past the cut at the pair-1 flow's precision (P = 64,
cut at u = 2.788, where the original returns 0) and in the moment
∫u⁸⁰⁰Φ_DH du at dps 75 (the original is off by 1.7e-4 in its log); with the
original floor put back, 4 of its 5 tests go red.

**What the floor reached here: no quadrature node.** `DHFlow` evaluates the
weight at dps + 10 digits, so its floor sits at 10^-(dps+18), and ends its
integral where the integrand of its design box (t ≤ 0.12, |Im z| ≤ 1.6)
falls to 10^-(dps+12). In every rule a published stage built, that limit
stops short of the cut, by 0.0125 in u at dps 40 (validate) closing to
0.0013 at dps 165 (survey pair 9); the default rule would first cross it
between dps 250 and 300. So no node ever carried weight 0. The floor did cut the n = 2
term early in a band of u, so the weights at the nodes move with the fix,
by at most 5.7e-45 relative (dps 40) down to 1.7e-138 (dps 165), and H and
H′ at sampled contour points by at most 9.2e-44 relative (measured with
both cutoffs on every published rule).

**Re-verification, 2026-10-19.** Every stage that evaluates the DH weight
was re-run with the fix on GitHub Actions (run 39355357518, `RUNS.md`) and
every field compared with `results.json` by `compare_rerun.py`; the report
is `rerun_2026-10-19.json`. 12 stage blocks, 370 fields, 364 identical as
printed (only `seconds` is skipped), 6 changed, all in one figure.

- **pair1, precision, lesions, survey pairs 2 to 9: identical in every
  field.** Every t\* in §1 and §5 to its last stored digit, the headline
  Λ_DH ≥ 0.0576518 (pair 5), the precision spread 0.0, the t = 0 checks of
  §0 (y₀ to 24 digits, winding defect 8.5e-29, Δ(0) + 4y₀² = 4.7e-29), the
  slope 9.248 and the lesion rows of §4 stand as printed.
- **validate: one published number changes.** §0's "relative defect
  ≤ 4.2e-51 for |u| ≤ 0.5 at dps 50" re-runs as **≤ 7.1e-51**
  (`phi_evenness_defect`, relative, at u = 0.1, 0.2, 0.35, 0.5: 2.35e-51,
  0.0, 4.15e-51, 3.47e-51 become 7.05e-51, 0.0, 5.53e-51, 6.94e-51; the
  absolute column moves the same way). Both are rounding, not the floor: at
  every probe, each side of the check is within 4 units of 2^-169 = 1.3e-51
  (the dps-50 rounding unit) of a 120-digit reference, under either cutoff;
  the fixed sum multiplies by the factored-out leading term, which rounds
  differently. What it supported, Φ_DH even to working precision, stands.
  The rest of validate is identical (route agreement 7.2e-41, |c − 1| =
  4.2e-42, |a − 1| = 2.0e-18, the ζ sibling 5.4e-42, Φ_DH(0) to 25 digits).
  `results.json`'s `validate` block keeps the original values.
- **Not re-run: ode and figure.** They evaluate no DH weight; they read
  the polished zeros (from `dh_f`, no weight) and the PDE t\* values, which
  re-ran identical, so §3's table stands by construction.

Readers of these numbers: `hunts/jensen_clock` reads the pair1 and
precision blocks; its three stages that were waiting on this were re-run on
the re-run blocks and are unchanged (its RESULTS.md, "Correction").
`hunts/li_dh_onset` reads `results.json` only. `hunts/lambda_dh_bounds`
builds `DHFlow` at dps up to 205, also short of the cut, so its flows lose
no node either; its own published figures were not re-run here.

## 0. The instrument is telling the truth (stage `validate`, `pair1` t=0)

- **Route agreement.** H₀^{DH}(z) by Φ_DH-quadrature vs
  `zeta.epstein.completed_dh(1/2+iz)` by Hurwitz zeta, two code paths
  sharing nothing, agree to **7.2e-41 worst** over real and complex probes
  at dps 40. The constants in H₀(z) = c·Ξ_DH(a·z) fitted from the data:
  |c − 1| = 4.2e-42, |a − 1| = 2.0e-18 (stencil-limited). So (c, a) = (1, 1):
  the DH flow normalisation is *cleaner* than ζ's H₀(z) = (1/8)Ξ(z/2),
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
the Davenport–Heilbronn Ξ onto the real axis at a landing time t\*, read
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

**Measured lower bound: Λ_DH ≥ 0.0576518, attained by pair 5**, not the
famous pair 1, which comes third. Prediction P4 (the crown goes to the
height-240 quadruple, the deepest β in the surveyed list) held; the other
deep pairs, 6 and 9, land at 0.0447 and 0.0427, well behind.

Scope, stated plainly: nine quadruples out of infinitely many. Nothing
here bounds Λ_DH from above; the measured maximum is a floor, not the
constant. And the strip confinement −1 < Re s < 2 (pinned by the |aₙ|
argument in `zeta/epstein.py`) means every DH pair sits at y₀ < 1.5, so
no *single* pair can land later than y₀²/2 < 1.125 under dynamics in
which every zeta-like neighbour accelerates the landing, an observation
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
  [0, 0.2], the interval that bracketed Λ_ζ before Rodgers–Tao proved
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
the bare N-body dynamics ż_k = 2Σ 1/(z_k − z_j), no Dirichlet series, no
character, no conductor, just the measured starting positions, in the
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
(window ±40, density-model tail, RK4 step), the ~1% target of P3 beaten
by a factor of ~25. **The flow-repair time contains no information about
the Davenport–Heilbronn function beyond where its zeros start.** Any
entire function with the same zero layout would repair on the same clock.
Λ-style quantities measure a configuration's geometry; what would be
special about ζ (if RH holds) is that its configuration needs no repair,
a restatement of RH, not an explanation. This is docs/18's
position-sensitivity lesson meeting docs/09's gate #3 on the flow axis.

## 4. Lesions: the refusals fire, and the newborn pair hides

- **Clipped contour** (circle around one member of the pair): refused,
  `contour holds N=1 zeros, expected 2`. The moment machinery cannot be
  silently fed half a pair.
- **Grazing contour** (radius exactly y₀, passing through both zeros):
  winding came back ≈ 1.8e9, grotesquely non-integer, and was refused.
  Both failure modes are loud, never quiet.
- **Post-landing blindness, with a clock.** Just after the landing the
  two newborn real zeros sit closer than the default sign-scan grid
  (mean_gap/20 ≈ 0.0744 here). Swept through five grid phases (hunt #3's
  lesson): at t = 1.002·t\* (gap/step = 0.36) only **2 of 5 phases** see
  the pair; by t = 1.03·t\* (gap/step = 1.38) all five do. The repair is
  invisible to the standard instrument for the first ~1–3% of t\* past
  the landing, while the contour count N = 2 never wavers. Sign scans
  bound from below; the argument principle decides, the same moral as
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
survey seeds). The measurement itself: Λ_DH ≥ 0.0577, repair times for
nine off-line quadruples, the null-control agreement, appears
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

## 7. The v6 census sweep: every off-line pair below height 20,000 (2026-10-30)

Added after the original record; nothing above changes. `census_sweep.py`
lands all 1,268 off-line pairs of the Davenport-Heilbronn v6 census (Nathan
Berzai, Zenodo 10.5281/zenodo.23585903, data CC-BY-4.0) with §3's null
control, raw numbers in `census_sweep.jsonl`, pins in `test_census_sweep.py`.
Grade: **measured**, a float ODE model of zero motion. §3 compared it with
the measured flow only up to height 412; above that it is the model alone.

**Inputs, no zero search.** The window zeros come from the replayed census
receipts in `data/dh_v6_replay/receipts.tar.gz` (25,078 on-line ordinates;
window closure exact in all 400 windows, `docs/46`), the pairs from the
census table in the same tarball, both read after the manifest hash check.
Completeness is the census's own: `docs/46` replayed it by one route, the
author's verifier, which stops short of hardened (its section 3).
The dynamics are a numpy transcription of `probe.ode_null_control`, same
window ±40, 800 RK4 steps, mirrors, tail and t_end. The full census takes
about three minutes on 16 cores (`RUNS.md`).

**Checks.** The transcription equals `ode_null_control` on identical inputs
to 1e-13. Pairs 1 to 5 from the receipts reproduce §3's `results.json`
landings to 5e-8 relative with identical zero counts. `hunts/lambda_dh_exact`
landed the same model on windows it built itself (sign scan, located
off-line zeros, closed strip counts): its 21 pairs below 10^4 agree to
1.1e-6 and its 19 pairs in [10^4, 2·10^4] to 4.3e-6. Deleting one on-line
zero next to pair 5 moves its landing by more than 1e-4, so the
reproduction check can fail.

**Results.** 1,268 of 1,268 pairs land, every one before its isolated
y0²/2. Three pairs (v6 ranks 1266 to 1268) are flagged `edge`: their window
runs past the census top, which lacks the zeros above 20,000. All three
are shallow, landing near 0.01. The latest landings:

| rank | v6 n | height γ | y0 | t\*_ODE | y0²/2 | shave |
|------|------|----------|----|---------|-------|-------|
| 1 | 5 | 240.40 | 0.36953 | 0.05766566 | 0.0682764 | 15.54% |
| 2 | 107 | 2442.53 | 0.39775 | 0.05586457 | 0.0791026 | 29.38% |
| 3 | 24 | 857.30 | 0.35611 | 0.05065116 | 0.0634070 | 20.12% |
| 4 | 12 | 531.28 | 0.34695 | 0.05033976 | 0.0601885 | 16.36% |
| 5 | 21 | 783.65 | 0.35300 | 0.05000168 | 0.0623050 | 19.75% |

In the ODE model, the pair at height 240.4 lands last of all 1,265 non-edge
pairs, so P4's winner stands across the census, extending
`hunts/lambda_dh_exact`'s census of the 21 pairs with β > 0.85 below 10^4 (its
RESULTS.md section 8.6) to every depth below 20,000. The deepest pair (height
2442.53) has the largest isolated estimate and is shaved 29.4% into second
place.

*Added at landing, 2026-10-31.* This sweep is also the antecedent that
`hunts/lambda_dh_exact`'s own P4 ("a complete census to 10^4 raises the best
landing") lacked: its RESULTS.md section 8.7 grades it "unresolved, evidence
against" because pairs with y0 at most 0.35 were never landed. With every v6
pair below 10^4 landed by the same ODE, the best landing is not raised. That
verdict belongs to that hunt and is not changed here.

**The deep predictions file.** `deep_predictions_v1.json` (SHA-256
2616116f…) holds a crowding-model refit's predictions for the ten pairs with
y0 > 0.37. Its estimand is the flow landing; it is compared here with the ODE
landing, which §3 tied to the flow only below height 412.

*Corrected at landing, 2026-10-31.* This paragraph first called the file
frozen and said it was written before any of the ten was landed. The tree
supports neither. The file first appears in the commit that compares it,
with no timestamp, and neither its source (`source_sha256` 18010823…) nor
the refit's code is committed, so the predictions cannot be reproduced from
here. The ODE landings of all ten pairs had been in the tree since
2026-10-26 (`hunts/lambda_dh_exact/census_1e4.json` and
`census_runs/full_r2/census_1e5.json`), and this sweep reproduces them to
1e-5 (`test_census_sweep.py`). Read the table as a measured disagreement
between a committed file and the ODE, not as a blind test of the model.

| v6 n | height γ | y0 | t\*_ODE | predicted | over |
|------|----------|----|---------|-----------|------|
| 107 | 2442.53 | 0.39775 | 0.0558646 | 0.0566378 | 1.38% |
| 302 | 5833.28 | 0.37409 | 0.0475998 | 0.0488878 | 2.71% |
| 442 | 8235.59 | 0.37534 | 0.0466194 | 0.0480719 | 3.12% |
| 465 | 8561.59 | 0.38364 | 0.0434682 | 0.0494872 | 13.85% |
| 670 | 11535.29 | 0.37960 | 0.0414844 | 0.0478231 | 15.28% |
| 725 | 12313.80 | 0.38663 | 0.0466823 | 0.0488729 | 4.69% |
| 848 | 14063.60 | 0.37278 | 0.0427576 | 0.0460308 | 7.66% |
| 1028 | 16620.38 | 0.37419 | 0.0444943 | 0.0457942 | 2.92% |
| 1081 | 17363.41 | 0.37377 | 0.0350859 | 0.0455968 | 29.96% |
| 1211 | 19239.53 | 0.39063 | 0.0424246 | 0.0481579 | 13.51% |

All ten predictions are too high and none lands inside its parameter-only
95% band: mean overprediction 9.51%, maximum 29.96%. The bands carry
parameter uncertainty only, not model error, so the miss points at the
model's form rather than its fitted constant (a reading, not a test).

Scope: one census to height 20,000, a measured maximum over 1,265 pairs,
a floor for Λ_DH as in §1 and never its value.

## Standing-checklist accounting

- **Rival**: this hunt runs *on* the rival, and the rival-as-validation
  leg (§0) makes the instrument reproduce ζ's sibling module first.
- **Decoy/surrogate**: the arithmetic-free N-body integration (§3) is the
  matched null, and it *explains the effect*, the honest outcome for a
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
