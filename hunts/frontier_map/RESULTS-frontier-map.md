# RESULTS — the frontier map

**Status: a map, not a result.** Every computed number below was produced by
`frontier.py` (optimiser shared with `wide_search`), cross-checked against
the paper's closed form where one exists, and run through the controls in
`probe.py`. Every non-computed number carries a line citation to the
10 August 2026 paper (*More than two thirds of the zeros of the Riemann zeta
function lie on the critical line*; URL in `../wide_search/HANDOFF.md`) or to
a `wide_search` RESULTS file, with that file's caveats inherited. Nothing here
is evidence for or against RH; the paper itself states that nothing in its
method distinguishes "two thirds" from "all" (§7.5(a)).

Reproduce everything:

    .venv/bin/python hunts/frontier_map/frontier.py --json --figure
    .venv/bin/python hunts/frontier_map/probe.py

The picture is `figures/frontier_map.png`; the machine-readable map is
`frontier_map.json` (regenerated, not hand-edited).

## 1. The λ-landscape (computed here)

The method has one dial: the bandwidth λ ≤ 1 of the pair-correlation data it
consumes. For each λ the optimal window problem is a Rayleigh quotient
(paper eq. 7.3, kernel-generalised as in `../wide_search/xiprime.py`), solved
in an even polynomial basis. Measured, on the grid λ = 0.05 … 1.00:

| quantity | ζ (Montgomery F) | ξ′ (Farmer–Gonek–Lee F₁) |
|---|---|---|
| onset λ₀ where H > 0 first | 0.550194 | 0.513320 |
| H at the wall λ = 1 (simple, on line) | 0.6725007037 | 0.8686415005 |
| Hd at λ = 1 (distinct) | 0.8362503518 | 0.9343207503 |
| monotone increasing on (0.35, 1] | observed, 0 decreases | observed, 0 decreases |

The certificate is empty for λ ≤ 1/2 (paper §7.5(a): "nothing at λ ≤ ½");
the measured onsets sit just above that line, and the ξ′ kernel switches on
earlier and runs higher everywhere — consistent with F₁ ≤ F pointwise where
it matters.

**Cross-check (control 1).** For ζ the paper solves the problem in closed
form (eq. 7.4): c\*\_λ = √2·tanϑ/(1+ϑ·tanϑ), ϑ = λ/√2. Max deviation of the
numeric curve from the closed form over the whole band: **9.5e-15**. The
closed form was not used in building the optimiser. A lesion — the same
comparison against eq. (7.4) with its √2 mis-set to 1.5 — shows a minimum
deviation of **1.5e-2**, twelve orders larger, so the agreeing comparison is
capable of disagreeing (control 3). Both λ = 1 constants are stable to
< 6e-15 under a basis/quadrature ladder (control 4), and match the paper's
Theorem D and `RESULTS-xiprime.md`'s sharp constant respectively.

## 2. The fixed points (cited, not computed)

Prior art and ceilings, as pinned in `frontier.py:REFERENCE_BARS` with
sources and caveats. Highlights:

- **ζ, Levinson's line**: 1/3 (Levinson 1974) → 2/5 (Conrey 1989) → 5/12 ≈
  0.4167 (PRZZ 2020, standing record before the paper). The paper's
  Theorem A lifts the unconditional on-line proportion to 2/3, and its
  Theorem D to 0.6725007 — by the *other* line (pair correlation), which had
  been RH-conditional since Montgomery 1973.
- **ζ, the ceiling**: no configuration-by-configuration certificate on
  bandwidth-one data can deliver more than **0.68185** (Remark 1.1).
  Standing caveat from `../wide_search/RESULTS-pair-ceiling.md`: the
  published N=256 extremal law delivers this only for certificates with
  |r′(1)| + ∫|r″| ≤ 8.38043; the paper's bare sentence elides that
  hypothesis.
- **ξ′**: Wu 2015 has 0.86957 unconditionally for zeros merely *on* the
  line; the method's 0.8686415 carries simplicity and falls short of Wu's
  bar by 9.285e-4 with no admissible window able to close it
  (`RESULTS-xiprime.md`). The 0.79874 attributed to Conrey 1989 is carried
  as the paper's attribution only — `wide_search` could not locate it in
  that paper.

## 3. The lanes: where the frontier is open, closed, blocked, walled

Coordinates in `frontier_map.json:open_lanes`.

1. **Open — ζ attained-to-ceiling, the interval (0.6725007, 0.68185).**
   Width 9.3e-3. The scalar-moment joint-window LP collapses to the left
   endpoint exactly (PR #12); what remains is the full-data LP over marked
   periodic configurations. This is the one lane where bandwidth-one data
   might still yield something, and `../wide_search/HANDOFF.md` THREAD 1
   is its operating state.
2. **Closed negatively — ξ′ vs Wu.** The variational problem is solved
   sharp (H\* = 0.86864150052976706411); the gap of 9.285e-4 to Wu's bar is
   a property of the method, not of the window search.
3. **Blocked — ξ^(κ), κ ≥ 2.** Bian 2008 gives F_κ as a ~14-fold partition
   sum with no closed form and no tail bound; the 11-term truncations fail
   exactly at the λ = 1 optimum the map needs (impossible proportions
   1.198, −2.64 for κ = 2, 3). Either a closed form or a real tail bound
   reopens the lane (`RESULTS-higher-derivatives.md`).
4. **Walled — λ > 1.** Remark 1.1: reaching 0.70 / 0.80 / 0.90 by this
   route needs pair-correlation input on Fourier support out to ≈ 1.04 /
   1.26 / 1.70 — i.e. Hardy–Littlewood-strength information about prime
   pairs. The wall is drawn on the figure in the shaded region; the three
   crosses are the paper's own coordinates for what lies beyond it.

## 4. What the map says, in one paragraph

Both computed curves rise steeply from their onsets just above λ = 1/2 and
hit the λ = 1 wall while still climbing — the method is input-limited, not
optimisation-limited. For ζ the remaining slack *within* bandwidth-one data
is the 9.3e-3 interval of lane 1 and no more; for ξ′ even the sharp optimum
stops 9.3e-4 short of the strongest same-strength comparison bar. Every
larger number on the chart is either RH-conditional (Montgomery–Taylor,
CGdL) or on the far side of the shaded wall. A future session that wants to
move anything on this map has exactly two doors that are not walled:
lane 1's full-data LP, and lane 3's tail bound for Bian's F_κ.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| cross-check (independent route) | `probe.crosscheck_zeta_curve` | max dev 9.5e-15 over λ ∈ [0.1, 1] |
| lesion (planted mis-constant) | `probe.lesion` | min dev 1.5e-2 — seen |
| convergence response | `probe.convergence_response` | ζ: ≤ 1.5e-14 per rung, final vs pinned 5.8e-15; ξ′: ≤ 1.8e-15, final vs pinned 1.1e-16 |
| monotonicity on refinement grid | `probe.monotonicity` | 0 decreases, both kernels |
| rival | not run here | the paper's §7.5: for Davenport–Heilbronn-type functions Prop. 5.6 fails and the certificate is empty — quoted, not tested |
