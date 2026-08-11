# Results — the Jensen clock

**Status: probe, complete. Instrument kept; no claim promoted; the headline is
a measured dictionary — finite Jensen degree acts on the counterexample's
off-line pair as de Bruijn–Newman heat with t_eff = |x₀|/(8d) — plus the
corollary that textbook-degree Jensen scans are structurally blind to an
actual RH violation, and a null control showing the clock reads zero
configuration, not arithmetic.**

Everything below is the accurate regime (mpmath floats, measured cross-route
defects). Raw numbers in `results.json`; predictions were pre-registered in
`MISSION.md`; PDE-side targets are hunt #4's measurements
(`hunts/flow_repair/results.json`), reused, never recomputed here.

## The object

For the Davenport–Heilbronn weight Φ_DH, E(x) = Σ γ(n)xⁿ/n! with
γ(n) = n!/(2n)!·M₂ₙ puts the completed function's zeros at x = (ρ−1/2)²:
negative real when ρ is on the critical line, off the axis otherwise. The
degree-d Jensen polynomial obeys the exact identity
J^{d,0}(x/d) = Σ γ(j)/j!·Π_{i<j}(1−i/d)·x^j, and the binomial damping
Π(1−i/d) ≈ e^{−j²/2d} is a Gaussian coefficient multiplier — de Bruijn's
smoothing, applied by the degree itself. Read at the cosh-series saddle
j ≈ zu/2 it matches the flow multiplier e^{tu²} at the pair's image x₀ with

    t_eff(d) = |x₀| / (8d).

## What was measured

- **Instrument first (stage `validate`).** The ζ pipeline reproduces
  `zeta.li.xi_taylor_coefficients` (itself twice-derived) to 1.3e-51 relative
  over n ≤ 40; two unrelated quadratures agree on the DH γ-table to 2.6e-41;
  the undamped Newton root reproduces hunt #4's polished pair 1 to 40 digits.
  Cancellation at the pair is 86.7 digits — measured, and the reason a
  dps-15 scan could never see any of this.
- **The dictionary, pointwise (P1: holds, with its edge measured).** Under
  t_eff = |x₀|/(8d) the Jensen root trajectory tracks the PDE pair trajectory
  at 7.8e-8 relative (d = 10⁹) through 4e-4 (d = 4·10⁴, i.e. 52% of the way
  to landing), degrading to 1.2% at t_eff = 0.0399 and 13% at the last
  pre-landing rung — both curves are near-vertical there, so a fixed
  dictionary defect inflates in Im x. The drift constant
  C = lim d·(Im x₀ − Im x(d)) = 595021 against the flow-side composition
  590652 — 0.74%, inside P1's 2%.
- **The clock adjudicates (P2: holds).** The landing degree for pair 1 is
  d\* = 20785.13, i.e. t\*_J = 0.0441690, against the PDE landing
  t\* = 0.0441263 — **0.097%** — while the isolated-pair value 0.0475914 is
  7.2% away. The Jensen clock reads the interacting flow, neighbors included,
  not the naive pair formula.
- **Scaling across pairs (P3: holds, 10× sharper than asked).** Pair 2
  (γ ≈ 114.16) lands at d\* = 146365 — 7.04× pair 1's degree — and its clock
  reads 0.0111308 vs the PDE 0.0111296: **0.011%**.
- **Specificity (P4: holds).** ζ through the identical pipeline, no plant:
  Newton from the DH seed collapses onto the real axis (relative Im 1.2e-200)
  and the winding box at the pair location counts 1.3e-63.
- **The lesion, and the null that explains it (P5: qualitative content holds;
  the mission's quantitative guess was wrong and is recorded as such).** A
  pair planted into ζ's γ-table at exactly x₀ (an exact three-term
  recurrence) is detected, with d\* = 21046 → clock 0.0436212. `MISSION.md`
  predicted this would read close to the isolated value 0.0476 — **that
  prediction failed** (8.3% away), because the mission's neighborhood
  estimate forgot that ζ's ordinates appear doubled in this x-plane, so the
  plant is *not* isolated: it has a line neighbor at z-distance 0.96,
  comparable to DH's own spacing. The correct configuration-only prediction —
  hunt #4's arithmetic-free N-body dynamics ż = 2Σ1/(z−z′), integrated for
  the plant's actual zero configuration in collision-safe (x_c, Q)
  variables — gives 0.0435805, and the Jensen clock read **0.094%** away
  from it. Same x-plane position as DH, different neighbor field: the two
  clocks separate by 1.1%, and pure zero geometry predicts each. The clock
  reads configuration, not arithmetic — hunt #4's null result, now on the
  coefficient side.
- **Two clocks add (P6: holds).** Flowing the γ-table to time t before
  damping: t_land(d) + |x₀|/(8d) = 0.0441507 at d = 6·10⁴ (0.055% from t\*)
  and 0.0441398 at d = 1.2·10⁵ (0.030%).
- **Precision response (P7: holds).** d\* is identical to the printed 14
  digits across dps 130 → 160, series cutoff 320 → 360 and two quadrature
  geometries; the deliberately underpowered dps-110 run moves it by 8.9e-5
  relative. The truncated-series detector's validity margin at the final
  contour is 36 orders (tail bound 1e-64.6 vs min |F| = 1e-28.5).

## The corollary worth keeping

A blind hyperbolicity scan over d ≤ 32, all shifts n ≤ 250, sees nothing on
the counterexample — measured here before the targeted instrument was built.
The dictionary says why that is structural, not a matter of effort: degree d
carries effective flow time |x₀|/(8d), and any d below ~2·10⁴ has already
flowed the height-85.7 violation past its landing before the polynomial is
inspected. Finite Jensen hyperbolicity at textbook degrees is not a weak
detector of off-line zeros; at those degrees it is *the wrong side of the
landing*. Conversely the targeted detector (winding box in the x-plane at
the pair image) does separate the rival from ζ at d > d\* — a
position-sensitive instrument in the sense of `docs/18`, and, by the N-body
null above, exactly as arithmetic-blind as a position detector should be:
it says where zeros sit, not what arithmetic put them there. So nothing here
distinguishes ζ structurally, and nothing here is evidence about RH.

## Prior-art hooks

Gaussian coefficient multipliers and their zero-realifying character are
classical (Pólya–Schur multiplier sequences; de Bruijn's e^{−λD²} smoothing;
Turán), and Griffin–Ono–Rolen–Zagier obtain hyperbolicity of J^{d,n} for
fixed d, n → ∞ through a Hermite/heat limit in the *shift*. The reading of
the *degree* itself as a quantitative de Bruijn–Newman time, with the
dictionary t_eff = |x₀|/(8d) measured against a PDE flow on a non-trivial
counterexample, is not something this tree can locate in that literature —
and no novelty is claimed for it; a literature pass would be the next step
if anyone wants to promote the observation.

## Disposition

Instrument kept; no ledger entry. The surviving observation — the landing
degree is the flow landing time on another dial, and both are configuration
geometry — is the null control *explaining* the quantity, which is a
closure of the same kind hunt #4 recorded, not a lead. Nothing here is
evidence for or against RH: the nine known pairs bound Λ_DH-type quantities
from below and the dictionary adds no new zero knowledge; it re-expresses
where known zeros sit. Spine candidate recorded in `NOTES.md`: a docstring
line for `zeta/li.py`'s hyperbolicity scanners stating the finite-degree
blindness window (a `zeta/` change, not this hunt's).
