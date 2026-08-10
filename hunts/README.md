# `hunts/` — exploratory studies

A **hunt** is an exploratory study: a scoped directory where an agent or a
person pursues one specific idea, with the understanding that most such
ideas fail.

`hunts/` is the one place in this repository where a claim can be written
down before any control has been run against it. So the classification is
explicit:

> **A hunt is exploratory. Nothing in `hunts/` is a result — not a result,
> and not evidence.**

Per `harness/README.md`, the admission rule for a *department* is
**no department without a battery** — work whose claims nothing in this tree can
falsify is not a department; it is exploratory, and exploratory work belongs
where nobody will mistake it for a result. That place is here.

A hunt can never become a department by growing, for the reason `ROADMAP.md`
records for `dossier/`: a hunt's negative controls are the *zeta*
department's, and a department whose battery belongs to another department
is not a department. A hunt borrows the zeta battery. That is the correct
relationship, not a deficiency — but the battery does have to actually be
invoked.

## What a hunt may and may not do

| May | May not |
|---|---|
| build its own instruments under `hunts/<name>/` | modify `zeta/`, `ontology/` or `harness/` without explicit permission |
| record raw measurements in its own `results*.json` | write a verdict into `README.md`, `ROADMAP.md` or `HANDOFF.md` as an established finding |
| use the word *measured*, *observed*, *consistent with* | use *verified*, *confirmed*, *definitively*, *proves* — and never *certified*, which `zeta/rigor.py` owns |
| propose a candidate for the funnel or the battery | promote its own claim |

A hunt that wants its claim to count takes it through the battery
(`docs/doors/refute.md`) or the funnel (`docs/doors/discover.md`). Those are
the two routes that can say "yes", and neither of them is the hunt itself.

## The standing checklist

Before a hunt's finding leaves `hunts/`, it must have survived the four
control roles — and the checks are the ones the tree already owns:

1. **Rival.** Does the claim also hold for a function that shares the
   structure and violates RH? `zeta.epstein.battery`. Note the trap below:
   if your test set *is* the rival set, you have measured your own selection
   criterion.
2. **Decoy / surrogate.** Does a matched null with no arithmetic in it
   reproduce the effect? `zeta.surrogate`, `NULLCONTROLS.md`. `ROADMAP.md`
   records the calibration that matters here: against a null of random
   non-factoring sequences, Davenport–Heilbronn sits at the **27th
   percentile** — typical, not exotic. Anything claiming a factorization
   effect must beat that null.
3. **Lesion.** Does the detector notice a violation planted on purpose, and
   can it tell that planted violation apart from the claimed signal? If it
   cannot, the detector is measuring the plant.
4. **Precision response.** Does the effect move when the approximation
   improves? `ROADMAP.md`'s standing rule, earned three times: **an artifact
   does not respond to added precision; a real quantity does.**

## Case log

### Hunt #5 — a norm at every place (`local_positivity/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline is
a negative result about globalisation, plus an honest boundary on what the gate
actually tests.**

An ontology attempt in the sense of `docs/09` §4, pushed at Requirement C of
§5.1: construct, from prime data alone, a structure in which the Weil form is a
norm square, so its sign becomes formal. Reached one place at a time — and the
localisation is exactly where it dies. Raw numbers in
`local_positivity/results.json`:

- **The prime side factors place by place into a manifest norm.** With
  `Φ_p f = Σ_{m≥0} p^{−m/2} f(· − m log p)` it decomposes as
  `−Σ_p log p (Q_p(f) − ‖f‖²)`, `Q_p = (1−1/p)‖Φ_p f‖²` — a norm at every
  place, from coefficients only, with no zeros entering any definition.
  Reconstruction agrees with `zeta.weil.explicit_formula_sides` to 22 digits.
- **And the local norms do not assemble, which is the result.** `Q_p − ‖f‖²` is
  not of definite sign: 52 of the first 60 places positive, 8 negative. Local
  positivity is therefore compatible with either sign of `W`. Files under
  `docs/09` §5.1's taxonomy item #5, *finite approximants*.
- **Gate #3, with a crisp answer.** The place kernel has the closed form
  `K_p^(d)(θ) = Σ_j (1−|α_j|²/p)/|1−α_j p^{−1/2}e^{iθ}|²`, so `c_p ≤ d` is
  *exactly* the local bound `|α_j| ≤ √p`, with `d` read off each object's own
  gamma factors and never chosen. ζ and `L(χ)` quadratic mod 5 measure
  `c_p = 0.8284` and PASS (matching `2/(√p+1)` to 12 digits);
  Davenport–Heilbronn measures `1.8361` and FAILS at `p = 2, 3`; both disc −23
  Epstein forms FAIL, at `5.995` and `6.462`. "Where exactly does DH fail to
  embed?" — at `p = 2`, excess 0.836.
- **Decoy / surrogate.** Swapped coefficients move the verdict by 15 orders of
  magnitude — the control whose absence made the Imposter Gauntlet vacuous
  (`docs/15`). Against 300 random period-5 sequences 100% fail, median excess
  +5.88, and **DH sits at the 6th percentile**: a mild failure, not an exotic
  near-miss, echoing `ROADMAP.md`'s 27th-percentile calibration from an
  unrelated statistic.
- **Lesion.** Interpolating ζ → DH, blindness sets in at `ε* = 0.184`, so a
  PASS means "no violation above ~18% of the way from ζ to DH at the tested
  places", and nothing stronger. The PASS side is not vacuous either: across 60
  Satake angles the genuine degree-2 family keeps margin ≥ 0.343.
- **The honest boundary, stated so nobody overclaims it.** The gate is *not* a
  test for "has an Euler product". A genuine degree-2 product with
  `α = 2.3, 1/α` — legitimate in the Selberg class, violating Ramanujan — is
  rejected at `p = 5` with `c_p = 65.24`. It tests the local Selberg bound, and
  `localpos.scope()` says so inside the module rather than only in prose.

**Disposition:** instrument kept, avenue closed and recorded so nobody reopens
it; no ledger entry. Nothing here is evidence for or against RH. This is the
third statistic, after `D(f)` (`docs/18` §6) and the Fourier quasicrystal
separation (§4), to read arithmetic and stay blind to the *position* of the
critical line — `ζ(s−δ)` has the same coefficients. Whether that repetition
rises to a standing constraint on the whole coefficient-side programme is a
`ROADMAP.md` call, which this hunt may not make for itself. Full record in
`docs/24-the-local-positivity-attempt.md`; the session's own corrections,
including a citation defect it found in `docs/12`, are in
`local_positivity/CORRECTIONS.md`.

### Hunt #4 — repairing the counterexample (`flow_repair/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline
is a measured constant for the rival — and a null control that explains it.**

Pointed the de Bruijn–Newman flow (`zeta/heatflow.py`'s deformation, rebuilt
generic-Φ in the probe) at the Davenport–Heilbronn function for the first
time. Derived Φ_DH = 4e^{3u/2}Σ n aₙ e^{−πn²e^{2u}/5}, then *measured* the
normalisation rather than trusting the derivation: (c, a) = (1, 1) to 4.2e-42,
route agreement with `completed_dh` to 7.2e-41, and the same evaluator
reproduces `zeta.heatflow.H_t` to 5.4e-42 before being trusted on the rival.
Raw numbers in `flow_repair/results.json`:

- **The nine known off-line quadruples (Spira 1994; Balanzario–Sánchez-Ortiz
  2007, each re-polished in-tree) land on the real axis at measured times
  t\* between 0.00275 and 0.05765.** Each is a lower bound for
  Λ_DH := inf{t : H_t^{DH} real-rooted}; the max comes from the height-240
  pair (β ≈ 0.8695), **not** the famous height-85.7 zero, which places third.
  Λ_DH ≥ 0.0577 measured — inside [0, 0.2], the interval that historically
  bracketed Λ_ζ. In flow time, the counterexample fails RH by less than ζ's
  own uncertainty span: "Λ is small" distinguishes nothing (gate #3 on the
  flow axis).
- **Null control, the headline**: the arithmetic-free N-body zero dynamics
  ż = 2Σ1/(z−z') seeded with the measured t = 0 configuration reproduces
  every PDE repair time to **±0.04%** (target was 1%). The repair clock reads
  zero geometry, not arithmetic — the flow-time distance to real-rootedness
  is a property of where the zeros sit, shared by any function with that
  layout. Position-sensitivity (docs/18) meets the counterexample gate.
- **Method worth keeping**: the pair is tracked through its collision by
  contour moments — Δ(t) = 2q₂ − q₁² is analytic through the landing, so t\*
  is a clean root even though the zeros themselves have a branch point.
  Zero-census accounting closed in all five checked windows (line + 2·pairs
  = strip count; e.g. 49 + 4 = 53 at pair 1).
- **Lesions**: a contour clipping one pair member is refused (N=1 ≠ 2); a
  contour through the zeros returns winding ~1.8e9 and is refused. Post-
  landing, the newborn real pair is invisible to the default mean-gap/20
  sign scan at 3 of 5 grid phases until gap/step ≳ 1.4 — hunt #3's blind
  spot, measured on the other side of a collision.
- **Precision response**: t\*₁ = 0.0441263445516 identical to the last digit
  across dps 44/54/70 and 96/192 contour nodes; spread exactly 0.

**Disposition:** measurement portrait of a rival's flow geometry; no ledger
entry (the surviving observation — repair times are configuration geometry —
is the null control *explaining* the quantity, which is a closure, not a
lead). Nothing here is evidence for or against RH; nine pairs bound a sup
over infinitely many from below and say nothing about Λ_DH itself. Spine
candidate recorded in `flow_repair/NOTES.md`: a Φ-parametric entry point for
`zeta/heatflow.py` (a `zeta/` change, not this hunt's).

### Hunt #3 — the closest call (`lehmer_pair/`)

**Status: probe, complete. Instrument kept; no claim promoted; the headline
is a negative result supplied by the rival.**

Pointed the ball-arithmetic arm at Lehmer's pair γ₆₇₀₉/γ₆₇₁₀ ≈ 7005.06/7005.10
(gap 0.0377, mean spacing 0.895). Measured, with raw numbers in
`lehmer_pair/results.json`:

- The near-miss bump between the pair was decided **positive at 64 bits by
  both backends** — `proven_sign` pattern −,+,− on exact rationals, midpoints
  agreeing on `Z(7005.0819) = 0.003967335016595021` to all 16 digits — and a
  dense scan found exactly 2 sign changes with zero undecided samples.
- **Lesion**: the default grid policy of `rigor.certified_sign_changes`
  (mean_spacing/20 ≈ 0.0448) is *wider than the Lehmer gap*; sweeping the
  window phase, the default grid missed the pair entirely at 1 of 5 phases.
  Honest both times (a sign-change count is a lower bound), but blind.
- **Precision response**: enclosure widths shrink ~2^−prec with the midpoint
  pinned; at 32 bits flint straddles zero while mpmath.iv decides — the
  backends disagree about *decidability* at the boundary, never about value.
- **Rival, the headline**: the predicted "failed Lehmer bump" at
  Davenport–Heilbronn's off-line zero does not exist — Z_dh's closest
  approach on [85.2, 86.2] is **−0.357**, two orders of magnitude farther
  from zero than ζ's bump clears it, while hiding 2 strip zeros. So
  "|Z| gets small" flags nothing: it fires on ζ's healthiest close pair and
  stays silent at an actual RH violation. Magnitude heuristics die here;
  sign counting vs strip counting survives.

**Disposition:** portrait, not conjecture — no ledger entry. Spine candidate
recorded in `lehmer_pair/NOTES.md`: the default-step blind spot deserves a
docstring line on the packaged scanner (a `zeta/` change, not this hunt's).

### Hunt #2 — factorization vs. position (`factorization_vs_position/`)

**Status: probe, not established. The instrument used cannot support the
claim that was recorded.**

The hunt asked whether the factorization defect `D(F)` quantitatively
controls the Weil position residue, and recorded a "verified" correlation on
Epstein forms of discriminants −15, −20, −23, −24. Three defects, each
checked in-tree:

- **The completeness gate was never called.** `zeta/detector.py`'s own
  docstring states the load-bearing caveat: the residue measures "zeros
  unaccounted for by the supplied on-line list", so *a missing on-line zero
  produces a residue indistinguishable from an off-line zero*, and **a scan
  whose completeness has not been checked reports nothing trustworthy**.
  `online_list_is_complete` appears nowhere in `hunts/`. The on-line zeros
  were found by a `step=0.05` sign-change scan, which skips close pairs.
- **The lesion confirms the confound, measured.** Give ζ — factorization
  defect `2.65e-32`, a perfect Euler product — a zero list with **one
  on-line zero removed**, and the residue jumps from `0.0038` to **`1.99`**.
  An O(1) position residue is therefore produced by an incomplete list at
  *zero* factorization defect, which is precisely the signal the hunt read as
  off-line zeros. The recorded residues (4.07–4.33) sit at about twice that
  lesion.
- **The test set is the rival set.** The discriminant −23 principal form
  `(1,1,6)` is a **registered rival in `zeta.epstein.battery`**, admitted
  precisely because it lacks a scalar Euler product while keeping the
  functional equation. Confirming that the battery's rivals lack an Euler
  product and have off-line zeros restates their admission criterion. Under
  gate #3 that distinguishes nothing.

Separately, the recorded data does not show the claimed relationship:
across `results2.json` the defect varies by 2.7× (4.25 → 11.46) while the
residue moves 6% (4.07 → 4.33), and in `results.json` a 67× change in defect
(1.58 → 105.95) moves the residue 1.36× with `argmax_c` pinned at the same
`86.0` for all nine rows — the scan-window signature `docs/17` §2 says to
distrust.

**Disposition:** instrument retained, claim withdrawn, no ledger entry. The
correction to `HANDOFF.md` is in the same commit as this note. What the hunt
did produce is real and worth keeping: a *generalized* residue detector that
accepts an arbitrary archimedean bracket, which is the reusable part.
Pinned by `tests/test_hunt_probe_discipline.py`.
