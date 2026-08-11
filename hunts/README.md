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

### Higher xi derivatives (`higher_xi/`)

**Status: 2008 discrepancy resolved as a chapter-11 calculation error, two
measured oracles retained, no higher-derivative zeta constant claimed.** Ji
Bian's Figure 10.1 coefficients, substituted exactly into equation (11.5), give
`-202/36855` for `kappa=2` and `-10284002/1216215` for `kappa=3`, not the
reported `0.9544` and `0.9774`. The same substitution at `kappa=1` gives
`348002/405405 = 0.8584057917...`, matching the known control, so this is not
a global normalization mismatch. Page 93 also changes three signs from Figure
10.1; neither row produces the headline. Reconciling it would require omitted
tails canceling `95.46%` and `99.76%` of the shown weighted sums, contradicting
the page's negligible-tail premise. A completed-CUE experiment and an
independent Dirichlet-coefficient recurrence both put the tested
second-derivative form factor well below the displayed eleven-term
polynomial. The finite-cutoff window ladder decreases from `0.9342893` at
`ell=8` to `0.9311081` at `ell=14`; it is a discovery sequence, not a limit or
a theorem. Resolution in `higher_xi/RESOLUTION-2008-DISCREPANCY.md`; full
experiment in `higher_xi/RESULTS-higher-xi.md`.

### Frontier math (`frontier_math/`)

**Status: clean kill of the candidate constant, one measured collapse, one
quantified wall.** Continues `wide_search` THREAD 1 against the 10 August
2026 paper. Measured: the pair-measure LP (positivity + bandwidth-one data +
multiplicity types) reduces exactly to 2 − sup D and descends toward the
paper's 0.6725007 — the measure level adds nothing, answering THREAD 1's
residual question; the ceiling gap is configuration realizability. The
constructive half is withdrawn: the scan used `u u*`, while upstream uses
`u u^T`; the exact witness `1`, `i`, `-i` gives `tr(P₁Q′)=-2`, and the
proposed additive inequality can demand `9 ≥ 13`. The former candidate
**N₀ˢ ≥ 0.672529·N** therefore has no zeta implication. The ordered-gap LP
remains a measured configuration problem, and the bin-width ladder still
records its earlier midpoint-assignment defect. Also recorded: the sieve route to λ > 1
fails at scale T^{λ−1} (only HL itself closes it), and the CGdL transplant
reduces to one named obstruction (inertia counting for non-Gram kernels),
with BGSTB 2023's unconditional F ≥ 0 pinned as known. Closure record in
`frontier_math/CLEAN-KILL-REPORT.md`.

### The frontier map (`frontier_map/`)

**Status: a map, not a result — the `wide_search` findings and the source
paper's own limits assembled into one instrument, one JSON, one figure.**

Builds directly on `wide_search` and the 10 August 2026 pair-correlation
paper. `frontier.py` computes the whole λ-landscape H(λ) for the two kernels
the method accepts unconditionally (ζ and ξ′), pins the ceilings, prior-art
bars and the paper's structural wall as cited data, and renders
`figures/frontier_map.png`. Measured: onsets λ₀ = 0.550194 (ζ) and 0.513320
(ξ′) just above the paper's "nothing at λ ≤ ½" line; both curves monotone and
still climbing at the λ = 1 wall. The numeric ζ curve matches the paper's
closed form (eq. 7.4) to 9.5e-15 pointwise, and a planted mis-constant lesion
moves that comparison by 1.5e-2, so agreement is informative. The map's open
lanes are recorded as intervals: (0.6725007, 0.68185) for ζ within
bandwidth-one data, ξ′-vs-Wu closed negatively at 9.285e-4, κ ≥ 2 blocked on
Bian's missing tail bound, λ > 1 walled behind Hardy–Littlewood-strength
input. Results in `frontier_map/RESULTS-frontier-map.md`; controls in
`frontier_map/probe.py`.

### The wide search (`wide_search/`)

**Status: one measured constant, two negative results and one reproduction, all
about somebody else's method — not a result about zeta.**

An operator asked for one externally checkable mathematical contribution
adjacent to zeta: generate in volume, kill aggressively, search prior art,
reproduce independently, call nothing new without a novelty gate. Mission and
scope in `wide_search/MISSION.md`.

The breadth-first phase was abandoned as the wrong altitude. The target became
the paper of 10 August 2026 that raised the unconditional proportion of zeros
of ζ on the critical line to 0.6725, and specifically the one place it leaves a
variational problem unsolved: its Remark 7.3 on the zeros of ξ′, where it
reports a flat window and an unexplained quartic and records that neither
reaches Wu's unconditional 0.86957.

- **The sharp constant for that method is
  `0.86864150052976706411...`** (simple and on the critical line;
  `0.93432075...` distinct), attained at `lambda = 1`. Full account, with the
  functional and its provenance, in `wide_search/RESULTS-xiprime.md`.
- **It does not reach Wu's 0.86957**, falling short by `9.285e-4`. No admissible
  window closes the gap, so the comparison the paper leaves open is settled
  negatively. The paper's own quartic was already within `1.5e-6` of sharp.
- Checks: the instrument reproduces the paper's Theorem D to 10 digits before
  being pointed at anything unknown; the functional reproduces all four
  published constants of Remark 7.3 to every printed digit; three independent
  derivations of it agree and five independent computations of the optimum
  agree to 14 digits; the coefficient formula is checked exactly by Dirichlet
  convolution; and Bian's 2008 thesis reproduces the same `k = 1` coefficients
  exactly, from sixteen years earlier.
- **Higher derivatives are blocked, and `RESULTS-higher-derivatives.md` records
  why**: `F_k` for `k >= 2` already exists in an unpublished 2008 Rochester
  thesis, it has no closed form, its author states he cannot bound the tail, and
  the tabulated 11-term truncations are measured here to diverge at the
  bandwidth the method needs (`F_4(1) ~ 2476` against `F_1(1) ~ 2.78`, giving
  proportions of 1.198 and −2.64).

A second pass took the remaining thread — whether ζ's own 0.6725 can be moved
toward the 0.68185 ceiling — as far as the public material allows.
`wide_search/RESULTS-pair-ceiling.md`:

- **The scalar-moment formulation collapses, exactly.** Retaining only
  `(tr, ||.||_F^2)` per window makes the joint feasible set the intersection of
  the single-window half-lines, hence `sup_v H(v) = 0.6725007037...`. That route
  cannot move the number, and is closed rather than unfinished.
- **The published ceiling data reproduces.** `wide_search/pair_ceiling.py`
  recomputes, from the enclosures in the public `LawN256.lean` alone and with
  exact rationals, the `2^140` scale, 256 rows, the worst interior error
  `1.83670992316e-40`, `D(1) = 0.8239531607128352`, the stability coefficient
  `2.5431315104166665e-6` and the simple fraction `0.6818286874638315`. All
  agree with the repository. The extremal law itself needs a certificate file
  the authors state is available on request.
- **Remark 1.1's ceiling is stated more uniformly than its finite instance
  supports.** The `N = 256` law gives the `0.68185` sentence for certificates
  with `abs(r'(1)) + integral abs(r'') <= 8.38043022204...`. The formalisation
  carries the error terms and does not make that elision.

**Disposition:** the ξ′ constant and its negative consequence stand, and are
reproducible from this directory. One thread is closed (the scalar-moment LP),
one is blocked (a closed form for `F_k`, `k >= 2`), and one remains genuinely
open: the full-data LP over marked periodic configurations, which does not
reduce to the single-window bounds. No claim promoted, no ledger entry. Nothing
here is evidence for or against RH, and nothing here is a defect report against
the paper's Theorems A-E.

### The director run (`director_run/`)

**Status: not a hunt in the usual sense and not a result — a directorate record.
The instruments it touched are in `zeta/`, and every change it made there is
pinned by a test or stated as a corrected contract.**

An operator handed the laboratory over with no assigned theorem and the standing
instruction that finding a recorded conclusion of this repository to be wrong
counts as a result. Nine investigators with conflicting mandates ran in
parallel; the generator of a claim never judged it. Full record in
`docs/25-the-director-run.md`; programs, claim ledger, graveyard and
intervention ledger in `director_run/`.

- **Six defects in recorded claims**, each reproduced by the director before
  being written down. The most serious: `zeta/rigor.py`'s abscissa conversion
  parsed unrecognised numeric types from their *printed decimal*, so
  `proven_sign` returned a **wrong** nonzero sign on a `numpy.float32` input —
  identically on both backends, because the fault sits upstream of the split.
- **A strategic conclusion corrected.** The claim that a coefficient functional
  is "blind to the position of the critical line by construction" is false as
  written and mis-cited (`docs/18` §6 says *ordinate* statistics). The true
  statement is a threshold — `c_p ≤ d` for `ζ(s−δ)` exactly when `δ ≤ ½` — and
  it is the Selberg-class axiom's `θ < ½`, i.e. known. The `ROADMAP.md` call
  that hunt #5 asked for is answered: **no**, this does not become a standing
  constraint on the coefficient-side programme.
- **Two positives that held under attack.** A blind replicator, given the
  statement only and forbidden the package, reproduced the flagship Weil
  enclosure to 43 digits from scratch; and the Lean arm rebuilt on a cold
  machine, 8715 jobs, zero `sorry`s.
- **The formal arm's blocker was mis-diagnosed and is now measured.** Rung 3's
  centre could not have passed at any Taylor order — its budget counts the tail
  radius once where the norm counts it twice — and the width floor is the κ
  enclosure, not the exponential Taylor order. A configuration with ≥1.1×
  margins exists at 1.63× the term count and the same literal sizes.

**Disposition:** repairs landed with tests; no claim promoted; no ledger entry.
Nothing here is evidence for or against RH.


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
critical line. **The reason recorded here was wrong, and the `ROADMAP.md` call
it asked for has now been made — the answer is no** (2026-08-11, `docs/25`).
`ζ(s−δ)` does *not* have the same coefficients: it has `n^δ a_n`, and `c_p`
reads that twist with threshold exactly `δ = ½` (`c_p = 2x/(1+x)`,
`x = p^{δ−½}`). Blindness is a property of a statistic invariant under that
twist, not of reading arithmetic — and a coefficient-side statistic equivalent
to RH is already in this tree (Mertens, `criteria.py` face 1). So the
repetition across three instruments does **not** rise to a standing constraint
on the coefficient-side programme, and must not be recorded as one. Full record in
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
