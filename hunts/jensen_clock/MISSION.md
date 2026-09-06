# Hunt #6: the Jensen clock (`jensen_clock/`)

**Question.** `zeta/li.py`'s real-rootedness lane asks about Jensen polynomials
J^{d,n}; hunt #4 (`flow_repair/`) measured when the de Bruijn–Newman flow lands
the Davenport–Heilbronn off-line pairs. This hunt connects them: **at what
finite Jensen degree does hyperbolicity actually witness the counterexample's
off-line pair, and is the finite degree itself a heat clock?**

The observation driving the design (found in a scratch prototype before this
mission was written, recorded honestly as such): with
E(x) = Σ γ(n) xⁿ/n! and γ(n) = n!/(2n)! · M₂ₙ the moment sequence of the DH
weight Φ_DH, the degree-d Jensen polynomial satisfies exactly

    J^{d,0}(x/d) = Σ_j γ(j)/j! · Π_{i<j}(1 − i/d) · x^j,

and the damping Π(1 − i/d) ≈ e^{−j²/2d}, read at the cosh-series saddle
j ≈ zu/2, acts like the flow multiplier e^{t u²} with an effective time

    t_eff(d) = |x₀| / (8 d),      x₀ = (β − 1/2 + iγ)²  the pair's image.

A prototype trajectory ladder saw the DH height-85.7 pair's image in J^{d,0}
drift to the real axis and land between d = 10⁴ and 3·10⁴, with the drift rate
agreeing with hunt #4's measured pair dynamics through the dictionary above at
the percent level. A naive grid scan (d ≤ 32, all shifts n ≤ 250) sees nothing,
which the dictionary explains: those degrees carry t_eff far beyond the pair's
landing time, so the degree itself has smoothed the violation away before the
polynomial is even inspected.

## Pre-registered predictions

Targets below use hunt #4's measured values, read from
`hunts/flow_repair/results.json`: pair 1 (β ≈ 0.8085, γ ≈ 85.699,
t\* = 0.044126344551623946, isolated-pair naive value y₀²/2 = 0.047591…),
pair 2 (β ≈ 0.6508, γ ≈ 114.163, t\* ≈ 0.0111296).

- **P1 (dictionary, pointwise).** Under t_eff = |x₀|/(8d), the Jensen pair
  trajectory Im X(d) matches the PDE trajectory Im X_PDE(t) pointwise within
  5% relative over t_eff ∈ [0, 0.8·t\*], and the drift constant
  C = lim_{d→∞} d·(Im X(∞) − Im X(d)) matches
  C_pred = |d Im X_PDE/dt|₀ · |x₀|/8 within 2%.
- **P2 (the clock adjudicates).** The landing degree d\* gives
  t\*_J := |x₀|/(8 d\*) inside (0.042, 0.047), and **closer to the PDE landing
  0.0441263 than to the isolated-pair 0.0475914**, i.e. the Jensen clock
  feels the same neighbor interaction the PDE flow does.
- **P3 (scaling across pairs).** Pair 2 lands at d\* ≈ 1.5·10⁵ with t\*_J
  within 8% of its PDE t\* = 0.0111296, a 7× change in d\* tracked by the
  same dictionary.
- **P4 (specificity).** ζ through the identical pipeline, no plant: Newton
  from x₀ collapses onto the real axis and a winding box at the DH pair
  location counts zero.
- **P5 (lesion, geometry vs arithmetic).** A pair planted into ζ's γ-sequence
  at exactly x₀ (an exact three-term recurrence, multiplication of E by
  (x − x₀)(x − x̄₀)) is detected, with its own landing degree; since its
  x-plane neighborhood is ~5× sparser than DH's, its clock should read close
  to the isolated value 0.0476 rather than DH's 0.0441. Same position,
  different arithmetic, different neighbor field → different d\*: the clock
  reads configuration, extending hunt #4's null result to the coefficient
  side.
- **P6 (two clocks add).** Flowing the γ-sequence to time t before damping,
  the landing time t_land(d) satisfies t_land(d) + |x₀|/(8d) = t\* within 5%
  of t\* at d = 6·10⁴ and 1.2·10⁵.
- **P7 (precision response).** d\* moves by < 0.1% under dps 110 → 160,
  series cutoff 280 → 360 and quadrature (U, segments, degree) changes; the
  undamped Newton root reproduces hunt #4's polished pair to ≥ 30 digits.

## Phase 2: the shift direction (registered 2026-08-11, after phase 1 closed)

Phase 1 fixed the shift n = 0 and measured the degree axis. The shifted
Jensen polynomial is exactly the damped n-th derivative,
J^{d,n}(x/d) = Σ_j γ(n+j)/j! · Π_{i<j}(1−i/d) · x^j = damped E⁽ⁿ⁾(x), so the
shift axis asks: what does differentiation in x do to the off-line pair's
image, on the same clock? Differentiation of real entire functions is
believed to act on zeros as a smoothing flow (Gauss–Lucas pulls complex pairs
toward the real hull; there is a modern PDE literature on repeated
differentiation as an erosion/heat-like flow on the zero distribution, a
literature pass is part of this phase). Pre-registered questions and
predictions, written before any phase-2 measurement:

- **Q1 (per-step clock).** At d = 10⁸ (degree damping negligible) the pair's
  image in E⁽ⁿ⁾ descends toward the real axis as n increases, and the
  per-step effective flow time c_n := t-equivalent of step n → n+1 (read off
  the PDE trajectory) is of order 1/(2u₀²) with u₀ ≈ 1.3–1.5 the measured
  cosh-series saddle abscissa at the pair, i.e. **c₀ ∈ [0.2, 0.35]·t\*/0.0441
  … loosely, c₀ ∈ [0.005, 0.05]** is the honest wide bracket; the saddle
  heuristic is weak and this question is genuinely open. The sharp
  registered prediction is only the *direction* (descent, monotone) and that
  c_n is set by configuration, not arithmetic.
- **Q2 (three clocks add).** For cells (d, n, t) with all three knobs on,
  t_land(d, n) + |x₀|/(8d) + g(n) = t\* within 1%, where g(n) = Σ_{k<n} c_k
  is the measured shift clock, no free parameters once c_k are measured at
  t = 0.
- **Q3 (the map).** The detection region for pair 1 in the (d, n) plane is
  the corner {|x₀|/(8d) + g(n) < t\*}: boundary cells flip
  detected/not-detected as that inequality predicts, including the n-axis
  end (the largest n at which any degree can see this pair, predicted
  n_max = max{n : g(n) < t\*}).
- **Q4 (specificity).** ζ through the same shifted cells stays silent.

Phase 2 may also touch only `hunts/jensen_clock/`.

## Phase 3: the falsifier and the trichotomy (registered 2026-08-11, after
phase 2 closed)

- **Q5 (strong additivity, zero free parameters).** Phase 2's Q2 was left
  honestly untested. The test: re-measure t_land(n = 1) at d = 10⁶. The
  additive picture predicts it moves from the d = 10⁸ value −0.118667407 by
  exactly the degree-budget difference −|x₀|/8·(10⁻⁶ − 10⁻⁸) = −0.00090888,
  i.e. **t_land(n=1, d=10⁶) = −0.11957629 ± 0.0001**. If this fails, phase
  2's additive budget rule was curve-fitting and the hunt's map claim is
  withdrawn.
- **Q6 (the trichotomy: Li is an accumulating discriminator).** The third
  coefficient-side detector, Li's criterion, has a kernel 1 − (1 − 1/ρ)ⁿ
  that *amplifies* off-line zeros (|1 − 1/ρ| > 1 for β < 1/2) instead of
  smoothing them. Registered predictions: (i) for a planted symmetric
  quadruple at ρ_p = 0.8 + 2.5i added to ζ's Li sum (Bombieri–Lagarias
  form), the sum first goes negative at the envelope crossing of
  2·rⁿ against λ_n(ζ), r = |1 − 1/(1 − ρ_p)| ≈ 1.0466, predicted onset
  **n_Li ∈ [80, 160]**, with negativity arriving within one oscillation
  period (≈ 16) of the envelope crossing; (ii) the identical formula
  applied to DH pair 1 (r − 1 ≈ 4×10⁻⁵) puts its onset **beyond 10⁵**,
  unreachable by any Li computation in this tree; (iii) hence the
  trichotomy: degree and shift are *erasing clocks* (their blind sets are
  cofinal, all small d, all n ≥ 1), Li is an *accumulating discriminator*
  (its blind set is an initial segment). Blind in opposite directions;
  neither blindness is a matter of effort.
- **Q7 (specificity).** The unplanted λ_n(ζ) stays positive over the whole
  tested range (already pinned by `tests/test_li.py`; recomputed here so the
  planted run has its own control).

## Scope

May touch: `hunts/jensen_clock/` only. Reads (never writes)
`hunts/flow_repair/results.json`, `zeta.epstein`, `zeta.heatflow`, `zeta.li`.
No changes to `zeta/`, `ontology/`, `harness/`, no cache invalidation, no
ledger entry unless something survives the checklist in `hunts/README.md`.

Everything here is the accurate regime, mpmath floats with measured
cross-route defects; the strongest words used are *measured* and *observed*.
The truncated-series detector reports its own validity margin (tail bound vs
minimum modulus on the contour) rather than assuming it.

Prior-art hooks, recorded so nothing is overclaimed: coefficient multiplier
sequences of Gaussian type are classical (Pólya–Schur; de Bruijn's e^{−λD²}
operators; Turán), and Griffin–Ono–Rolen–Zagier relate large-*shift* Jensen
polynomials to Hermite polynomials through exactly this kind of heat limit.
The degree-damping-as-heat reading may well be implicit in that literature;
this hunt claims measurements on the counterexample, not novelty.
