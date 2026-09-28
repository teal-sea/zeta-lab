# 36. What you can run, and what it prints

Moved off the front page on 2026-09-05. `README.md` is an index, and
`AGENTS.md` says so in as many words: "Keep `README.md` an index, not a manual.
Do not let it grow back into a single 400-line front page for four different
audiences." It had grown to 605 lines. This document is the manual half.

Everything below runs from a clone with the venv set up (`README.md`
"Quickstart"). Expensive computations cache under `data/`, so a second run of
anything here is fast.

## Twelve things you can run right now

1. **Rebuild the primes from the zeros**, the moment the subject becomes real:

   ```bash
   python scripts/03_primes_from_zeros.py
   ```

   Von Mangoldt's explicit formula, live. Input: the first 500 zeros of ζ and
   *nothing else*. You will see ψ(100) converge from 98.16 (0 zeros) to
   94.03 (250 zeros; exact value 94.0453); a table of measured jumps showing
   the cosine sum jumping by log p exactly at 73, 79, 81 = 3⁴, 83, 89, 97 and
   staying flat at every composite in between; the edge at p = 97 sharpening
   as zeros are added; and the dual "music of the primes" spectrum with peaks
   at x = 2, 3, 5, … The zeros know where the primes are.

2. **Find every zero below height 100 and verify RH there**:

   ```bash
   python scripts/02_find_zeros.py --T 100
   ```

   Hardy's Z(t) locates 29 sign changes; the argument principle counts
   N(100) = 29 zeros in the *whole strip*; 29 = 29, so every zero below
   height 100 is simple and exactly on the critical line (Backlund/Turing
   method, modulo the floating-point caveat printed by the script itself).

3. **Derive the functional equation from heat flow**:

   ```bash
   python scripts/01_verify_functional_equation.py
   ```

   Three measured residuals, each ~1e-30: the theta modular identity
   θ(1/x) = √x·θ(x), Riemann's symmetric Mellin representation, and
   ξ(s) = ξ(1−s), including at a point 3.5e-8 away from the first zero.

4. **Test the zeros against random-matrix theory**:

   ```bash
   python scripts/04_gue_statistics.py
   ```

   10,000 unfolded zero spacings vs the exact GUE Gaudin law (KS distance
   D ≈ 0.029), vs an *actual* 800×800 random GUE matrix run through the same
   pipeline (D ≈ 0.035), vs Poisson (D ≈ 0.31, rejected by a factor ~10),
   plus Montgomery's pair correlation. The zeros repel like eigenvalues.

5. **Run the heat flow and watch zeros collide**:

   ```bash
   python scripts/05_heat_flow.py
   ```

   Certifies H₀ = Ξ/8 and the backward heat equation numerically, tracks the
   first ten zeros of H_t as t varies (repulsion forwards, attraction
   backwards), demonstrates a real root collision on a polynomial toy model,
   and prints exactly what is proved about Λ (and by whom).

6. **Balance the Riemann–Weil explicit formula, then probe Weil positivity**:

   ```bash
   python scripts/07_weil_positivity.py
   ```

   You will see the same number computed two unrelated ways, zeros on one
   side, primes and Γ-factors on the other, agree to ~1e-31, and then the
   Weil functional W(h) (RH ⟺ W ≥ 0) stay positive across families of
   positive-type test functions, with its margin visibly controlled by the
   first zero γ₁ = 14.1347…

7. **Watch a zeta-shaped function fail RH**:

   ```bash
   python scripts/08_wrong_shape_zeta.py
   ```

   You will see the Davenport–Heilbronn function, exact functional equation,
   real coefficients, a real Hardy-style Z, everything except the Euler
   product, get caught by the argument principle with more zeros in the strip
   than on the line, and the excess polished to a verified zero at
   0.8085… + 85.6993…i, OFF the critical line: symmetry alone cannot give RH.

8. **Prove it instead of measuring it**: the same verification in ball
   arithmetic:

   ```bash
   python scripts/09_certified_verification.py
   ```

   Two independent certified backends (Arb via python-flint, and mpmath's
   interval context with a hand-rolled Euler–Maclaurin ζ) enclosing Z(100) and
   overlapping; 29 *proven* sign changes below T = 100; N(100) = 29 proven from
   an enclosure of width 6.5e-56 containing exactly one integer; and the
   floating-point run printed beside it, same integers, different epistemic
   status. Also the honest failure mode: at the float nearest γ₁, where
   |Z| ≈ 6.7e-16, 32 bits make `proven_sign` return 0, "not decided", never
   "probably", and 64 bits then decide it.

9. **Watch RH as positivity and as real-rootedness**:

   ```bash
   python scripts/10_li_and_jensen.py
   ```

   Li's λ_n by two independent routes (a Cauchy pass on ξ that never touches a
   zero, and a zero sum that never touches ξ) agreeing to 1.9e-7, with
   λ₁ = 1 + γ/2 − log(4π)/2 = 0.0230957089661… matched exactly; then 72 Jensen
   polynomials J^{d,n} (d, n ≤ 8) all hyperbolic, decided twice: Durand–Kerner
   and an *exact* Sturm count in ℚ[X].

10. **See the one RH that is a theorem**:

    ```bash
    python scripts/11_finite_field_rh.py
    ```

    Curves over finite fields: 380 curves across 10 primes, zero Hasse
    violations, `Re(s) = ½` exactly, and the Lefschetz prediction for N₂ matched
    against a brute-force point count in F_{p²}, the operator interpretation is
    real, not formal. Then what is missing over Spec ℤ, stated plainly.

11. **Run four exact equivalences at once**:

    ```bash
    python scripts/12_equivalence_faces.py
    ```

    Mertens, Nyman–Beurling/Baez-Duarte, Robin/Lagarias and Speiser on one
    dashboard: zero violations in every finite range checked, and the Mertens
    face is there precisely to show what "zero violations" was worth for the
    century before Odlyzko and te Riele disproved the conjecture.

12. **Run the conjecture factory, and measure its own hit rate**:

    ```bash
    python scripts/13_discovery_run.py --dry-run   # a full pass, nothing written
    python scripts/13_discovery_run.py             # a real pass
    python scripts/13_discovery_run.py --report    # the dashboard over the ledger
    ```

    Seven generators mine the laboratory's computed objects for candidate
    observations; a catalogue and six screens filter them; every step is
    logged, so the conversion rate *per generator* can be measured. On a fresh
    ledger the seven produce 32 candidates, and the funnel's verdict on them is
    26 already known (81.2 %), 1 trivial, 5 inconclusive, 0 survivors. That
    table is the deliverable: most numerical "discoveries" are already known
    or trivial, and a pipeline that does not measure its own hit rate has no
    way to know this about itself. A survivor, when one appears,
    is a **lead**, not a result, not evidence for RH, and "not recognised
    offline" is not novelty: there is no network here, so nothing was looked
    up. (The survivor path is exercised end to end by an opt-in candidate,
    `legendre_mass_constant`: whose one recorded run, operator literature
    check included, is in `ROADMAP.md`.) The ledger lives in `conjectures/`,
    which is gitignored; it is a private notebook of unreviewed leads.
    Design: `ontology/README.md`.

## The gallery


Every figure is generated by one function in `zeta/plots.py`
(`scripts/make_figures.py` rebuilds them all).

**The primes rebuilt from the zeros**, the explicit formula converging to
the ψ staircase, jump detection at prime powers, and the prime spectrum
(`scripts/03_primes_from_zeros.py`):

![Primes from zeros](figures/03_primes_from_zeros.png)

**Theta modularity**, the two faces of the heat kernel and the measured
defect of θ(1/x) = √x·θ(x) (`plot_theta_modularity`):

![Theta modularity](figures/theta_modularity.png)

**Zero spacings vs GUE vs Poisson**, the Montgomery–Odlyzko law
(`plot_spacing_histogram`):

![Spacing histogram](figures/spacing_histogram.png)

**Zeros of H_t under the de Bruijn–Newman flow**, repulsion forwards,
collision backwards (`plot_heatflow_trajectories`):

![Heat flow trajectories](figures/heatflow_trajectories.png)

The rest: [ζ on the critical line](figures/zeta_critical_line.png) ·
[Hardy's Z](figures/hardy_Z.png) ·
[domain coloring of ζ](figures/zeta_domain_coloring.png) ·
[heat evolution of Θ](figures/theta_heat_evolution.png) ·
[explicit formula](figures/explicit_formula.png) ·
[prime spectrum](figures/prime_spectrum.png) ·
[pair correlation](figures/pair_correlation.png) ·
[N(T) staircase and S(T)](figures/zero_counting.png) ·
[polynomial root repulsion](figures/polynomial_root_repulsion.png) ·
[GUE quick-peek](figures/spacings_gue_quickpeek.png) ·
[Weil positivity](figures/weil_positivity.png) ·
[the off-line zero](figures/offline_zero.png) ·
[certified enclosures of Z](figures/certified_enclosures.png) ·
[Li coefficients](figures/li_coefficients.png) ·
[Jensen polynomial roots](figures/jensen_roots.png) ·
[RH over finite fields](figures/finite_field_rh.png) ·
[vertical Sato–Tate](figures/sato_tate.png) ·
[the Mertens walk](figures/mertens.png)

## Repository map


```
zeta/               the package (flat layout; pip install -e .)
  core.py           ζ by three independent routes, θ, ξ, Ξ, Z, Mellin, defects
  zeros.py          zero hunting, Gram points, N(T), verify_rh_up_to (Turing)
  explicit.py       explicit formula: ψ/π from zeros; prime spectrum (dual)
  statistics.py     unfolding, spacings vs GUE/Poisson, pair correlation
  moments.py        external zero/value tables, finite moments, gated scorecards
  heatflow.py       Φ, H_t, zero tracking, Λ facts (de Bruijn–Newman)
  weil.py           Riemann–Weil explicit formula, both sides; Weil positivity
  epstein.py        Davenport–Heilbronn: zeta-shaped symmetry, a zero off the line
  rigor.py          ball arithmetic: enclosures, proven signs, certified N(T)
  li.py             Li's criterion (λ_n) and Jensen polynomials (real-rootedness)
  finitefield.py    curves over F_p, the one RH that is a THEOREM, checked by counting
  criteria.py       four equivalence faces: Mertens, Baez-Duarte, Robin/Lagarias, Speiser
  plots.py          the publication figures
ontology/           the conjecture funnel, a discovery pipeline that logs itself
  schema.py         what a candidate observation is; five kinds, six verdicts, dedup
  registry.py       the plug-in seam: Generator, Screen, KnownnessDetector, Domain
  ledger.py         append-only JSONL: the candidate stream and the run stream
  funnel.py         generate→dedup→known→cheap→expensive→terminal, count in = count out
  metrics.py        the conversion tables (an empty denominator is None, never 0.0)
  knownness.py      the already-known gate: PSLQ closed forms, a fact registry, no novelty
  historical_cases.py  replay claims whose outcome is already settled
  domains/          the only subject-aware code in the package (zeta_domain, zeta_history)
harness/            DEMOTED 2026-08-13, read harness/VERDICT.md first. Two things:
                    the ledgers (graveyard, guards, review) are live lab bookkeeping
                    with a consumer in scripts/70_lab_state.py and stay; the
                    generalized framework below was tested against the practice it
                    meant to improve and did not earn its keep.
                    four control roles (rival, decoy,
                    surrogate, lesion), a Battery, a Department, domain-agnostic
                    by test
  departments/      the only subject-aware code in the package (zeta_department)
hunts/              exploratory studies, explicitly not results, they borrow the
                    zeta battery, and a claim counts only after passing the
                    battery or the funnel (hunts/README.md)
lean/               Lean 4 + Mathlib (package ZetaLean); kernel-checked
                    theorems, zero sorrys, `lake build`
scripts/            01–05 and 07–13 one demo each, 06_tour.py runs the whole
                    story, make_figures.py regenerates figures/
docs/               00–13, the reading course (see the table above)
tests/              the pytest suite; every number claimed in a docstring is
                    pinned by a test
data/               caches (zero tables as .json are committed; .npz scans
                    regenerate on first use)
conjectures/        the discovery ledger, gitignored, a private notebook of
                    unreviewed leads; publish the metrics report, never the log
figures/            the PNGs linked above
references/         annotated reading list (papers.md), plus mathlib-open-targets.md,
                    generated: what Mathlib says it wants and does not have
```

## Known limitations, and what is slow


- **The default route is not interval arithmetic.** `verify_rh_up_to` and the
  sign-change scans evaluate Z(t) in ordinary floating point at a stated
  precision; the "proof for this range" is therefore modulo the correctness of
  those sign evaluations (rigorous verifications à la Platt–Trudgian use
  interval arithmetic precisely to close this gap; see
  `docs/08-why-it-is-hard.md` §3.1). `zeta/rigor.py` is the closed-gap
  counterpart, `verify_rh_certified` runs the same argument in ball
  arithmetic, so every sign and the count N(T) are proven rather than measured;
  use `zeros.py` to explore and `rigor.py` to certify. What it still rests on:
  the ball library (Arb via python-flint, or mpmath's interval context) and the
  two quoted theorems. And the certificate is still about a finite interval,
  it buys trust, not evidence (`docs/08`).
- **Cold caches cost minutes.** The first `make_figures.py --full` heat-flow
  sweep (H_t trajectories at 13 flow times) and the first bulk zero scans are
  the expensive steps; results land in `data/` and are instant afterwards.
- **Empirically-tuned working ranges.** Some internals (e.g. the η-series
  workload model) are tuned and tested on documented ranges (Re s ≥ −20.5);
  far outside them you are extrapolating.
- **Statistics are finite-height.** The residual D ≈ 0.03 against GUE is
  real O(1/log γ) drift at height ~10⁴, not a discrepancy and not perfection;
  the docs and scripts say so at the point of use.
- **The conjecture factory measures itself, and its own measurement has
  limits.** `ontology/`'s conversion rates are honest about what they count,
  and `ontology/README.md` §7–§9.3 states where they are not: a candidate
  record needs a candidate, so *individual payloads a generator built and
  refused* reach no ledger (only `scripts/13`'s per-run table); deduplication is
  a **lower** bound, so `unique` counts are a ceiling; the five historical cases
  were chosen to span the outcome vocabulary, not at random, and four of the
  five right answers were carried by the catalogue alone rather than by anything
  that examined the mathematics (`gate_dependence` is the query that reports
  it). "Not recognised offline" is the absence of a lookup, there is no
  network, and is never rendered as novelty anywhere in the layer.
- **And the big one:** nothing here bears on the truth of RH. That is the
  point of the whole of `docs/08`. A funnel survivor is a lead, not a result;
  every one carries a `proof_gap` field saying so in its own record.
