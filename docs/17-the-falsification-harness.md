# 17 — The falsification harness: how five claims died in one day

*A methods retrospective. Everything in docs/00–16 is about the mathematics;
this document is about the refereeing. It exists because 2026-08-05 produced
an unusually clean natural experiment: five independent claims of
Riemann-zero structure arrived in a single day from exploratory "rogue lab"
sessions, and the repository's standing instruments dispatched all five —
four rejected, one confirmed-negative by its own pre-registered prediction —
without any of the verdicts depending on taste.*

The problem this solves is asymmetry. A plausible spectral "explanation" of
RH now costs minutes to generate — a discretized operator, a fitted
spectrum, an evocative physical story — while a referee's rebuttal
traditionally costs days. The instruments below make the rebuttal cost
minutes too. None of them require knowing whether the claim is true; they
only require that the claimant's *evidence* survive contact with controls.
Per the honest-scope rule (docs/08), nothing here is evidence for or against
RH itself. The harness adjudicates a weaker and more decidable question:
*is the demonstration about ζ at all?*

## 1. The instruments

Four standing pieces, all in-tree before the claims arrived:

1. **The counterexample battery** (`zeta.epstein.battery`, docs/09 gate #3).
   The Davenport–Heilbronn function satisfies a Riemann-type functional
   equation, has real Dirichlet coefficients and a real Hardy-style Z — and
   violates RH. Any claimed structure that "explains" why zeros stay on the
   line must fail for DH, or it explains nothing. Crucially, the battery
   also catches *tests of the battery*: case 2 below flunked it by testing
   the wrong function.
2. **The counting gates** (`zeta/spectral_gate.py`). A claimed zero-counting
   model must (a) grow logarithmically with the cutoff in the 1:2 ratio the
   explicit formula forces, (b) predict a held-out cutoff, (c) move by
   ≥ 10% when the primes are swapped for decoys, and (d) be invariant under
   permuting the primes. Thresholds are pinned constants, declared before
   any model runs.
3. **Pre-registration in the plan document.** A review of a sprint plan
   records its predicted outcome *in the repository, before the first run*
   (docs/16 carries a complete worked example: prediction, outcome entry,
   closure). The corollary that had to be enforced this week: the review
   section belongs to the reviewer, and a pre-registered prediction may
   never be edited away by the party it constrains.
4. **Reserved language.** "Certified" belongs to `zeta/rigor.py` alone;
   everything else is at best *accurate*. A verdict sentence must say which
   it is.

## 2. One transferable checklist

Every rejection this week reduced to one of five checks, each cheap enough
to run before reading a claim's prose:

* **Count the free parameters against the data.** An affine fit (2
  parameters) of seven increasing eigenvalues onto seven targets dominated
  by a smooth trend produces small *relative* errors for any input. If a
  claim's headline is a calibration, refit the same spectrum to made-up
  targets first.
* **Ablate the claimed mechanism, both directions.** Replace the special
  structure (primes, polygon areas, coefficients) with noise; if the result
  survives, the structure was not load-bearing. Then run the battery: hand
  the same construction a known impostor and require a *fail*.
* **Distrust thresholded quantities.** A floating-point rank is a function
  of its SVD tolerance; a "detected peak" is a function of its scan window.
  Demand the sensitivity table, or sweep it yourself (blind, full-range).
* **Check the trivial explanation for any inequality.** "All eigenvalues
  ≥ 1/4" is implied by a positive potential of mean ≈ 39; it needed no
  arithmetic input at all.
* **Ask what the identity already implies.** A construction whose input is
  the primes and whose output is peaks at the zeros has rediscovered the
  explicit formula (docs/04, `zeta/weil.py`), not new physics.

## 3. The case log (2026-08-05)

Structural claims below are pinned at reduced size by
`tests/test_rogue_lab_controls.py`; the quoted percentages are session
measurements at the original sizes, reproducible from the committed scripts.

**Case 1 — the geometric dust torus** (`ontology/10_geometric_dust_torus.py`).
Claim: a torus Laplacian plus a potential built from polygon area
remainders calibrates to the zeros with sub-1% error, with min eigenvalue
≥ 1/4. Controls: the affine fit gives ~20% mean error against the real
zeros, ~19% when the potential is replaced by noise, ~23% against invented
targets; the eigenvalue bound follows from positivity of the potential.
Verdict: two-parameter curve fitting; rejected.

**Case 2 — the Dirichlet xp "imposter gauntlet"**
(`ontology/13_dirichlet_polya_hilbert.py`). Claim: weighting a divisor-graph
xp operator by Dirichlet coefficients keeps ζ's spectrum on the line while
throwing Davenport–Heilbronn off it. Controls: the "DH coefficients" used
were the raw character mod 5 — i.e. L(s,χ), whose zeros *are* on the line —
while the true DH coefficients are real (1, κ, −κ, −1, 0;
`zeta.epstein.dh_coefficient`), so the genuine counterexample yields a real
antisymmetric matrix and *passes*, as does random real noise. The gauntlet
is a realness detector, misclassifying in both directions. Verdict:
rejected; the battery exists precisely to catch this.

**Case 3 — the Sierra–Townsend density fix**
(`ontology/15_fixing_the_density.py`). Claim: discretizing H = x(p + 1/p)
forces the Riemann–von Mangoldt E log E level density. Measurement: the
spectrum is an equally spaced ladder (gap CV ≈ 2.5%, linear density) whose
scale tracks the arbitrary momentum box; by mode 100 it counts 100 levels
where the zero-counting law says 20.5. Verdict: rejected.

**Case 4 — the acoustic absorber** (`ontology/16_adelic_acoustic_absorber.py`).
Claim: a "prime crystal" chokes transmission exactly at the zeros. A blind
full-range scan confirms peaks near 14.13, 21.02, 24.97, … — the one claim
that reproduces. But the reflection amplitude is the Fourier transform of
the weighted prime staircase minus its main term: the explicit formula,
already in `zeta/weil.py` and `zeta.explicit.prime_spectrum`, with primes as
*input*. Verdict: true, known, and not an operator; filed as a rediscovery.

**Case 5 — the Poisson cokernel sprint** (docs/16,
`scripts/32_poisson_cokernel_matrix.py`). The system working end to end:
the plan was reviewed with three blockers and a pre-registered prediction
(ablation ≈ 0%, gate rejects); the prediction was restored after being
edited away; the build confirmed it (ablation 0.0%, growth ratio 8.9); a
follow-up showed the *entire* singular-value spectrum indistinguishable
under prime ablation at every tolerance from 1e−2 to 1e−12; the p-adic
tensor factors were then implemented as demanded and the gate still failed
(4.8%). Verdict: matrix route closed by experiment — a negative result with
a chain of custody, which is the only kind that stays closed.

## 4. What the week actually demonstrated

The interesting output is not that four claims were wrong; generating wrong
claims is now free, so that was guaranteed. It is that *verdict cost
collapsed to claim cost* once the controls were standing infrastructure:
each rejection above was one short script reusing in-tree instruments, and
each verdict survives independent rerun because the evidence is committed
next to the claim. The one confirmed claim was identified as a rediscovery
in the same pass, by the same instruments.

The discipline that cannot be automated remains the social one: reviews are
appended, never rewritten; predictions are filed before runs; the reviewer
owns the review. The one attempted violation this week (the self-approval
edit, reverted in `6c70907`) was caught by git history, not by any gate —
version control is the fifth instrument.
