# Zeta Lab Research Portfolio Recommendation

> Transcribed from `Zeta Branches - Hunt.pdf` (19 pages, dated August 11,
> 2026; audience "Zeta Lab research leadership / research-allocation decision
> maker"). Mathematical typography restored where PDF extraction garbled it;
> content otherwise unaltered. This is an outside recommendation, not a
> result — see `docs/reviews/README.md` for the directory contract and
> `ROADMAP.md` ("The outside memos, triaged") for what was adopted from it.

**Purpose**: Identify the highest-value live research fronts in the current
Zeta Lab repository and recommend how available parallel-agent capacity should
be allocated.

## Executive Summary

Zeta Lab is currently in an unusually favorable position.

Several exploratory programs have already eliminated their cheapest or most
misleading formulations. That matters because the surviving problems are no
longer vague searches for "something that might work." In multiple areas, the
repository has isolated sharp mathematical frontiers with:

- known failed relaxations;
- explicit remaining gaps;
- reusable computational infrastructure;
- adversarial regression tests;
- quantitative targets;
- identifiable next lemmas.

The recommendation is therefore not to concentrate all capacity on a single
continuation of the current best bound. Instead, Zeta Lab should operate a
parallel research portfolio centered on three major programmes:

- **Flagship — Full-data zero-configuration realizability / Level-6 counting
  dual.** This is the most compelling immediate frontier. The existing scalar
  relaxation collapses to the known 0.6725007 result, but the richer
  ordered-configuration problem does not. The remaining gap toward the
  approximately 0.68185 configuration ceiling represents information that has
  genuinely not yet been extracted.
- **Theory Builder — General higher-ξ derivative hierarchy.** The correction
  of the ξ″ coefficient/form-factor machinery should be generalized from one
  repaired case into a theory of ξ⁽ᵏ⁾/ξ⁽ᵏ⁺¹⁾, C_{k,i}, F_k(α) for arbitrary
  derivative order k.
- **Moonshot — Global positive structure assembled from prime-local
  arithmetic.** The naive place-by-place positivity programme has failed, but
  that failure sharply identifies a deeper question: whether local arithmetic
  objects can be coupled globally into a canonical positive pairing
  reproducing the Weil criterion.

These programmes are mathematically distinct enough to run concurrently, while
sharing Zeta Lab's verification and adversarial infrastructure.

## 1. Highest Priority: Full-Data Configuration Realizability

### Why this deserves the largest allocation

The central numerical interval — 0.6725007 to approximately 0.68185 — should
not be viewed as a small optimization gap.

The repository has already established that the obvious scalar/pair-measure
version of the problem collapses back to the existing single-window bound.
That negative result is important: it identifies exactly what information is
missing.

The missing information lives at the level of actual zero configurations:

- ordering;
- multiplicities or marks;
- neighboring-gap structure;
- overlap between pair constraints;
- consistency between local configurations;
- realizability of candidate pair distributions by a genuine ordered point
  process.

The richer configuration problem therefore remains substantially different
from the dead scalar LP.

Recent work further narrows the target to a mixed-depth two-dimensional
counting problem involving the interaction kernel T(dt, y, y′).

The existing level-4 machinery reportedly exhibits a measurable budget deficit
rather than an indefinite qualitative failure. Two different sharpenings
appear large enough, at least numerically, to potentially close that deficit.

That combination is rare:

> a known theorem barrier + a quantified deficit + multiple plausible sources
> of recoverable slack.

### Recommended subteams

Allocate 6–7 agents.

- **Team A — Mixed-depth counting dual.** Derive the strongest possible
  two-dimensional dual involving dt, y, y′. Retain depth information that
  previous scalar projections discarded. The immediate objective is a rigorous
  Level-6 inequality rather than another numerical relaxation.
- **Team B — Recover discarded payments.** Audit the level-4 counting argument
  for losses caused by: non-adjacent interactions; crude multiplicity caps;
  discarded overlapping constraints; uniform bounds replacing
  geometry-sensitive bounds. Measure the exact amount recoverable from each
  refinement.
- **Team C — Collective charging / local potentials.** The existing pointwise
  pair charging appears potentially much looser than necessary. Search for a
  local potential or collective energy argument in which several neighboring
  pairs pay jointly rather than independently. This is one of the most
  plausible mechanisms for beating the current deficit.
- **Team D — Configuration adversary.** This team should not construct proofs.
  Its task is to generate hostile realizable configurations: periodic
  lattices; perturbed lattices; clustered configurations; alternating-depth
  patterns; quasi-periodic configurations; configurations near the empirically
  dangerous spacing around 0.6; high-multiplicity or mixed-mark examples where
  permitted. Any proposed inequality must survive this team.
- **Team E — Exact certification.** Translate promising numerical duals into:
  rational certificates; interval enclosures; exact finite LP duals; formally
  checkable inequalities where practical. The numerical optimizer must never
  be the final authority.
- **Team F — Independent theorem reconstruction.** Re-derive the zero-side
  machinery directly from the pinned upstream definitions. This team must
  specifically guard against another transpose-versus-conjugate-transpose
  substitution.

### Definition of success

A success is not necessarily reaching 0.68185.

A major success would be either θ_full > 0 for a genuinely
configuration-sensitive correction that propagates through the exact zero-side
theorem, or a rigorous dual obstruction proving that bandwidth-one information
cannot improve the 0.6725007 result through this entire configuration class.

Either outcome materially changes the frontier.

## 2. Build the General Higher-ξ Hierarchy

The ξ″ investigation appears to have become much more important than its
original objective. What began as a check of historical percentages has
produced:

- corrected coefficient arithmetic;
- an explicit generating mechanism;
- a controlled coefficient tail;
- a rebuilt logarithmic-derivative representation;
- a new bridge argument extending beyond an apparent 1/2 barrier.

The next question should no longer be "What else can we calculate for ξ″?" It
should be:

> What is the general theory for zeros of derivatives of ξ?

For R_k(s) = ξ⁽ᵏ⁾(s)/ξ⁽ᵏ⁺¹⁾(s), derive a uniform mechanism for arbitrary k.

### Research targets

Seek formulas or recurrences for C_{k,i} and the associated form factors
F_k(α). Determine whether there are general laws governing:

- signs;
- rationality;
- generating functions;
- coefficient asymptotics;
- radius of convergence;
- entire continuation;
- behavior as k → ∞;
- dependence of the local zero process on derivative order k.

Use multiple independent constructions:

1. Bell-polynomial / differential-algebra derivation;
2. Dirichlet-convolution derivation;
3. symbolic generating-function derivation;
4. independent exact implementation.

### Allocation

3–4 agents.

### High-value outcome

A single general theorem generating the corrected higher-derivative arithmetic
would transform the Bian correction from a historical repair into a reusable
new theory.

## 3. Push the ξ″ Bridge from 0.51 Toward Bandwidth One

The current ξ″ work suggests a recurring pattern: several apparent bandwidth
barriers have turned out to be artifacts of lossy estimates.

The most recent extension beyond 1/2 is especially significant because it
arose from preserving the true logarithmic frequency separation instead of
collapsing it into a cruder cutoff estimate.

The right next question is therefore:

> What genuinely fails at 0.6, 0.75, 0.9, 1 − ε?

Do not merely rerun the same proof with larger parameters. Construct a
complete exponent budget for every analytic error term as a function of α. At
each target bandwidth, identify the first inequality that ceases to close.
Then classify that obstruction as:

- fundamental analytic barrier;
- avoidable Cauchy–Schwarz loss;
- cutoff artifact;
- finite-prime problem;
- contour choice;
- overly crude norm;
- lack of cancellation.

### Allocation

3 agents, plus an independent adversarial reviewer.

### Best possible outcome

A theorem valid throughout every compact subset of |α| < 1. A rigorous proof
of a genuine barrier below one would also be valuable.

## 4. Turn the Completed-CUE Oracle into Mathematics

The completed-CUE derivative experiments currently serve as a powerful
independent numerical oracle. That should be upgraded into a theorem
programme. The key question is:

> F_k^CUE(α) =? F_k^arith(α)

after the appropriate scaling and normalization.

Instead of merely observing agreement between random matrices and arithmetic,
derive the limiting derivative-zero process analytically.

### Approaches to parallelize

- determinantal-process methods;
- characteristic-polynomial identities;
- asymptotic random-matrix analysis;
- differential identities for completed characteristic polynomials.

### Allocation

2–3 agents.

### Why this is unusually attractive

Success would create a three-way equivalence:

> differential algebra ⟷ Dirichlet arithmetic ⟷ random matrices.

That would explain the higher-ξ coefficients structurally rather than merely
reproduce them.

## 5. Determine the Full Local Process of Derivative Zeros

Pair correlation captures only second-order information. A more ambitious
programme should ask what differentiation does to the entire local
GUE/CUE-style zero process.

Targets include: nearest-neighbor spacing, 3-point correlation, n-point
correlation, repulsion exponents, clustering statistics, and the dependence of
these quantities on derivative order.

The conceptual question is:

> Does differentiation induce a universal transformation on the local zero
> point process?

This could potentially unify several otherwise isolated observations in the
higher-ξ work.

### Allocation

2–3 agents. This should be regarded as a theory-building programme rather than
an immediate bound-improvement project.

## 6. Identify the Analytic Function Behind Corrected F₂

The coefficient series for corrected F₂ appears computationally well
controlled. That makes the next problem conceptual:

> What function is it?

Search systematically for:

- differential equations;
- integral representations;
- functional equations;
- hypergeometric forms;
- Bessel-type representations;
- continued fractions;
- explicit transforms;
- coefficient asymptotics;
- singularity or entire-function structure.

Numerical recognition methods such as PSLQ may be used for discovery, but no
recognized identity should be promoted without proof.

### Allocation

2 agents. A successful closed or structural representation may simplify both
bandwidth-one analysis and the general-k hierarchy.

## 7. Complete the Kernel-Checked Davenport–Heilbronn Result

This is one of the strongest near-term formalization opportunities.

The architecture already appears largely present for a machine-checked theorem
showing that zeta-like functional symmetry alone cannot imply RH, using the
Davenport–Heilbronn example.

The main remaining cost is certified evaluation.

A promising optimization is to replace rectangular complex enclosures for
m^{−s} with a polar or mean-value representation that avoids significant
dependency inflation.

### Allocation

2 agents. One owns the analytic enclosure. One owns certificate generation,
Lean integration, and final kernel checking.

### Win condition

A zero-sorry, independently checkable theorem in the proof assistant. This
would be a clean standalone contribution even if none of the numerical zeta
bounds move.

## 8. Upstream Formal Mathematics into Mathlib

Two particularly good formalization targets have emerged.

- **Sturm root counting.** This is broadly useful outside the zeta project and
  appears to fill a genuine general-purpose gap.
- **Hardy Z.** A formal Hardy Z construction would provide the correct
  foundation for future critical-line computations and may avoid some of the
  branch-management difficulties associated with direct complex logarithms
  of Γ.

### Allocation

2 agents, operating mostly independently. Avoid duplicating other ongoing
formalization efforts where equivalent theorems are already being developed
elsewhere.

## 9. Moonshot: Solve the Local-to-Global Positivity Problem

The earlier local-positivity experiment found that individual prime/place
contributions can sometimes be represented as norms. However, the local pieces
do not consistently possess the sign required to make naive prime-by-prime
positivity work globally. That route is closed in its simple form.

The more interesting successor is:

> What additional global structure would make the local arithmetic pieces
> assemble into a single canonical positive pairing?

Potential structures include:

- cross-place coupling;
- global cocycles;
- intersection pairings;
- cohomological constructions;
- operator models;
- constrained Hilbert-space embeddings.

The desired architecture is:

> prime arithmetic → global object → canonical pairing → ‖Φ(f)‖² → Weil
> positivity.

### Mandatory adversaries

Any construction must structurally exclude non-RH rivals such as
Davenport–Heilbronn and inappropriate Epstein combinations. It is not
sufficient for the proposed representation to "work numerically" for ζ.

### Allocation

2 long-horizon agents. This is low-probability but potentially
transformational.

## 10. Generalize the de Bruijn–Newman Repair Clock

Previous experiments suggest that certain collision times under heat flow may
be determined largely by the geometry of the initial zero configuration rather
than by arithmetic coefficients. That observation should be generalized across
families.

Build a parametric heat-flow framework for completed L-type kernels and ask:

- which flow observables are universal consequences of zero geometry?
- which retain genuine arithmetic information?
- can zero-dynamics approximations be rigorously connected to the underlying
  PDE?

### Allocation

2 agents. The desirable outcome is a theory separating universal zero dynamics
from genuinely arithmetic flow invariants.

## 11. Revisit Euler-Product Defect vs. Zero Geometry — Correctly

The earlier attempt to correlate factorization defect with a zero-position
statistic was not methodologically valid enough to support its conclusion.

Do not simply rerun the correlation. Invert the research question. Ask:

> Are Euler-product structure and zero geometry fundamentally independent
> coordinates, or is there a deeper joint invariant connecting them?

Construct families in which factorization defect and zero geometry can be
varied independently. Attempt either to:

- discover a real structural coupling; or
- prove an independence theorem/counterfamily showing no scalar relationship
  can suffice.

### Allocation

1–2 agents. A rigorous negative theorem would be a successful outcome.

## 12. Build a Certified Adversarial Weil-Function Explorer

The existing Weil machinery can be turned into a much stronger experimental
platform.

One agent searches large spaces of admissible spectral factors/test functions
for extremal or suspicious behavior. A second independent backend certifies
candidate values rigorously. A third implementation should eventually
duplicate the certification without sharing the same upstream transformation
code.

The purpose is not to infer RH from finite positivity testing. The purpose is
to:

- stress-test structural conjectures;
- locate extremal test functions;
- generate counterexamples;
- identify where candidate positivity principles actually become sharp.

### Allocation

2–3 agents.

## 13. Make Verifier Independence Measurable

One of Zeta Lab's most important methodological findings is that two
independent numerical backends can agree and still be wrong when they share
the same faulty upstream transformation.

Therefore:

> "checked by two implementations" is not enough.

Build a provenance DAG for every important computation. Record shared ancestry
in:

- source data;
- parsers;
- normalizations;
- mathematical transformations;
- discretizations;
- contour choices;
- intermediate formulas;
- certification policies.

Then quantify something like an **independence radius**:

> At what earliest mathematical/implementation layer do the two verification
> paths become genuinely independent?

### Allocation

2 infrastructure agents. This would improve the reliability of every other
programme.

## 14. Run a Repository-Wide Guard Offensive

The existing verification work has already shown that guard failures are a
meaningful source of false confidence.

A dedicated adversarial team should inspect every important guard and ask:

> What exact incorrect computation is this guard supposed to detect, and has
> that detection power actually been demonstrated?

For each guard:

1. identify its intended lesion;
2. construct the smallest mutant exhibiting that lesion;
3. confirm the guard fires;
4. identify nearby lesions it does not detect;
5. document its true scope.

### Allocation

2 destroyer agents. They should do no feature development.

## 15. Complete the External-Referee Experiment

Zeta Lab's verification methodology should be tested by outsiders — or by
agents operating without access to the internal cultural assumptions that
created it.

Give a clean specification to an isolated team and see whether it can
independently construct a meaningful adversarial battery.

Likewise, stronger external semantics tools such as Alive2 should be
incorporated where applicable in compiler-oriented experiments.

### Allocation

1–2 agents. This tests whether Zeta Lab's methodology is genuinely
transferable rather than internally self-consistent.

## 16. Turn the Equivalence Web into a Research Scheduler

The repository already records relationships among methods and statements.
That information should become operational.

Construct a theorem/dependency graph linking areas such as: pair correlation;
simplicity; zero density; derivative-zero statistics; explicit formulas;
moments; Weil positivity; Li/Jensen-type criteria; Newman flow; Selberg-class
structure.

Then rank unresolved statements by their downstream leverage. The scheduler
should favor questions where one resolution:

- opens many paths;
- kills many redundant paths;
- resolves multiple equivalent formulations;
- invalidates a broad family of heuristics.

### Allocation

1–2 agents. This could substantially improve the efficiency of future
parallel-agent research.

## Recommended Allocation for ~30 Research Agents

A reasonable first allocation is:

| Programme | Agents |
| --- | --- |
| Full-data configuration / Level 6 | 7 |
| Higher-ξ hierarchy | 3 |
| Push ξ″ bridge toward bandwidth 1 | 3 |
| CUE theorem + derivative-zero process | 3 |
| Formalization / Mathlib | 3 |
| Global positivity / ontology moonshots | 2 |
| Heat-flow programme | 2 |
| Weil / structural experiments | 2 |
| Verification, guards, provenance, adversarial review | 5 |

The numbers should remain flexible. Agents should be reassigned when a branch
hits a proven barrier rather than being kept alive merely because capacity was
originally assigned to it.

## Organizational Rule: Constructors and Destroyers Must Be Separate

The strongest lesson from Zeta Lab's recent work is methodological.

Do not assign every agent to construct a proof. For major claims, maintain
three roles:

- **Constructor.** Find the strongest possible theorem.
- **Independent reconstructor.** Derive the result by a genuinely different
  mathematical route.
- **Destroyer.** Assume the theorem is false. Search specifically for:
  normalization failures; transposes replaced by adjoints; shared
  implementation ancestry; hidden completeness assumptions; invalid limit
  interchange; non-realizable extremizers; missing tails; finite-grid
  artifacts; rival examples.

For important results, the destroyer should ideally work without seeing the
constructor's detailed reasoning until it has independently generated hostile
examples.

## Explicit Do-Not-Fund List

Unless materially new information appears, avoid allocating research capacity
to:

- another scalar/pair-measure LP;
- generic window reoptimization with unchanged information;
- the withdrawn transpose-to-adjoint positivity construction;
- attempts to bypass the λ > 1 obstruction without new prime-side input;
- another unchanged CGdL transplant;
- naive prime-by-prime positivity;
- the closed finite Poisson-cokernel matrix route;
- Lehmer heuristics based only on small |Z|;
- rediscovery of Bian's historical percentages;
- numerical optimization before the underlying arithmetic object is certified.

These mechanisms have already provided their useful information.

## Recommended Executive Decision

Authorize three principal programmes immediately:

1. **Flagship** — Full-data configuration realizability / Level-6 mixed-depth
   dual. Give this the largest team and explicit authority to pursue either a
   positive correction beyond 0.6725007 or a rigorous impossibility result.
2. **Theory Programme** — General F_k hierarchy for zeros of derivatives
   of ξ. Treat the repaired ξ″ calculation as the k = 2 instance of a
   potentially general theory.
3. **Moonshot** — Global positive pairing from prime arithmetic. Pursue the
   deeper local-to-global structure exposed by the failure of naive placewise
   positivity.

At the same time, maintain an independent verification division covering:

- adversarial configurations;
- theorem reconstruction;
- guard testing;
- verifier-independence analysis;
- exact/interval certification.

## Bottom Line

Zeta Lab should not behave as though it has one promising idea left.

It currently has multiple mathematically distinct live frontiers, several of
which became clearer precisely because earlier approaches failed. The
highest-value strategy is therefore a portfolio:

> configuration-level zeta frontier + general derivative-zero theory +
> structural moonshots + hostile verification.

The full-data configuration problem deserves the strongest immediate push
because it sits directly at a known quantitative frontier and retains
information that all cheaper relaxations discard.

The higher-ξ programme deserves simultaneous investment because the correction
of F₂ appears to have exposed a broader derivative-zero theory waiting to be
developed.

The structural programmes should remain alive because a genuinely new route to
RH is unlikely to look like another decimal-level optimization of machinery
whose information ceiling is already understood.

The operating principle should be: **exploit known sharp fronts aggressively,
while maintaining enough independent bandwidth to discover an entirely
different theorem.**
