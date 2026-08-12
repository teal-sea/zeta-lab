# A machine-audited candidate improvement to the Cheer–Goldston refinement slot of the two-thirds theorem

**Zeta Lab — August 2026.  Working paper: candidate result, external review invited.**

## Statement

The August 2026 paper *"More than two thirds of the zeros of the Riemann
zeta function lie on the critical line"* establishes, unconditionally,

    N0(T, 2T) / N(T, 2T)  >=  2 − 1/c*₁ − o(1)  =  0.6725007036… − o(1),

where 1/c*₁ = ½ + 2^{−1/2}·cot(2^{−1/2}) is the Montgomery–Taylor
constant.  This working paper assembles, and audits step by step, a
candidate strengthening of the same chain by a Cheer–Goldston-type
gap-census floor transplanted into the paper's finite Frobenius
framework:

    candidate:   H  =  0.6725007037 + 2·θ·c_u  =  **0.6725106958**,

with θ = 0.995 the measured adversarial retention of the on-line
internal Gram mass and c_u = 5.021179×10⁻⁶ the hardened bucket floor of
the Montgomery–Taylor kernel at density ν = H.  The improvement is
+1.0×10⁻⁵ — small, but the point of this paper is not its size; the
point is the audit trail, which we believe is unusually complete for a
two-day, single-operator, consumer-hardware project, and which is
published in full.

**This is a candidate, not a theorem.**  Two inputs are cited from the
source paper rather than re-derived (its prime-side trace asymptotics
and its Theorem B simple-zero density), and no external expert has yet
reviewed the chain.  Everything else is measured, interval-hardened, or
kernel-checked as detailed below.  We state plainly what would make it
a theorem: review of the composition against the paper's §4–6
bookkeeping, and nothing else that we know of.

## What is kernel-checked (Lean 4 + Mathlib, sorry-free, standard axioms)

Both files were produced through the Aristotle theorem-proving service
and are in this repository with their `#print axioms` lines; the
statements were specified by us, the proofs machine-found and
kernel-checked.

1. **The composition skeleton** (`t3_composition_skeleton.lean`).  For
   unit vectors u_i, positive integer multiplicities m_i, N = Σm_i,
   P = Σ m_i u_i u_iᵀ, symmetric Q, R = Σ_{i≠j} m_i m_j ⟨u_i,u_j⟩², and
   D = R + 2tr(PQ) + ‖Q‖²_F:

       s ≥ 2N − ‖P+Q‖²_F + D,

   and the corollary: ‖P+Q‖²_F ≤ C·N and D ≥ θ·R₀ imply
   s ≥ (2−C)N + θR₀.  This removes the "does θ really enter
   multiplicatively?" analogy: it is exact arithmetic.

2. **The grid-incidence law** (`law_d_incidence.lean`).  For even,
   bounded, measurable φ supported in [−½, ½] — continuity NOT assumed;
   the paper's window jumps at the box edge —

       Σ_{n∈ℤ} φ̂(x−n) φ̂(y−n)  =  2π · FT(φ²)(x−y),

   with the three windows used here as explicit theorems.  The prover
   found a *better proof than we asked for* (polarised Parseval on
   ℝ/2πℤ instead of Poisson summation, so bounded-measurable suffices)
   and it *refuted a hypothesis gap in our own submission*, exhibiting
   a counterexample showing evenness is necessary — included in the
   file as `grid_incidence_needs_even`.

## What is measured and interval-hardened

- **The window identification.**  The paper's Theorem D window carries
  the cos(√2·) profile on φ² (its §7.1: "Writing φ²(u) = v(u/L)…",
  maximiser v*(s) = cos(√2 s)).  Its incidence kernel is then exactly
  the Montgomery–Taylor kernel — the mass kernel and the floor kernel
  coincide by construction, dissolving a pairing ambiguity that our own
  earlier window choice had created (and which cost us a conservative
  reading until caught).  The paper's functional (7.3), implemented
  once, reproduces the MT constant at v* (defect 7×10⁻⁹ on a shrinking
  ladder), Montgomery's 2/3 at v = 1, and shows our earlier window was
  an admissible-but-weaker class member (H = 0.667324).
- **The retention θ = 0.995**, at the paper's own field: single-pair
  band dual and multi-pair joint layer; pure box and ramp-mollified
  window (every allowed ramp fraction; the ramp costs margin, never the
  verdict); float and ball arithmetic (python-flint acb, both sides of
  every comparison enclosed, no Lipschitz blankets — the hardened caps
  are *tighter* than float).  An independent adversary hunt sandwiches
  the same grid point.
- **The identification dictionary.**  On explicit truncated-grid
  matrices: Gram = ω under LAW D normalisation; u·Q_p·u equals the
  chain's damage field W to 5×10⁻⁵; the pair Frobenius surplus equals
  the chain's slack(y) with trQ_p = 2 and one positive eigenvalue per
  pair measured; pair-pair cross traces measured NEGATIVE — the last
  place a hole could hide — and covered by the composition's 4-per-pair
  cushion.  End-to-end, gross and sharp inequalities hold on all
  configurations including adversarial placements derived from the
  field itself, and the measured worst adversary (0.0796) sits under
  the hardened cap (0.0907) under the budget (0.1534), nesting exactly
  as a one-sided chain must.
- **The bookkeeping.**  The census floor is monotone in ν (so the cited
  Theorem-B density enters one-sidedly); R/N converges on an N-ladder
  to the closed-form lattice reference; the beyond-window tail is an
  order under its charged allowance.

## What is cited, and what that means

The prime-side evaluation of tr G̃ and tr G̃² and the Theorem B density
are the source paper's theorems.  We use them as published.  A referee
of this candidate needs to check our composition against the paper's
§4–6 units and o(N) accounting — our finite-grid measurements of
exactly that bookkeeping are in `closing_bookkeeping.py` — and needs to
check nothing else that our ledger does not already expose.

## The defect ledger, or why we believe the rest

This project's controls caught **nine defects of our own** during the
work, including: a recurring blanket-margin artifact (three guises); a
θ = 1 convention mislabel; a kernel-pairing conflation that forced a
downward revision of our own headline; stale-constant propagation; a
quadrature under-resolution that ran a convergence ladder backwards; a
truncation-direction claim refuted by its own control within minutes;
and a missing evenness hypothesis caught by the theorem prover with a
counterexample.  Every one was found by a control or an independent
route; none by inspection.  We publish the full ledger
(`PROOF-LEDGER.md`, `TRANSPLANT-LEMMA.md`) because a result whose
error-catching record is hidden is a result whose error rate is
unknown.

## Reproduction

Everything runs from this repository on consumer hardware:

    hunts/frontier_math/paper_pin.py            # window pin, functional (7.3)
    hunts/frontier_math/paper_chain.py          # theta at the paper field
    hunts/frontier_math/paper_joint.py          # multi-pair joint layer
    hunts/frontier_math/hardened_paper.py       # ball-arithmetic pass
    hunts/frontier_math/ramped_field.py         # ramp mollification
    hunts/frontier_math/identification_seam.py  # the dictionary
    hunts/frontier_math/closing_bookkeeping.py  # census / units / tails
    hunts/frontier_math/*.lean                  # the kernel-checked pieces

The test suite pins every number quoted above.  Total elapsed effort:
two days, one operator, one consumer subscription plan, with the
theorem-proving service contributing two proofs in under forty minutes
combined.

## Invitation

We are seeking exactly one thing: adversarial review.  The fastest way
to make this a theorem — or to add a tenth line to the defect ledger —
is for someone who knows the source paper's §4–6 to read
`TRANSPLANT-LEMMA.md` top to bottom against it.  Both outcomes are
wins; the ledger is built to survive either.
