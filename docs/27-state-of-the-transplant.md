# 27 — State of the transplant: what is kernel-checked, what is refuted, what is open

**12 August 2026.** A reading of the laboratory's current frontier work, written
because the state changed four times in one day and the front page carries only
the conclusions. `hunts/frontier_math/PREPRINT.md` is the working paper,
`hunts/frontier_math/PROOF-LEDGER.md` is the obligation-by-obligation ledger,
and this document is the map between them: what each piece claims, at which rung
of the certainty ladder, and what the day's two refutations cost.

Nothing here is evidence about the Riemann Hypothesis, and the laboratory claims
no progress toward it. The subject is one constant in one theorem
(`docs/08-why-it-is-hard.md` for why that distinction is not modesty).

---

## 1. The candidate

An outside paper of 10 August 2026 established unconditionally that

    N0(T, 2T) / N(T, 2T)  ≥  2 − 1/c*₁ − o(1)  =  0.6725007036… − o(1),

with `1/c*₁ = ½ + 2^{−1/2}·cot(2^{−1/2})` the Montgomery–Taylor constant, by a
finite Frobenius/rank-trace argument. This laboratory assembled and audited a
**candidate** strengthening of the same chain, transplanting a
Cheer–Goldston-type gap-census floor into the paper's framework:

    H  =  0.6725007037 + 2·θ·c_u  =  0.6725106958,

with θ = 0.995 the adversarial retention of the on-line internal Gram mass and
`c_u = 5.021179×10⁻⁶` the census floor of the Montgomery–Taylor kernel. The
improvement is +1.0×10⁻⁵.

It is a **candidate**, not a theorem, and the reason is structural rather than
social: a composite claim takes the grade of its weakest step, and one step is
open (§4). The certainty ladder in `AGENTS.md` is what licenses the word at each
rung; nothing below is rounded upward.

## 2. What is kernel-checked

Lean 4 + Mathlib, sorry-free, standard axioms only, no `native_decide`, no
floating point. Four pieces, each with its `#print axioms` line in the tree;
statements specified here, proofs machine-found through the Aristotle service
and checked by the kernel.

| # | Name | Statement | Where |
| --- | --- | --- | --- |
| 0 | The census floor | The census floor: `c_u ≥ 5.021172019×10⁻⁶` for the **genuine** MT kernel (`Real.sin`, `Real.sqrt 2`, `π`, not a rational surrogate), by explicit rational weak duality plus four kernel bounds proved with from-scratch Taylor machinery and explicit truncation error. Stated for any cost vector dominating those four bounds, so it survives their re-derivation. | `zeta23ext/Zeta23Ext/FloorCert.lean` |
| 0b | The retention certificate | The retention certificate's arithmetic: the recorded band-dual cover closes at its four depths, with `cap` defined by the genuine band supremum and infimum of ω², so the recorded numbers enter only as one-sided bounds and the statement cannot be vacuous, together with "no band was missed" as a property of the cover. | `zeta23ext/Zeta23Ext/BandCert/` |
| 1 | The composition inequality | The composition inequality `s ≥ 2N − ‖P+Q‖²_F + D`, with the corollary that `‖P+Q‖²_F ≤ C·N` and `D ≥ θ·R₀` give `s ≥ (2−C)N + θR₀`. This is what removes the question "does θ really enter multiplicatively?": it is exact arithmetic, not analogy. | `t3_composition_skeleton.lean` |
| 2 | The grid-incidence law | The grid-incidence law `Σ_{n∈ℤ} φ̂(x−n)φ̂(y−n) = 2π·FT(φ²)(x−y)` for even, bounded, measurable φ supported in [−½, ½]. Continuity is **not** assumed, which matters: the paper's window jumps at the box edge. | `law_d_incidence.lean` |
| 3 | The Pub 1 strong closure | The Pub 1 source-admissible strong closure: the supremum of `⟨1,v⟩²/⟨Av,v⟩` over the source-admissible class is `c* = ⟨1, A⁻¹1⟩`, with the reciprocal orientation as the matching infimum, and `orientation_not_symmetric` recording that the two quotients are genuinely different quantities so the load-bearing orientation cannot be silently swapped. **Conditional**: the principal theorem carries four analytic facts about `w` as explicit named hypotheses rather than assuming them as axioms, listed in `ZetaLean/Pub1/OBLIGATIONS.md`. The tree is sorry-free and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) against pinned Mathlib `v4.33.0-rc2`. | `lean/ZetaLean/Pub1.lean` |

Two things about item 2 are worth recording as method rather than result. The
prover returned a *better* proof than was requested — polarised Parseval on
ℝ/2πℤ instead of Poisson summation, so bounded-measurable suffices — and it
**refuted a hypothesis gap in our own submission**, exhibiting a counterexample
showing evenness is necessary. That counterexample ships in the file as
`grid_incidence_needs_even`. A prover that only ever agrees is not a check.

The reduction of the retention to the certificate of item 0b is carried as an
explicit named hypothesis (`H3`), on paper, not hidden inside the Lean
statement. That seam is named again in §4.

## 3. The two gaps closed on 12 August

**Depth-uniformity of the retention** (single-pair layer, `depth_uniform.py`).
The bound θ = 0.995 had been established at four sampled depths
y ∈ {0.02, 0.1, 0.3, 0.49}, while an off-line pair sits at an arbitrary
y ∈ (0, ½); until it was quantified over all y, the hypothesis the composition
consumes did not follow. Eighteen cells now tile (0, ½] exactly, and the shallow
end — which no ladder of cells can reach, since the interval has no smallest
point — is closed by homogeneity instead: the damage scales as y², the square
completion is convex through the origin, and slack/y² is bounded below by its
own limit at 0. One finite inequality where a grid cannot go. Grade: **hardened**
at double precision; arb or rational hardening over the eighteen cells is a named
next step, and the multi-pair layer's depth quantifier folds into §4.

**The finite-grid → asymptotic transfer.** The dictionary into the source's units
is derived and the conversion factor is exactly 1 (the normalised Gram is
grid-step independent); `a` equals our `A` bit-identically; and since
`‖P‖²_F = Σm² + R` exactly, the hypothesis becomes, purely in the source's own
objects, `‖Â‖²_F ≥ Σ_{S₁∪S₂} m_ρ² + 2θc_u·N(I′)`. The improvement does not drown
in the paper's error terms: it is a fixed constant against o(1), so the composed
statement is the same logical type as the source's own ε-form.

**The caveat that came with it belongs in the headline, not a footnote.** The
improvement is **not numerically effective at any reachable height**. The
crossover, where the error budget falls below the improvement, sits at
T ≈ 10^(1.7×10⁶), with shape `T₀ ≈ exp(38.5/ε)` for an ε-improvement. That shape
is inherited from the *source's* own o(1) coefficients rather than introduced by
the transplant, and the dominant term is not the paper's `calE` but a
window-moment drift whose constant we derive from parts (35.519106, matching
measurement to four digits). Reading "improvement" as "better at heights anyone
can compute" would be wrong, and it is cheaper to say so than to be asked.

## 4. What is open, and the route that was refuted

**Multi-pair universality.** The joint verdict is established over a tested set
of configurations — 320 randomised ones opened nothing, and the search
rediscovered the binding family blind — not over all configurations.

The obvious route was proposed here and is now **refuted**, which is the day's
second deliverable. The idea was per-pair domination: damage is additive across
pairs before the positive-part clipping, so `max(0, Σ) ≤ Σ max(0, ·)` should push
the joint cap under a sum of single-pair caps. It fails twice.

1. The field-level inequality holds exactly, as expected, but does not survive
   the square completion. A coincident stack collects k times the damage while
   paying the internal charge once; the joint cap exceeds the sum of single-pair
   caps by up to 3.4× for coincident stacks, with exact excess
   `[2Σ_{i<j}F_iF_j − (k−1)(cK)²]/(4cK)`. What moves is the occupancy, not the
   band set.
2. Decisively, the route could not have worked at all. From four pairs on a
   unit lattice — three at float grade only; the k = 3 line sits inside the
   float-vs-hardened gap and fits under budget at the hardened cap (+0.006) —
   the **sum of single-pair caps already exceeds the budget** while the joint
   verdict closes with 40 % margin. (The k = 3 boundary was first stated one
   grade too strongly; session defect #12, corrected in the ledger row it
   overstated.) The joint field's shielding is
   load-bearing, so no per-pair argument reaches θ = 0.995 in either direction.
   The slack assumed additive is not: its pair term is signed and erodes up to
   84 % of a pair's slack on the worst lattice.

Both attempted repairs fail for stated reasons. What survives is better posed
than what it replaces: with `c₂ = φ²∗φ²` (closed form, supported in [−1,1],
positive inside), `E[G] = A⁻²∫c₂|G|²`, `F_on(w) = Σ_x e^{ixw}` and
`F_p(w) = Σ_i 2cosh(y_i w)e^{it_i w}`, the whole verdict restates as a single
bandlimited nonnegative-kernel inequality in two exponential sums. A sharper
target than the obligation it replaces, and the machinery is in
`hunts/frontier_math/joint_universal.py` with its tests.

Two further inputs are **cited** from the source paper rather than re-derived:
its prime-side trace asymptotics and its Theorem B/D density. External review:
invited, none yet. That is the rung above kernel-checked on the ladder, and the
only one that makes words like "established" available.

## 5. A clean negative result elsewhere: `hprime`

Independently of the transplant, the Lean frontier's item 19 gate (`hprime`) is
**unprovable as stated** by a Chebyshev route: the inequality
`(2j)(2j+1)D_j(X) ≤ B(X)A_j(X)` puts the true mass on the right, which would
require an order-uniform *lower* bound on `A_j`. Two derivation chains, run
independently and told to differ deliberately, reached the same three
conclusions, with every link checked numerically at X = 250 and X = 5000: the
literal gate cannot close; it should be retargeted to a majorant `A_j ≤ M_j`
with the recurrence carried on M, which is what everything downstream actually
consumes; and the majorant satisfies that recurrence with **equality**, because
the factorial denominator makes `(j+1)(2j)(2j+1)` exactly the step ratio — the
tightness that defeats the literal gate is the equality the majorant enjoys.

Item 3 is kernel-checked (`ZetaLean/MajorantBypass.lean`). Route A reaches
`D = log 16 ≈ 2.7726` and is the one to formalise; route B reaches
`D = 60·log 4 ≈ 83.178`, a factor 30 worse, and is kept because its obstruction
argument is independent and sharper and its analysis is strictly
one-dimensional, which is a real formalisation advantage. Both chains are
written out in full in `hunts/higher_xi/HPRIME-ROUTES.md`, captured because they
existed only in a transient agent transcript.

## 6. Why the ledger is published with the result

Nine defects of our own were caught during this work: a recurring
blanket-margin artifact in three guises, a θ = 1 convention mislabel, a
kernel-pairing conflation that forced a downward revision of our own headline,
stale-constant propagation, a quadrature under-resolution that ran a convergence
ladder backwards, a truncation-direction claim refuted by its own control within
minutes, and the missing evenness hypothesis the prover refuted. Every one was
found by a control or an independent route. **None by inspection.**

That number is the reason the full ledger ships alongside the claim. A result
whose error-catching record is hidden is a result whose error rate is unknown,
and the honest reading of "nine caught" is not "we are careful" but "the rate is
high enough that the tenth exists". The invitation is therefore specific: a
reader who knows the source paper's §4–6 should read `TRANSPLANT-LEMMA.md` top
to bottom against it. Making this a theorem and adding a tenth line to the
defect ledger are both wins, and the ledger is built to survive either.

Everything reproduces from this repository on consumer hardware; the scripts are
listed in the preprint's Reproduction section and the suite pins every number
quoted above. Total elapsed effort at the time of writing: two days, one
operator, one consumer subscription, with the theorem-proving service
contributing two proofs in under forty minutes combined.

## 7. What landed alongside

`docs/26-the-adopted-builds.md` records the machinery that landed the same week
and the negative space around each piece: verification independence made
measurable (`harness/independence.py`, where backend agreement is evidence about
the ball arithmetic and nothing else), the guard offensive's ledger with its
tri-state `fired` whose default is "nobody has demonstrated anything", and
HuntSpec on probation. Read that document before treating any of it as a
capability; the honest edges are stated there, not here.
