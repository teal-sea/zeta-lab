# Gate-5 property 6: the question is not well posed, and that is the finding

**Status: settled, in the sense that matters, and explicitly not settled in
one arm.** Nothing here is a result in the repository's sense, and nothing
here is evidence for or against RH (`docs/08`). A hunt is exploratory.

Parameters were preregistered in `MISSION.md` and committed at `c29c876`,
before any winding number was computed. `results.json` was written after.
The commit order is checkable in `git log`.

## The claim under test

`docs/09` gate #3, property 6:

> in a box strictly off the critical line, the completed function has no
> zeros

## Answer

**Property 6 as stated has no truth value, because the box is a free
parameter of the sentence and the verdict is a function of it.** Holding the
σ-band fixed at [0.7, 0.9] and changing only the height window flips the
verdict between DISTINGUISHES and VACUOUS. Both poles are realised, in the
same band, by the same code, at the same precision.

That is not a failure to settle the question. It is the answer to a
different and better question, and it is the one that had to be answered
first: **you cannot ask whether property 6 distinguishes until you say which
box, and the gate as written does not say.**

Once a box is named, each named box does have a verdict, and those are
reported below.

## The table

Zeros counted by the argument principle (`zeta.epstein.count_zeros_box`),
same routine for every function. `-` means not attempted; see *What I could
not settle*.

| box | σ-band | t-window | ξ | f (DH) | Λ_Q (2,1,3) | Λ_Q (1,1,6) | verdict for that box |
| --- | --- | --- | --- | --- | --- | --- | --- |
| B1 | [0.7, 0.9] | [85.5, 85.9] | 0 | **1** | – | – | DISTINGUISHES (partial: not all rivals run) |
| B2 | [0.7, 0.9] | [10, 14] | 0 | 0 | 0 | 0 | **VACUOUS** |
| B3 | [0.7, 0.9] | [40, 44] | 0 | 0 | – | – | **VACUOUS** (forced by f alone) |
| B4 | [1.05, 1.55] | [10, 14] | 0 | 0 | 0 | 0 | **VACUOUS** |

All three rivals satisfy property 6 on B2 and on B4. On B2 that is three
independent RH-violating functions passing a property zeta passes, in a box
strictly off the critical line, which is exactly what "vacuous" means in
gate #3's sense.

Full per-count records, including evaluation counts, wall-clock and the
working precision each count ran at, are in `results.json`.

### Reading the flip

B1 and B2 and B3 share a σ-band. Every one of them is "a box strictly off
the critical line". In B1 the Davenport–Heilbronn function has a zero and
zeta does not, so property 6 separates them. In B2 and B3 neither has a
zero, so property 6 holds of the rival too and separates nothing. Same
property, same band, same code, opposite verdicts.

The mechanism is not subtle and is worth stating plainly: an
RH-violating function does not violate RH *everywhere*. Davenport–Heilbronn
has a positive proportion of its zeros on the critical line, and its
off-line zeros are sparse. A box that misses them sees a function that looks
exactly like one satisfying RH. So a *local* zero-free statement cannot
carry a *global* distinction, and property 6 is local by construction.

## What I chose, and why

The choices are in `MISSION.md` with their reasons; the short version:

- **σ ∈ [0.7, 0.9]** — strictly off the line, strictly inside the strip,
  clear of the Λ_Q pole at s = 1, and containing 0.80852, the real part of
  the Davenport–Heilbronn off-line zero this repository pins. That
  containment is **declared non-blind**: B1 exists to realise the
  "a rival fails" pole, not to supply a verdict.
- **B2 and B3 are blind** — width-4 windows at low and middling height,
  chosen for short boundary, with no knowledge of where any rival's zeros
  are.
- **σ ∈ [1.05, 1.55]** for B4 — the band where zeta is zero-free as a
  theorem rather than as a computation, testing whether property 6 is
  anything other than the Euler product that property 5 already tests.
- **Total boundary length, not box area, is the cost.** The prior attempt's
  box has boundary 20.6 at t ≈ 90, which is the most expensive place the
  Epstein evaluation can be asked to work. The four boxes here total 27, but
  three sit low.

## The defect that cost this hunt its high-t Epstein arm

The first run of `probe.py` used dps = 20 everywhere, as preregistered, and
did not return on the first Epstein count. The cause is a real and
reproducible precision defect in `zeta.epstein.epstein_completed`, measured
at σ = 0.8 on form (2,1,3) by comparing dps = 20, 40 and 80:

| t | \|Λ_Q\| | dps 20 vs dps 80 |
| --- | --- | --- |
| 5 | 9.53053e-4 | agrees to 6 significant figures |
| 14 | 2.06288e-9 | agrees to 6 significant figures |
| 44 | 1.02595e-29 | dps 80 gives 1.0261e-29 — **4 correct digits**, and arg differs in the 3rd |

The cause is structural. `epstein_completed` returns
`d^{s/2} · (first + second/√d + 1/(√d(s−1)) − 1/s)`, whose last two terms
are O(1/t), while the answer decays like |Γ(s)| ~ exp(−πt/2). So about
`πt / (2 ln 10) = 0.6822 · t` digits cancel. At dps = 20 the **phase** of
Λ_Q is noise above t ≈ 30, and `count_zeros_box`'s adaptive bisection then
recurses to its depth limit (45) on every segment. It does not fail; it
does not return.

**This is very likely what killed the previous attempt too.** That run asked
for exactly this — Epstein counts at working precision in a box reaching
t = 90 — and reported a timeout. The natural reading was "the contour is
long". The measurement above says the contour length was not the binding
constraint: at t = 90 the count was being driven by a phase that carried no
correct digits, and no amount of waiting would have produced an answer. That
reading is offered as a diagnosis consistent with the symptom, not as a
verified account of a run this hunt did not observe.

The response was a documented deviation from `MISSION.md`: Λ_Q is evaluated
at `dps = 20 + ceil(0.6822 · t_max)`, a rule that is a function of the box
alone and was written from the accuracy table above, before any Epstein
winding number existed. ξ and f keep dps = 20; both were checked to be
unaffected. The deviation is recorded here rather than folded into the
preregistration.

## What I could not settle

**The Epstein arm on B1 and B3.** The guarded precision the rule demands is
dps ≈ 79 for B1 and dps ≈ 50 for B3, at roughly 9 s and 3.5 s per
evaluation respectively, against 24 and 124 boundary evaluations per form
before adaptive refinement. That is about 15 minutes per box for the two
forms together, and it did not fit this run. It is a cost, not an obstacle:
**both are reachable in about half an hour of compute**, and nothing about
them is uncertain except the numbers.

Consequences for the table, stated exactly:

- **B1's verdict is partial.** DISTINGUISHES holds on the rivals actually
  run. An Epstein zero inside B1 would not change it; an Epstein *absence*
  would flip B1 to VACUOUS and would strengthen, not weaken, the
  well-posedness finding.
- **B3's verdict is not partial in any way that matters.** VACUOUS is
  already forced by Davenport–Heilbronn alone, because gate #3 asks the
  structure be ungrantable to *every* rival, so one rival sharing it settles
  the box. Running the Epstein arm on B3 cannot change the verdict; it would
  only add two numbers.

So the well-posedness conclusion does not depend on the missing arm: it
needs B1 to be DISTINGUISHES-or-not-VACUOUS and B2/B3 to be VACUOUS, and
Davenport–Heilbronn supplies both on its own.

## What a well posed version would be

The gate is asking for a *global* zero-free statement and has written a
*local* one. Three repairs, in increasing order of how much they actually
say:

1. **Name the box in the gate.** Make property 6 read "no zeros in
   σ ∈ [0.7, 0.9], t ∈ [85.5, 85.9]". Then it has a truth value and it
   DISTINGUISHES (on the rivals run here). It is also worth almost nothing,
   because the box was chosen knowing where a rival's zero is. A gate whose
   discriminating power comes from having been shown the answer is measuring
   its own selection criterion, which is the trap `hunts/README.md` names
   under control role #1.
2. **Quantify over all boxes in a band**: "for every t, the completed
   function has no zeros with σ ∈ [1/2 + δ, 1]". This is RH with a margin.
   It distinguishes, and it is not checkable in a box — which is the honest
   content of the observation, not a defect of the repair.
3. **Quantify over the band where zeta has a theorem**: "no zeros with
   σ > 1". Zeta satisfies this by the Euler product, unconditionally.
   Davenport–Heilbronn does not — Davenport and Heilbronn proved in 1936
   that it has zeros in σ > 1, and the same is classical for Epstein zetas
   of class number greater than one. This repair is checkable, it
   distinguishes, and it is the interesting one — but note what it has
   become: **it is the Euler product again**, which is property 5, which the
   battery already records as DISTINGUISHES.

That last point is the substantive content of this hunt beyond the
well-posedness finding. Every repair of property 6 that both (a) has a truth
value and (b) distinguishes, turns out to be either RH itself or the Euler
product. Property 6 does not appear to be an independent sixth property. It
is a local shadow of properties the battery already has, and its apparent
independence comes entirely from the box it does not name.

B4 was designed to test exactly this, and it came back **VACUOUS**: in
σ ∈ [1.05, 1.55], t ∈ [10, 14], all four functions have no zeros. That is
the asymmetry B4 could not escape, and it is worth stating as a result
rather than as a disappointment. Zeta's 0 in that band is a *theorem* and
holds for every t; each rival's 0 is a *measurement* in a window of height
4, and is silent about the band as a whole. Davenport–Heilbronn's zeros in
σ > 1 exist by the 1936 theorem; a width-4 window that misses them is not
evidence that they do not. So even the good repair, restricted to a box,
reports VACUOUS — the discriminating content lives in the quantifier over
all t, which no box can carry.

## Controls

- **Rival** (`hunts/README.md` #1): the rivals are the battery's own, and
  the trap named there applies to B1 and is declared, not evaded.
- **Precision response** (#4): the Epstein arm was re-run at raised
  precision precisely because the dps = 20 phase failed to respond as a real
  quantity should; the accuracy table is the response curve. ξ and f were
  checked to be insensitive at dps = 20 over these boxes.
- **Self-consistency**: zeta's count is 0 on all four boxes, so no box
  invalidated itself under the preregistered rule.
- **Not run**: no lesion or surrogate control. Neither is meaningful for a
  winding-number count whose oracle is integrality.

## Loose threads

- **The Epstein arm on B1 and B3.** Two counts per box at dps 79 and 50.
  About half an hour of compute settles both. Nothing conceptual is missing.
- **`epstein_completed` loses 0.68·t digits and says nothing about it.**
  A caller asking for dps = 20 at t = 44 gets four correct digits and no
  warning. A height-aware guard, or a returned accuracy estimate, would
  have saved this hunt an hour and probably saved the previous attempt its
  fifty minutes. This is a defect in a core module and this hunt may not fix
  it; it is reported.
- **`count_zeros_box` has no wall-clock or evaluation ceiling.** When the
  phase is noise, the adaptive bisection recurses to depth 45 and the call
  simply never returns. A depth-exhaustion counter that raised
  `ArithmeticError` — the failure mode the routine already documents — would
  have converted a hang into a diagnosis in seconds.
- **The battery counts Davenport–Heilbronn on `f` and the others on their
  completions.** Harmless in σ > 0, where the completion factors are
  zero-free and pole-free, and this hunt's boxes are all in σ > 0. It would
  not be harmless for a box reaching σ ≤ 0, where the trivial zeros
  enter and the two conventions genuinely differ.
- **Where are the Epstein σ > 1 zeros?** Davenport–Heilbronn's theorem
  guarantees they exist for class number greater than one, but this hunt
  found no height for them and did not look. A hunt that located the lowest
  one would turn repair #3 above from a citation into a computation.
- **Is any gate-5 property independent of properties 4 and 5?** This hunt
  suggests property 6 is not. Whether 1–3 are shadows of each other in the
  same way is not asked anywhere and is cheap to check.
