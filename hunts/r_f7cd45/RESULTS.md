# Hunt r_f7cd45: which structural properties of ζ actually discriminate

**Status: settled for the five properties issue #21 queued; the sixth was
already settled by earlier hunts in this tree, and what this run adds to it is
the number that says why it is expensive.**

Publishes the artifact
[issue #21](https://github.com/teal-sea/zeta-lab/issues/21) recorded as
queued. Gate #3 of `docs/09-new-ontologies.md`: whatever structure an ontology
grants ζ must be **ungrantable** to functions that share ζ's analytic
structure and violate RH. A property those rivals also satisfy distinguishes
nothing and cannot be the load-bearing step of an RH proof.

The three rivals are `zeta.epstein.battery`'s defaults: the
Davenport–Heilbronn function, and the Epstein zetas of the two discriminant
−23 forms (2,1,3) and (1,1,6). All three are linear combinations of legitimate
Euler products, which is the point: linear combination preserves the
functional equation and destroys the primitive multiplicative structure
(`docs/09` §5.1).

Nothing here is evidence for or against RH (`docs/08-why-it-is-hard.md`).
Gate #3 is eliminative, never probative: *prime-blind ⟹ not an explanation*,
but **not** *prime-sensitive ⟹ proof*.

Reproduce: `.venv/bin/python hunts/r_f7cd45/probe.py`

## The five properties (stage 1)

`dps = 25`, all four functions, every cell computed. ✓ = the function has the
property.

| # | claimed property of ζ | ζ | D–H | Eps (2,1,3) | Eps (1,1,6) | rivals surviving | verdict |
|---|---|---|---|---|---|---|---|
| 1 | the completed function satisfies F(s) = F(1−s) | ✓ | ✓ | ✓ | ✓ | 3 of 3 | **VACUOUS** |
| 2 | there is a Hardy-style Z, real-valued for real t | ✓ | ✓ | ✓ | ✓ | 3 of 3 | **VACUOUS** |
| 3 | the function has zeros on the critical line | ✓ | ✓ | ✓ | ✓ | 3 of 3 | **VACUOUS** |
| 4 | the Dirichlet coefficients are multiplicative | ✓ | ✗ | ✗ | ✗ | 0 of 3 | **DISTINGUISHES** |
| 5 | the coefficients are completely multiplicative | ✓ | ✗ | ✗ | ✗ | 0 of 3 | **DISTINGUISHES** |

This reproduces issue #21's table exactly, cell for cell, from a probe that
runs end to end. Three of the properties most often cited as structural
insight into ζ are worth nothing as discrimination: every RH-violating
look-alike has all three. Only the prime structure kills the rivals.

Cost, measured: 24.3 s, 23.9 s, **853.8 s**, 0.0 s, 0.0 s. Property 3
dominates the run by a factor of thirty, because it counts sign changes of Z
on `t ∈ [10, 40]` for two Epstein forms. A narrower window would have bought
the same verdict; that width was not tuned and should have been.

### What was chosen, and why

- **Property 4's pair set excludes m = 1 on purpose.** The Epstein coefficient
  is a representation count with r(1) ≠ 1, so a pair (1, n) would fail on
  normalisation rather than on multiplicative structure. Restricting to
  coprime m, n ≥ 2 gives every rival its best shot. They fail anyway: for the
  principal form (1,1,6), r(2) = r(3) = 0 but r(6) = 2; for
  Davenport–Heilbronn, a₆ = a₁ = 1 but a₂a₃ = −κ² = −0.0807….
- **Property 2 carries a degeneracy guard.** A Z identically zero would
  satisfy "real-valued for real t" vacuously, so the claim first requires Z to
  be somewhere non-zero on the sample set.
- **Properties 1 and 4 reuse `zeta.epstein.claim_functional_equation` and
  `claim_multiplicativity`** rather than restating them, so the published
  verdict is the packaged claim's verdict. Properties 2, 3 and 5 are new here.
- **Positive control throughout: ζ satisfies all five.** A probe in which ζ
  failed a property it demonstrably has would be reporting a defect in itself.

## The sixth property (stage 2): already settled, and here is the price tag

Issue #21 lists a sixth property, *"in a box strictly off the critical line
the completed function has no zeros"*, as unfinished at a 50-minute timeout.
**That is stale.** Three hunts in this tree settled it after the issue was
written:

- **Hunt #13** (`gate5_p6_a/`): VACUOUS on an adversarially chosen box.
- **Hunt #14** (`gate5_p6_b/`): VACUOUS on two of three boxes, with the
  Davenport–Heilbronn zero recovered as a positive control on the third.
- **Hunt #15** (`gate5_p6_c/`): the question as written **has no truth value**,
  the box is a free parameter of the sentence, and holding the σ-band fixed
  while moving the height window flips the verdict.

This run reproduces that independently on two preregistered boxes
(`MISSION.md`, committed at `53c8cd1`, before any winding number was
computed), σ ∈ [0.6, 0.9]:

| box | Im | ζ | D–H | Eps (2,1,3) | Eps (1,1,6) | verdict |
|---|---|---|---|---|---|---|
| B1 | [80.0, 81.0] | 0 zeros | 0 zeros | inadmissible | inadmissible | **VACUOUS**, forced by D–H alone |
| B2 | [85.0, 86.0] | 0 zeros | **1 zero** | inadmissible | inadmissible | **UNDECIDED** |

B1 is VACUOUS and the undecided Epstein cells cannot overturn it: gate #3 asks
the structure be ungrantable to *every* rival, so one surviving rival settles
the verdict on its own. B2's D–H cell returns exactly **1**, recovering the
off-line zero this repository pins at 0.8085171824… + 85.6993484853…i. That is
the run's positive control, and it is why B2 is undecided rather than vacuous:
with D–H failing the property, the verdict turns on the Epstein arm, which
this run could not afford.

Same property, same σ-band, same code, opposite verdicts one height apart.
That is hunt #15's finding, reproduced.

### The number this run adds: the precision floor, measured

The Epstein cells are marked *inadmissible*, not *slow*. Before spending any
budget on a winding number, the probe ran each completed function up a dps
ladder at 0.75 + 85.5i and asked where the value stops moving. 15 was the lowest rung tested, so a floor recorded as
15 means "≤ 15", not "exactly 15":

| function | converged \|F(0.75+85.5i)\| | convergence floor | preregistered dps = 15 |
|---|---|---|---|
| ξ (Riemann) | 3.04e−26 | ≤ 15 | adequate |
| Davenport–Heilbronn | 3.00e−29 | ≤ 15 | adequate |
| Epstein (2,1,3) | **1.99e−58** | **dps 60** | **inadequate** |
| Epstein (1,1,6) | **5.00e−58** | **dps 60** | **inadequate** |

At `dps = 15` the Epstein completed function returns ≈ 5e−30 where the true
value is ≈ 2e−58: noise larger than signal by 28 orders of magnitude. At the
`dps = 20` that `battery` actually uses it returns ≈ 2e−33, still noise by 25
orders of magnitude. This independently confirms the cancellation defect hunts
#14 and #15 reported (≈ 0.6822·t digits lost; 0.6822 × 85.5 ≈ 58, which is
exactly the gap measured here) and puts a floor on it: **dps ≈ 60 at t ≈ 85.5**.

Two consequences worth stating plainly:

1. **`count_zeros_box`'s integrality check does not catch this.** Noise winds
   to an integer as happily as signal does. A box count run below the floor
   returns a plausible small integer and is not a zero count. My own
   preregistered `dps = 15` would have produced one; the probe skips those
   cells rather than publish them.
2. **`battery` cannot clear its own floor.** Both rival interfaces hardcode
   `dps=min(dps, 20)` into `count_zeros_box` (`zeta/epstein.py:1091`,
   `:1141`). No value the caller passes reaches the routine above 20, so the
   packaged property-6 route is below the convergence floor for every
   t ≳ 30 and cannot be fixed from the outside. This is a `zeta/` defect,
   outside this hunt's scope, reported and not patched.

At `dps = 60` one `epstein_completed` evaluation costs 8.8 s (measured), and a
unit-height box boundary needs of order 10²–10³ of them. That is the price tag
on the Epstein arm, and it is why three hunts in a row have declared it out of
budget. It is not a hard problem; it is an expensive one, and the expense is a
fixable implementation defect rather than a fact about the mathematics.

## What this run could not settle

- **The Epstein arm of property 6, on any box above t ≈ 30.** Third
  independent time. Affordable only after the cancellation defect is fixed;
  the estimate above is 10²–10³ × 8.8 s per cell as the code stands.
- **Anything about novelty.** No literature search was run. These are original
  results of this laboratory in the provenance sense; whether the observation
  is new to the world is unsearched and is not claimed.
- **Whether properties 4 and 5 are the *only* discriminators.** Five
  properties were tested because five were queued. The battery admits any
  claim; nothing here bounds the space of properties that might also
  distinguish.

Grade: **measured**, float and mpmath, one route per cell, with ζ as a
positive control on every property and the pinned Davenport–Heilbronn zero as
a positive control on box B2. Not hardened: no enclosure carries these steps.

## Loose threads

- **`battery`'s rival interfaces cap `count_zeros_box` at `dps = 20`.**
  Why it might matter: it silently caps the packaged gate-#3 property-6 route
  below its own convergence floor for every t ≳ 30, and the routine's
  integrality check cannot detect the resulting noise, so the failure mode is
  a plausible wrong integer rather than an error. Hunts #14 and #15 reported
  the cancellation; this adds that the cap makes it unreachable from the
  caller. First step: change `min(dps, 20)` at `zeta/epstein.py:1091` and
  `:1141` to a floor derived from the box height, hunt #14's measured
  ≈ 0.6822·t digit loss plus guard digits, which at t = 85.5 predicts ~58 and
  brackets the 60 measured here, and pin it with a test that the count at
  t ≈ 85.5 is stable between `dps = 60` and `dps = 100`.
- **Property 3 cost 853.8 s of a 900 s stage for a verdict visible in
  seconds.** Why it might matter: `zeros_on_line` is quantified over a window
  that nothing chose, and the same VACUOUS verdict follows from any window
  containing one zero of each function. First step: narrow `LINE_WINDOW` to
  `(10, 16)` in `probe.py` and confirm the five verdicts are unchanged; if so
  the whole stage runs in under a minute.
- **Property 6 is still carried by the battery as a property.** Why it might
  matter: three hunts have now concluded it is a (function, box) pair rather
  than a property, and hunt #13 already proposed retiring it. It keeps
  attracting budget, this run included. First step: the disposition is a
  `zeta/` decision, not a hunt's; someone with that scope should either retire
  it or replace it with the box-free version hunt #13 drafted.
- **Issue #21's "not yet settled" section is stale.** Why it might matter: it
  is what routed this run at the sixth property, and it will route the next
  one the same way. First step: comment on issue #21 pointing at hunts #13,
  #14, #15 and at this artifact, and edit that section.
