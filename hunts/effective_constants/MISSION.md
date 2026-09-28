# MISSION: `effective_constants`

**Opened 2026-08-13.** Nothing in this directory is a result.

## Why this hunt exists

The transplant chain's headline caveat is that the improved constant is a
**liminf** statement and is not numerically effective: the crossover sits at
`T₀ ≈ 10^(1.6773e6)`, and `PROOF-LEDGER.md` records the shape as
`T₀ ~ exp(38.5/ε)`, so an ε-improvement costs height exponential in `1/ε`.
That caveat is inherited from the source paper, not introduced by the
transplant.

The usual reading of "inherited" is that nothing can be done about it. That
reading looks wrong, and this hunt exists to test it.

**The ineffectivity is localised, not diffuse.** `PROOF-LEDGER.md` (blocker 3,
residual (i)) already states it: *"T₀ is a reference not an effective bound,
four existential EvBound constants would make it effective and nothing else in
the budget would."* Everything else in the error budget is explicit; the
dominant term was derived from parts (`35.519106`, matching measurement to
four digits at `l = 1e4/1e5/1e6`).

**And the fog enters as an assumption, not as a derivation.** In the upstream
package the relevant facts are fields of a `Facts` structure, inputs the
formalisation takes from the paper's prose, each tagged with the paper's own
reference (`[prop:trace]`, `[lem:ends]`, `[prop:mumu]`, `[prop:PP]`,
`[prop:cross]`). Their common shape is

```lean
def EvBound (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → |f T| ≤ C * g T
```

whose own docstring says: *"explicit inequality with named constants, no
filter-o(1) until the final liminf wrapper."* So the design keeps constants
explicit right up to the end and then existentially quantifies them at the
interface. The constants are not lost to a mathematical obstruction; they were
never carried across the interface, because the paper's goal was a limit
statement and effectivity was not the objective.

That is a bookkeeping boundary, and bookkeeping boundaries can be crossed.

## What this hunt tries

Identify which `EvBound` fields are load-bearing for effectivity (the ledger
says four), read the source paper's proofs of exactly those propositions, and
determine for each whether its constant is **extractable** (the proof's
estimates carry trackable constants) or **essential** (the ineffectivity comes
from a genuine obstruction of the kind that makes Siegel's theorem
ineffective).

The verdict matters either way, and the negative verdict is the more
interesting one:

- **Extractable**: then an effective form of the chain is arithmetic, not new
  mathematics, and the crossover becomes a number someone can write down.
- **Essential**: then the obstruction has a name and a location, which is
  worth recording precisely because "it is inherited" currently functions as an
  explanation and is not one.

An effective form of the underlying bound would stand on its own, independently
of the `+1.0e-5` improvement it was reached through, and arguably matters more:
the improvement is unreachable at any computable height, while an effective
constant is usable at every height above its threshold.

## Scope

This hunt reads and measures. It does not modify the transplant chain, and it
does not touch `zeta/`, `ontology/` or `harness/`. Its output is a map of the
four constants with a per-constant verdict and, where a constant is
extractable, the extraction written out with its arithmetic checked.

```huntspec
id: effective_constants
question: Is the transplant chain's ineffectivity extractable bookkeeping or an essential obstruction?
frontier: crossover T0 ~ 10^(1.6773e6); shape T0 ~ exp(38.5/eps); dominant error constant already derived from parts at 35.519106
proposed_attack: locate the load-bearing EvBound assumptions, read the source proofs of exactly those propositions, and classify each constant as extractable or essential
dead_routes:
  - sharpening the transplant's own damage constants, blocker 3 records that the crossover shape comes from the source's o(1) coefficients, so no local sharpening moves it
  - treating calE as the dominant error term, measured wrong, the dominant term is a window-moment drift
required_oracles:
  - the source paper's own text, pinned by SHA-256
  - independent recomputation of any extracted constant from the stated estimate
  - interval arithmetic for any numeric threshold that is claimed
kill_conditions:
  - a load-bearing constant is shown to depend on an ineffective input of Siegel type, in which case the essential verdict is recorded and the extraction is abandoned
  - an extracted constant fails independent recomputation
  - the extracted threshold does not improve on the existential reference by any margin worth stating
agents_may:
  - read
  - derive
  - measure
  - code
  - record a per-constant verdict
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - modify the transplant chain
```
