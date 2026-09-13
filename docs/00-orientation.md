# 00. Orientation

Zeta Lab is a computational and formal workbench for studying the Riemann zeta
function, attempting original mathematics toward the Riemann Hypothesis (RH),
and establishing useful intermediate results. This is a research objective,
not a claim that RH has been proved by the laboratory.

**Scope clarification, 2026-09-12.** The owner has removed the old prohibition
on attempting RH or formalizing new mathematics. The current mandate is
[ALIGNMENT.md](../ALIGNMENT.md). A surprising result must be checked, not
accepted or dismissed automatically. Finite experiments, proof candidates,
ordinary proofs, numerical enclosures and kernel-checked theorems retain
different meanings and must be labeled accordingly.

The previous longer orientation is preserved
[unchanged as historical reading](../history/research-guidance-2026-09-12/orientation.md).
Its numerical examples, source notes and dated records have not been
re-audited by this scope correction. Its research prohibitions are not active.

## 1. The object

For `Re(s) > 1`, the Riemann zeta function has the convergent expressions

    zeta(s) = sum_{n >= 1} n^(-s) = product_p (1 - p^(-s))^(-1).

Unique factorization connects the sum over integers to the product over primes.
Analytic continuation gives a meromorphic function with a simple pole at 1.
The completed function

    xi(s) = (s(s-1)/2) pi^(-s/2) Gamma(s/2) zeta(s)

is entire and satisfies `xi(s) = xi(1-s)`. The details and conventions are
in `01-sums-integrals-and-continuation.md`,
`02-theta-heat-and-modularity.md` and `03-functional-equation.md`.

## 2. The statement

RH asserts that every nontrivial zero of the Riemann zeta function has real
part `1/2`. It does not also assert simplicity or a particular spacing law.
Those are different questions. Keep `xi(s)` distinct from the convention
`Xi(t) = xi(1/2 + it)` used by the code.

A proof attempt may use an equivalent formulation. Writing down the
equivalence alone does not establish the remaining condition, but the fact
that a condition is equivalent to RH is not a reason to prohibit studying it.
`07-equivalences-and-criteria.md` and `zeta/criteria.py` supply examples.

## 3. Why anyone cares

The explicit formula relates zeros to the weighted prime count
`psi(x) = sum_{p^k <= x} log p`. A term associated with a zero
`rho = beta + i gamma` has the form `x^rho/rho`. The full formula requires
its summation conventions, endpoints and remaining terms; an isolated
planted wave is not an alternative sequence of actual primes.

The classical von Koch equivalence connects RH to

    psi(x) = x + O(sqrt(x) (log x)^2).

See `04-explicit-formula.md` for the prime-zero connection and its precise
conventions. A finite pattern may motivate an estimate. Proving that
estimate uniformly requires an argument beyond the observed values.

## 4. What is rigorously known

The reading course covers zero-free regions, zero-density estimates,
positive-proportion theorems, finite-range zero verification and heat flow.
They address different statements and are not percentages of RH solved.
A displayed upper bound that permits an exceptional zero does not exhibit
one. Nor does failure to exclude that zero prove that the method can never
be strengthened.

Use each theorem in its stated hypotheses and range. For a numerical record,
new source input or contemporary frontier comparison, read the actual source
and record its version rather than repeating a historical introductory
number as current. No literature-wide update is claimed by this page.

A rigorous finite-range verification is a theorem about its verified range.
It does not settle an unbounded assertion merely by covering many examples.
Conversely, a finite certificate can support a uniform theorem when a proved
reduction supplies that implication. The reduction and certificate must both
be checked.

## 5. What is conjectural or heuristic

The lab also studies statistical models, candidate inequalities, spectral
interpretations, real-rootedness and analogies with other settings. A fit,
model analogy or agreement between implementations is not automatically a
proof. Record the mechanism it suggests and the exact step still to establish.

Use rivals with judgment. Davenport-Heilbronn is a useful control against an
argument that relies only on structures it shares with zeta. It is not a
reason to reject every shared intermediate lemma or any proof that uses
additional arithmetic absent from the rival. Match the full hypotheses.

## 6. Scope of this repository

**Original research and proof attempts are permitted.** The workbench
supports constructing, testing, connecting, challenging and formalizing
mathematics toward RH and intermediate objectives. The purpose is not merely
to explain why candidates fail, and no method family is prohibited solely
because it has not yet supplied an RH proof.

The evidence rules remain strict. A finite floating-point scan is a diagnostic,
not an unqualified theorem. An enclosure must cover every claimed step.
A Lean claim must name the checked statement, assumptions and dependencies;
no `sorry` is allowed in a theorem claimed as kernel-checked. A handwritten
argument states its sources and review status. A composite result is no
stronger than its weakest unproved link.

The Lean arm can formalize both known mathematics and new results. A
candidate surviving the discovery funnel remains a candidate until its
mathematical claim is established; an unrun literature lookup is not evidence
of novelty. Negative conclusions have the same scope obligations: distinguish
an invalid candidate, a theorem about a restricted class, an unresolved
attempt and an allocation pause. See `ALIGNMENT.md` sections 4 and 5.

This scope change grants no new compute, account, publication or deployment
permission. It changes no prior experimental data or theorem status.

## 7. Map of the repository

- `zeta/` contains the mathematical instruments: evaluation, zeros, explicit
  formulas, statistics, moments, heat flow, Weil and rival controls, interval
  arithmetic, Li/Jensen, finite fields and equivalent criteria.
- `lean/` contains the formal arm. Read its actual toolchain and proof scope.
- `hunts/` contains scoped explorations and their records. A directory name
  does not decide whether a particular statement is measured, derived,
  reviewed or formal. Keep that status explicit and do not self-promote.
- `ontology/` contains discovery machinery; `harness/` contains both live
  bookkeeping and a demoted generalized framework. Do not expand the latter
  merely because an older introductory page describes it.
- `tests/`, `scripts/`, `data/` and `references/` support reproducibility.
  `CONTEXT.md` is the generated index; `docs/README.md` is the reading guide.
  Private operational allocation is kept in its owning repository.

The foundational reading sequence is `00 -> 01 -> 02 -> 03 -> 04`.
Then use `05-de-bruijn-newman.md` for heat flow,
`06-hilbert-polya-and-gue.md` for spectral and statistical ideas,
`07-equivalences-and-criteria.md` for reformulations, and
`08-why-it-is-hard.md` for scoped limitations and controls.
`09-new-ontologies.md`, `10-trace-formulas-and-connes.md` and
`11-f1-and-the-missing-geometry.md` discuss additional research programmes,
not the only permitted forms of research.

## 8. Canonical sources

The course's foundational references include Riemann's 1859 memoir;
H. M. Edwards, *Riemann's Zeta Function*; Titchmarsh, revised by Heath-Brown,
*The Theory of the Riemann Zeta-Function*; Iwaniec and Kowalski,
*Analytic Number Theory*; and Bombieri's Clay problem description.
Source details and the longer historical reading list are retained in the
[previous orientation](../history/research-guidance-2026-09-12/orientation.md#8-canonical-sources).
Use the primary theorem and its hypotheses for a research dependency rather
than treating this introduction as a substitute for the source.

## Where to go next

Read the foundational sequence or the relevant instrument for the assigned
question, then construct something checkable within that mission. Compare
alternative mechanisms when the mandate permits it. Preserve a useful
intermediate result even when its intended application remains open.
A failed attempt should change what is tried next, not silently redefine the
laboratory's purpose as avoiding discovery.
