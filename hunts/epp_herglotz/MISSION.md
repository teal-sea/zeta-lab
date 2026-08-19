# `hunts/epp_herglotz` — one mechanism for RH, stated before it was attacked

**Nothing in this directory is a result.** `hunts/README.md` classifies the
area: a hunt is exploratory, and this one was opened to state a single
mechanism for the Riemann Hypothesis and then spend its whole budget trying
to destroy it.

The mechanism paragraph below was written **before any code in this
directory existed**, and the commit that introduced this file contains
nothing else. That ordering is the point: a mechanism written after the
numbers is a description, not a prediction.

---

## The mechanism (written first, 2026-08-19)

Write `F = ξ'/ξ`. Two facts are free. First, differentiating `ξ(s) = ξ(1−s)`
gives `F(1−s) = −F(s)`, so `Re F` vanishes identically on `Re s = 1/2`.
Second, the paired Hadamard product gives `F(s) = Σ_ρ (s−ρ)^{-1}`, so
`Re F(σ+it) = Σ_ρ (σ−β)/|s−ρ|²`. Together these give an equivalence rather
than an implication: **RH holds if and only if `Re F(s) ≥ 0` throughout
`Re s > 1/2`**, that is, if and only if `z ↦ F(1/2+z)` is a Herglotz function
on the right half-plane, in which case its boundary measure on the line is
forced to be `π` times the counting measure of the ordinates. RH is therefore
the statement that one explicitly computable real quantity has a determined
sign on a half-plane. Now split that quantity the only way the arithmetic
offers, `F = G − A`, with prime side `A(s) = Σ_n Λ(n) n^{−s}` and archimedean
side `G(s) = 1/s + 1/(s−1) − (1/2)log π + (1/2)ψ(s/2)`. Each half carries its
own positivity, and the two are of different types. `Λ(n) ≥ 0` **is** the
Euler product, and by Bochner's theorem it makes `t ↦ A(σ+it)` a positive
definite function for every `σ > 1`: every Toeplitz matrix
`[A(σ + i(t_j − t_k))]_{j,k}` is positive semidefinite, and
`|A(σ+it)| ≤ A(σ)`. On the other side `Re G(σ+it) = (1/2)log(|t|/2π) + O(1/|t|)`,
which is positive in the strip and grows. **The mechanism is that these two
positivities compose**: the prime side's vertical positive definiteness,
transported from `σ > 1` across `1/2 < σ ≤ 1` by the functional equation
(which pins `Re F ≡ 0` on the line and so fixes the transported boundary data
exactly), together with the strictly positive and growing archimedean term,
forces `Re(G − A) ≥ 0` on `Re s > 1/2`. If that composition step is a
theorem, RH follows.

### Why this passes gate #3 on its face

The load-bearing hypothesis is `Λ(n) ≥ 0`, equivalently that
`log F` has non-negative Dirichlet coefficients. Call it EPP. Both standing
rivals of `zeta.epstein.battery` are linear combinations of legitimate Euler
products and have no scalar Euler product of their own, so EPP is expected to
fail for both. That expectation is measured in this hunt rather than assumed.
Passing gate #3 is necessary, and this hunt exists to find out whether it is
anywhere near sufficient.

### The step the hunt attacks

The composition step, and nothing else. The two positivities live in
different directions (`A` is positive definite along `t` at fixed `σ`;
Herglotz is a statement about `Re` along `σ`) and in different regions
(`σ > 1` versus `σ > 1/2`). The attack is to look for a function that has
every hypothesis the mechanism uses and for which the conclusion is false.

```huntspec
id: epp_herglotz
question: Does Euler-product positivity plus the functional equation force Re ξ'/ξ ≥ 0 on Re s > 1/2?
frontier: RH ⟺ Re ξ'/ξ ≥ 0 on Re s > 1/2 is an equivalence with no proof in either direction; the classical use of Λ ≥ 0 (the 3-4-1 inequality) reaches only σ > 1 − c/log t
proposed_attack: build a rival carrying every hypothesis the mechanism uses, including a scalar Euler product with non-negative log-coefficients and an exact s ↦ 1−s functional equation, and locate its off-line zeros
dead_routes:
  - local positivity at each finite place, docs/24: the place-by-place quadratic form is positive and the globalisation has no sign
  - ordinate-only statistics, docs/18 section 6: blind to the position of the critical line
  - coefficient functionals invariant under the twist a_n to n^δ a_n, docs/24 section 6, blind exactly on |δ| ≤ 1/2
required_oracles:
  - mpmath zetazero and siegelz as an independent implementation
  - argument-principle zero counts in a box
  - exact Dirichlet-coefficient recursion for the log-derivative, checked against an independent Euler-product expansion
  - zeta.epstein.battery
kill_conditions:
  - a function satisfying EPP and the functional equation is exhibited with a zero off its own critical line
  - the claimed positivity of the prime side is shared by a rival that violates RH
  - the composition step is shown to require a bound rather than a positivity, with the required bound of RH strength
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```
