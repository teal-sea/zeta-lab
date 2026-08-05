# 00 — Orientation

**The short version.** The Riemann zeta function starts life as the sum `1 + 1/2^s + 1/3^s + ...`,
which converges only when `Re(s) > 1`, but extends uniquely to a function defined on the whole
complex plane except for a single pole at `s = 1`. That extended function has zeros. Some are boring
and fully understood (`s = -2, -4, -6, ...`); the rest all lie in the strip `0 ≤ Re(s) ≤ 1`, and the
Riemann Hypothesis (RH) asserts that every one of them has real part exactly `1/2`. This is not a
curiosity about a special function: the zeros are, via an exact formula, the *complete* correction
term for the count of prime numbers, and RH is precisely equivalent to the statement that the count
of primes below `x` deviates from its smooth approximation `Li(x)` by no more than about `√x log x`.
RH has been open since 1859. This repository is an instrument for seeing all of this happen
numerically — not an attempt to prove it.

---

## 1. The object

For `Re(s) > 1` the series and the product below both converge, and Euler's identity says they are equal:

```
             ∞
   ζ(s)  =   Σ  n^(-s)   =   Π  ( 1 - p^(-s) )^(-1)        (Re(s) > 1)
            n=1              p prime
```

That identity is the whole reason zeta matters. The left side knows about *all* integers; the right
side knows only about primes. Unique factorization is what glues them together — expand each factor
as a geometric series `1 + p^-s + p^-2s + ...`, multiply out, and every `n^-s` appears exactly once,
because every `n` has exactly one prime factorization. So any analytic fact about `ζ` is, in
disguise, an arithmetic fact about primes.

The series diverges at `s = 1` (it's the harmonic series) and everywhere left of it. But `ζ` has a
unique analytic continuation to `C \ {1}`, with a simple pole of residue 1 at `s = 1`
(`docs/01-sums-integrals-and-continuation.md` builds this by hand). The continuation satisfies a
functional equation, cleanest in terms of the *completed* zeta function

```
   ξ(s) = (1/2) · s · (s-1) · π^(-s/2) · Γ(s/2) · ζ(s),        ξ(s) = ξ(1-s)
```

`ξ` is entire, and the reflection `s ↦ 1-s` is a symmetry of it about the vertical line
`Re(s) = 1/2`. (You can check this numerically right now: `zeta.core.functional_equation_defect`
returns `|ξ(s) - ξ(1-s)|`; at `s = 0.3 + 7.1i` I get about `10^-31` at 30-digit precision. The
derivation is `docs/03-functional-equation.md`.)

The `Γ(s/2)` factor has poles at `s = 0, -2, -4, ...`, which forces `ζ` to vanish at
`s = -2, -4, -6, ...` to keep `ξ` entire (`s = 0` is absorbed by the `s` factor). Those are the
**trivial zeros**. Everything else — the **non-trivial zeros** — must lie in the *critical strip*
`0 ≤ Re(s) ≤ 1`, since the Euler product shows `ζ ≠ 0` for `Re(s) > 1`, and the functional equation
reflects that into `Re(s) < 0`.

The first few non-trivial zeros sit at `1/2 ± 14.134725...i`, `1/2 ± 21.022040...i`,
`1/2 ± 25.010858...i`. There are 29 with imaginary part in `(0, 100)` and 649 in `(0, 1000)`
(both checked against `mpmath` while writing this).

## 2. The statement

> **CONJECTURE (Riemann, 1859) — the Riemann Hypothesis.**
> Every zero of `ζ(s)` with `0 ≤ Re(s) ≤ 1` satisfies `Re(s) = 1/2`.

Equivalently: after the substitution `s = 1/2 + iz`, the entire function `Ξ(z) := ξ(1/2 + iz)` has
only real zeros. Equivalently again: `ζ(s) ≠ 0` for `Re(s) > 1/2`.

Two things to be clear about. First, Riemann did not present this as a central goal; he remarked in
passing that it was "very probable" and that after some fleeting attempts he had set the search for
a proof aside. Second, RH says nothing about *simplicity* or *spacing* of the zeros — those are
separate open questions (§5).

## 3. Why anyone cares

Let `π(x)` be the number of primes `≤ x`, and `Li(x) = ∫₂^x dt/log t` the logarithmic integral.

> **THEOREM (Hadamard; de la Vallée Poussin, independently, 1896) — the Prime Number Theorem.**
> `π(x) ~ x / log x`, equivalently `π(x) ~ Li(x)`.
>
> The proof turns on showing `ζ(1 + it) ≠ 0` for all real `t ≠ 0`: the PNT is exactly the statement
> that zeta has no zeros on the *edge* of the critical strip.

That is the template for everything that follows. **Where the zeros are controls how well the primes
are distributed.** The mechanism is von Mangoldt's *explicit formula* (1895): writing
`ψ(x) = Σ_{p^k ≤ x} log p` for the weighted prime count,

```
   ψ(x)  =  x  -  Σ  x^ρ / ρ  -  log(2π)  -  (1/2)·log(1 - x^(-2))
                  ρ
```

summed over non-trivial zeros `ρ` in conjugate pairs. This is an *identity*, not an approximation
(with the standard proviso that at a prime-power `x` the left side means the midpoint of the jump;
`docs/04-explicit-formula.md` and `zeta/explicit.py` spell this out). Read it: the smooth main term
is `x`; every zero `ρ = β + iγ` contributes an oscillating term of magnitude `x^β / |ρ|` and
frequency `γ` in `log x`. A zero far to the right is a loud, slowly-decaying wave of error in the
primes. So the size of the error term is governed by `sup β` over all zeros — and RH is exactly the
statement `sup β = 1/2`, giving errors of size `√x`.

> **THEOREM (von Koch, 1901).** RH holds **if and only if**
> `π(x) = Li(x) + O(√x · log x)`.
> (Equivalently `ψ(x) = x + O(√x (log x)²)`, or `π(x) = Li(x) + O(x^(1/2+ε))` for every `ε > 0`.)

This is a genuine equivalence in both directions — RH is *not* merely sufficient for square-root
error, it is necessary. So RH is a precise assertion about the regularity of the primes: they are as
evenly distributed as a random-looking sequence could plausibly be, no worse than the square-root
cancellation of a coin-flip model.

Concretely, at `x = 10^10`: `π(x) = 455,052,511` and `Li(x) ≈ 455,055,613.5`. The discrepancy is
about 3103 — under seven parts per million, and far inside `√x log x / (8π) ≈ 91,617`. (I recomputed
all four numbers with `mpmath`/`sympy` while writing this. The `√x log x/(8π)` bound is Schoenfeld's
1976 refinement, valid under RH for `x ≥ 2657` — commonly cited as such; check the source before
leaning on the constants.)

A caution against over-reading numerics: `Li(x) > π(x)` for every `x` anyone has ever computed,
which looks like a law. It isn't.

> **THEOREM (Littlewood, 1914).** `π(x) - Li(x)` changes sign infinitely often.

No explicit crossing is known; the smallest known upper bound for one is astronomically large (the
Skewes-number literature; figures around `10^316` are commonly cited, and I would verify the current
record before quoting one). This is the single most useful cautionary tale in the subject: **the
first `10^10` cases can be unanimous and still wrong about the truth.**

## 4. What is rigorously known

A ledger, all **THEOREM** unless marked otherwise.

**Counting.** *(Riemann asserted, von Mangoldt proved, 1905.)* The number `N(T)` of zeros with
`0 < Im(ρ) < T` satisfies

```
   N(T)  =  (T/2π)·log(T/2π)  -  T/2π  +  7/8  +  O(log T)
```

so the zeros get *denser* as you go up: mean spacing near height `T` is `2π / log(T/2π)`
(≈ 2.27 at `T = 100`, ≈ 1.24 at `T = 1000`). I checked the smooth part of the formula against exact
zero counts at several heights up to `T = 400`; it was never off by more than 0.6 at the heights I
sampled. (`zeta/zeros.py` implements the *exact* form of this identity, with the `S(T)` argument
term, in `N_of_T`.)

**Zeros on the line.**
- *Hardy (1914):* infinitely many zeros lie on `Re(s) = 1/2`. The first real foothold.
- *Hardy–Littlewood (1921):* at least `cT` of them up to height `T` — a positive *density*, but a
  vanishing fraction of `N(T) ≍ T log T`.
- *Selberg (1942):* a positive **proportion** of all zeros lie on the line.
- *Levinson (1974):* more than 1/3.
- *Conrey (1989):* **more than 2/5** lie on the critical line and are simple. This is the number
  usually quoted. Later refinements have pushed the proportion a little past 41% (a bit over 5/12 is
  the figure `docs/08-why-it-is-hard.md` uses); I would check the literature for the current record
  before citing a specific value.

Note what this does *not* say. Even "99% of zeros on the line" would leave infinitely many possibly
off it, and by §3 a single zero at `β = 0.51` would already break RH.

**Numerical verification.**
- *Platt–Trudgian (2021):* RH verified for all zeros up to height `3 × 10^12` — about `1.24 × 10^13`
  zeros. This is a rigorous interval-arithmetic computation, which matters: some earlier
  larger-height announcements had less complete error control.
- *Odlyzko (1987 onward):* zeros computed in windows around the `10^12`-th zero and later the
  `10^20`-th and `10^22`-nd — not a verification of everything below, but the data that made the
  statistical picture of §5 credible.

**Zero-free regions** — the "how far right can a zero be?" question.
- *de la Vallée Poussin (1899):* no zeros with `σ ≥ 1 - c/log|t|`.
- *Vinogradov–Korobov (1958):* no zeros with `σ ≥ 1 - c / ((log|t|)^(2/3) (log log|t|)^(1/3))`.
  Still essentially the best known *shape*, nearly seventy years on. Explicit constants exist
  (Ford, 2002, and refinements since).
- Explicit classical region: `σ ≥ 1 - 1/(5.573412·log|t|)` for `|t| ≥ 2` (Mossinghoff–Trudgian,
  2015) is commonly cited, and has since been slightly improved.

Look hard at that list, because it is the honest measure of the gap. Every known zero-free region
*touches* the line `Re(s) = 1` asymptotically, pulling away from it more and more slowly as `|t|`
grows. **No known theorem excludes a zero with real part 0.99 at some large height.** RH asks us to
exclude everything past `0.5`. Why that gap is structural and not a matter of effort is the subject
of `docs/08-why-it-is-hard.md`.

**Zero density** — "how *many* zeros can be far right?" — is the complementary, more tractable
attack. `N(σ,T)` counts zeros with `Re(ρ) ≥ σ` up to height `T`; RH says `N(σ,T) = 0` for
`σ > 1/2`, and density theorems say off-line zeros are at least rare. Ingham's 1940 bound
`N(σ,T) ≪ T^(3(1-σ)/(2-σ)+ε)` stood essentially unimproved near `σ = 3/4` for over eighty years.

> **THEOREM (Guth–Maynard, 2024), "New large value estimates for Dirichlet polynomials."**
> A new bound on how often a Dirichlet polynomial can be large, yielding the first improvement on
> Ingham's density estimate around `σ = 3/4`. The commonly quoted form is
> `N(σ,T) ≪ T^(30(1-σ)/13 + o(1))` for `3/4 ≤ σ ≤ 1` — **I am confident in the qualitative claim
> and the attribution, less so reciting the exponent from memory; check the paper.** A headline
> consequence: intervals `[x, x + x^(17/30 + o(1))]` contain a prime for large `x`, improving
> Huxley's long-standing `x^(7/12)`.

Two precision points, since this result is often loosely described. It is a **large-values /
zero-density** theorem, not a zero-free-region theorem — a different axis of progress. And it does
not approach RH: it improves how *rare* far-right zeros are, while RH needs them *absent*.

**The heat-flow frontier.** Deform `Ξ` by a heat flow, producing a family `H_t` of entire functions
with `H_0 ∝ Ξ` (up to scaling — `docs/05-de-bruijn-newman.md` pins the normalisation down
empirically). De Bruijn showed that zeros, once all real, stay real as `t` increases, so there is a
threshold — the **de Bruijn–Newman constant** `Λ` — with `H_t` having only real zeros exactly when
`t ≥ Λ`. Then:

- `RH  ⟺  Λ ≤ 0`.
- *de Bruijn (1950):* `Λ ≤ 1/2`.
- *Newman (1976)* **conjectured** `Λ ≥ 0` — "the Riemann Hypothesis, if true, is only barely so."
- *Rodgers–Tao (announced 2018, published 2020):* Newman's conjecture is a **THEOREM**: `Λ ≥ 0`.
- *Polymath 15 (2019):* `Λ ≤ 0.22`; combining their machinery with the Platt–Trudgian verification
  height gives `Λ ≤ 0.2`, the bound now commonly cited.

So RH is equivalent to the single equality `Λ = 0`, pinned into `[0, 0.2]` from both sides. This is
the subject of `zeta/heatflow.py` and `docs/05-de-bruijn-newman.md`, and it is the most vivid thing
in the repo: you can watch zeros of `H_t` collide and go complex as you run the flow backwards.

## 5. What is conjectural or heuristic

Clearly separated from §4.

- **CONJECTURE (Montgomery, 1973) — pair correlation / GUE.** Rescale the zeros to unit mean
  spacing. Montgomery **proved**, *assuming RH and for a restricted class of test functions*, that
  their pair correlation matches that of eigenvalues of the Gaussian Unitary Ensemble of random
  matrix theory; the **conjecture** is that the restriction can be removed. Dyson recognized
  Montgomery's formula as the GUE correlation; Odlyzko's computations at great height show agreement
  to striking precision. See `docs/06-hilbert-polya-and-gue.md` and `zeta/statistics.py`, which let
  you run the comparison yourself.
- **HEURISTIC — Hilbert–Pólya.** The zero ordinates are the spectrum of some self-adjoint operator,
  which would force them onto a line. No such operator is known. A research programme and an
  organizing intuition, not a theorem or even a sharply-stated conjecture. Also in `docs/06`.
- **CONJECTURE — Lindelöf.** `ζ(1/2 + it) ≪ |t|^ε`. Implied by RH and formally weaker — it is
  not known to imply RH — still open.
- **Open even under RH:** are all zeros simple? Do the gaps obey the GUE predictions? RH by itself
  answers neither.

## 6. Scope of this repository — an honest statement

This is a **laboratory instrument**. It exists to make the objects above concrete: to compute `ζ`
where the defining series diverges, to find zeros and count them with certificates, to rebuild the
primes from the zeros and watch the error shrink as you add more, to test the GUE statistics against
real data, and to run the heat flow.

It is **a proof by construction**, aimed at building the Adelic spectral operator whose spectrum is the zeros. However, no amount of numerical computation here is evidence for RH. That is not a disclaimer of ambition; it is Littlewood's theorem (see §8). Proof will come from constructing the operator, not from measuring zeta harder. §4 records `1.24 × 10^13` verified zeros, and §3 records Littlewood's
theorem, which guarantees that a pattern holding for every computed case can still be false.
Numerics in this subject are for building intuition, checking that formulas mean what you think they
mean, and generating questions — never for evidence of truth. If a computation here appears to
settle something, the correct inference is that there is a bug.

Where a result is conditional on RH, the code and docs are meant to say so at the point of use.

That rule extends to the one part of the repository that looks like it might break it. `discovery/`
(§7) generates *candidate observations* and records the small number nothing killed as **survivors**.
A survivor is a lead to be examined by hand — not a result, not a theorem, not evidence for RH —
and the funnel writes that sentence into every such record's own `proof_gap` field. Because there is
no network here, nothing is looked up in OEIS or arXiv either: "not recognised offline" is the
absence of a lookup, and the layer has no code path that renders it as novelty. If a run of it
appears to settle something open, the inference is the same as everywhere else in this repository —
there is a bug.

## 7. Map of the repository

The package is `zeta/`, twelve analysis modules (plus `plots.py`, which draws the figures):

- **`core.py`** — the bedrock. Arbitrary-precision `ζ` by three independent routes (Dirichlet/eta
  series, Euler–Maclaurin, Mellin transforms), theta functions and their heat-kernel form, the
  completed functions `ξ`, `Ξ`, Hardy's `Z(t)` and the Riemann–Siegel theta, plus *defect* functions
  (`functional_equation_defect`, `theta_modular_defect`, ...) that measure how well the identities
  hold — the lab's habit of checking everything against itself.
- **`zeros.py`** — zero hunting and counting: sign changes of `Z(t)`, Gram points, the exact
  `N(T) = 1 + θ(T)/π + S(T)` identity, and `verify_rh_up_to`, a Turing-style check that no zero
  below a given height was missed.
- **`explicit.py`** — the explicit formula in code: `ψ(x)` and `π(x)` reconstructed from zero data
  (`psi_from_zeros`, `pi_from_zeros`), Riemann's `R(x)`, and the dual direction — `prime_spectrum`,
  which recovers the zeros as spectral peaks of the prime-counting error.
- **`statistics.py`** — fast vectorized Riemann–Siegel evaluation, bulk zero ordinates, unfolding,
  nearest-neighbour spacings versus the Wigner surmise and the exact GUE gap distribution, pair
  correlation versus Montgomery's prediction, and honest GUE eigenvalue sampling for comparison.
- **`moments.py`** — validated ingestion of LMFDB plain-text exports and Odlyzko's six public
  zero tables. High ordinates remain exact decimal base-plus-offset data, so float64 cannot erase
  their local gaps; checksums, index continuity, ordering, counts and source accuracy notes travel
  with each table. It computes no zeros.
- **`heatflow.py`** — `Φ(u)`, the family `H_t`, zero-tracking under the flow, and `lambda_facts`:
  the de Bruijn–Newman story of §4 made executable.
- **`weil.py`** — the Riemann–Weil explicit formula with both sides computed independently, the
  Weil functional `W(h)` (RH ⟺ `W ≥ 0`), positivity probes and honest truncation-tail accounting.
- **`epstein.py`** — the Davenport–Heilbronn counterexample: a function with ζ's functional equation
  and a zero *off* the line, plus `battery`, the standing test that symmetry alone explains nothing.
- **`rigor.py`** — ball (interval) arithmetic: enclosures of `Z(t)`, *proven* signs, a certified
  `N(T)` by the argument principle, and `verify_rh_certified` — the rigorous counterpart of
  `zeros.verify_rh_up_to`. Two independent backends (Arb via python-flint; mpmath's interval
  context) so each can check the other. Anything it cannot certify is reported, never guessed.
- **`li.py`** — Li's criterion (`λ_n ≥ 0 ⟺` RH) by two independent routes, and the Jensen
  polynomials of Pólya's real-rootedness criterion, decided both numerically and exactly in `ℚ[X]`.
- **`finitefield.py`** — curves over `F_p`, where RH is a **theorem**: point counts, Frobenius
  eigenvalues on `|α| = √p`, the Lefschetz formula checked against brute-force counting in `F_{p²}`,
  and the vertical Sato–Tate statistics — the blueprint the programmes of `docs/11` are measured against.
- **`criteria.py`** — four equivalence faces of RH made executable: Mertens/Möbius,
  Nyman–Beurling/Baez-Duarte, Robin/Lagarias, Speiser.

A second package, `discovery/`, sits on top of that one and studies the laboratory rather than the
subject. It is a **discovery funnel**: generators mine the computed objects above for candidate
observations, a catalogue and a battery of screens try to kill them, and every step is logged — so
the conversion rate *per generator* can be measured. The premise is unflattering and load-bearing:
most numerical "discoveries" are already known or trivial, and a system that does not measure its
own hit rate is measuring its operator's enthusiasm. On a fresh ledger the six generators produce 26
candidates and the funnel's verdict is 20 already known (76.9 %), 1 trivial, 5 inconclusive, 0
survivors — and that table, not the survivor list, is the output.

It is split along one seam. `schema.py`, `registry.py`, `ledger.py`, `funnel.py`, `metrics.py` and
`historical_cases.py` are **domain-agnostic**: they name no quantity the laboratory computes and
import nothing from `zeta`, so the same machinery would serve a chemistry laboratory; three tests
enforce it. Everything that knows what is being studied lives in `discovery/domains/`. Before the
funnel is pointed at anything unsettled it has to reproduce history: five claims whose status later
work has established — proved, still open, disproved, provably equivalent to an open problem, and
one constructed coincidence — are replayed through it and must land where that later work says they
belong. The case that matters is Mertens' conjecture, which every computation feasible for a century
supported and which is false. **The funnel does not endorse it**, and the harness refuses to
register a case that expects it to, so the suite cannot be edited into agreement.

Read `discovery/README.md` before touching any of it; §7–§9.3 there is the honest statement of what
the layer cannot express and where its own validation is thinner than it looks. Run it with
`scripts/13_discovery_run.py`. Nothing it produces is evidence for RH: a survivor is a **lead**, and
"not recognised offline" is the absence of a lookup — there is no network — never a claim of
novelty. Its ledger lives in `conjectures/`, which is gitignored, because a list of unreviewed leads
published under a repository that is otherwise checked would be read as a set of claims.

Docs, in numbered reading order:

| Doc | Leans on | What it covers |
| --- | --- | --- |
| `00-orientation.md` | — | This document: statement, stakes, status, scope. |
| `01-sums-integrals-and-continuation.md` | `core.py` | Harmonic series and the pole at `s=1`; Euler–Maclaurin as the sum-vs-integral bridge; how `ζ(-1) = -1/12` is forced; how the code actually evaluates `ζ` everywhere. |
| `02-theta-heat-and-modularity.md` | `core.py` | Theta as the heat kernel on the circle; Poisson summation; the modular relation `θ(1/x) = √x·θ(x)`. |
| `03-functional-equation.md` | `core.py` | `ζ` as the Mellin transform of theta; the functional equation derived line by line from `02`'s modularity. |
| `04-explicit-formula.md` | `explicit.py`, `zeros.py` | Zeros ↔ primes as an identity: `ψ(x)` from waves, one per zero, and the primes' spectrum. The payoff of `01`–`03`. |
| `05-de-bruijn-newman.md` | `heatflow.py` | Heat flow *on* `Ξ`; zero collisions; `Λ ∈ [0, 0.2]` and RH ⟺ `Λ = 0`. |
| `06-hilbert-polya-and-gue.md` | `statistics.py` | The spectral dream, Berry–Keating, Montgomery–Odlyzko, GUE statistics on your laptop. |
| `07-equivalences-and-criteria.md` | several | A catalogue of statements exactly equivalent to RH, with honest notes on which reformulations ever led anywhere. |
| `08-why-it-is-hard.md` | — | The failure catalogue: what each known technique provably cannot do, and why numerics cannot decide RH. |
| `09-new-ontologies.md` | — | What "RH needs new mathematics" means: the Weil-conjectures precedent, the F1 / Connes / Deninger programmes, and how to stress-test a proposed new ontology. |
| `10-trace-formulas-and-connes.md` | `weil.py` | The Weil explicit formula as a trace formula (spectrum ↔ orbits); Selberg's working analogue; Connes' programme; the positivity criterion, run live. |
| `11-f1-and-the-missing-geometry.md` | `epstein.py` | The field with one element, Borger's and Connes–Consani's attempts, Deninger's dynamical programme — the hunt for the geometry under ℤ. |
| `12-how-hard-problems-die.md` | `finitefield.py`, `criteria.py`, `li.py` | A kill board: eight problems that fell, the mechanism that killed each (ontology rebuild, bridge, finite reduction, effective squeeze, flow, insight, equivalence web), and an honest scoring of which of them RH's live formulations touch — and which it provably does not. |
| `13-moments.md` | `moments.py` | The external-data contract for the moments programme: LMFDB/Odlyzko formats, exact base-plus-offset storage, validation, provenance, and deliberate non-goals. |
| `14-how-new-mathematics-gets-invented.md` | `finitefield.py`, `epstein.py` | Companion to the kill board, one level earlier: eleven recurring ways new mathematics has appeared (posit the object, negate an axiom, change the base ring, object-valued invariants, dictionaries, compute for anomalies, …), each scored against `docs/11`'s missing Frobenius over ℤ. Historical, not testable — flagged as such in the document. |

Supporting directories: `scripts/`, `figures/`, `data/` (cached zero tables and scan
results), `tests/` (every module has a test file — the defect functions are tested to tight
tolerances), `references/`, and `conjectures/` — the discovery ledger, **gitignored**, a private
notebook of unreviewed leads. Publish `discovery.metrics.render_text`, never the log.

**Recommended reading order.** `00 → 01 → 02 → 03 → 04` is a single argument and should be read in
sequence: continuation gives you a function with zeros at all, theta/modularity gives the functional
equation, and the explicit formula shows why the zeros *are* the primes. After `04`: read `05` for
the heat-flow frontier (it builds directly on `02` and `03`), `06` for the statistical picture, `07`
and `08` in either order to calibrate what "equivalent to RH" and "progress on RH" actually mean,
and `09` for what a genuinely new attack would have to look like. `10` and `11` are deeper digests
of the two live research programmes `09` sketches — trace formulas/Connes and F1/Deninger — each
backed by a module (`zeta/weil.py`, `zeta/epstein.py`) and a demo (`scripts/07`, `scripts/08`).
`12` closes the course by widening the sample: how eight other famous problems actually died, and
where RH sits on that board — backed by `zeta/finitefield.py`, `zeta/criteria.py` and `zeta/li.py`
(`scripts/10`–`12`), with `zeta/rigor.py` and `scripts/09` supplying the certified-computation
standard §3.1 of `08` insists on.
If you have one hour, read `01` and `04` and run the explicit-formula code.

## 8. Canonical sources

- **Riemann, B.** *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse* (Monatsberichte
  der Berliner Akademie, November 1859). Eight pages; contains the functional equation, the explicit
  formula in outline, and the hypothesis. Worth reading even in translation and even where it is
  opaque — it is astonishingly compressed. English translations: the appendix of Edwards (below),
  and David Wilkins' translation, freely available online.
- **Edwards, H. M.** *Riemann's Zeta Function* (Academic Press, 1974; Dover reprint 2001). The best
  entry point for exactly this document's audience: it works through Riemann's memoir line by line
  and develops the analysis as it goes. If you buy one book, buy this one.
- **Titchmarsh, E. C.** *The Theory of the Riemann Zeta-Function*, 2nd ed., revised by D. R.
  Heath-Brown (Oxford, 1986). The standard reference monograph. Dense; use it to look things up.
- **Iwaniec, H. and Kowalski, E.** *Analytic Number Theory* (AMS Colloquium Publications 53, 2004).
  The modern graduate reference for the wider field — zero-density estimates, the large sieve,
  general L-functions. Harder than Edwards by a wide margin.
- **Bombieri, E.** *Problems of the Millennium: The Riemann Hypothesis* — the official problem
  description for the Clay Mathematics Institute, available from claymath.org. Short, authoritative,
  and the right citation for the precise statement and its context.

For the specific results of §4, go to the papers: Conrey (*J. reine angew. Math.* 399, 1989);
Platt–Trudgian (*Bull. London Math. Soc.*, 2021); Rodgers–Tao (*Forum of Mathematics, Pi*, 2020);
Polymath 15 (*Research in the Mathematical Sciences*, 2019); Guth–Maynard (arXiv, 2024).

## Where to go next

1. Read `01-sums-integrals-and-continuation.md` and get `zeta/core.py` evaluating `ζ` at
   `s = 0.3 + 7.1i`, where the defining series is meaningless — by two independent methods that
   agree. Convince yourself the continued value is forced, not chosen.
2. Read `02` and `03` as a pair: the heat kernel's self-similarity *is* the functional equation.
   Then find the first zero at `t = 14.134725...` yourself with `zeta.zeros.zeros_by_sign_change`,
   and understand why Hardy's real-valued `Z(t)` reduces zero-finding to hunting sign changes.
3. Read `04-explicit-formula.md`, which is the payoff. Add zeros one at a time to the `ψ(x)` sum and
   watch the prime staircase materialize out of waves. This is the moment the subject stops being
   formal.
4. If you want the live frontier rather than the foundations, skip to `05-de-bruijn-newman.md` and
   the `Λ ∈ [0, 0.2]` story, then `08-why-it-is-hard.md` to see precisely why none of this — and no
   computation — closes the gap.

Keep §6 in view throughout. The purpose is to understand the question well enough to respect it.
