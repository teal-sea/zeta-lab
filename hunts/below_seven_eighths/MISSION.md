# MISSION: `below_seven_eighths`, pushing the zero-free half-plane under 7/8

**Opened 2026-10-21. Hunt #136.** The owner directed the laboratory on 2026-10-21 to
attack RH. This hunt is the campaign's first track because a fixed zero-free half-plane
is the RH-direct quantity the field is moving right now, and the only one whose
argument consumes the Euler product at a named step. Nothing in this directory is a
result until the case log in `hunts/README.md` says how it ended.

Grades used here: *cited* (a line of a paper's LaTeX source, quoted), *derived*
(algebra done here, checked in exact rational arithmetic by this hunt's tests),
*inferred* (a reading of a paper's structure that no computation here checks),
*measured*, *hardened* (independent routes agree, or ball enclosures carry every step)
and *kernel-checked* (Lean, zero `sorry`, standard axioms). The reserved enclosure word
belongs to `zeta/rigor.py` and appears nowhere in this directory.

## The question

> Can the zero-free half-plane for every Dirichlet L-function be pushed below the best
> public abscissa, 0.8748867? What is the smallest abscissa reachable (a) inside
> OpenAI's Part II assembly by strengthening its row-count inputs, whose ceiling hunt
> #134 places at 13/15, and (b) by a probe whose constants are not tied to the sextic
> pole?

## Starting point

- OpenAI, *The Quasi-Riemann Hypothesis*, preprint of 2026-09-30, Theorem 1.1: no
  Dirichlet L-function has a zero with real part above 7/8. Its formal statements are
  kernel-checked here on two kernels (`docs/38` section 7). No person has reviewed the
  argument.
- Hunt #134 (`seven_eighths_pin`, unlanded, `origin/claude/hunt-134-seven-eighths-pin`):
  the target is sigma_0 = 5/6 + (M - 2l)/12. The paper's geometry (l, M, b) =
  (1/6, 5/6, 1/8) sits at the corner of M + l <= 1 and M - 2l >= 1/2. Re-choosing the
  geometry with the paper's row counts held fixed gains at most 5.8e-5 (0.8749417).
  Perfect row counts stop this assembly at 13/15.
- Public follow-ups, as this campaign's external map records them on 2026-10-21:
  Guo 0.8749570194, Liu 0.874957, Xu and Sang 0.8748867, and Liu 0.874887 for every
  finite-order Hecke L-function over every number field, claimed optimal for that
  comparison system. None of them claims a route toward 1/2.
- The source: `github.com/openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
  `preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`, 16,677
  lines, SHA-256 `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`.
  That hash matches hunt #134's record. It is read as data from a copy outside the
  tree, at `<cache>/openai-math-adc7f124/paper.tex` on the campaign
  box.

## Scope

- **In scope.** The Part II final assembly and the lemmas that supply its row counts;
  the public follow-ups; Lemma 7.1 and the other steps where the Euler product is used;
  alternative comparison systems, priced under the paper's generic estimates; OpenAI's
  Lean development of the Part II geometry; rival checks at any step claimed to use
  arithmetic.
- **Out of scope.** Any statement about real part 1/2, or about RH itself. A smaller
  half-plane, if one is found, is a candidate about this argument and not a theorem,
  until its chain has been reviewed and, where possible, kernel-checked.
- **Budget and stop rule.** The first wave is one workflow on the campaign box (32
  vCPU, 115 GiB). A lane stops when its binding input is located and priced, or when a
  cited lemma turns out to depend on the target in a way the reading cannot resolve. At
  most one Lean build runs on the box at a time, and never beside heavy numerics
  (`CLAUDE.md` compute rule 6).

```huntspec
id: below_seven_eighths
question: Can the zero-free half-plane for every Dirichlet L-function be pushed below the best public abscissa 0.8748867, and what is the smallest abscissa reachable inside OpenAI's Part II assembly by strengthening its row-count inputs, or by a probe not tied to the sextic pole?
frontier: 7/8 (OpenAI 2026-09-30, formal statement kernel-checked here, argument unreviewed); public follow-ups 0.8749570194 (Guo), 0.874957 (Liu), 0.8748867 (Xu and Sang), 0.874887 for Hecke L-functions (Liu); hunt 134 places the geometry corner at M + l <= 1 and M - 2l >= 1/2, the re-optimized geometry at 0.8749417 and the perfect-row-count ceiling at 13/15
proposed_attack: price every row-count input of the final assembly by exact shadow prices, read the proofs of the binding inputs for slack, test any sharper count by exact enumeration, check the Euler-product step by exact local computation, and price alternative comparison systems under the paper's generic estimates
dead_routes:
  - substituting a smaller number for 7/8 in the final section without rederiving the row counts and the bootstrap it inherits (hunt 134)
  - re-choosing the Part II geometry with the paper's row counts held fixed, which gains at most 5.8e-5 (hunt 134)
  - reading the half-plane as information about real part 1/2 (docs/39)
  - treating a zero of a linear combination of L-functions as a counterexample to a statement about single L-functions (hunt 120)
required_oracles:
  - the paper's LaTeX source at the pinned commit, quoted by line number, with its SHA-256 checked
  - exact rational arithmetic reproducing every printed constant of the paper
  - exact small-case enumeration for any sharpened counting input
  - exact local computation of Euler factors and Gauss sums for the Euler-product step
  - the Lean kernel for any formal piece, with axioms printed
kill_conditions:
  - the symbolic assembly fails to reproduce 7/8, the margin 49/440640 or the re-optimized 0.8749417 at their stated parameters
  - a sharpened input fails exact enumeration at a small case or contradicts a step of the cited lemma's proof
  - a claimed improvement is matched or beaten by a public follow-up already on record
  - a claimed arithmetic step also holds for a function with a zero beyond the claimed abscissa, such as an Epstein zeta or a linear combination of L-functions
agents_may:
  - read and quote papers
  - derive
  - code exact arithmetic
  - attack derivations
  - formalize
  - build the pinned Lean closure locally, one build at a time
agents_may_not:
  - declare novelty
  - declare theorem status
  - claim any improvement to the half-plane as established
  - promote their own claim
  - push, publish or contact outside parties
```
