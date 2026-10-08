# Linnik's constant from the 7/8 zero-free half-plane

Base commit: `ef4e0564349c19c9e6ca91e78ebe3e4f5e224997`, branch `hunt/qrh-linnik`.
Opened 2026-10-08.

## Question and scope

Take as input OpenAI's "The Quasi-Riemann Hypothesis" (October 2026), Theorem
1.1: no Dirichlet L-function, including zeta, vanishes in `Re s > 7/8` (the pole
of the principal character at `s = 1` excepted). Its Lean statements
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` and
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` were kernel
checked by this lab on 2026-10-08 on two kernels (section 7 of the new docs note
on unmerged PR #271). The 195-page argument has had no human review. This
hunt uses the theorem; it does not audit, replay or re-check it.

Target: an effective bound `p(q,a) << q^(L+eps)` for the least prime
`p = a (mod q)`, with the smallest `L` that the published zero-density
literature for a single modulus actually supports, together with a complete
written proof, and the corollaries that come with it (prime counts in every
reduced class above `q^(L+eps)`, and a bound for almost all classes).

Known boundary before this hunt: unconditional `L = 5` (Xylouris 2011), `5 - eps`
(Xylouris 2018); an AI-assisted preprint claims 3.99 (Naslund, 2026-10-02,
unreviewed); under GRH `L = 2 + eps`. The English Wikipedia table on 2026-10-08
lists `L = 2.4` as a corollary of the 7/8 theorem, which is the Ingham-Huxley
exponent 12/5; the OpenAI paper text available here states no Linnik bound.

## What is used, and at what grade

Every result here is "proved, given OpenAI's Theorem 1.1", and its grade is that
of its weakest input: OpenAI's unreviewed argument. The density input is named
in each statement: the classical single-modulus estimates (Montgomery 1971,
Huxley 1975; refereed), or Chen, Gupta and Li, arXiv:2507.08296v2 (2026-07-27;
preprint, refereeing status unknown). The deduction written here is an ordinary
proof, model-written, with no external review yet: candidate, pending external
review. The hunt does not promote its own claim.

## Resource boundary

Exact rational exponent algebra and one serial sieve computation of least primes
for moduli up to a few thousand, well under one CPU-hour and 3 GB. No Lean build,
no paid compute, no push, no pull request. Write only this directory, the case-log
entry in `hunts/README.md`, an entry in `docs/37-methods.md`, and the regenerated
`CONTEXT.md`.

```huntspec
id: qrh_linnik
question: Given OpenAI's 7/8 zero-free half-plane for all Dirichlet L-functions, what Linnik exponent L does a complete proof from published single-modulus zero-density estimates give?
frontier: unconditional L = 5 (Xylouris 2011) and 5 - eps (Xylouris 2018); 3.99 claimed by an unreviewed AI-assisted preprint (2026-10-02); 12/5 listed on Wikipedia as a 7/8 corollary; GRH gives 2 + eps
proposed_attack: smoothed explicit formula with height cutoff a small power of x, zeros above 7/8 removed by the input theorem, the rest counted by the best single-modulus density estimate, maximised over 1/2 <= sigma <= 7/8
dead_routes:
  - Log-free density near sigma = 1 and Deuring-Heilbronn repulsion: superseded rather than refuted, since the input removes every zero with real part above 7/8
  - Treating the 7/8 value itself as binding: any fixed half-plane with theta at least 5/7 gives the same exponent from current density estimates
required_oracles:
  - exact rational and algebraic arithmetic for every exponent optimisation, checked against a dense float grid
  - an independent brute-force least-prime enumeration against the sieve implementation
  - the published statements of the cited density theorems, read at source
  - external human review of the written deduction, pending
kill_conditions:
  - a step of the explicit-formula deduction fails, for instance in the treatment of imprimitive or principal characters
  - the exponent algebra disagrees under exact recomputation or under a planted lesion it should detect
  - Chen-Gupta-Li Theorem 1.2 is withdrawn or found in error, which drops the main exponent from 7/3 to the classical 12/5
  - the sieve and brute-force least-prime tables disagree at any modulus
agents_may:
  - search the literature
  - derive
  - code exact checks and bounded numerical sanity runs
  - attack the deduction
agents_may_not:
  - re-audit or replay the input theorem
  - claim novelty from an empty search
  - promote their own claim
  - alter shared implementations outside this hunt
  - launch heavy local work, paid compute or publications
```
