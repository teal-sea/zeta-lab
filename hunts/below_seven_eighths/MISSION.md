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

## Disposition draft, 2026-10-26 (resumed in place; the owner decides)

Added when the lane was resumed in place by the owner's decision of 2026-10-26. The text above
is the mission as opened and is kept unchanged. This section is a draft: a hunt cannot
promote or close itself, and allocation is the owner's call.

**The bar has moved.** The question names 0.8748867. On 2026-10-21 the lane recorded smaller
public claims, down to 0.8748087 merged and 0.8747729897 in a draft (`FOLLOWUPS.md` section
1). On 2026-10-26 the smallest bound merged on QuasiRiemannTracker is 349843/400000 =
0.8746075 (PR 76, merged 2026-10-26T01:30:22Z), and the open PR 79 claims 4373037/5000000 =
0.8746074 (`FOLLOWUPS.md` section 14). None is refereed or replayed here. Every tracker entry
from PR 63 to PR 78 keeps M + l = 1 and the h/6 signal in its Lean import closure (inferred
from a source reading; not built). So the 13/15 floor model still frames that line, if its
floor rows are still counted in full, which was not checked.

**The kill condition, read honestly.** "A claimed improvement is matched or beaten by a public
follow-up already on record" needs a claimed improvement, and this hunt has none: every lane
page says that no smaller half-plane is claimed. The condition is therefore not triggered. That
is not a success. It only shows that the condition was written for a candidate the hunt never
produced. Its intent was not to spend on what the public record already covers, and that
intent now applies with more force. Part (a) would have to land between 13/15 and 0.8746075,
a window 0.0079408 wide (X22). The public line works on the same row-count and moment inputs
(section 5 of `FOLLOWUPS.md`: I1, I3, I5, I6) and moved 2.0e-4 in five days. This hunt's
row-count lane found no recount that gains at the paper's inputs.

**Dispositions (ALIGNMENT.md section 5), proposed:**

- **Part (a), row counts inside the Part II assembly: attempt unresolved.** Nine possible
  sharpenings were examined. Five died under exact enumeration or algebra, three hold but buy
  nothing at the paper's inputs, and the floor rows (I7) were not recounted (`ROWCOUNTS.md`).
  This is not an obstruction. 13/15 is the perfect-count ceiling of a model (hunt #134,
  unlanded, derived there), not a theorem about every count.
- **Part (b), a probe not tied to the sextic pole: attempt unresolved.** It was priced, not
  proved. Orders below 6 are cheaper in principle, and no system of such order was found with
  the lemmas it needs (`PROBE.md`).
- **The Euler-product step: no candidate refuted, nothing promoted.** Lemma 7.1 and its
  Gauss-sum inputs agree with two code-disjoint exact routes on the stated primes and boxes
  (`EULER_STEP.md`, `referee/REFEREE_W1.md`). This is *derived* on those ranges, not a proof
  of the lemma.
- **The sixth-power amplification (I2): priced as a door outside the assembly**
  (`amplification/LOSS_MAP.md`). Guo's Hypothesis 11.1 remains unproved.
- **The hunt as a whole: paused by allocation (proposed).** Further progress on part (a) needs
  a new lemma at I7, I9 or I2, the inputs the public line has not moved. Beating a public line
  that moves on the other inputs every few days does not look like the lab's best use of
  money. This is an allocation judgement, not a mathematical no-go, and the owner decides it.

Grades: the bar and the PR states are *cited* from the tracker's API; the floor-model reading
of each PR is *inferred*; the gaps are *derived* (pinned by `test_followups_identities.py`).
