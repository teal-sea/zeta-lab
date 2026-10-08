# MISSION: what moves under QRH(theta), priced before the fact

**Opened 2026-10-08. Hunt #121.** Nothing in this directory is a result until
the case log in `hunts/README.md` says how it ended, and even then nothing here
is evidence about RH: every statement below is conditional on a hypothesis
that nobody known to this laboratory has replayed. The strongest words used
here are *derived* (an ordinary argument on cited inputs, written out),
*measured* (one mpmath route at a stated precision) and *cited* (somebody
else's statement, with its location). The reserved enclosure word belongs to
`zeta/rigor.py` and appears nowhere in this directory.

## The hypothesis

On 2026-10-06 OpenAI published `github.com/openai/math`. Its family 003 claims
that every Dirichlet L-function, zeta included, is zero-free in Re s > 7/8,
uniformly in the modulus, with a companion paper (2026-10-05) proving 11/12
by the same method. No replay by anyone known here, no peer review. The lab's
reading of the release is `38-the-quasi-riemann-claim.md`, the course's
document 38, at commit `715d572` on branch `claude/openai-math-release-2026-10-06`;
it is not on `main` as of 2026-10-08, which is why this directory names the
file and never writes the usual bare reference to it.

Call the hypothesis **QRH(theta)**: for every Dirichlet character chi mod q
and every s with Re s > theta, L(s, chi) is nonzero except the principal pole,
with theta = 7/8, and theta = 11/12 as a second instance. **It is a hypothesis
in this hunt, never a theorem.** Every consequence drawn here is stated in the
form "Under QRH(theta): ...", and if the claim is withdrawn or refuted by an
independent replay, every such statement is void and this hunt says so.

## The question

Which of this laboratory's priced walls and conditional results would move
under QRH(7/8), by how much, and which would not move at all? Document 38
section 6 priced two consequences (the de Bruijn-Newman record does not move,
the simple-zero proportions take no strip as input) and left one open: the
q = 1 component of `hunts/prime_pair_error/UPPER_BOUND.md` (1), which
`SW_EFFECTIVE.md` records as "a full power of N short of (31)". This hunt
answers that one with every exponent explicit, extends the pricing to the
q > 1 components, Theorems A and B, the signed-mean frontier, the ineffective
constants, Li's criterion, and records the non-movers with citations.

```huntspec
id: qrh_conditional
question: Which of this laboratory's priced walls and conditional results move under the hypothesis QRH(theta) that every Dirichlet L-function is zero-free in Re s > theta, theta = 7/8 (and 11/12), by how much in the exponent, and which do not move at all?
frontier: hunts/prime_pair_error rank 1 at N^3 L^{-2H} (a full power short of (31)), rank 2 at N^{13/5} L^6, completed bound (1) at N^3 L^{-C}; Theorem A empty unconditionally; de Bruijn-Newman record 0.2 with 9/32 under the strip (document 38 section 6); Li coefficients nonnegative only as far as computed
proposed_attack: replace every prime-counting remainder the hunt reads by x^theta (log qx)^2, carry the exponent arithmetic exactly, and keep the hypothesis in every sentence
dead_routes:
  - treating QRH(theta) as a theorem of this laboratory, it is an unreplayed claim and nothing here changes that
  - re-deriving the de Bruijn-Newman consequence, document 38 section 6 already did that arithmetic and it is cited here
  - bootstrapping the strip through the circle-method bound, the map theta to (2 + theta)/3 drifts toward 1 and has no fixed point below it
  - reading a strip as a zero-density estimate, it bounds neither the number nor the heights of hypothetical off-line zeros
required_oracles:
  - exact rational arithmetic on the exponents displayed in hunts/prime_pair_error/UPPER_BOUND.md and RESULTS.md
  - mpmath at stated precision, dps 30, bisection on a one-variable sign change
  - Davenport, Multiplicative Number Theory, chapters 16, 17, 19 and 20, as published
  - Johnston and Yang, arXiv 2204.01980, Theorem 1.1, as read from the arXiv rendering on 2026-10-08
  - the hunt's own recorded exponents in UPPER_BOUND.md, read and not re-proved
kill_conditions:
  - QRH(theta) is withdrawn or refuted by an independent replay, in which case every conditional statement here is void and this hunt says so
  - an exponent in RESULTS.md is shown not to follow from UPPER_BOUND.md's displayed inequalities plus the uniform remainder x^theta (log qx)^2, which retires that line and its row in the table
  - the Johnston and Yang constants are found misquoted against the journal version, which voids the two crossover heights and nothing else
  - a reader exhibits a consequence of the strip for rank 2 or for the Li coefficients at finite n that this hunt said does not follow, which reopens that row as unresolved rather than closed
agents_may:
  - derive
  - code
  - measure
  - cite
  - price
agents_may_not:
  - assign evidentiary status to any output of this hunt
  - state any consequence of QRH(theta) unconditionally, or without the hypothesis in the sentence
  - declare novelty
  - declare theorem status
  - promote their own claim
  - edit anything outside hunts/qrh_conditional and the one entry in hunts/README.md
```

---

## 1. What was read, and what was not

Read in full: `hunts/prime_pair_error/SW_EFFECTIVE.md`, `UPPER_BOUND.md`,
`RANK3_SCOPE.md`, `FRONTIER_2026_09_12.md`, `RESULTS.md` sections 12 and 16
to 19 and its "The doors" section, the 2026-09-10 entry of `HANDOFF.md`,
`zeta/li.py`'s module docstring, document 38 sections 2 and 6, and pages 1
and 2 of the 11/12 preprint
(`/home/user/openai/math/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf`),
where Corollary 1.2 states that under its Theorem 1.1, for x >= 2,
sup over 1 <= q <= x and (a, q) = 1 of |pi(x; q, a) - (1/phi(q)) Li(x)| << x^{11/12} log x
with an absolute effective implied constant.

Read only at the header: `SIEGEL_UNIFORMITY.md` (its displayed bound (1) and
the sentence saying when its exceptional terms are present), `tb_bind_grh.py`.
Not read: the RANK3_BDH, RANK3_QUARTIC and RANK3_ROUTE documents, the
remaining 180 pages of either preprint, and any Lean. Where RESULTS.md says a
document was not read, the statement about it is limited to what its header
says.

## 2. Rules binding this hunt

- A conditional result keeps its hypothesis in every sentence that uses it.
- Every number stated is pinned by `test_qrh_conditional.py` or hedged at the
  point of use.
- Under `hunts/` the reserved word is banned lexically; it is not typed here,
  not even to disclaim it.
- No em dashes in prose written here; quoted material keeps its punctuation.
- This hunt does not assign evidentiary status to its own output. The grades
  it writes (derived, measured, cited) say what was done, not what it is worth.
