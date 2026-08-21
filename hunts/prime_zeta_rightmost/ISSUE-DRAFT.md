# ISSUE-DRAFT.md: a drafted GitHub issue, not posted

**Status: drafted 2026-08-16, not posted.** Posting is an operator action;
this hunt may not open issues on its own behalf, and this file is the
artifact, not the act.

## Should this be an issue at all?

The repository's rule (`AGENTS.md`, "Observations, and the work roster") is
that an observation is public and a lead is private. An issue says "this is
true and unresolved"; the roster says "this one is next".

The bridge below qualifies on all three counts:

- **It is a statement about the subject, not about our allocation.** It says
  a published open conjecture already follows from an earlier published
  theorem. It is true or false independently of whether this laboratory ever
  works on it again.
- **A stranger can check it.** Both papers are open access, both statements
  are quoted verbatim in `PRIOR-ART.md`, and the specialization is four
  hypothesis checks, none of them long.
- **It is unresolved in the literature.** Neither paper cites the other, and
  the conjecture is still printed as open.

What would make it a *lead* instead, and therefore private, is a plan to
write it up, contact the authors, or otherwise pursue it. That decision is
the operator's and belongs in the roster in `fulcrum`, not here. The issue
below states the fact and stops.

One caution worth stating in the issue itself: this is a literature
observation, not a theorem of ours. The grade is "new as a literature
observation, zero new mathematics", and the issue should not be written in a
way that lets it read as a result of this laboratory.

---

## Drafted issue text

**Title:** A published open conjecture on the prime zeta function is already
a corollary of a 2022 theorem on almost periodic functions

**Labels (suggested):** observation, literature

**Body:**

While adjudicating prior art for hunt #60 (`hunts/prime_zeta_rightmost/`)
we noticed that two published results, which do not cite each other, are the
two directions of one statement, and that one paper's open conjecture is the
other paper's theorem.

**The conjecture, still printed as open.** Belovas, Cepaityte and
Sabaliauskas, "On the zero-free region and the distribution of zeros of the
prime zeta function", An. St. Univ. Ovidius Constanta Ser. Mat. 33(2) (2025)
27-44, DOI 10.2478/auom-2025-0017 (open access). Their Theorem 1 states that
the prime zeta function P(s) = sum_p p^(-s) has no zeros in the half-plane
sigma > sigma_0, where sigma_0 = 1.77954465354699... is the root of
U(sigma) = 2^(1-sigma) - P(sigma). Their Conjecture 1 states that
lim_{T -> infinity} sigma_T = sigma_0, where sigma_T is the supremum of the
real parts of the zeros of P with |t| < T. Their Remark 1 records
sigma_M = 1.682628788045196... for |t| < 200000, so their numerics leave a
gap of about 0.097 to the wall.

**The theorem that settles it.** Sepulcre and Vidal, "On the real
projections of zeros of analytic almost periodic functions", Carpathian J.
Math. 38 (2022) no. 2, 489-501 (preprint arXiv:1805.02041, 2018), Theorem
4.3 = preprint Theorem 6. For an almost periodic function f on a vertical
strip U with Dirichlet series sum_{n >= 1} a_n e^{lambda_n s}, frequencies
{lambda_n} Q-linearly independent, and sigma_0 in that strip, sigma_0 lies
in the closure of the set of real projections of the zeros of f if and only
if |a_j| e^{sigma_0 lambda_j} <= sum_{i != j} |a_i| e^{sigma_0 lambda_i} for
every j.

**The specialization.** Take f = P on a fixed strip
{1 + delta < Re s < infinity} with 0 < delta < sigma_0 - 1. Almost
periodicity holds uniformly on that strip (P is bounded there); the
frequencies -log p are Q-linearly independent by unique factorization; there
are infinitely many terms; and the domination condition collapses, because
p -> 2 p^(-sigma) is strictly decreasing so the index p = 2 binds, to

    2 p_j^(-sigma_0) <= P(sigma_0) for all j   <=>   2^(1-sigma_0) - P(sigma_0) <= 0,

which is exactly Belovas et al.'s U(sigma_0) <= 0. Hence:

- the "only if" half re-proves their Theorem 1 (no zeros with
  Re s > sigma_0);
- the "if" half gives closure{Re s : P(s) = 0} intersect (1, infinity) =
  (1, sigma_0], and since sigma_T is nondecreasing and bounded above by
  sigma_0, it forces sigma_T -> sigma_0. That is their Conjecture 1.

**Provenance and grade.** This is a literature observation, not a result of
this repository: no new mathematics is involved, and both statements are
used exactly as published. Grade: new as a connection between two published
papers; the underlying theorems are theirs.

**Where the working is.** `hunts/prime_zeta_rightmost/PRIOR-ART.md`
sections 6 and 7 carry the verbatim statements of both results, the
hypothesis-by-hypothesis specialization, and a gap analysis of the bridge
(two harmless technicalities noted: max versus sup on an open condition, and
sigma_T being undefined for small T). Section 10 records why our own search
missed both papers, which is the more transferable lesson.
`docs/30-prime-zeta-rightmost-zeros.md` is the public reading-course page,
rewritten to lead with the prior art.

**What is not claimed.** Nothing here bears on the Riemann Hypothesis: every
zero discussed lies in Re s > 1 and belongs to P, not to zeta. Nothing here
is kernel-checked. We have not contacted the authors and have made no
attempt to publish; whether anyone pursues this is not what this issue is
for.
