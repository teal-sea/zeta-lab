# MISSION — `frontier_math`

## Persona

The operator's instruction: go find previously unknown mathematics adjacent to
the 10 August 2026 paper (*More than two thirds of the zeros of the Riemann
zeta function lie on the critical line*), continuing from where `wide_search`
stopped. Its HANDOFF left one pre-registered open thread (THREAD 1: "the
full-data LP over marked periodic configurations") and one blocked one.
This hunt works that frontier: what is the best unconditional constant the
paper's kind of data can deliver, and can any known conditional refinement be
made unconditional through the paper's machinery?

## Concurrent sessions

More than one session has worked this directory at once. **Read
`ACTIVE-CLAIMS.md` before launching an agent, a prover submission, or a
build here**, and add a row for anything you start that runs longer than
a few minutes. `HANDOFF.md` remains the serial, between-sessions record;
`ACTIVE-CLAIMS.md` is the live one.

## Scope

**This hunt may write**: `hunts/frontier_math/` and `figures/`. It may add a
cross-reference line to `hunts/wide_search/HANDOFF.md`'s THREAD 1 section
(that hunt's own operating state, not a repo-level verdict).

**This hunt may not write**: `zeta/`, `ontology/`, `harness/`, `lean/`
without explicit permission; no verdicts into repo-level `README.md`,
`ROADMAP.md` or `HANDOFF.md`. It may not promote its own claims: anything
here that looks like a theorem is a *candidate* with named unproven lemmas
until it goes through the routes that can say yes.

## Objective

Three lanes, worked in order of expected value:

1. **Answer THREAD 1.** Formulate and solve the LP over pair-measure data
   (positivity + bandwidth-one evaluation + multiplicity types): does it
   collapse to the paper's 0.6725007, or move into (0.6725007, 0.68185)?
2. **Transplant audit.** For each known RH-conditional refinement in the
   pair-correlation class (Cheer–Goldston 1993; Chirre–Gonçalves–de Laat
   2020), determine exactly which inputs the paper's unconditional machinery
   supplies, which it does not, and whether the refinement transfers. Compute
   the transferred constant where it does.
3. **The walls, quantified.** Where a transplant fails, record the mechanism
   at the level of a computation (not a feeling), so the next session does
   not re-derive it.

## The standing checklist, answered in advance

1. **Rival.** Structural claims here are about *methods* (optimisation values,
   certificate mechanisms), not about ζ being special; the paper itself
   records that its certificate is empty for Davenport–Heilbronn-type
   functions. Any claimed positivity structure that is supposed to hold for
   conjugate-closed multisets generally is checked numerically on a multiset
   with genuinely off-line points (the lab's DH configuration), where it must
   ALSO hold — a structural lemma failing on the rival would be a bug, and
   passing distinguishes nothing (it is not that kind of claim).
2. **Decoy / surrogate.** LP and floor computations are checked against
   planted-wrong inputs (a mis-set kernel constant, wrong λ_k) that must
   break the agreement.
3. **Lesion.** See 2; each instrument carries one.
4. **Precision response.** Every optimisation value is re-run up a
   discretization ladder (grid, tolerance, bucket count) before being
   written down.

## Vocabulary

*Measured*, *observed*, *consistent with*. Never the reserved word owned by
`zeta/rigor.py`; not *verified*, *confirmed*, *definitively*. A "candidate
theorem" here means: mechanism written down, constants computed, named gaps
listed — and nothing more. Nothing in this hunt is evidence for or against
RH.
