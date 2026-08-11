# MISSION — `frontier_map`

## Persona

A cartography exercise, not a search. `wide_search` mined one method — the
10 August 2026 paper *More than two thirds of the zeros of the Riemann zeta
function lie on the critical line* — for a sharp constant and a ceiling
reproduction. This hunt assembles what that work scattered across three
RESULTS files into one instrument and one picture: **the frontier map** of
unconditional critical-line proportions reachable by the paper's
pair-correlation machinery, as a function of the one dial the method has
(the bandwidth λ), against the ceilings and prior-art bars that box it in.

A map is not a discovery. Every number on it is either computed here by the
laboratory's own optimiser, taken from the paper with a line citation, or
inherited from `wide_search` with its caveats attached. The value of the map
is that the open gaps become *coordinates* — intervals with two computed
endpoints — instead of prose.

## Scope

**This hunt may write**: `hunts/frontier_map/` and `figures/`.

**This hunt may not write**: `zeta/`, `ontology/`, `harness/`, `lean/`
without explicit permission, and may not write a verdict into `README.md`,
`ROADMAP.md` or `HANDOFF.md` as an established finding. It may not promote
its own claim. It reads (and does not modify) `hunts/wide_search/`, whose
`xiprime.py` optimiser is the shared instrument.

## Objective

Three deliverables, all measurements:

1. **The λ-landscape.** For each kernel the paper's machinery accepts
   unconditionally — Montgomery's F (ζ) and Farmer–Gonek–Lee's F₁ (ξ′) —
   the optimal proportion H(λ) of simple on-line zeros over the admissible
   band λ ∈ (0, 1], with the distinct-zero companion Hd(λ) = (1+H)/2, the
   onset λ₀ where the certificate first becomes non-empty (H > 0), and the
   value at the wall λ = 1.
2. **The cross-check.** The paper's eq. (7.4) gives the ζ optimum in closed
   form; the numeric optimiser must match it along the whole curve, not only
   at λ = 1. A generator of a curve never judges it; the closed form was not
   used to build the optimiser.
3. **The gaps, as intervals.** Attained-versus-ceiling for ζ
   (Remark 1.1's 0.68185, with the hypothesis-scope caveat measured in
   `wide_search/RESULTS-pair-ceiling.md`), attained-versus-Wu for ξ′, the
   blocked κ ≥ 2 lane, and the paper's own structural wall: the bandwidths
   ~1.04 / 1.26 / 1.70 it states would be needed for 0.70 / 0.80 / 0.90.

## The standing checklist, answered in advance

1. **Rival.** No structural claim about ζ is made here, so the battery has
   nothing to distinguish; the paper itself records (§7.5) that for
   Davenport–Heilbronn-type functions Proposition 5.6 fails and the
   certificate is empty, which is the correct rival behaviour for the
   *method* and is quoted on the map, not tested here.
2. **Decoy / surrogate.** Not applicable to a map of published constants;
   the computed curves get control 4 instead.
3. **Lesion.** `probe.py` runs the optimiser against a deliberately wrong
   closed form (a mis-set constant in eq. 7.4) and must see the discrepancy
   that the honest comparison does not show.
4. **Precision response.** Every computed point on the map is re-run up a
   convergence ladder (basis size, quadrature order) and the settled digits
   recorded before it is written down.

## Vocabulary

This directory says *measured*, *observed*, *consistent with*. It does not
say *verified*, *confirmed*, *definitively*, and it never uses the reserved
word that `zeta/rigor.py` owns for enclosure-carrying quantities — a ban
`tests/test_hunt_probe_discipline.py` enforces on the bytes of every file
here. Nothing in this hunt is evidence for or against RH, in either
direction; the map charts a *method*, and the method's own paper states that
nothing in it distinguishes "two thirds" from "all" (§7.5(a)).
