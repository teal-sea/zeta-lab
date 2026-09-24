# REVIEW: referee/, the ΔT error bound (internal review, not external)

**Status: phase 1 committed; phase 2 (review of bound_trunc/, bound_quad/,
assembler/) waits for routing.** Nothing in those three folders was read
before the phase 1 commit (BRIEF.md, Independence). One disclosure: while
checking the branch, `git log --oneline` showed the subject lines of
bound_trunc/'s and bound_quad/'s milestone 1 commits (4a0818f, ab0f8fa). No
file of theirs was opened; the test design and the plant list were fixed
before those lines appeared, and nothing changed after them was prompted by
them (later edits follow this folder's own plant numbers only).

A second disclosure. The first full run of `test_referee_bounds.py`, just
before this commit, found `bound_quad/eps_quad.py` and both JSON files
already on disk (uncommitted work in progress) and so executed them. What
reached this folder was pytest's summary only: a `ValueError` raised in
`eps_quad.py`, the trunc JSON without an entry at the 280-mode build's
S_exact, and every entry of both JSON files null at that moment. No source
line was read. The phase 1 tests were verified before the commit on the
subset that needs no bound (7 tests) plus `tests/test_hunt_probe_discipline.py`
and `tests/test_docs_numbering.py` (13 tests), all passing; nothing in the
tests was changed after that run.

## Phase 1: what the tests check (`test_referee_bounds.py`)

The bound interface is BRIEF.md's, fixed in advance: `eps_trunc` and
`eps_quad` of (c, N, nvec, S, Kmax), each an arb ball, and one JSON file per
folder. The bound on ΔT of one build is ε = eps_trunc + eps_quad; Q and T_∞
cancel in every difference the tests form.

**The inequality.** For two builds a, b of the same (c, N), a valid bound
implies ‖ΔT_a − ΔT_b‖₂ ≤ ε_a + ε_b (I), and nothing stronger. The tests
that ask for more name the assumption they add:

- **M**: the reference b is refined far enough that ε_a alone dominates the
  change (the brief's "bound at the degraded configuration").
- **R**: a knob the interface does not carry is refined, or the samples are
  perturbed within their measured float64 error, and the bound at a's
  configuration covers that build too; then (I) reads change ≤ 2 ε_a.
- **D**: eps_quad alone bounds the distance to the exact ΔT of the same
  modes, as the brief's error-source table assigns it; with R, a change that
  keeps the modes gives change ≤ 2 eps_quad(a).
- **W2**: two_adic/ s7b's runs use s panel width 2, the stored builds width
  1; the bound at the s7b configurations is taken to cover width 2.

**Plants** (`run_referee_plants.py`, `referee_plants.json`), on
c ∈ {2.2, 2.5, 2.9} and N ∈ {8, 16, 32}:

| kind | plants | error source |
|---|---|---|
| interface | nvec 40, 60 against 80 at S = 2400 | truncation (bound_trunc/) |
| interface | S 800, 1200, 200, 150 against 2400 at 80 modes | s cutoff (bound_quad/) |
| interface | Kmax 8, 9, 10 against 12 at (40, 1200) | dyadic w truncation and the 1/w tail (bound_quad/) |
| refinement | w nodes per panel 12 → 16; s nodes 8 → 12; s width 1 → 0.5; tail terms 25 → 40; derivative orders 14 → 20 | w and s quadrature, tail series (bound_quad/) |
| refinement | samples perturbed by 2^−53 and by 1e−13 relative; ρ by SVD instead of QR; at cond(F_z) of about 17, 7e11 and 4e14 | mode data, Gram step (bound_quad/) |
| refinement | assembly sums correctly rounded (`math.fsum`) | float64 assembly (bound_quad/) |
| outside | w nodes per panel 12 → 6 | measured only: the interface cannot express it |
| defect | mode 0 or mode 10 dropped; ρ by the explicit inverse | not covered, labelled |

**Observed responses:** every pair of stored builds of the same (c, N) at
N = 16 and N = 32, and two_adic/ s7b's nvec chain at S = 4800 and S chains
(c = 2.2, N = 8, under W2).

**Internal consistency:** every one of the 33 (c, build) entries present in
each JSON, keyed by the S the build used (`S_exact` in checker/'s snapshot,
non-integer for the 280, 319 and 364-mode rows), Kmax = `kmax_for(nvec)`,
eps_upper ≥ the ball's upper end (exact rational comparison) and within 1 %
of it, and every null with a reason.

## The interface finding (sent to the coordinator with the phase 1 commit)

The interface takes (c, N, nvec, S, Kmax) only. The w Gauss nodes per panel,
the s panel width and nodes, the term counts of the 1/w tail series and the
derivative orders of φ̃_n at 1 are fixed inside two_adic/ and are not
arguments. A coarsening of any of them therefore cannot be tested against
the bound, only a refinement under assumption R; and the s7b runs, built at
s panel width 2, lie outside the stored builds' quadrature, so their
dominance test needs W2. At (80, 1200), c = 2.2, N = 8 the width-2 build
differs from the stored width-1 build by 4.8e−13 in spectral norm
(`test_s7b_width_2_against_the_stored_width_1`), so W2 is harmless there;
the derivation still has to say which widths it covers.

## Phase 2

Pending routing of bound_trunc/, bound_quad/ and assembler/.
