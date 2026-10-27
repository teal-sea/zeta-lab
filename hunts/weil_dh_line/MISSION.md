# MISSION: `weil_dh_line`, Weil window positivity for zeta where the Davenport-Heilbronn form is negative

**Opened 2026-10-21. Hunt #146.** Branch `hunt/weil-dh-line`, worktree
`.claude/worktrees/weil-dh-line`, from `origin/main` at fb647bfc7. Route 4 of the
campaign the owner directed on 2026-10-21 (wave 2, lane `weil-dh-line`). The task
text proposed hunt number 139; numbers 138 to 144 are reserved for landings being
renumbered by another workflow, so this hunt is #146 (no ref under `refs/heads` or
`refs/remotes/origin` used #145 to #149 when it opened). Nothing in this directory
is a result until the case log in `hunts/README.md` says how it ended.

Grades used here are the three rungs of `CLAUDE.md`: *measured* (one route, float
grade), *hardened* (independent routes agree, or ball enclosures carry every step)
and *kernel-checked*. Nothing here is kernel-checked. The reserved enclosure word
that `CLAUDE.md` gives to `zeta/rigor.py` and the Lean arm appears nowhere in this
directory.

## The question

> Can Weil window positivity for zeta be proved, with enclosures, on a window
> where the Davenport-Heilbronn form is provably negative, that is on
> `supp f ⊆ [-L, L]` with `L ≥ L_DH := (log 30.617188)/2 = 1.7107808`?

## Why that window

- The Davenport-Heilbronn (DH) continuum Weil form is negative on every window
  `c ≥ 30.617188` (a hardened negative cell at `(c, N) = (30.617188, 256)` plus
  the nesting argument, which is ordinary and unreviewed;
  `hunts/weil_propagation/numerics/RESULTS.md` s3.2). In the normalization of
  arXiv:2608.24827 (Zhu) used by `hunts/oob_envelope`, `c = e^{2L}`.
- Epstein `(1,1,6)` is negative on every window `c ≥ 27.741699` in the odd
  sector (`L ≥ 1.66147`) and `c ≥ 29.304199` in the even sector
  (`L ≥ 1.68887`), same file, s9.2.
- So a positivity statement for zeta on such a window is a statement both rivals
  fail. Its proof has to read arithmetic they lack. In the out-of-band route of
  `hunts/oob_envelope` that arithmetic enters through one number, the envelope
  constant `S ≥ sup_t (P_L - H)(t)`, and the reduction runs at a split height
  `T#` above `2π e^S`.

## Windows

`L = 7/5`, `31/20`, `L_DH = 171079/100000` and `L_31 = 171699/100000`.

The task text names `1.71078`. As an exact rational it lies `7.8e-7` below
`L_DH` (`e^{2 * 1.71078} = 30.61714 < 30.617188`), so it is **not** a window on
which DH is proved negative. `171079/100000` is the least five-decimal rational at
or above `L_DH`, and it is used wherever the task says `1.71078`. `L_31` is the
largest five-decimal rational below `(log 31)/2 = 1.7169936`; both DH-line windows
read the same comb (`n ≤ 29`).

## Starting point (read-only inputs)

- `hunts/oob_envelope/theory/RESULTS.md`: Lemma 1 (out-of-band orthogonality),
  Theorem 1′ (`Q ≥ R_H`), Theorem 2 (strong duality, the best constant is
  `S*_L = λ_max(P)` of the windowed comb operator), Theorem 3 (`S*_L ~ e^L`),
  section 1.7 (no `H` beats the floor `T_res ≥ 2π e^{S*_L}`).
- `hunts/oob_envelope/numerics/`: the per-prime sine-kernel envelopes, the Arb
  assembly of `R_H` (`assemble.py`), unit costs (`RUNS.md`), the even bound
  `5.71789230595e-48` at `L = 1.19` (candidate, hardened by two routes).
- Local-only branches `teal-sea/oob-odd` and `teal-sea/oob-odd-referee`: odd
  sector `3.42853488205e-44` and the combined complex bound
  `5.71789230595e-48` at `L = 1.19`. Read with `git show`, never merged.
- Seed numbers at `L = 1.4` (oob_envelope `MISSION.md`, measured): per-prime
  `S_sep = 5.575` (Fejér degree 64), comb floor `S_opt = 3.708`.

## Tasks

1. At each window: the comb-operator floor `S*_L` with an enclosure; the
   separable per-prime envelope `S_sep`; the best evaluable joint out-of-band
   envelope (an LP over almost periodic `H` with every frequency at least `2L`,
   then a rigorous upper bound on `sup(P_L - H)` over the whole torus, not at
   sample points). Convert each to `T#`, mode count `N`, bits, memory and
   core-hours by the recorded rules. Go/no-go: **go only if some evaluable
   envelope gives `S ≤ about 6.2` at `L_DH`.**
2. At `L = 7/5`, a measured stage-A scout of `λ_min(R_H)` against `T#` with the
   best valid envelope, one unit timed first.
3. K2: the same pipeline run on DH at `L = 7/5` and at `L_DH` must return no
   bound.

Deliverables: `MISSION.md`, `PRICE.md`, `price.py`, `test_price.py`,
`scout_L140.json`, `RUNS.md`, and the case-log entry in `hunts/README.md`.

## Rules

- Scope: `hunts/weil_dh_line/` and this hunt's case-log entry. Everything else is
  a read-only input. Not `zeta/`, `ontology/` or `harness/`.
- Compute (the swarm box, 32 vCPU, 115 GiB, no swap, shared): keep
  `MemAvailable` above 20 GiB and wait while it is below 30 GiB before a process
  that may exceed 8 GB; at most 8 parallel numeric processes; wait while the
  one-minute load average is above 64 before a heavy job; time one unit and write
  the estimate in `RUNS.md` before any run longer than about 20 minutes, and
  checkpoint per unit. Pytest with `-n0` or at most `-n 4`, never the whole suite.
- Commits to `hunt/weil-dh-line` only, own paths only. No push, no pull request,
  no publication, no contact outside this machine.
- No em dashes in prose. Every number in a `.md` here is pinned by `test_price.py`
  or hedged where it stands.

```huntspec
id: weil_dh_line
question: Can Weil window positivity for zeta be proved, with enclosures, on a window supp f in [-L, L] with L at least (log 30.617188)/2 = 1.7107808, where the Davenport-Heilbronn form is provably negative?
frontier: the even-sector bound 5.71789230595e-48 at L = 1.19 (oob_envelope, hardened by two routes, candidate) and the odd sector 3.42853488205e-44 on a local-only branch; no zeta window bound recorded above L = 1.19; DH negative on every window L at least 1.7107808 (weil_propagation, hardened cell plus nesting); seed envelopes at L = 1.4 are S_sep 5.575 and comb floor 3.708 (measured)
proposed_attack: price the out-of-band reduction at L = 1.4, 1.55, 1.71079 and 1.71699 through the comb floor, the per-prime envelope and the best joint envelope that can be bounded on the whole torus, decide go or no-go at the DH line against S at most about 6.2, scout lambda_min(R_H) at L = 1.4, and run K2 on DH
dead_routes:
  - a constant envelope below the comb-operator floor S*_L, excluded for every finite-measure H by weak duality (oob_envelope theory Proposition 2.1)
  - replacing the symbol above a resolved height by a constant minorant with no envelope (arXiv 2608.24827 section 15, failed route 2), which leaves the form indefinite
  - the per-prime Euler-product envelope applied to DH, which has no Euler product, so the bound does not hold for its comb
required_oracles:
  - Arb ball arithmetic from python-flint for every enclosure and every frequency decision
  - exact rational and dyadic arithmetic for every coefficient that enters a stated bound
  - scipy and numpy float eigensolvers and mpmath at two precisions as independent second routes, never as the proof
  - weak duality as a gate, every evaluable envelope at or above the Arb lower endpoint of S*_L
kill_conditions:
  - an evaluable envelope below the Arb lower endpoint of S*_L, which weak duality forbids and so marks a defect
  - a frequency of a proposed H below 2L, or a supremum bound that holds only at sample points
  - the K2 pipeline returns a positive bound for DH at L = 1.71079
  - the scout's sign at a checkpoint changes under a precision or mode-count refinement
agents_may:
  - read
  - derive
  - code
  - compute on the swarm box under its rules
  - attack the construction
agents_may_not:
  - declare novelty
  - declare theorem status for anything not kernel-checked
  - promote their own claim
  - push, publish or contact outside parties
  - edit zeta, ontology or harness
```

## Corrections (2026-10-26)

Appended when the owner resumed this lane in place on 2026-10-26. The text above
is left as written on 2026-10-21.

1. **The odd sector is on main.** "Starting point" and the huntspec `frontier`
   cite the odd sector `3.42853488205e-44` at `L = 1.19` as being "on a local-only
   branch" and "never merged". That was true when this hunt opened; main merged
   it the same day in PR #327 (merge commit `f7ff060aa`, from
   `land/oob-odd-sector-20261021`). It now lives in
   `hunts/oob_envelope/numerics/RESULTS.md`, with the referee's weaker
   reproduction recorded beside it. Read it there, not with `git show`.
2. **Push and pull request.** "Rules" says no push and no pull request. The
   owner's decision of 2026-10-26 superseded that for this branch: it is pushed to
   `origin/hunt/weil-dh-line` and carried by a draft pull request. The other rules
   stand.
3. **What K2 at `L = 7/5` can say.** Task 3 asks that K2 "on DH at `L = 7/5` and
   at `L_DH` must return no bound". The DH form is known negative only on windows
   `L >= 1.7107808`, so at `L = 7/5` there is no negativity for the pipeline to
   detect, and a stage-A block with no negative pivot there contradicts nothing.
   The kill condition was always the narrower one in the huntspec (a positive
   bound for DH at `L = 1.71079`). `PRICE.md` item 6 records the reconciliation.

## Corrections (2026-10-27)

Appended when the owner asked, after the adversarial review of PR #356, for the
measured refusal at `T# <= 800` to be raised or shown unraisable. The text above
is left as written.

4. **Kill condition 3 at every `T#`.** The stage-A block `R(T#)` increases to the
   `N`-mode DH form `Q_N` (no split) as `T#` grows, under the pipeline's own
   inputs, so K2 refuses DH at `L_DH` at every `T#` exactly when `Q_N` has a
   negative eigenvalue. `witness.py` assembles `Q_N` in position space in Arb:
   it has one, `-1.943e-30` at `N = 856`, and every leading block from 101 modes
   on has one (`PRICE.md` item 7, hardened). The kill condition "the K2
   pipeline returns a positive bound for DH at `L = 1.71079`" therefore cannot
   fire at stage A at any `T#` or any `N >= 101` while `S` is valid; the
   composite is measured at the validity of `S`.
5. **Kill condition 4 was not tested** by the recorded responses: the leading
   `N - N//13` block is a principal submatrix (interlacing), not a refinement,
   and the `prec - 128` reduction copied the data unrounded (`PRICE.md` items 5
   and 6). `scout.responses_of` now rounds the data.
6. **Deliverables added**: `witness.py`, `test_witness.py`, `witness_q856.json`,
   `witness_v856.json`, `witness_v101.json`, `v800_T800.json`,
   `c800_block100.json` (the leading 100-mode block of the stored `C(800)` and
   `G(800)`, for the calibration and lesion tests), `stage_a_v800.json`,
   `stage_a_witness.json`, and the `lesion_S` record in `k2_scouts.json`.
