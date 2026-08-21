# RESULTS: controls for the F1 discovery engine

**Exploratory. Nothing in `hunts/` is a result or evidence** (`hunts/README.md`).
What follows is measured, at the sizes stated, with the instruments in this
directory. The claims it corrects are in `docs/15-the-f1-discovery-engine.md`,
whose *Corrections* section carries the same three findings for a reader who
arrives there instead.

Grade: **measured**. Two of the three findings are arithmetic statements about
a finite matrix and could be hardened; none of them is about zeta.

## The setting

`docs/15` writes up seven prototypes and closes with a Reality Check of five
critiques, sourced to outside checkers, that dial its own rhetoric back. The
Reality Check is the honest half of that page. It had also never been tested:
five assertions in prose, one of them a closed-form arithmetic law, one of them
a claim about a prototype's behaviour, and no test anywhere in the tree touching
either. The prototypes are frozen (`AGENTS.md`), so everything here reads them
by path and modifies nothing.

## Finding 1: the ln 2 multiplicity is `dim ker C`

Reality Check item 5 explains the degenerate eigenvalue at `ln 2` in
`ontology/04_transcendental_matrix.py` as a truncation artifact "with
multiplicity `pi(N/2) - pi(N/3) - 1`". The artifact reading holds. The formula
is the special case in which every dead-end node is prime.

Derivation and mechanism: `ln2_law.py`, module docstring. In short, the nodes
`u` with `2u <= N < 3u` carry a private `ln 2` rung at the top of the graph; the
eigenvalue equation is automatic on their support and constrains only the hubs
`u/q` below them; so the multiplicity is the kernel dimension of the hub
incidence matrix `C`. Prime dead ends share the single hub `1`, giving
`|D| - 1 = pi(N/2) - pi(N/3) - 1`. Composite dead ends normally pin their own
coefficients to zero, until they close into a pattern.

- The law agreed with the eigenvalue count at **all 251 sizes `N = 10 … 260`**
  and at a coarser scan through `N = 800`. No disagreement.
- Both rank routes (40-digit elimination, double-precision LAPACK) agree at
  every size checked.
- The measured cluster sits within `~1e-15` of `ln 2`: exact degeneracy, not a
  near-degeneracy that a tolerance manufactured.
- The quoted formula first undercounts at **`N = 338`**, where the semiprimes
  `121 = 11^2`, `143 = 11 x 13`, `169 = 13^2` give three columns over the two
  hubs `11` and `13`.

Raw scan: `results_ln2.json`.

## Finding 2: the density gap widens under refinement

Reality Check item 2 says the prototype has "dozens of frequencies below 17.7,
where zeta only has one zero". Counted at the 400-node truncation of `docs/15`
section 6: **171 modes below 17.7 against 1**, and **159 modes below the first
ordinate 14.1347 against 0**.

The refinement response is the part worth keeping. Spurious low modes accumulate
at roughly `0.35 N`, while the top of the spectrum creeps like `log N`, about
3.7 units of frequency per doubling of the node count.

| nodes | modes | top mode | below `gamma_1` |
|---|---|---|---|
| 100 | 42 | 12.24 | 42 |
| 200 | 88 | 15.56 | 87 |
| 400 | 172 | 19.12 | 159 |
| 800 | 349 | 22.95 | 294 |
| 1200 | 522 | 25.34 | 421 |

Extending the trend puts the 20th ordinate (`77.145`) somewhere near `10^7`
nodes, with millions of modes below zeta's first zero. That extrapolation is a
trend line and is labelled as one; the finding does not rest on it.

Raw scan: `results_density.json`.

## Finding 3: the gauntlet's criticism was aimed at the wrong half

Reality Check item 4 calls `07_the_imposter_gauntlet.py` vacuous because "the
construction never actually consults zeta". Measured, that splits three ways.

1. **True of the operator.** `build_polya_hilbert_operator` takes `N` and
   nothing else, so no candidate function can enter it. "The geometry
   structurally rejects the imposter" is not about the geometry.
2. **False of the predicate.** What `07` runs is a coefficient multiplicativity
   test, which the tree owns as `zeta.epstein.claim_multiplicativity`. Through
   `zeta.epstein.battery`: passes zeta, fails Davenport-Heilbronn and both
   discriminant `-23` Epstein rivals, `distinguishes: True`, `shared_with: ()`.
3. **The real defect in `07`'s conclusion.** Both mod-5 Dirichlet L-functions
   whose combination is Davenport-Heilbronn pass that predicate, as does every
   primitive L-function with an Euler product. The test separates Euler products
   from linear combinations of them. That is what `battery`'s docstring says it
   separates, and it is a real answer to `docs/11` gate #3. It is not immunity
   to false positives, and it does not single out zeta.

Raw output: `results_gauntlet.json`.

## What was not corrected

`docs/15`'s two headline numbers still come out of the prototypes unchanged:
Mode 5 at `8.169` on the transcendental prime grid, Mode 20 at `1.937` for the
400-node prototype. Reality Check items 1 and 3 are judgments, not measurements,
and are left as written.

## Disposition

The three findings are pinned by `tests/test_f1_engine_controls.py` (30 tests,
about 4 s, fast tier). `docs/15` carries a correction notice at its head and the
detail at its foot. The stale `discovery/` paths that survived the rename to
`ontology/` are repaired in `docs/15` and `docs/09`, and
`tests/test_docs_paths.py` now fails if any document in `docs/` points a reader
at a Python file that is not there.

No claim here goes to the funnel or the battery: none of it is about zeta.
