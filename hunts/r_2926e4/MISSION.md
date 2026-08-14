# Hunt R-2926E4: what `o9_leaf.py`'s 1-D O9 table costs on the kernel's own leaves

**Question.** `hunts/frontier_math/o9_leaf.py` states a **LEAF CAVEAT**: its
transcendental leaves come from Arb at 300 bits rounded outward with a 4-ulp
pad, `BandCert/Leaves.lean` builds them from truncated Taylor series, and the
two "agree to well under `2^-60`", so a cell passing with margin is safely
predicted. Issue #23 says that is false on wide cells, because the two objects
differ in kind rather than in precision. The module's headline **344 cells**
rests on the caveat. What is the count once the leaves are computed the way the
kernel computes them, and by how much was 344 wrong?

**Scope.** This hunt writes only `hunts/r_2926e4/` plus its case-log entry in
`hunts/README.md`. It reads `hunts/frontier_math/` and imports from it; it
changes nothing there. `o9_leaves_kernel.py`, the mirror of `Leaves.lean` pinned
against Lean's own `#eval`, already exists in that directory and is the
instrument this hunt consumes rather than rebuilds.

**Not in scope.** Whether `damageIv_mem` (the soundness lemma the whole table
waits on) exists; the `k >= 2` range; the 2-D route, which was already repaired.
Nothing here is evidence about RH.

```huntspec
id: r_2926e4
question: What is o9_leaf.py's 1-D O9 cell count when its transcendental leaves are computed the way BandCert/Leaves.lean computes them, rather than with Arb?
frontier: o9_leaf.py reports 344 cells, max depth 20, min margin 3.63e9 ulp, on Arb leaves; the analogous 2-D table moved from 598 to 1939 leaves (3.2x) when its leaves were repaired, and decide +kernel had already refuted 7 of the 9 chunks of this 1-D table
proposed_attack: swap o9_leaf.leaves for o9_leaves_kernel.kernel_leaves, leave every other line of the walk byte-identical, and rerun
dead_routes:
  - trusting a width comparison on a single hand-picked interval; the ratio varies by leaf and by cell width, so one interval is not the statistic
  - assuming a wider leaf layer only loosens margins; it also changes which cells are decidable at all, so the walk depth must be re-established rather than reused
  - building the Lean arm here to obtain the verdict directly; zeta23ext has no .lake cache in this container and would need Mathlib from source
required_oracles:
  - fixed-point integer arithmetic at scale 2^64, exact in Python ints, no floating point in the decision path
  - the leaf mirror's round-trip against Lean #eval output, integer for integer, in tests/test_o9_leaves_kernel.py
  - the unmodified o9_leaf walk as the baseline, rerun rather than quoted
kill_conditions:
  - the baseline rebuild does not reproduce 344 cells at min margin 3.63e9 ulp, which would mean the comparison is not against the recorded artifact
  - the rebuilt walk fails to terminate inside the depth cap, in which case the answer is a bound and not a count
  - every baseline cell still passes on kernel leaves, which would leave the caveat standing and the cell-count question empty
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - claim a kernel verdict without a Lean build
```
