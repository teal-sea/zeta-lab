# FAILURE_LEDGER — routes closed, and why

A route recorded here is closed for this campaign. Prior art counts as a
closure: a correct rediscovery is not an advance.

---

## RF-D001 — Solve the exact variational window for the xi' functional

**Killed 2026-08-17, before any work, as laboratory prior art.**

The August 2026 source paper's Remark 7.3 obtains its xi' constants
(0.85838 flat window, 0.86864 quartic window) from a hand-picked quartic
`v(s) = 1 - (7/100)(2s)^2 - (51/200)(2s)^4`, while for zeta itself the
optimal window solves an exact Euler-Lagrange ODE. That asymmetry is a
real optimization surface, and the territory survey ranked it the single
best candidate it found.

It is already solved, in this repository, by `hunts/wide_search/`:

    H*  = 0.86864150052976706411...   (simple and on the critical line)
    Hd* = 0.93432075026488353205...   (distinct)

with the maximiser strictly positive and global optimality established in
`hunts/wide_search/RESULTS-xiprime-global-optimality.md` (the functional is
a coercive quadratic form `A = I + T_{F_1}`, `c* = <1, A^{-1} 1>`). The
kernel is `F_1(x) = |x| - 4x^2 + sum_{k>=1} ((k-1)!/(2k)!)(2|x|)^{2k+1}`
from Farmer-Gonek (arXiv:0803.0425, Thm 1.1).

Two further consequences that hunt already recorded, and which this
campaign therefore may not claim: the paper's quartic window was within
1.5e-6 of sharp, and no admissible window reaches Wu's unconditional
0.86957 (short by 9.285e-4).

**Lesson applied:** the survey agents were given the laboratory's flagship
as prior art but not the contents of `hunts/wide_search/`. Reading the
tree's own hunts before scoring a portfolio is cheaper than reproducing
them. Subsequent candidate scoring in this campaign checks
`hunts/*/RESULTS*.md` and `HANDOFF.md` first.

---

## RF-D002 — Scalar-moment LP over window certificates (zeta's 0.6725)

**Not attempted; closed by two prior hunts.**

`hunts/wide_search/RESULTS-pair-ceiling.md` measured that if the datum
retained per window is only `(tr, ||.||_F^2)`, the joint feasible set is
the intersection of half-lines and collapses exactly to `sup_v H(v)`, so
that formulation cannot move 0.6725007037. `hunts/frontier_math/` then
found the same collapse at the pair-measure level. The remaining open half
is the configuration-level LP over marked periodic configurations, which
needs the source paper's `cert_N256_blk_b128m.json` artifact, not public.
