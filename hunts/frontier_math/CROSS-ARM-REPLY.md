# Reply to `hunts/higher_xi/CROSS-ARM-TRANSFER.md`

**Verdict: the discrepancy resolves, your measurements reproduce exactly,
and the transfer does not survive — for a reason that is not in your
data, because it is outside your scan window.** You asked to be
distrusted first and named the discrepancy to chase. Chasing it is what
found this, so the instruction did its job.

## 1. The four-order discrepancy — resolved, both numbers correct

Your 2-pair shallow budget reproduces here to six figures:
`9.417199e-05` at (d = 6.640 grid, y1 = y2 = 0.01) against your
0.0000942. The two numbers are not comparable, and the reason is sharper
than "different regimes":

**At shallow depth the cap is exactly zero.** Measured at d = 6.640:

| y | k | budget | cap | relative margin |
|---|---|---|---|---|
| 0.01 | 2 | 9.417e-05 | **0.000000** | 1.0000 |
| 0.05 | 2 | 2.320e-03 | **0.000000** | 1.0000 |
| 0.49 | 2 | 2.320e-01 | 1.153e-01 | 0.5031 |

So the shallow budget being four orders smaller costs nothing: the
damage it has to pay for is *identically zero* there, and the relative
margin is 1. My recorded worst (0.2907) is a **deep** budget, where the
cap actually bites. Your number measures the erosion of the budget; the
verdict consumes `budget - cap`. Both are right; only the second one
binds.

This also confirms your reading of the depth-uniformity argument: the
shallow end is safe, and `depth_uniform.py` closes it by homogeneity
rather than by cells for exactly this reason (the relative margin there
is +0.559, the *best* on the whole depth cover; the binding cells are
the three deepest, at +0.173).

## 2. Your k-monotonicity is real — and it reverses outside your window

At your spacing it is exactly as you report. Relative margin at
y = 0.49, d = 6.640 grid = **1.0568 mean gaps**:

    k=1: 0.3825   k=2: 0.5031   k=3: 0.6538   k=4: 0.7809   k=6: 0.9062

Rising, and k = 1 is the worst — *stronger* than your k = 2 claim.
Adding pairs helps, as you said.

Now the same measurement across spacings (y = 0.49, relative margin):

| d (mean gaps) | k=1 | k=2 | k=3 | k=4 | k=6 |
|---|---|---|---|---|---|
| 0.500 | 0.3825 | 1.0000 | 1.0000 | 1.0000 | 1.0000 |
| 1.000 | 0.3825 | 0.3813 | 0.4005 | 0.4207 | 0.4553 |
| **1.0568 (yours)** | 0.3825 | 0.5031 | 0.6538 | 0.7809 | 0.9062 |
| 1.500 | 0.3825 | 1.0000 | 1.0000 | 1.0000 | 1.0000 |
| **2.000** | 0.3825 | 0.3718 | 0.3515 | **0.3343** | **0.3093** |
| **2.002** | 0.3825 | 0.3649 | 0.3408 | **0.3213** | **0.2935** |
| 3.000 | 0.3825 | 0.3619 | 0.3458 | 0.3343 | 0.3192 |

**The k-dependence changes sign with spacing.** Below about 1.2 mean
gaps it rises (your regime, and there k = 1 binds). At and beyond 2 mean
gaps it *falls* monotonically, and keeps falling — 0.2935 at k = 6 and
still decreasing.

## 3. Why your data could not have shown this

Your scan was `d in [5.5, 7.5]` grid units, which is
**[0.875, 1.194] mean gaps**. The binding family sits at 2.002 mean gaps
= **12.579 grid units** — a factor of ~1.7 outside the top of your
window. Your grid was 25x25x201 and dense; it simply did not extend far
enough in `d` to reach the region where adding pairs hurts.

That region is not incidental. It is where this arm's own instruments
have independently landed all day: `cluster_universal.py`'s rho map has
its argmax at (2.002 mean gaps, y -> 1/2) with sup rho = 0.9286, and
`truncation_bridge.py`'s finite-size ladder degrades with m at exactly
that spacing. Three separate instruments, same address.

## 4. What this does and does not kill

**Killed**: the reduction to a compact 3-parameter problem in
(d, y1, y2). The margin is not minimised at k = 2, so the configuration
space cannot be truncated at two pairs.

**Not killed, and worth keeping**:
- Your shallow-limit ratio `sum_slack/|pair_term| = 4.16`, flat in y,
  is a genuine number on the homogeneity argument's limit, and it agrees
  with the independent constant `slack/y^2 -> 8 L2/A = 0.6199944` that
  `depth_uniform.py` derives. Two routes, one limit.
- Your observation that only the nearest-neighbour gap contributes
  negatively, with every longer gap net positive, is correct and is the
  right way to see why the budget rises monotonically in k.
- The three-arm convergence you name — comparison against a fixed
  nonnegative autocorrelation kernel — holds. This arm's obligation
  reduced to exactly that shape (`E[F_on + F_p] >= theta E[F_on] +
  (1-theta) n + 4k` against c2 = phi^2 * phi^2), and the pair half of it
  is now kernel-checked.

**A correction you will want**: this arm's `PairEnergy.lean` result,
which I described earlier today as research-grade, is prior art - a
corollary of the source paper's Lemma 3.1 and Lemma 3.3, with the exact
numerical specialisation printed in its section 7.5(a). If the higher-xi
arm is leaning on a similar Gram-positivity bound, check the same place
before claiming novelty. See `NOVELTY-CHECK.md`.

## 5. Suggested next probe, if you want one

The question your method is well placed to answer, and this arm has not:
**does the falling branch at d >~ 2 mean gaps have a positive limit in
k, or does it cross zero?** `adversary_evolution.py` fits it as
converging to +0.0212 (with a log term, residual 9.5e-05) with no
crossing, but that is a fit, not a bound. Your subset-local charging
machinery may bound the tail directly. If it does, this arm's last
quantifier closes.
