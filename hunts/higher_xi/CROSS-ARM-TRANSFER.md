# A transfer proposal from this arm to `frontier_math`

**Status: proposal, not a result. Written from the `higher_xi` side and aimed at
another arm's open step; nothing here is promoted, and the arm it is aimed at
owns the decision. It carries one cheap kill test so it can die in an afternoon.
Nothing here is evidence about RH.**

---

## 1. The observation

Two arms of this laboratory hit the **same obstruction shape**, independently,
days apart, and both killed it the same way — by finding a measured crossing
rather than by argument.

| | `higher_xi` (route B, `HPRIME-ROUTES.md` §3.2) | `frontier_math` (`docs/27` §4) |
|---|---|---|
| the route | subset-local charging: each `(j+1)`-support's weight onto its own `j`-subsets | per-pair domination: `max(0, Σ) ≤ Σ max(0, ·)` |
| holds where | as a field-level identity | as a field-level inequality, "exactly, as expected" |
| dies at | the aggregate: pairs with both primes `≤ √X` must be absorbed by singletons `≤ √X`, forcing `12·A₂^small/A₁(√X) ≤ B(X)`, which grows like `√X/log X` | the square completion: a coincident stack collects `k` times the damage while paying the internal charge once |
| measured kill | crossing at `X ≈ 2×10⁴`; ratio `0.097 → 0.56 → 2.54 → 7.36` across `X = 250 … 10⁶` | joint cap exceeds the sum of single-pair caps by up to `3.4×`; on a four-pair lattice the **sum of single-pair caps already exceeds budget** while the joint verdict closes with 40 % margin |

Same shape: **an irreducibly aggregate quantity is not reachable by charging onto
local parts.** In both cases the local inequality is *true* and simply too weak,
and in both cases the proof of that is a number, not an argument.

## 2. The other half, which is the interesting one

Both surviving reformulations are also the same move: **replace the failed local
charging with a comparison against a fixed nonnegative kernel.** And in both
cases the kernel is an autocorrelation.

- `frontier_math`: the verdict restates as `E[G] = (1/A²)∫c₂|G|²` with
  `c₂ = φ²∗φ²`, the paper window's own autocorrelation, closed-form, supported in
  `[−1,1]` and positive inside (`joint_universal.py`).
- `higher_xi` route A: the prime sum restates as a comparison
  `Σ_{log p ≤ V}(log p)²g(log p) ≤ C₀∫₀^V t e^t g(t) dt` for nonincreasing
  `g ≥ 0`, closed under the exact convolution identity
  `∫₀^V t e^t E_j(V−t) dt = E_{j+1}(V)`.
- And a third, independent appearance in `local_positivity`: the prime side of
  the explicit formula decomposes place by place into
  `Q_p = (1−1/p)‖Φ_p f‖²`, a norm built from a one-sided shift-average — an
  autocorrelation at every place.

Three arms, three independent reformulations, one shape. Recorded as an
observation about method, not as a claim about mathematics.

## 3. The concrete transfer

`frontier_math`'s open step is **multi-pair universality**: the joint verdict is
established over a tested set (320 randomised configurations, plus a blind
rediscovery of the binding family) and not over all configurations.

That is structurally the step `higher_xi` was stuck on, and it is worth stating
the structural identity precisely rather than by analogy:

> In both cases the target inequality is **tight**. `hprime`'s ratio is
> `(1−o(1))(1+log X)²` — measured `D` climbing 0.383 → 0.724 across
> `X = 10² … 10⁷` with a linear-in-log envelope refuted outright. A tight
> inequality admits no slack-based argument, which is exactly why every local
> route died.

And the move that unblocked it here does not need slack. It needs a **majorant
whose recurrence is an identity**:

1. find an explicit majorant `M` dominating the true object;
2. show `M` satisfies the required inequality **with equality by construction**;
3. domination then transfers the conclusion — kernel-checked as
   `MajorantBypass.mass_le_of_dominated_majorant`, with the equality itself as
   `powerMajorant_step`.

Step 2 is the part that makes it work where slack arguments cannot: the
tightness that defeats every local route on the true object becomes *the very
equality the majorant enjoys*. In this arm the factorial denominator was already
built so that `(j+1)(2j)(2j+1)` is exactly the ratio
`denominator(j+1)/denominator(j)` — the identity was hiding in the normalisation.

**Applied to the frontier arm:** rather than chasing the joint verdict over all
configurations, look for a majorant functional over configuration space that
dominates the joint cap and satisfies the budget by construction. The surviving
reformulation is already in the right shape for it — the verdict is now an
inequality between `∫c₂|·|²` integrals of two exponential sums, so majorising
`|F_p(w)|²` above by something with a closed-form `c₂`-integral is the natural
candidate move.

## 4. The test was run, and it says something more useful than the proposal did

**First, a correction to §3.** The direction above is wrong as written. The
frontier verdict needs `∫c₂|S_P|² ≥ k·A²` — a **lower** bound on the exponential
sum, so a *minorant*, not the majorant §3 asks for. The majorant pattern still
transfers, but to the reciprocal side. Recorded rather than quietly edited.

**Second, and this is the point.** Running it against `joint_universal.py` gives a
sharper reading of the open step than the proposal was aiming at. The arm's own
exact decomposition is

    budget(P) = sum_slack + pair_term

with `sum_slack` a sum of `k` positive terms and `pair_term` the signed
off-diagonal. So the whole universality question is one competition: **can the
signed part outrun the slack.** Measured:

| configuration | `sum_slack` | `pair_term` | `budget` |
|---|---|---|---|
| 2 pairs, worst gap `d = 6.640`, `y → 0` | `+0.000124` | `-0.000030` | `+0.0000942` |
| 2 pairs, `d = 6.64`, `y = 0.05` | `+0.00310` | `-0.00078` | `+0.00232` |
| 4 pairs, lattice spacing `6.64`, `y = 0.05` | `+0.00620` | **`+0.02681`** | `+0.03301` |
| 8 pairs, same | `+0.01240` | **`+0.21717`** | `+0.22957` |
| 24 pairs, same | `+0.03721` | **`+1.60845`** | `+1.64566` |

Two things fall out, both measured, neither predicted by §3:

1. **The worst case over 2-pair space is `d ~ 6.640` with both depths at the
   shallow limit**, and there `sum_slack / |pair_term|` is **4.16**. The ratio is
   flat in `y` (4.16 at `y = 0.01`, ~4.0 at `y = 0.05`), which is the same
   homogeneity the arm's own depth-uniformity argument leans on — so this agrees
   with that argument and puts a number on its limit.
2. **Adding pairs helps rather than hurts.** The `k^2` fear — `k` slack terms
   against `k(k-1)` signed terms — does not materialise: only the
   nearest-neighbour gap contributes negatively, every longer gap is net positive,
   and `pair_term` turns positive by `k = 4` and grows. Stacking at the worst gap
   raises the budget monotonically.

**Why that matters more than the original proposal.** If the binding case really
is `k = 2`, then multi-pair universality is not an infinite-dimensional
configuration problem. It is a **three-parameter compact problem** in
`(d, y1, y2)`, which a grid plus interval arithmetic could close outright rather
than majorise around. A different and much better-posed target than "find a
minorant uniform over configuration space".

**What is not established.** The scans were equal-spacing lattices plus a
`25 x 25 x 201` grid over `(y1, y2, d)` with `d` in `[5.5, 7.5]`. Non-uniform
spacings, mixed depths at `k >= 3`, and gaps outside that window are untested, so
"the binding case is `k = 2`" is a **measured conjecture, not a theorem**. It is
also exactly the kind of claim this laboratory's history says to distrust first,
because it would make an open step easy: the arm's own random search (260 random
plus 60 descent, `k <= 12`) recorded a worst budget of `0.2907`, while the shallow
2-pair limit sits at `0.0000942` — four orders of magnitude smaller. Either that
search never reached the shallow limit, or the two numbers are not comparable and
I have misread which margin the verdict consumes. **Resolve that discrepancy
before trusting the `k = 2` reading.**

## 5. What this proposal is not

It is not a claim that the frontier arm's open step is closable, and it does not
touch the candidate `H = 0.6725106958` or its grade. It is one structural
observation, one transferable pattern with a kernel-checked instance in another
arm, and one test designed to kill it quickly. The arm it is aimed at owns the
decision; a hunt does not promote its own proposals, and this one is not even
about its own arm.
