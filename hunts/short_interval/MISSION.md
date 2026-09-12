# Mission: the bandwidth dial was physical all along

**Opened 2026-09-12.** Nothing in this directory is a result. Nothing here
bears on RH (`docs/08-why-it-is-hard.md`).

Read `CLAUDE.md` and `ALIGNMENT.md` first. Then read §3, §4 and §5, which are
three findings established on the day the hunt opened, before any compute was
spent, and which between them killed the plan the hunt was opened for and
reordered everything else. The routes are §6 to §8, ranked.

```huntspec
id: short_interval
question: Wang's short-interval bound is the laboratory's own bandwidth landscape evaluated at lambda = theta. Given that, what does this tree hold on that axis that nobody else does, and what is the band edge worth?
frontier: the zeta landscape 2 - lambda/2 - (1/sqrt 2) cot(lambda/sqrt 2) is already computed in hunts/frontier_map/frontier.py from the source paper's eq. (7.4), agrees with Wang's c(theta) to 1e-16 and dies at 0.5501939647441547; the xi-prime landscape is computed on the same grid, sits 0.11 to 0.20 higher at every bandwidth, dies at 0.51332, and has no short-interval counterpart in the literature; the bandwidth-one configuration ceiling is 0.6818286874638 against a window optimum of 0.6725007036794116, and the bandwidth-theta ceiling is computed nowhere
proposed_attack: audit whether Wang's Theorem 2.2 supplies the arithmetic input the xi-prime functional consumes, since that is the one place the tree holds something the field does not; compute the bandwidth-theta configuration ceiling as the stopping criterion for everything else; and price the band edge rather than treating it as a wall
dead_routes:
  - substituting c(theta) into the affine bridges Phi_3 and Phi_4: the certificate's cost is proportional to the second moment, which diverges like 1/theta, so the gain is negative below theta 0.808 and no re-optimization repairs it; the bridges are also band-width-one and dyadic (section 4)
  - re-optimizing the certificate's window shape at each bandwidth: measured worth about lambda^3/180, and at the vacuity threshold the whole optimal-versus-flat advantage is 3.2e-4 (section 5)
  - deriving the closed form of the landscape as new work: it is the source paper's eq. (7.4), already in the tree, and independently Wang's Proposition 4.1
  - proving the landscape optimal at bandwidth theta: Wang's Proposition 4.1 already is that statement, since the Euler-Lagrange condition differentiates to f'' + 2f = 0 at every interval length
  - converting out-of-band POSITIVITY into an unconditional certificate: closed by hunt #118 on 2026-09-06; positivity is a lower bound on F and this method needs an upper one, so it is wrong-signed information
  - closing the cycle_moments quartic route on second and third moments alone: a matched finite fourth-moment bound is required and is not established
required_oracles:
  - the published statements of arXiv:2609.07918 and arXiv:2609.02882, read directly
  - Alpoge-Furman Remark 7.1's two published xi-prime figures, as the calibration for any F_1 landscape computed here
  - independent numerical solve of the window variational problem by a discretization not shared with the closed form it checks, with the zeta control run at the same settings so method error is visible
  - interval or ball arithmetic for any constant entering a claimed inequality
  - Lean 4 kernel with zero sorrys, for anything stated as a theorem
kill_conditions:
  - the xi-prime derivation's deterministic corrections turn out to have been established by a dyadic average that does not survive a T^theta block, and no route recovers them
  - the bandwidth-theta configuration ceiling collapses onto the landscape, leaving no room for any certificate
  - the n-point family rebuilt at bandwidth theta does not exceed the landscape anywhere in (0.5501939647441547, 1)
  - no unconditional constant upper bound on F beyond the band is reachable, closing section 8
agents_may:
  - search
  - derive
  - code
  - measure
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - edit zeta/, ontology/ or harness/
  - claim the reserved word
```

## 1. Why this hunt exists

Biao Wang (Yunnan University) posted arXiv:2609.07918 on 2026-09-07: zeros in
`(T, T + T^theta]` are simple and on the critical line in proportion at least
`c(theta)`, and distinct in proportion at least `d(theta) = (1 + c(theta))/2`,
unconditionally, for every fixed `0 < theta < 1`. The laboratory did not
notice for five days and then heard about it from a stranger's email. The
companion brief `meta/literature-monitor.md` covers that half.

Provenance, because this tree is in it: an internal research version of Claude
produced the original argument, Alpöge and Furman verified and published it
(arXiv:2608.13637), Lamzouri reproved it more simply (arXiv:2609.02882),
Wang extended it to short intervals. This tree's `Phi_3` and `Phi_4` are built
on `anthropics/zeta-23-lean`, which is arXiv:2608.13637.

## 2. What the papers prove

**Wang, Theorem 1.1.** Unconditional, fixed `0 < theta < 1`, on
`I = (T, T + T^theta]`:

    liminf N_0^s(I)/N(I) >= c(theta) = 2 - theta/2 - (1/sqrt 2) cot(theta/sqrt 2)
    liminf N^d(I)/N(I)   >= d(theta) = (1 + c(theta))/2

`c` strictly increasing with `c'(theta) = (1/2) cot^2(theta/sqrt 2)`, zero at
`theta_0 = 0.550193964744154`; `d` zero at `theta_d = 0.346658926139761`.
`theta = 1` is **not** in the stated range; the global constants are the
`theta -> 1^-` limits.

**Wang, Theorem 2.2**, the actual technical contribution. For fixed
`0 < lambda < theta < 1` and `g` real, even, `C_c^infinity`, `supp g` in
`[-lambda, lambda]`:

    sum_{gamma, gamma' in I} ghat(i(rho - rho')L/2pi) w(rho - rho')
        = (HL/2pi)(g(0) + integral |alpha| g(alpha) dalpha) + O_g(H + T^lambda L^2)

`w(z) = 4/(4 - z^2)`, `H = T^theta`, `L = log T`. Unconditional. The
counterpart of Lemma 5 of Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh (Acta Arith. 214 (2024), arXiv:2306.04799), built from
their Lemmas 1, 3 and 4. **The error is `o(HL)` precisely because
`lambda < theta`**, and the proof of Theorem 1.1 closes by letting
`lambda -> theta`. So the bandwidth available in a short interval of exponent
theta is theta, and the band is the open interval `(-theta, theta)`.

**Wang, Proposition 4.1.** Over real `f` in `L^2(J)` with `integral_J f = 1`,
`J = [-lambda/2, lambda/2]`, the functional
`C(f) = integral f^2 + double-integral |u - v| f f` has unique minimizer
`f_lambda(u) = cos(sqrt 2 u)/(sqrt 2 sin(lambda/sqrt 2))` and minimum
`C_lambda = lambda/2 + (1/sqrt 2) cot(lambda/sqrt 2)`, so `c = 2 - C_theta`.
Uniqueness by Dirichlet-Poincaré. The Euler-Lagrange condition is
`f(u) + integral_J |u - v| f(v) dv = const`, differentiating to
`f'' + 2f = 0`, **at every interval length**. That last clause matters: it
means Proposition 4.1 already is the bandwidth-theta optimality statement, so
the method class "Lamzouri's inequality plus in-band pair correlation" is
capped at `c(theta)` for every theta, and there is nothing to prove there.

**Lamzouri, Proposition 2.1.** For `Z` a finite conjugation-invariant
multiset and `K = Fourier(eta^2)` with `eta` real, even, supported in
`(-lambda, lambda)`, `K(0) = 1`: simple real elements at least
`2|Z| - sum K(z-s)^2`, distinct at least `(3/2)|Z| - (1/2) sum K(z-s)^2`.
**No positivity hypothesis on `K`** and, importantly for §8, **no cap on
`lambda`**. The cap lives entirely in the analytic input. The window density
is `f = eta^2` and is therefore nonnegative, which §8 depends on.

## 3. Finding one: Wang's curve is already in this tree

**Measured, agreement to 1e-16.** `hunts/frontier_map/frontier.py` computes
the unconditional proportion as a function of bandwidth, from the source
paper's eq. (7.4):

```python
def zeta_H_closed(lam):
    theta = lam / math.sqrt(2.0)
    t = math.tan(theta)
    c = math.sqrt(2.0) * t / (1.0 + theta * t)
    return 2.0 - 1.0 / c
```

Since `(1 + t tan t)/(sqrt 2 tan t) = (1/sqrt 2) cot(lambda/sqrt 2) + lambda/2`,
this **is** `c(lambda)`. It agrees with Wang at every bandwidth tested and
crosses zero at `0.5501939647441547`, his `theta_0` to every digit he prints.
The same module computes `Hd = (1 + H)/2`, his `d(theta)`. **Both constants in
Wang's Theorem 1.1 were already being computed here.**

**So what Wang adds is that the dial is physical.** `frontier.py` records
bandwidth as "exactly one dial, lambda, capped at 1 by the Rudnick-Sarnak /
Montgomery support restriction", and notes the source paper's remark that "the
certificate is empty for lambda <= 1/2". The tree held the low-bandwidth
regime as a hypothetical, because the whole game was pushing the dial up.
Theorem 2.2 says bandwidth theta is exactly what counting in an interval of
length `T^theta` buys. The lab's dial and Wang's exponent are the same number,
so the landscape's interior carries an unconditional theorem.

That is a reading of existing material, not a new result. State it that way.

## 4. Finding two: the transplant is dead, and the reason is the second moment

Substituting `c(theta)` for `H` in the two kernel-checked bridges fails, and
the sharp diagnosis is not the one an earlier draft of this file gave.

Rewrite `Phi_3` in the coordinate the problem is actually affine in,
`R = 2 - c`, which is the normalized second moment `C_theta`:

    R -> 1.001343 R - 0.002019

The certificate buys a fixed absolute `0.002019` and pays a **relative
0.134% of whatever second moment it consumes**. Since
`R(theta) = C_theta = 1/theta + theta/3 - theta^3/180 - ...` diverges like
`1/theta`, the proportional penalty grows without bound while the gain stays
fixed. Break-even is at `R = 1.5037`, that is `theta = 0.8082`. So the
overhead is intrinsic in the worst possible way: **it is proportional to the
one quantity that blows up in a short window.**

The cheapest kill, and the thing to do if anyone wants to revisit this:
locate the single step in the `Phi_3` derivation whose loss is a multiple of
the input rather than an additive constant. If it is a truncation tail bounded
by a fraction of the second moment, the transplant is dead at every
`theta < 0.81` and no re-optimization rescues it.

Independently, the transplant has no analytic footing at all, for two
reasons. **The band is `(-theta, theta)`, open and strict**, so a certificate
needing the band edge cannot take the endpoint even in a limit without care;
the bridges read `[-1, 1]`, and `hunts/family_wall/famlib.py` holds `H` as a
module constant with a kernel that is the closed form of
`integral_{-1/2}^{1/2} cos(sqrt 2 t) cos(2 pi x t) dt` with no free
half-length. **And the bridges are dyadic**: 21 occurrences of `2 * T` in
`Bridge/Main.lean` alone, with `S8` concluding in `N(T, 2T)`, `S9` absorbing
deleted end strips of width `2 pi L` against it, and `S15`'s span bound being
`LT/2pi = N(T,2T) + o(N(T,2T))`. A per-block error absorbed against
`N(T,2T)` and reappearing against `HL = T^theta log T` **carries a hidden
`T^(1-theta)`**. Check that before anything else on any route here.

## 5. Finding three: window shape is worth nothing in a short interval, so there is nothing to re-optimize

**Measured; `landscape.py` reproduces all of it.** Substituting
`v(u) = phi(u/lambda)` into the laboratory's functional gives

    R(lambda, phi) = A(phi)/lambda + lambda B(phi),
    A = integral phi^2/(integral phi)^2,
    B = double-integral |u-v| phi phi/(integral phi)^2

and `A >= 1` by Cauchy-Schwarz with equality iff `phi` is constant. So the
`1/lambda` cost is a pure L2-against-L1 defect of the window and the only way
to cheapen it is to be flat. The flat window gives `R = 1/lambda + lambda/3`
exactly, verified, whose threshold is the root of `theta^2 - 6 theta + 3`,
that is `3 - sqrt 6 = 0.5505102572`.

Against Wang's optimal-window `theta_0 = 0.5501939647`, **the entire value of
the Montgomery-Taylor window over a flat one is 3.2e-4 of threshold**, and the
flat-minus-optimal gap is about `lambda^3/180` (measured `0.00122` at
`lambda = 0.6` against `0.00120`; `0.00583` at `lambda = 1` against
`0.00556`). The optimal window flattens as the bandwidth shrinks.

Be precise about what that does and does not say. At full bandwidth the flat
window gives `2 - 4/3 = 0.6667` and the optimal one `0.6725`; that `0.0058` is
**exactly the Montgomery-Taylor improvement over Montgomery's two thirds**, so
at bandwidth one the window shape is the whole famous step. The point is that
its worth decays as bandwidth cubed, so it is the full-range game and not the
short-interval one.

Consequence, and it kills a recommendation an earlier draft of this file made:
at `theta = 0.55` the whole window-shape game is worth about `9e-4`, and an
n-point family whose bandwidth-one share of it is `2.4e-4` is worth roughly
`4e-5`. **There is nothing to re-optimize. Wang's `c(theta)` already is the
re-optimization.**

## 6. Route one: the xi-prime arm, unoccupied as far as was checked

**The best bet here, and the only place the tree holds something the field
does not.**

`hunts/frontier_map/frontier.py` computes the landscape for **two** kernels:
Montgomery's `F(x) = |x|` for zeta, and Farmer-Gonek-Lee's

    F_1(x) = |x| - 4x^2 + sum_{k>=1} ((k-1)!/(2k)!) (2|x|)^(2k+1)

for `xi'`, which is this tree's own line of work. **Wang does only zeta.** He
does not mention `xi'`, `F_1`, or Farmer-Gonek-Lee. **What was searched, per
the novelty rule in `CLAUDE.md`:** three papers. Farmer-Gonek-Lee (JLMS 2014)
is RH-conditional and full-range; Alpöge-Furman Remark 7.1 is unconditional
and dyadic; Wang is zeta only. Nothing beyond those three was searched, so
"unoccupied" means unoccupied in those three and in this tree, and the hunt
owes a real prior-art pass before any stronger word.

Measured in `landscape.py`, with the `F_1` implementation calibrated against
**two published figures** from Alpöge-Furman Remark 7.1 (flat window at
bandwidth 1 giving `0.858384` against their `0.85838`, and `0.929192` against
their `0.92919`), so a mis-transcribed series would have been caught:

| bandwidth | zeta | xi-prime | difference |
|---|---|---|---|
| 1.00 | +0.672513 | +0.868660 | +0.1961 |
| 0.80 | +0.486277 | +0.682554 | +0.1963 |
| 0.60 | +0.134562 | +0.281718 | +0.1472 |
| 0.55 | -0.000570 | +0.130262 | +0.1308 |
| 0.50 | -0.165957 | -0.052054 | +0.1139 |

**Vacuity thresholds: zeta `0.55019`, xi-prime `0.51332`.** So a
short-interval `xi'` statement would be non-vacuous in a range where Wang's is
not, and carries constants 0.11 to 0.20 higher throughout. The zeta control at
the same settings is off by `+1.2e-5` from a value known exactly, which is the
error bar on every `xi'` figure above. In particular the `xi'` solve's
`0.868660` against the laboratory's quartic-certificate `0.8686415005` is a
`+1.9e-5` gap that is **method error, not a free gain**; the control proves it.

**Does Wang's Theorem 2.2 supply the input?** The argued answer is yes and the
arithmetic is not the obstruction. `F_1` has exactly one arithmetic term, the
`|x|` that is Montgomery's; the `-4x^2` and the series carry no `Lambda(n)`
and are a deterministic transfer from zeta zeros to `xi'` zeros. Theorem 2.2
delivers that one arithmetic term on `supp g` in `(-lambda, lambda)` with
error `o(HL)`, and the `xi'` zero count in the same interval has the same
`HL/2pi` normalization, so the same `o(HL)` suffices.

**The audit that gates this, and it is the same hazard as §4.** The
deterministic corrections in the `xi'` derivation were established by a
**dyadic average**. Grep the `xi'` derivation for every division by
`N(T, 2T)` and every step that averages over `[T, 2T]`, and verify each
yields `o(HL)` with the block replaced by `T^theta`. That is where a
`T^(1-theta)` hides. Second and smaller risk: unconditionally there is no
Rolle interlacing between `xi` and `xi'` zeros, so any step pairing them needs
the source paper's index bookkeeping rather than RH.

**If that audit passes, that is the deliverable of this hunt.** If it fails,
the failure is a scope boundary on the whole `xi'` arm and worth writing down,
because the tree currently has no statement either way.

**Do not conflate the two constants both called `c*`.** The zeta one has
kernel `|alpha|`, `1/c*_1 = 1.3274992963205884`, and is Wang's. The `xi'` one
in `lean/ZetaLean/Pub1/Setting.lean` has kernel `F_1` and gives
`H* = 0.8686415005`. An earlier draft of this brief claimed
`PALOMAR-2026-08-21-000004` was the `lambda = 1` case of Wang's Proposition
4.1. It is not, and that claim is withdrawn here rather than quietly deleted.

## 7. Route two: the bandwidth-theta configuration ceiling, as a stopping criterion

The window class is capped at the landscape by Wang's Proposition 4.1 (§2).
That caps **windows**, not **certificates**: the bandwidth-one configuration
ceiling is `0.6818286874638` against a window optimum of `0.6725007036794116`,
a headroom of `0.00933` that no window reaches, and `Phi_3`, `Phi_4` and the
`0.675142509660254` family saturation all live inside it.

**The bandwidth-theta configuration ceiling is computed nowhere.** It is the
number that bounds this tree's entire remaining program on this axis, and
competitors' too. `Zeta23.PairCeiling.ceiling_law256` is the template and
`hunts/frontier_math/configuration_lp.py` is the machinery, whose band data
`R2hat(alpha) = delta(alpha) + |alpha|` on `[-1,1]` is exactly the object that
has to become `[-theta, theta]`.

Compute it **before** funding anything else in §7 or §9. A prediction offered
to be falsified: the ceiling headroom scales like `theta^3` the way the window
headroom does (§5), giving about `0.0015` at `theta = 0.55`. If that is right,
the short-interval n-point program is not worth funding, and establishing that
cheaply is the point of computing the ceiling first.

This is also the most valuable formalization target here. A theta-indexed
ceiling law is a **cap**, which is the kind of statement this laboratory is
unusually good at producing and nobody else is producing. Nothing in it should
be harder in Mathlib than what the source development already did.

## 8. Route three: the band edge has a finite price, and nobody has priced it

**Largest prize, lowest probability, and the one that is not a
short-interval question at all.** Recorded here because it fell out of
thinking about the bandwidth axis, and it should probably become its own hunt
or a GitHub issue rather than living in this one.

`hunts/outband_certificate/RESULTS.md` states the laboratory's reason for
bandwidth one: "`F` has no unconditional upper bound outside the band, so
bandwidth one is forced". **That names the missing input. It does not price
it.** Note also the direction, which hunts #110 and #118 got the other way
round: those priced out-of-band **positivity**, a lower bound, and positivity
is wrong-signed information for this method. What the method needs beyond the
band is an **upper** bound, because the out-of-band contribution enters as
`integral F(alpha) (f correlated with f)(alpha) dalpha` and the
autocorrelation of the nonnegative `f = eta^2` is nonnegative.

Priced in `landscape.py`, by minimizing
`integral f^2 + double-integral_{|u-v|<=1} |u-v| f f + B double-integral_{|u-v|>1} f f`
over `f` on `[-L/2, L/2]` with `integral f = 1`, and checking the minimizer's
sign, because a sign-changing minimizer is outside Lamzouri's class and its
value is not a bound:

| F <= B | L = 1.05 | L = 1.10 | L = 1.20 |
|---|---|---|---|
| 2 | 0.702950 | 0.726768 | 0.760859 |
| 3 | 0.701549 | 0.721863 | 0.746779 |
| 6 | 0.697810 | 0.710023 | 0.718168 |
| 20 | 0.686561 | sign-changing | sign-changing |

Baseline `0.672508` at this discretization. **Every admissible cell with
`B <= 6` exceeds the entire bandwidth-one ceiling headroom of `0.00933`**, and
`B = 20` on a sliver of width `0.05` still gains `0.0142`, which is about
sixty times the `Phi_3` gain. The mechanism is that the shadow price of
bandwidth is linear, in closed form
`c'(1) = (1/2) cot^2(1/sqrt 2) = (3/2 - H)^2 = 0.6847550854111`, while the
out-of-band autocorrelation mass of a stretched window is quadratically
small, so the optimal extension is strictly positive for **any** finite `B`.

**So the required input is not the pair correlation conjecture beyond the
band. It is an unconditional `integral_1^(1+delta) F(alpha) dalpha <= B delta`
for some finite `B` and some `delta > 0`.**

**What is not established, and it is the whole question.** Positive
definiteness gives only `F(alpha) <= F(0)`, which grows like `log T` and is
therefore not a constant. So the trivial route does not supply an admissible
`B`, and an averaged unconditional statement about `F` beyond the band is
genuinely hard: if it were easy it would have been done in the 1980s. The
cheapest kill, in order: read the Fourier-optimization and "three integrals"
literature (arXiv:2502.05106 and arXiv:2108.09258) for any unconditional upper
bound on averages of `F` beyond 1; then check whether the nonzero prime-pair
terms enter Montgomery's identity with a controllable sign for
`1 < alpha < 1 + delta`. If both fail, the door is shut and the reason is
publishable as a scope caveat, which is an acceptable outcome.

## 9. Leads

- **Higher trace moments are near-dead, with one live corner.** The
  Rudnick-Sarnak support condition means the k-th moment needs bandwidth
  `lambda <= 2/k`, so the band cost `1/lambda = k/2` is linear in `k` while
  the payoff is bounded, and `k = 2` stays optimal. The live corner: **below
  `theta_0` the `k = 2` bound is vacuous, so any positive certificate wins by
  default**, and `hunts/cycle_moments`'s quartic family is the tool, with its
  blocker (a normalized fourth-moment bound) unconditionally available at
  bandwidth below 1/2 by Rudnick-Sarnak. Cheapest test: evaluate the quartic
  certificate at bandwidth `theta/2` for `theta` in `(0.45, 0.55)` and ask
  only whether it is positive. Low expectation. Note it competes with §6 for
  the same headline and loses, since `xi'` reaches `0.5133` with machinery
  that already exists.
- **Two unread unconditional moment-bound papers** that may bear on
  `cycle_moments`'s blocker: arXiv:2609.11619 (Hagen) and arXiv:2609.01101
  (Durkan, Karak, Mahatab). Shape unchecked.
- **The distinct-zero track.** The lab computes `Hd = (1 + H)/2` and has never
  chased it. Lamzouri's Proposition 2.1 gives both bounds from the same kernel
  sum via *different* elementary inequalities, so the distinct constant is not
  a corollary of the simple one.
- **`T^theta` already appears in the tree, unrun.**
  `hunts/rogue_frontier/IDEA_PORTFOLIO.md` carries "rigorize the hybrid
  q-aspect Theorem E: `q <= T^vartheta` with proportion `H(1/(1+vartheta))`",
  flagged by the source as unchecked. Same landscape, second physical axis.
  The narrow-box `b` curve in `FRONTIER_MAP.md` is a third.
- **Wang's Theorem 2.2 is reusable beyond this hunt.** Anything here that
  consumes full-range pair correlation now has a short-interval counterpart.
- **Lamzouri is at v2; the tree cites v1.** Check what changed.
- **Read `github.com/AxiomMath/ZetaZeros` before writing any Lean.**
  Lamzouri's Appendix A records that AxiomProver produced a formal certificate
  for his Proposition 2.1 unconditionally, and for his Theorem 1.1 modulo
  BGST's Lemma 5 and Riemann-von Mangoldt. A second verification venue
  alongside Palomar, possibly already holding what a formalization here would
  build.

## 10. Closed. Do not re-enter.

**Out-of-band positivity.** Hunt #118 closed it on 2026-09-06: worth zero to
any certificate whose positivity input is Weil's Hermitian form, which is
every unconditional one, and what hunt #110 priced was the RH-conditional
pointwise class. The closure rests on a proved edge lemma, that a real even
spectral profile's autocorrelation is strictly positive just inside its
support edge, so it can never be nonpositive on the strip; false for odd
factors, giving a dichotomy where an even factor is Gram-able and strip-blind
and an odd factor is strip-capable and never a Gram kernel. §8 above is the
**upper-bound** question, which is a different object and is open; do not let
the two blur.

The measured `+0.0068` is best read as the price of removing RH rather than as
an unclaimed gain: under RH one drops off-diagonal terms using pointwise
`W >= 0`, which is compatible with a sign-indefinite transform.

`docs/35` predates the closure and reads as an open opportunity. See §11.

## 11. Corrections this hunt owes the tree

Small, real, none of them this hunt's mathematics:

1. **`docs/35` is stale.** It is hunt #110's front door and does not record
   hunt #118's closure. Add it.
2. **`docs/35` and `hunts/outband_intake/RESULTS.md` disagree numerically.**
   The doc says `+0.0068` with method error `2.2e-3`; the hunt and case log
   say `+0.0065` with `1.8e-3`. Find out which is right.
3. **`references/papers.md` has no entry for Baluyot, Goldston, Suriajaya and
   Turnage-Butterbaugh at all.** Not arXiv:2306.04799, whose Lemma 5 is the
   arithmetic engine of this entire line of work, and not arXiv:2501.14545.
   Add both, plus Lamzouri and Wang, in the file's annotated format.
4. **`hunts/frontier_map/RESULTS-frontier-map.md` should record that its
   landscape now has a theorem attached at each bandwidth**, citing Wang. One
   paragraph, not a new claim.

## 12. Scope

May: build instruments under `hunts/short_interval/`, record measurements
here, read anything in the tree, make the four corrections in §11, write one
new `docs/NN-*.md` with the number from `scripts/science_preflight.py` and the
heading in the enforced form `# NN. Title`, and open GitHub issues for
observations it is not chasing (§8 is the first candidate).

May not: edit `zeta/`, `ontology/` or `harness/`; write a verdict into
`README.md`, `ROADMAP.md` or `HANDOFF.md`; use the reserved word; claim
novelty; or assign its own claims a status. Use *measured*, *observed*,
*derived*, *consistent with*.

Per `CONTRIBUTING.md` and `scripts/71_contribution_check.py`: `MISSION.md`
with a valid `huntspec`, `RUNS.md` with at least one `runmanifest` including
runs that produced nothing, `RESULTS.md` stating the bounded outcome, a
case-log entry naming the directory in `hunts/README.md`, and a numerical test
or explicit hedge for every quantitative claim.

Compute goes to GitHub Actions, never to the operator's machines, with an
estimate in `RUNS.md` before launching and a checkpoint per unit above twenty
minutes. `CLAUDE.md`'s compute discipline was written after a day that cost
roughly a third of a month's budget and crashed the operator's laptop
repeatedly. It is not advisory.

## 13. The doors

Preliminary: this hunt has measured no ceiling of its own yet, so the
inventory is what §3 to §8 expose. Whoever runs §7 replaces this with the
measured version, ranked by shadow price.

**Active constraint.** One: **bandwidth**. Its shadow price is known in closed
form, `(3/2 - H)^2 = 0.6847550854111` per unit at bandwidth 1, and §3 is the
news that it is a physical parameter rather than a free dial. Its door is §8.

**Frozen-constant inventory**, with what relaxing each trades against.

1. **The band edge at 1.** Frozen by the absence of an unconditional upper
   bound on `F` beyond it, not by choice. Priced in §8: worth more than
   everything else here combined, at a probability the brief states honestly.
   Genuine trade shape: it spends an out-of-band bound of any finite quality
   to buy linear band width.
2. **The kernel.** The zeta arm is fixed to `F(alpha) = |alpha|`. The tree also
   computes the `F_1` landscape and Wang does not, so this is the frozen choice
   where the tree holds something the field does not. §6. Changes the
   information class.
3. **The dyadic counting range.** Frozen in the Lean bridge by what was
   available to formalize. Relaxing costs the re-derivation of `S8`, `S9` and
   `S15` against a `T^theta` denominator, and §4 and §6 both say that is where
   a hidden `T^(1-theta)` would be found. Same information class.
4. **The window shape.** Measured in §5 to be worth about `lambda^3/180`, and
   `3.2e-4` at the threshold. **This door is closed by measurement**, and it is
   listed so nobody opens it again.
5. **The window's single frequency `sqrt 2`.** `hunts/amtopa_ceiling`
   established that the `2 j pi` harmonics are exactly M-orthogonal to the
   `sqrt 2` term at bandwidth one, so the window maximum over the whole
   coefficient space is the pure `sqrt 2` value. Whether that orthogonality
   survives at bandwidth theta is unchecked and cheap to check, though §5
   bounds the prize.

**Information class.** Doors 1 and 2 leave the class; 3, 4 and 5 stay inside
it and are therefore under the configuration ceiling, which is itself a
bandwidth-one number and unmeasured at bandwidth theta. That measurement is
§7 and it is the stopping criterion for the whole axis.
