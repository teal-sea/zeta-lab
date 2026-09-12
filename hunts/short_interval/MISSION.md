# Mission: the bandwidth dial was physical all along

**Opened 2026-09-12.** Nothing in this directory is a result. Nothing here
bears on RH (`docs/08-why-it-is-hard.md`).

Read `CLAUDE.md` and `ALIGNMENT.md` first. Then read §3, which is the finding
that sets the hunt's question, and §4, which kills the plan the hunt was
opened for. Both were established before any compute was spent.

```huntspec
id: short_interval
question: Wang's short-interval bound is the laboratory's own bandwidth landscape H(lambda) evaluated at lambda = theta. What does this tree hold on that landscape that Wang does not, and what would the n-point family cost to rebuild at bandwidth below one?
frontier: the zeta landscape H(lambda) = 2 - lambda/2 - (1/sqrt 2) cot(lambda/sqrt 2) is already computed in hunts/frontier_map/frontier.py from the source paper's eq. (7.4), agreeing with Wang's c(theta) to 1e-16 and crossing zero at 0.5501939647441547; lab's kernel-checked full-bandwidth bounds Phi_3 = 0.6727373345 and Phi_4 = 0.6728470197 exist only at lambda = 1 and only on the dyadic range (T, 2T]; the xi-prime landscape is computed on the same grid and has no short-interval counterpart anywhere
proposed_attack: treat lambda as the physical short-interval exponent that Wang's Theorem 2.2 shows it to be, then ask what the tree already computes on that axis, starting with the Farmer-Gonek-Lee xi-prime curve which Wang does not touch
dead_routes:
  - substituting c(theta) into the affine bridges Phi_3 and Phi_4: the bridges are band-width-one and dyadic, with (T, 2T] baked into S8, S9 and S15, and their fixed overhead does not shrink with the input (section 4)
  - deriving the closed form of the landscape as new work: it is the source paper's eq. (7.4), already in hunts/frontier_map/frontier.py, and independently Wang's Proposition 4.1 (4.2)
  - converting out-of-band positivity into an unconditional certificate: closed by hunt #118 on 2026-09-06 by a proved edge lemma
  - closing the cycle_moments quartic route on second and third moments alone: a matched finite fourth-moment bound is required and is not established
required_oracles:
  - the published statements of arXiv:2609.07918 and arXiv:2609.02882, read directly
  - independent numerical solve of the window variational problem by a discretization not shared with the closed form it checks
  - the existing xiprime.optimise landscape as a second route to any curve value claimed here
  - interval or ball arithmetic for any constant entering a claimed inequality
  - Lean 4 kernel with zero sorrys, for anything stated as a theorem
kill_conditions:
  - Wang's Theorem 2.2 does not supply the pair-correlation input the xi-prime functional consumes, so the xi-prime curve has no short-interval reading
  - the xi-prime short-interval curve is nonpositive across the whole range where the zeta one is positive
  - the n-point family rebuilt at bandwidth theta does not exceed the landscape value anywhere in (0.5501939647441547, 1)
  - Carneiro-Chandee-Littmann-Milinovich Corollary 14 generalizes to bandwidth theta and proves the landscape value already optimal for the whole method class
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

Biao Wang (Yunnan University) posted arXiv:2609.07918 on 2026-09-07: zeros
counted in `(T, T + T^theta]` are simple and on the critical line in
proportion at least `c(theta)`, and distinct in proportion at least
`d(theta) = (1 + c(theta))/2`, unconditionally, for every fixed
`0 < theta < 1`. The laboratory did not notice for five days and then heard
about it from a stranger's email. The companion brief
`meta/literature-monitor.md` covers that half.

Provenance of the chain, because this tree is in it: an internal research
version of Claude produced the original argument, Alpöge and Furman verified
and published it (arXiv:2608.13637), Lamzouri reproved it more simply
(arXiv:2609.02882, 2026-09-02), Wang extended it to short intervals
(2026-09-07, crediting ChatGPT-6 Astra for implementing the proof ideas).
This tree's `Phi_3` and `Phi_4` are built on `anthropics/zeta-23-lean`, which
is arXiv:2608.13637.

## 2. What the papers prove

**Wang, Theorem 1.1.** Unconditional, for fixed `0 < theta < 1`, on
`I = (T, T + T^theta]`:

    liminf N_0^s(I)/N(I) >= c(theta) = 2 - theta/2 - (1/sqrt 2) cot(theta/sqrt 2)
    liminf N^d(I)/N(I)   >= d(theta) = (1 + c(theta))/2

`c` is strictly increasing with `c'(theta) = (1/2) cot^2(theta/sqrt 2)`;
`c` vanishes at `theta_0 = 0.550193964744154` and `d` at
`theta_d = 0.346658926139761`. Note `theta = 1` is **not** in the stated
range: the global constants are the `theta -> 1^-` limits.

**Wang, Theorem 2.2**, his actual technical contribution and the thing this
tree should care about. For fixed `0 < lambda < theta < 1` and `g` real, even,
`C_c^infinity` with `supp g` in `[-lambda, lambda]`:

    sum_{gamma, gamma' in I} ghat(i(rho - rho')L/2pi) w(rho - rho')
        = (HL/2pi)(g(0) + integral |alpha| g(alpha) dalpha)
          + O_g(H + T^lambda L^2)

with `w(z) = 4/(4 - z^2)`, `H = T^theta`, `L = log T`. Unconditional; no RH,
no zero-density hypothesis, no narrow-strip hypothesis. It is the
short-interval counterpart of Lemma 5 of Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh (Acta Arith. 214 (2024), arXiv:2306.04799), built from
their Lemmas 1, 3 and 4.

**The error term is `o(HL)` precisely because `lambda < theta`**, and the
proof of Theorem 1.1 closes by letting `lambda -> theta`. So the available
bandwidth in a short interval of exponent theta is theta.

**Wang, Proposition 4.1.** Over real `f` in `L^2(J)` with `integral_J f = 1`,
`J = [-lambda/2, lambda/2]`, the functional
`C(f) = integral f^2 + double-integral |u - v| f(u) f(v)` has unique minimizer
`f_lambda(u) = cos(sqrt 2 u)/(sqrt 2 sin(lambda/sqrt 2))` and minimum
`C_lambda = lambda/2 + (1/sqrt 2) cot(lambda/sqrt 2)`, so `c = 2 - C_theta`
and `d = 3/2 - C_theta/2`. Uniqueness is by Dirichlet-Poincaré. The
Euler-Lagrange condition is `f(u) + integral_J |u - v| f(v) dv = const`,
differentiated form `f'' + 2f = 0`, which is where every `sqrt 2` and `cot`
in the whole subject comes from.

**Lamzouri, Proposition 2.1**, the multiset inequality Wang imports
wholesale. For `Z` a finite conjugation-invariant multiset and
`K = Fourier(eta^2)` with `eta` real, even, supported in `(-lambda, lambda)`,
`K(0) = 1`: simple real elements at least `2|Z| - sum K(z-s)^2`, distinct
elements at least `(3/2)|Z| - (1/2) sum K(z-s)^2`. **No positivity hypothesis
on `K`**, which is the paper's stated innovation, replacing the Alpöge-Furman
matrix and rank-trace apparatus with Bessel plus two scalar inequalities.
`hunts/cycle_moments` generalizes exactly this.

**Lamzouri, Remark 3.4.** By Carneiro, Chandee, Littmann and Milinovich
(J. Reine Angew. Math. 725 (2017), Corollary 14), `C_MT` is **optimal for
Lamzouri's method**. Wang makes no corresponding claim for `C_lambda`.

## 3. The finding: Wang's curve is already in this tree

**Status: verified numerically to 1e-16. This is what the hunt is built on.**

`hunts/frontier_map/frontier.py` computes the unconditional critical-line
proportion as a function of bandwidth, from the source paper's eq. (7.4):

```python
def zeta_H_closed(lam):
    theta = lam / math.sqrt(2.0)
    t = math.tan(theta)
    c = math.sqrt(2.0) * t / (1.0 + theta * t)
    return 2.0 - 1.0 / c
```

Since `(1 + theta tan theta)/(sqrt 2 tan theta) = (1/sqrt 2) cot(lambda/sqrt 2) + lambda/2`,
this function **is** `c(lambda)`. Measured:

| lambda | `frontier.py` | Wang `c(theta)` | difference |
|---|---|---|---|
| 0.5000 | -0.165963850364986 | -0.165963850364986 | 2.2e-16 |
| 0.6000 | 0.134554281905059 | 0.134554281905059 | 2.2e-16 |
| 0.7500 | 0.419075012975424 | 0.419075012975424 | 0 |
| 1.0000 | 0.672500703679412 | 0.672500703679412 | 1.1e-16 |

The lab's curve crosses zero at `0.5501939647441547`, which is Wang's
`theta_0` to every digit he prints. The same module computes the distinct
companion as `Hd = (1 + H)/2`, which is Wang's `d(theta)`. **Both constants
in Wang's Theorem 1.1 were already being computed in this tree.**

**So what does Wang actually add?** `frontier.py` records bandwidth as
"exactly one dial, lambda, capped at 1 by the Rudnick-Sarnak / Montgomery
support restriction", and notes the source paper's observation that "the
certificate is empty for lambda <= 1/2". The tree therefore held the landscape
as a hypothetical: a curve describing what the method would give at bandwidths
it had no reason to want, since the whole game was to push lambda up to its
cap.

Wang's Theorem 2.2 says the low-bandwidth regime is **physical**. Bandwidth
theta is exactly what is unconditionally available when you count in an
interval of length `T^theta`, and the landscape's value there is an
unconditional theorem rather than a hypothetical. The lab's dial and Wang's
interval exponent are the same number.

That is the whole content of the identification, and it is a reading of
existing material rather than a new result. State it that way. What follows is
what it makes worth doing.

## 4. The plan this hunt was opened for is dead, twice over

The obvious move is to substitute `c(theta)` for `H` in the lab's two
kernel-checked bridges. It fails for two independent reasons, either
sufficient.

**Reason one: the bridges are bandwidth-one objects.** `Phi_3` and `Phi_4`
consume pair-correlation data on `alpha` in `[-1, 1]`, the cap being the
Rudnick-Sarnak / Montgomery support restriction. At bandwidth theta that band
does not exist. `hunts/family_wall/famlib.py` makes this concrete: `H` is a
module constant, and its kernel `Kraw` is the closed form of
`integral_{-1/2}^{1/2} cos(sqrt 2 t) cos(2 pi x t) dt` at the single frequency
`sqrt 2`, with **no free half-length anywhere**. Same in
`hunts/amtopa_ceiling/family.py`, where every `/2` is the integration limit
evaluated in closed form.

**Reason two: the bridges are dyadic.** The counting definitions take two
endpoints, but every theorem instantiates them at `(T, 2T]`, with 21
occurrences of `2 * T` in `Bridge/Main.lean` alone, and three analytic steps
depend on it. `S9` deletes end strips of width `2 pi L` holding at most
`1600 A_0 L^2` zeros and absorbs them against `N(T, 2T) >= TL/2pi - |C| log T`.
`S15`'s span bound is `x_S - x_1 <= T/h = LT/2pi = N(T,2T) + o(N(T,2T))`.
`S8` concludes in `N(T, 2T)` and `N0s(T, 2T)`. In a short interval the
denominator is `N(T, T^theta) ~ T^theta L/2pi`, so every one of those
absorptions needs re-deriving. The strip step plausibly survives for fixed
`theta > 0`, since `L^2 = o(T^theta L)`; the span bound is the one to check
first because it uses the dyadic structure directly rather than just the size
of the count.

**For the record only**, and not as a claim about any bound: the bridges are
affine in their analytic input with slope just above 1 and a negative
intercept, a fixed overhead that does not shrink with the input, so even a
legitimate substitution would lose to the landscape below `theta` about 0.808
and 0.830.

| | slope | intercept | overhead cancels at input | at which theta |
|---|---|---|---|---|
| `Phi_3` | 1.001343191 | -0.000666666 | 0.496330 | 0.808 |
| `Phi_4` | 1.002299344 | -0.001199994 | 0.521886 | 0.830 |

## 5. The best opportunity: the xi-prime curve has no short-interval reading anywhere

`hunts/frontier_map/frontier.py` computes the landscape for **two** kernels on
the same grid: Montgomery's `F(x) = |x|` for zeta, and Farmer-Gonek-Lee's

    F_1(x) = |x| - 4x^2 + sum_{k>=1} ((k-1)!/(2k)!) (2|x|)^(2k+1)

for `xi'`. The `xi'` arm is this tree's own line of work: Palomar entry
`PALOMAR-2026-08-21-000004` is the `xi'` window theorem, kernel `F_1` on
`[-1/2, 1/2]`, with `H* = 2 - 1/c* = 0.86864150052976706411` measured in
`hunts/wide_search/HANDOFF.md`. **Wang does only zeta.** He does not mention
`xi'`, `F_1`, Farmer-Gonek-Lee, or the reciprocal form.

So the question is whether Wang's Theorem 2.2 supplies the pair-correlation
input that the `xi'` functional consumes. If it does, the short-interval
`xi'` curve follows by running machinery this tree already wrote, and nobody
anywhere has it.

**Do this first, and do it as an analysis question before touching a
keyboard.** Theorem 2.2 is a statement about `sum ghat(i(rho-rho')L/2pi)
w(rho-rho')` over zeta zeros in `I`. The `xi'` arm needs the corresponding
sum over zeros of `xi'`, whose form factor is `F_1` rather than `|alpha|`.
That is not a substitution; it is a different arithmetic input, and Wang's
proof route runs through the explicit formula and Montgomery-Vaughan for
zeta specifically. The honest possibilities:

1. The `xi'` form factor has its own short-interval derivation by the same
   BGST route, in which case the work is to do it and the prize is a curve
   nobody has.
2. It does not, and the `xi'` arm has no short-interval counterpart. Record
   that as a scope boundary on the `xi'` work, which is worth writing down
   because the tree currently has no statement either way.

Note before starting: **two different constants in this tree are both called
`c*`** and they must not be conflated. `c*_1` is the zeta case, kernel
`|alpha|`, `1/c*_1 = 1.3274992963205883543`. `cStar` in
`lean/ZetaLean/Pub1/Setting.lean` is the `xi'` case, kernel `F_1`, with no
numeric value asserted and `H* = 0.8686415005`. The zeta functional is the one
in `hunts/frontier_math/paper_pin.py:c_star`, which is literally Wang's
`C(f)`, with `V_STAR = cos(sqrt 2 s)` already pinned as a profile. An earlier
draft of this brief conflated the two and claimed Palomar 000004 was the
`lambda = 1` case of Wang's Proposition 4.1. **It is not.** That claim is
withdrawn here rather than quietly deleted.

## 6. The n-point family at bandwidth below one

The second question, larger and more expensive. The n-point pressure family
is this tree's own construction with no counterpart in either paper, and §4
says it exists only at bandwidth one on the dyadic range. What is it worth on
the landscape's interior?

`hunts/family_wall/` proved the family saturates at
`sup Phi_n <= 0.675142509660254` against a configuration ceiling of
`0.6818286874638`. **Both are bandwidth-one numbers.** Deliverables, in order
of what gates what:

1. **Does the method class already cap the landscape?** Lamzouri's Remark 3.4
   cites Carneiro-Chandee-Littmann-Milinovich Corollary 14 for optimality of
   `C_MT` at bandwidth one. If that generalizes to bandwidth theta, the
   landscape value is already optimal for the whole class and everything below
   is bounded by it. Cheap, literature plus derivation, and it gates the rest.
   **Do it before spending compute.**
2. **The configuration ceiling as a function of theta**, by the same LP that
   produced the bandwidth-one ceiling (`hunts/frontier_math/configuration_lp.py`,
   whose band data `R2hat(alpha) = delta(alpha) + |alpha|` on `[-1,1]` is
   exactly the object that has to become `[-theta, theta]`). If the ceiling
   collapses onto the landscape, the hunt is over with a clean negative.
3. **The certificates re-derived at bandwidth theta**, parameters re-optimized
   rather than inherited, compared pointwise against the landscape on
   `(theta_0, 1)`.
4. **The dyadic dependency**, per §4 reason two: which of `S8`, `S9`, `S15`
   survive a `T^theta` denominator and what the span bound costs.

Cheapest informative measurement: re-optimize at `theta = 0.7` and see
whether the fixed overhead scales with the bandwidth or stays put. That
decides whether the useful range is a sliver near 1 or the whole interior.

## 7. Leads

- **The distinct-zero track.** The lab computes `Hd = (1 + H)/2` but has never
  chased it. Lamzouri's Proposition 2.1 delivers both bounds from the same
  kernel sum via *different* elementary inequalities, so the distinct constant
  is not a corollary of the simple one. Ask what the n-point family is worth
  there.
- **Wang's Theorem 2.2 is a reusable input beyond this hunt.** Anything in the
  tree that consumes full-range pair correlation now has a short-interval
  counterpart available. Inventory what that unlocks.
- **`hunts/cycle_moments` transfers, and hits the same wall.** It generalizes
  exactly the Lamzouri inequality Wang imports, so it applies in the
  short-interval setting by the same argument, and remains blocked on an
  unproved normalized fourth-moment bound. Two unconditional moment-bound
  papers landed this month, unread: arXiv:2609.11619 (Hagen, products of
  L-functions) and arXiv:2609.01101 (Durkan, Karak, Mahatab, shifted moments
  of Dedekind zeta). Whether either is the right shape is unchecked.
- **`T^theta` already appears in the tree, unrun.**
  `hunts/rogue_frontier/IDEA_PORTFOLIO.md` carries "rigorize the hybrid
  q-aspect Theorem E: `q <= T^vartheta` with proportion `H(1/(1+vartheta))`",
  flagged by the source as unchecked. That is the same landscape read along a
  different axis, and it is the second physical interpretation of the dial.
  Worth ten minutes to see whether the two axes interact.
- **The narrow-box curve.** `hunts/rogue_frontier/FRONTIER_MAP.md` records
  BGST's narrow-box result and that "a quantitative `b` to proportion curve is
  computed nowhere". Third axis on the same method.
- **Lamzouri is at v2; the tree cites v1.** Check what changed.
- **Prior art in Lean, read before writing any.** Lamzouri's Appendix A records
  that AxiomProver (Axiom Math) autonomously produced a formal certificate for
  his Proposition 2.1 unconditionally, and for his Theorem 1.1 modulo BGST
  Lemma 5 and Riemann-von Mangoldt, at `github.com/AxiomMath/ZetaZeros`,
  checked with a Lean tool called Comparator. A second Lean verification venue
  alongside Palomar, and possibly already holding what a formalization here
  would build.

## 8. Closed. Do not re-enter.

**The out-of-band positivity route.** Tempting because Wang's Theorem 2.2 is
built on the same BGST machinery as the out-of-band positivity theorem
(arXiv:2306.04799 Thm 1). **Hunt #118 closed it on 2026-09-06**
(`hunts/outband_certificate/`): the positivity is worth zero to any
certificate whose positivity input is Weil's Hermitian form, which is every
unconditional one, and what hunt #110 priced was the RH-conditional pointwise
class. The closure rests on a proved edge lemma, that a real even spectral
profile's autocorrelation is strictly positive just inside its support edge,
so it can never be nonpositive on the strip; false for odd factors, giving a
dichotomy where an even factor is Gram-able and strip-blind and an odd factor
is strip-capable and never a Gram kernel.

`docs/35` predates the closure and reads as an open opportunity. **Do not take
it at face value.** See §9.

The only non-relitigating version of the question: the edge lemma is a
statement about the support edge, and the bandwidth dial moves the support.
Does the dichotomy survive on `J = [-theta/2, theta/2]`? Start from
`hunts/outband_certificate/RESULTS.md` §8, which names the two inputs that
would reopen the route, and establish that one is in hand before spending
anything.

## 9. Corrections this hunt owes the tree

Found while writing this brief, all small, all real, none of them this hunt's
mathematics:

1. **`docs/35` is stale.** It is hunt #110's front door and does not record
   hunt #118's 2026-09-06 closure of the route. Add the closure.
2. **`docs/35` and `hunts/outband_intake/RESULTS.md` disagree numerically.**
   The doc states `+0.0068` with method error `2.2e-3`; the hunt and the case
   log state `+0.0065` with `1.8e-3`. One of them is wrong; find out which.
3. **`references/papers.md` has no entry for Baluyot, Goldston, Suriajaya and
   Turnage-Butterbaugh at all.** Not arXiv:2306.04799, whose Lemma 5 is the
   arithmetic engine of this entire line of work, and not arXiv:2501.14545.
   The shelf is missing the paper everything stands on. Add both, plus
   Lamzouri and Wang, in the file's existing annotated format.
4. **`hunts/frontier_map/RESULTS-frontier-map.md` should record that its
   landscape now has a theorem attached at each lambda**, citing Wang. That is
   a one-paragraph addition to an existing hunt's results, made by whoever
   picks this up, not a new claim.

## 10. Scope

May: build instruments under `hunts/short_interval/`, record measurements
here, read anything in the tree, make the four corrections in §9, write one
new `docs/NN-*.md` with the number taken from
`scripts/science_preflight.py` and the heading in the enforced form
`# NN. Title`, and open GitHub issues for observations it is not chasing.

May not: edit `zeta/`, `ontology/` or `harness/`; write a verdict into
`README.md`, `ROADMAP.md` or `HANDOFF.md`; use the reserved word; claim
novelty; or assign its own claims a status. Use *measured*, *observed*,
*derived*, *consistent with*.

Per `CONTRIBUTING.md` and `scripts/71_contribution_check.py`, this hunt must
carry `MISSION.md` with a valid `huntspec`, `RUNS.md` with at least one
`runmanifest` including runs that produced nothing, `RESULTS.md` stating the
bounded outcome, a case-log entry naming the directory in `hunts/README.md`,
and a numerical test or an explicit hedge for every quantitative claim.

Compute goes to GitHub Actions, never to the operator's machines, with an
estimate written into `RUNS.md` before launching and a checkpoint per unit for
anything over twenty minutes. The compute discipline in `CLAUDE.md` was
written after a day that cost roughly a third of a month's budget and crashed
the operator's laptop repeatedly. It is not advisory.

## 11. What this hunt owes on the way out

`RESULTS.md` ends with a section named **"The doors"**, per `CLAUDE.md`:
active constraints at the optimum, the frozen-constant inventory with what
relaxing each would trade against, and the information class of each door.
This hunt measures a ceiling, so that section is the deliverable.

Three entries are already known and belong in it. **Bandwidth** is the binding
constraint, and §3 is the news that it is a physical parameter rather than a
free dial, so its door is "read information from outside the current band",
which is the information-class question and which §8 says is closed for the
known route. **The certificate constants fitted at bandwidth one** are a
genuinely frozen choice and §6.3 is the door through them. **The dyadic range**
is frozen in the Lean bridge and §6.4 is the door through it.
