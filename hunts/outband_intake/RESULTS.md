# outband_intake — the information is worth about 0.0068, and no known certificate can spend it

**Verdict: the kill condition did NOT fire, and the hunt found a gap rather than a wall.**
The unconditional out-of-band positivity of Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh (arXiv:2306.04799, Theorem 1) is worth about `+0.0068` at the
measure level, landing the configuration class near `0.6793`. Separately, and this is
the point of the hunt, the certificate machinery that would turn that into a theorem
provably cannot reach it. What separates them is one structural obstruction, stated
below with a counterexample.

Grade: **measured**, and only that. Two LP ladders on matched grids with a calibrated
extrapolation. Nothing is kernel-checked, no theorem is claimed, and nothing here is
evidence for or against RH (`docs/08`).

## 1. The measurement

Four matched rungs, once with out-of-band nonnegativity enforced on `(1, 3]` and once
with bandwidth-one data alone. The discretisation restricts the adversary, so both
ladders descend toward their limits from above.

| X | J | out-of-band | in-band control | difference |
|---|---|---|---|---|
| 40 | 200 | 0.6918387 | 0.6793882 | 0.0124505 |
| 80 | 320 | 0.6862544 | 0.6775676 | 0.0086868 |
| 120 | 480 | 0.6847195 | 0.6768963 | 0.0078232 |
| 160 | 640 | 0.6838668 | 0.6764627 | 0.0074041 |

The in-band ladder was extended alone, being roughly 240 times cheaper: `0.6759394`
at `X = 240` and `0.6756339` at `X = 320`.

**The difference is the signal, and the method is calibrated before it is believed.**
Extrapolating `d(X) = v_out - v_in` by `a + b·X^(-p)` gives `a = +0.0068`. The same
fit applied to the in-band excess, whose true limit is known to be zero because the
in-band LP measures the Montgomery-Taylor dual, returns `+0.0022`. That is the method
error. The gain exceeds it by about threefold, so zero is excluded, though not
overwhelmingly. The implied class value is `0.6793`, which sits essentially on top of
Chirre, Goncalves and de Laat's `0.6792`.

**A ratio test was tried first and is withdrawn.** Comparing excesses over the record
gives `2.808, 2.714, 2.780, 2.869`, and an earlier draft of this file read that
flatness as proof of a common limit. It is not. Over this range the two ladders decay
at nearly the same rate, so the ratio is flat under both hypotheses and carries no
information; the slight rise across the range is in fact what a positive limit
predicts. The difference test with a calibrated error is the right instrument.
Recorded because the withdrawn argument was stated confidently and was wrong.

Solver robustness: the out-of-band solve at `X = 80` agrees to seven digits across
`highs`, `highs-ds` and `highs-ipm`. The in-band ladder independently reproduces the
published values in `frontier_math/RESULTS-frontier-math.md` §1.

## 1b. The information is local: 91% of it sits in `(1, 1.5]`

Lane B holds the grid at `X = 80, J = 320` and sweeps how far past the band the
positivity constraint is enforced.

| reach `A_out` | value | gain over in-band | share of the gain at 3.0 |
|---|---|---|---|
| none (in-band) | 0.6775676 | | |
| 1.25 | 0.6827996 | +0.0052320 | 60.2% |
| 1.5 | 0.6855095 | +0.0079419 | 91.4% |
| 2.0 | 0.6858061 | +0.0082385 | 94.8% |
| 3.0 | 0.6862544 | +0.0086868 | 100% |

**It saturates almost at once.** Three fifths of the value arrives by `alpha = 1.25`
and nine tenths by `alpha = 1.5`; doubling the reach from 1.5 to 3.0 buys another
`7.5e-4`. The `5.0` and `8.0` rungs were not reached before the run was stopped, and
on this curve they cannot matter.

This is the most useful thing lane B could have said, and it changes the shape of the
construction problem in §2. A certificate does not need to read far past the
boundary. It needs to read a *narrow strip* just outside it, roughly
`alpha in (1, 1.5]`. Whatever object eventually consumes this information has to be
signed only on that strip, which is a much smaller demand than a kernel signed on a
half-line, and it is the form any attempt on the §2 obstruction should take.

## 2. Why no certificate can spend it

The inertia argument that would consume out-of-band information needs the evaluation
form to be positive semidefinite. That forces the window's spectral density
`v = phi^2` to be nonnegative, and the pair weight in alpha-space is its
self-convolution `Khat = v * v`, nonnegative everywhere by identity. **The framework
never has a free `ghat`. It has a free `v >= 0`.** The source paper's own functional
carries `int |Khat|`, and `v >= 0` is exactly what discharges that modulus
(`hunts/frontier_math/paper_pin.py`).

The requirement cannot be weakened to something a signed kernel satisfies. Replacing
the Frobenius inner product by a weighted `tr(X^H S Y S)` with indefinite `S` keeps
the rank half of the lemma, which needs no definiteness, and breaks the inertia half,
which needs `S^(1/2)`. Minimal counterexample: one off-line pair with
`Q = t·[[0,1],[1,0]]`, `S = diag(1,-1)`, `c = 2` gives slack `+2.0` at `t = 1` and
`-0.5` at `t = 1.5`. Against 4000 random positive-semidefinite pairs the inequality
was never violated, worst slack `+0.001321`, so the instrument would have seen a
violation had one existed.

The first-order perturbation law says where the gain lives. Adding out-of-band mass
`-eps` where `F >= Lbar` moves the bound by `dJ/deps = (J - Lbar)/g(0)`, which is
adverse for every `Lbar` below about `1.3275`. BGSTB gives `Lbar = 0`, so the direct
channel pays nothing. **The entire gain is indirect**: negative out-of-band mass
relaxes the constraint and licenses an in-band profile that is not an autocorrelation.
That is precisely the profile the inertia framework cannot represent.

## 3. So the result is a gap, not a wall

The information supports about `0.679`. Every known certificate construction is
confined to `0.6725007`. The difference is not a missing computation and not a
frozen constant. It is that the only proof technology available insists on kernels
that are squares, and the value lives at a kernel that is not one.

**That gap is the research problem this hunt hands forward**, and it is the one
shape the operator asked for: not a ceiling, not a bridge over somebody's theorem,
but a construction nobody has. It is also why the CGdL value is conditional. They
reach `0.6792` with an isolation input that costs RH; the LP reaches the same place
with unconditional inputs, which says the RH is doing work in their *proof* that it
may not be doing in the *truth*.

## 4. One open question that bounds this entire file

**Whether the LP's constraint set is unconditionally valid for zeta's zeros has not
been checked here, and it is load-bearing.** The out-of-band constraint is BGSTB and
is unconditional. The `tau >= -1` bound is `rho >= 0`, the nonnegativity of a pair
density, true of any point process and costing no hypothesis. An intermediate report
claimed that bound smuggles in the diagonal-isolation drop and cited
`frontier_math/CLEAN-KILL-REPORT.md`; that document concerns a different object, the
`-2` off-line block interaction in the rank-trace inequality, and does not support
the claim. **The in-band pair-correlation data is the one not audited**, and until
someone traces it to an unconditional source rather than to Montgomery's
RH-conditional theorem, `0.6793` is a class value and not an unconditional one. That
audit is the cheapest next step and it decides whether §3's gap is worth funding.

## 5. Gate #3 fires, and what it does and does not mean

This hunt's own `MISSION.md` names it a kill condition: any candidate argument that
also passes the Davenport-Heilbronn control distinguishes nothing. The battery was run
after the rest of this file was written, and **it fires**.

```
riemann_zeta:        True
davenport_heilbronn: True     (10 zeros in the box)
epstein_2_1_3:       True
epstein_1_1_6:       True
shifted_product:     VOID     (see below)
```

The diagonal-isolation drop holds for the Davenport-Heilbronn function, which
satisfies a Riemann-type functional equation and has zeros off the critical line, and
for both discriminant `-23` Epstein forms. It is prime-blind.

**It does not kill the measured result, and the reason is a distinction worth keeping
straight.** Gate #3 exists to catch a structural property claimed to *explain* RH. The
isolation drop claims nothing of the kind: it is a counting input, and counting the
simple zeros of a function is meaningful whether or not that function's zeros lie on a
line. Davenport-Heilbronn has simple zeros to count. So the drop passing on a rival is
the expected behaviour of a counting tool, not the signature of a vacuous one.

**What it does establish is strategic and it is not comfortable.** Both of CGdL's
zero-side inputs are prime-blind. Every piece of arithmetic content in this whole
construction therefore sits on the prime side, in the in-band theorem. A hunt working
the zero side can re-optimise a certificate; **it cannot add arithmetic.** That is
independent evidence for the reading in §2, and it bounds what §3's gap can ever be
worth.

The `shifted_product` row is **void, not a finding**. The harness returned `False`
where it should have returned "undefined": that function had zero sign changes in the
test box, so the claim was never evaluated on it. Recorded because the void row would
otherwise read as the drop failing on a uniformly displaced zero set, which is not
something this run established.

**One lead, flagged as weak.** The drop also survived every planted off-line
configuration tried: zeta plus a pair at `1/2 ± 0.05, 0.2, 0.5 + 20i` gave slack
`+2.01, +2.08, +2.67`, and the Cauchy weight's pole at `2i` is reached exactly when a
planted zero leaves the strip, which is the mechanism this tree already cites for why
BGSTB holds. That hints the drop may survive unconditionally under a depth bound on
off-line zeros, which would be a route *through* the obstruction rather than around
it. It is weak evidence: four to thirteen zeros, one box, one planted pair at a time,
and the bulk-displacement case went untested for the harness reason above.

## 5b. A disagreement left standing

The adversary held, twice, that the LP earns its `0.0068` through `rho = 1 + tau >= 0`
and that this constraint *is* the diagonal-isolation drop, which would make the class
value RH-conditional rather than unconditional. **This file does not accept that**, for
the reason in §4: `rho >= 0` is the nonnegativity of a pair density, true of any point
process, and the document cited in support concerns the `-2` off-line block
interaction in the rank-trace inequality, a different object. The disagreement is
recorded rather than resolved because it is decidable by the §4 provenance audit and
should be settled by that audit rather than by whoever writes the last file.

## 6. Cost

Under two hours of laptop compute, no CI, no formalization. A negative would have
been reached before anything expensive was funded; so was a positive.

## The doors

**Active constraints at the optimum.** One binds: the certificate kernel must be an
autocorrelation. Everything in §2 is that constraint seen from a different angle, and
§1 measures what it costs, about `6.8e-3`.

**Frozen-constant inventory.**

| Frozen | Chosen as | What relaxing it would trade |
|---|---|---|
| kernel class: autocorrelations `Khat = v*v` | forced by the inertia lemma | **The door.** Any construction certifying a bound from a signed kernel converts §1's measured `0.679` into a theorem. Trades proof technology for `6.8e-3`, seven times the public race's total progress. |
| out-of-band reach `A_out` | 3.0 | **Now measured, see §1b.** Saturates: 91% of the gain is inside `(1, 1.5]`, and relaxing further buys `7.5e-4`. What this door closes is a demand rather than a lever: a certificate need only be signed on a narrow strip past the band, which is the smallest form the §2 construction can take. |
| truncation `X` | 160 out-of-band, 320 in-band | Sharpens the extrapolation and shrinks the `2.2e-3` method error, which is currently a third of the signal. The out-of-band arm costs about `X^2.8`; `X = 240` exceeded an hour on a laptop and was killed. Belongs in CI. |
| in-band data provenance | inherited from `frontier_math` | Not a constant but an unaudited assumption, see §4. Decides whether the number is unconditional. |

| off-line depth, taken as unbounded | never varied | **The §5 lead, and the only door that goes *through* the obstruction rather than around it.** Every planted off-line configuration left the isolation drop holding with slack `+2.01` to `+2.67`, and the Cauchy weight's pole at `2i` is reached exactly when a planted zero leaves the strip. If the drop survives under a depth bound on off-line zeros, existing machinery consumes the information with no new kernel class. Weakly evidenced, cheap to sharpen. |

**Information class.** The reach and truncation doors stay inside the data the family
already reads and buy only confidence. Three doors matter and none requires reading
more information: the kernel-class door, the provenance audit, and the depth-bound
lead. The information is already in hand and unspent. That is what makes this
different from the sieve wall of `frontier_math` §2, where the missing input is
Hardy-Littlewood grade and genuinely absent.

**Ranked, and the follow-up goes through the third.** The kernel-class door is the
largest prize and the hardest, since §2 shows the requirement is an identity. The
provenance audit is cheapest and gates whether any of this is unconditional. The
depth-bound lead is the one that could deliver the prize using machinery that already
exists, which is why the next hunt should take it: fix the harness guard that voided
the `shifted_product` row, then re-run on a fully displaced zero set, which is the
one configuration the inertia machinery was built to survive.
