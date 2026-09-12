# Bounded outcome

**No mathematics has been attempted in this hunt.** It was opened on
2026-09-12 and what follows is everything established on that day: three
findings, all reading and measurement rather than new mathematics, which
between them killed the plan the hunt was opened for and reordered its
routes. Grade: **derived and measured**, nowhere higher. Nothing here bears on
RH (`docs/08`).

`MISSION.md` carries the routes. This file records only what is settled.

## 1. Finding one: the tree already computes Wang's curve

Biao Wang's arXiv:2609.07918 Theorem 1.1 bounds the proportion of simple
on-line zeros in `(T, T + T^theta]` below by
`c(theta) = 2 - theta/2 - (1/sqrt 2) cot(theta/sqrt 2)`.
`hunts/frontier_map/frontier.py:zeta_H_closed(lam)`, taken from the source
paper's eq. (7.4), computes the same function of bandwidth. Measured equal to
1e-16 at five bandwidths, and the lab's curve crosses zero at
`0.5501939647441547` against Wang's printed `theta_0 = 0.550193964744154`.
The same module's `Hd = (1 + H)/2` is Wang's distinct companion. **Both
constants in Wang's Theorem 1.1 were already being computed here.**

What Wang adds is that the dial is physical. `frontier.py` holds bandwidth as
"exactly one dial, capped at 1 by the Rudnick-Sarnak / Montgomery support
restriction", a hypothetical, since the whole game was pushing it up. His
Theorem 2.2, an unconditional short-interval pair-correlation formula valid
for `supp g` in `[-lambda, lambda]` with `lambda < theta` strictly, says
bandwidth theta is exactly what counting in an interval of length `T^theta`
buys. The lab's dial and his exponent are the same number.

Every constant printed in both papers reproduces: `verify.py` checks `C_MT`,
both global proportions, `c(3/4)`, `d(3/4)`, `theta_0`, `theta_d`, Wang's
stated `c'(theta)`, and the closed form of the variational minimum against an
independent Nystrom solve at six bandwidths.

## 2. Finding two: the transplant is dead, and the reason is the second moment

Substituting `c(theta)` into the two kernel-checked bridges fails. In the
coordinate the problem is affine in, `R = 2 - c`, which is the normalized
second moment, `Phi_3` reads `R -> 1.001343 R - 0.002019`. The certificate
buys a fixed absolute `0.002019` and pays a **relative 0.134% of whatever
second moment it consumes**, and `R(theta) = 1/theta + theta/3 - ...` diverges
like `1/theta`. So the overhead is proportional to the one quantity that blows
up in a short window, and break-even is at `theta = 0.8082`. **No
re-optimization repairs that**, which is why §3 matters.

Independently the transplant has no analytic footing: the band is
`(-theta, theta)`, open and strict, while the bridges read `[-1, 1]` with no
free half-length anywhere in `famlib.py`; and the bridges are dyadic, with 21
occurrences of `2 * T` in `Bridge/Main.lean` alone and `S8`, `S9` and `S15`
all absorbing errors against `N(T, 2T)`. A per-block error absorbed against
`N(T, 2T)` and reappearing against `T^theta log T` **carries a hidden
`T^(1-theta)`**, and that hazard recurs on every route here.

## 3. Finding three: window shape is worth nothing

Measured in `landscape.py`. Writing the functional as
`R = A(phi)/lambda + lambda B(phi)` with `A = int phi^2/(int phi)^2 >= 1` by
Cauchy-Schwarz, equality iff `phi` is flat, the flat window gives
`R = 1/lambda + lambda/3` **exactly** (verified), whose threshold is the root
of `theta^2 - 6 theta + 3`, that is `3 - sqrt 6 = 0.5505102572`.

Against Wang's optimal-window `theta_0 = 0.5501939647`, **the entire value of
the Montgomery-Taylor window over a flat one is 3.2e-4 of threshold.** The
flat-minus-optimal gap is about `lambda^3/180`: measured `0.00122` at
`lambda = 0.6` against `0.00120`, and `0.00583` at `lambda = 1` against
`0.00556`. The optimal window flattens as bandwidth shrinks.

At `theta = 0.55` the whole window-shape game is therefore worth about `9e-4`,
and an n-point family whose bandwidth-one share of it is `2.4e-4` is worth
roughly `4e-5`. **Wang's `c(theta)` already is the re-optimization.**

## 4. Measured, and feeding the routes rather than settled

**The xi-prime landscape** (`MISSION.md` §6). `frontier_map` computes the
landscape for the Farmer-Gonek-Lee `F_1` kernel too, and Wang does only zeta.
Measured with the `F_1` implementation calibrated against **two published
figures** from Alpöge-Furman Remark 7.1 (`0.858384` against their `0.85838`,
and `0.929192` against their `0.92919`): the `xi'` curve sits `+0.11` to
`+0.20` above the zeta one at every bandwidth and stays non-vacuous down to
`0.51332` where zeta dies at `0.55019`. The zeta control at the same settings
is off by `+1.2e-5` from a value known exactly, which is the error bar on
every `xi'` figure; in particular the `xi'` solve's `0.868660` against the
lab's quartic-certificate `0.8686415005` is **method error, not a free gain**,
and the control is what establishes that. Whether Wang's Theorem 2.2 supplies
the input is the gating question and is unanswered; the audit it needs is in
`MISSION.md` §6.

**The price of the band edge** (`MISSION.md` §8).
`hunts/outband_certificate/RESULTS.md` states the reason for bandwidth one:
"`F` has no unconditional upper bound outside the band, so bandwidth one is
forced". That names the input and does not price it. Priced here by capping
`F <= B` beyond the band and checking the minimizer's sign, since a
sign-changing minimizer is outside Lamzouri's class and its value is not a
bound: `B = 2` at `L = 1.2` gives `0.760859`, and `B = 20` on a sliver of
width `0.05` still gains `0.0142`, against a bandwidth-one ceiling headroom of
`0.00933`. The mechanism is a linear shadow price,
`c'(1) = (1/2) cot^2(1/sqrt 2) = (3/2 - H)^2 = 0.6847550854111`, against
quadratically small out-of-band mass. **What is not established is that a
constant `B` exists unconditionally**: positive definiteness gives only
`F(alpha) <= F(0)`, which grows like `log T`. That is the whole question.

Note the direction, which hunts #110 and #118 had the other way round: they
priced out-of-band **positivity**, a lower bound, and this method needs an
**upper** bound, because the out-of-band contribution enters against the
autocorrelation of the nonnegative `f = eta^2`. Positivity is wrong-signed
information. The `+0.0068` those hunts measured is best read as the price of
removing RH rather than as an unclaimed gain.

## 5. Two readings withdrawn the same day

Recorded rather than deleted.

**Withdrawn: that the closed form of the variational minimum was this hunt's
finding.** It was derived here before the paper was read, and it is Wang's
published Proposition 4.1 equation (4.2) with a uniqueness proof the
re-derivation does not have. It is also already in this tree as
`frontier.py:zeta_H_closed`. `verify.py` keeps the derivation as a cross-check
of the paper, not as output.

**Withdrawn: that `PALOMAR-2026-08-21-000004` is the `lambda = 1` case of
Wang's Proposition 4.1.** It is not. Two different constants in this tree are
both called `c*`: the zeta one has kernel `|alpha|` with
`1/c*_1 = 1.3274992963205884` and is Wang's; the `xi'` one in
`lean/ZetaLean/Pub1/Setting.lean` has the Farmer-Gonek-Lee kernel `F_1` with
`H* = 0.8686415005` and is a different object. The withdrawn reading conflated
them, and would have sent a session to formalize a generalization of the wrong
theorem. It is the more instructive of the two.

A third recommendation, re-optimizing the certificate window at each
bandwidth, was written into an earlier draft and is killed by §3 rather than
withdrawn on a reading error.

## 6. Corrections owed to the tree

None of them this hunt's mathematics; fixes assigned in `MISSION.md` §11.
`docs/35` predates hunt #118's closure and reads as an open opportunity.
`docs/35` and `hunts/outband_intake/RESULTS.md` disagree on the measurement,
`+0.0068` with error `2.2e-3` against `+0.0065` with `1.8e-3`.
`references/papers.md` has **no entry at all** for Baluyot, Goldston,
Suriajaya and Turnage-Butterbaugh, though their Lemma 5 is the arithmetic
engine of this whole line of work. And
`hunts/frontier_map/RESULTS-frontier-map.md` should record that its landscape
now has a theorem attached at each bandwidth.

## 7. Reproduction

```bash
.venv/bin/python hunts/short_interval/verify.py      # the papers' constants
.venv/bin/python hunts/short_interval/landscape.py   # both landscapes, the band price
```

Both are stdlib only, so they also run under a bare `python3` during triage.
`verify.py` exits non-zero if any constant drifts from what the papers print
or from what `frontier.py` computes. `landscape.py` runs pure-Python solves at
`n = 120` to `200` and carries about `1e-5`; it prints the zeta control at
every step so that error is visible rather than assumed. Anything needing more
than four digits should be re-run on the repository's numpy path or with ball
arithmetic.

## The doors

Preliminary: this hunt has measured no ceiling of its own, so the inventory is
what §1 to §4 expose. `MISSION.md` §13 carries the full version with the
information-class column; the ranked summary is:

1. **The band edge at 1**, frozen by the absence of an unconditional upper
   bound on `F` beyond it rather than by choice. Priced in §4 as worth more
   than everything else here combined, at a probability stated honestly.
   Leaves the information class.
2. **The kernel**, fixed to `|alpha|` on the zeta arm while the tree also
   computes the `F_1` landscape that Wang does not. Leaves the class.
3. **The dyadic counting range**, frozen in the Lean bridge by what was
   available to formalize. Stays in the class.
4. **The window shape.** Closed by the measurement in §3, and listed so
   nobody opens it again.
5. **The window's single frequency `sqrt 2`.** `hunts/amtopa_ceiling` proved
   the `2 j pi` harmonics exactly M-orthogonal to it at bandwidth one, so the
   window maximum over the whole coefficient space is the pure `sqrt 2` value.
   Whether that survives at bandwidth theta is unchecked and cheap, though §3
   bounds the prize.

Doors 3, 4 and 5 sit under the configuration ceiling, which is itself a
bandwidth-one number (`0.6818286874638`) and **unmeasured at bandwidth
theta**. Measuring it is `MISSION.md` §7 and it is the stopping criterion for
this whole axis.
