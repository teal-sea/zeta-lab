# Bounded outcome

**No mathematics has been attempted in this hunt.** It was opened on
2026-09-12, and what follows is everything established on that day, which is
a reading of existing material plus two routes closed on analysis. Grade:
**derived and measured** where marked, and nothing else. Nothing here bears
on RH (`docs/08`).

Read `MISSION.md` for the question and the routes. This file records only
what is settled.

## 1. What is established

**The tree already computes Wang's curve.** Biao Wang's arXiv:2609.07918
Theorem 1.1 bounds the proportion of simple on-line zeros in
`(T, T + T^theta]` below by `c(theta) = 2 - theta/2 - (1/sqrt 2) cot(theta/sqrt 2)`.
`hunts/frontier_map/frontier.py:zeta_H_closed(lam)`, taken from the source
paper's eq. (7.4), computes the same function of bandwidth. Measured equal to
1e-16 at five bandwidths, with the lab's curve crossing zero at
`0.5501939647441547` against Wang's printed
`theta_0 = 0.550193964744154`. The same module computes the distinct
companion `Hd = (1 + H)/2`, which is Wang's `d(theta)`. Both constants in
Wang's Theorem 1.1 were already being computed here.

**What Wang adds is that the dial is physical.** `frontier.py` records
bandwidth as "exactly one dial, lambda, capped at 1 by the Rudnick-Sarnak /
Montgomery support restriction", with the source paper's note that "the
certificate is empty for lambda <= 1/2". The tree held the low-bandwidth
regime as a hypothetical. Wang's Theorem 2.2, an unconditional short-interval
pair-correlation formula valid for `supp g` in `[-lambda, lambda]` with
`lambda < theta`, says bandwidth theta is exactly what counting in an interval
of length `T^theta` buys, so the landscape's interior carries an
unconditional theorem. The lab's dial and Wang's exponent are the same
number.

**Every constant printed in both papers reproduces.** `verify.py` checks
`C_MT`, both global proportions, `c(3/4)`, `d(3/4)`, `theta_0`, `theta_d`, and
Wang's stated `c'(theta) = (1/2) cot^2(theta/sqrt 2)`, and confirms the closed
form of the variational minimum against an independent Nystrom solve of the
integral equation at six bandwidths.

## 2. What is closed, on analysis, before any compute

**Substituting `c(theta)` into `Phi_3` and `Phi_4` is not a bound.** Two
independent reasons, either sufficient.

*Bandwidth.* The two kernel-checked bridges consume pair-correlation data on
`alpha` in `[-1, 1]` and nothing else. `hunts/family_wall/famlib.py` holds `H`
as a module constant and its kernel is the closed form of
`integral_{-1/2}^{1/2} cos(sqrt 2 t) cos(2 pi x t) dt` at the single frequency
`sqrt 2`, with no free half-length; same in `hunts/amtopa_ceiling/family.py`.
At bandwidth theta that band does not exist.

*Dyadic range.* Every theorem on the bridge instantiates its counting
functions at `(T, 2T]`, with 21 occurrences of `2 * T` in
`Bridge/Main.lean` alone. `S9` absorbs deleted end strips of width `2 pi L`
against `N(T, 2T)`; `S15`'s span bound is `LT/2pi = N(T,2T) + o(N(T,2T))`;
`S8` concludes in `N(T,2T)` and `N0s(T,2T)`. A `T^theta` denominator requires
re-deriving each. The strip step plausibly survives for fixed `theta > 0`
since `L^2 = o(T^theta L)`; the span bound uses the dyadic structure directly
and is the one to check first.

*And, for the record only,* the bridges carry a fixed overhead that does not
shrink with their input: affine with slope just above 1 and negative
intercept, so even a legitimate substitution would lose to the landscape
below `theta` about 0.808 (`Phi_3`) and 0.830 (`Phi_4`).

**The out-of-band positivity route stays closed.** Hunt #118 closed it on
2026-09-06 by a proved edge lemma. It is tempting here only because Wang's
Theorem 2.2 shares BGST machinery with the positivity theorem.
`MISSION.md` §8 states the single remaining non-relitigating form of the
question and what must be in hand first.

## 3. Two readings withdrawn the same day

Recorded rather than deleted.

**Withdrawn: that the closed form of the variational minimum was this hunt's
finding.** It was derived here before the paper was read, and it is Wang's
published Proposition 4.1 equation (4.2), with a uniqueness proof the
re-derivation does not have. It is also already in this tree as
`frontier.py:zeta_H_closed`. `verify.py` keeps the derivation as a
cross-check of the paper, not as output.

**Withdrawn: that Palomar entry `PALOMAR-2026-08-21-000004` is the
`lambda = 1` case of Wang's Proposition 4.1.** It is not. Two different
constants in this tree are both called `c*`: the zeta one has kernel
`|alpha|` with `1/c*_1 = 1.3274992963205884`, and is Wang's; the `xi'` one in
`lean/ZetaLean/Pub1/Setting.lean` has the Farmer-Gonek-Lee kernel `F_1` with
`H* = 0.8686415005`, and is a different object. The withdrawn reading
conflated them. The zeta functional in this tree is
`hunts/frontier_math/paper_pin.py:c_star`, which is literally Wang's `C(f)`,
with `cos(sqrt 2 s)` already pinned as a profile.

The second error is the more instructive one: it would have sent a session to
formalize a generalization of the wrong theorem.

## 4. Corrections owed to the tree

Found while reading, none of them this hunt's mathematics, all listed with
their fix in `MISSION.md` §9: `docs/35` predates hunt #118's closure and reads
as an open opportunity; `docs/35` and `hunts/outband_intake/RESULTS.md`
disagree on the measured value (`+0.0068` with error `2.2e-3` against
`+0.0065` with `1.8e-3`); `references/papers.md` has no entry for Baluyot,
Goldston, Suriajaya and Turnage-Butterbaugh at all, though their Lemma 5 is
the arithmetic engine of this whole line of work; and
`hunts/frontier_map/RESULTS-frontier-map.md` should record that its landscape
now has a theorem attached at each bandwidth.

## 5. Reproduction

```bash
.venv/bin/python hunts/short_interval/verify.py
```

Stdlib only, so it also runs under a bare `python3` during triage. Exits
non-zero if any constant drifts from what the papers print or from what
`frontier.py` computes.

## The doors

Preliminary, and marked so: this hunt has measured no ceiling yet, so the
inventory below is what §1 and §2 already expose rather than the output of an
optimization. Whoever runs `MISSION.md` §6 replaces this section with the
measured version, ranked by shadow price where computable.

**Active constraints.** One, and §1 is the news about it: **bandwidth**. It
binds, and it is not a frozen constant that a better choice could relax. It
is fixed by the Rudnick-Sarnak / Montgomery support restriction at `lambda`
at most 1, and fixed below that by the length of the interval being counted.
Its door is therefore "read information from outside the current band", which
is an information-class question and not a parameter choice.

**Frozen-constant inventory.**

1. **The certificate constants fitted at bandwidth one.** `Phi_3` uses
   `c = 1345/1000000, m = 745, p = 3000` and `Phi_4` uses
   `c = 2310/1000000, m = 435, p = 2500`, all optimized against a
   bandwidth-one window. Relaxing means re-deriving them at bandwidth theta.
   The trade is unknown and is exactly `MISSION.md` §6.3. Genuine trade shape:
   the fixed overhead may be buying something that a short window does not
   need.
2. **The dyadic counting range.** Frozen in the Lean bridge, not by choice but
   by what was available to formalize. Relaxing costs the re-derivation of
   `S8`, `S9` and `S15` against a `T^theta` denominator. `MISSION.md` §6.4.
3. **The kernel.** The zeta arm is fixed to Montgomery's `F(alpha) = |alpha|`.
   The tree also computes the Farmer-Gonek-Lee `F_1` landscape for `xi'`, and
   Wang does only zeta, so this is the one frozen choice where the tree holds
   something the field does not. `MISSION.md` §5. Whether the short-interval
   pair-correlation input exists for `F_1` is the gating question and is
   unanswered.
4. **The window's single frequency `sqrt 2`.** `hunts/amtopa_ceiling`
   established that the `2 j pi` harmonics are exactly M-orthogonal to the
   `sqrt 2` term, so the window maximum over the whole coefficient space is
   the pure `sqrt 2` value. That is a proved reason this constant is not a
   door at bandwidth one. Whether the orthogonality survives at bandwidth
   theta has not been checked and is cheap to check.

**Information class.** Doors 1, 2 and 4 stay inside the data the current
family reads and so under its configuration ceiling, which is itself a
bandwidth-one number and unmeasured at bandwidth theta. Door 3 changes the
arithmetic input and therefore the class. The out-of-band door, the only one
that would leave the class outright, is closed per §2.
