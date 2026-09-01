# 35. The unspent fact: what out-of-band positivity is worth, and why nobody can claim it

**Hunt #110, `hunts/outband_intake/`.** Read `hunts/outband_intake/RESULTS.md` for the
measurements and the doors. This page is the front door: what the thread is, why it
exists, and what a session picking it up needs to know before running anything.

Grade: **measured**, throughout. No theorem is claimed here and nothing on this page
bears on RH (`docs/08`).

## 1. The situation

Every certificate in the public race for the proportion of simple on-line zeros of
zeta reads pair-correlation data on `[-1, 1]` and nothing else. Call that the band.
The configuration ceiling for that information class is `0.6818286874638`, proved in
the upstream development, and the entire public race sits between `0.6725007036794116`
and `0.6734164909714992949`. The race has therefore moved the record by `9.2e-4` in
total.

In 2023 Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh proved
(arXiv:2306.04799, Theorem 1) that the weighted form factor is nonnegative for every
`alpha`, **unconditionally**. Conjugate-closure of the zero multiset writes it as an
integral of a square, and the Cauchy weight's poles at `±2i` cover every pair of strip
zeros. This is information from outside the band, it costs no hypothesis, and this
laboratory re-derived it before finding it (`hunts/frontier_math` §4 records that so
nobody derives it a third time).

**Nobody had ever measured what it is worth.** That is what Hunt #110 did.

## 2. What it is worth

`+0.0068`, landing the configuration class near `0.6793`.

The measurement is two linear-programming ladders on matched grids: one with
out-of-band positivity enforced, one with band data alone. Both descend toward their
limits from above, because the discretisation restricts the adversary. The in-band
ladder is the control *and* the calibration, since its limit is known to be the record
itself, so the same extrapolation applied to it returns the method error, `2.2e-3`.
The difference extrapolates to `+0.0068`, about three times that error.

For scale, that is roughly seven times the whole public race's progress. It also
lands essentially on top of Chirre, Goncalves and de Laat's `0.6792`, which is reached
**under RH**. The same value falling out of unconditional inputs is the interesting
part: it suggests RH is doing work in their proof that it may not be doing in the
truth.

## 3. Why it is unspent

The only known technique for converting that information into a theorem runs an
inertia count, and the count needs the evaluation form to be positive semidefinite.
That forces the window's spectral density `v = phi^2` to be nonnegative, and the
pair weight in alpha-space is its self-convolution `Khat = v * v`, nonnegative
everywhere by identity. **The framework never has a free `ghat`. It has a free
`v >= 0`, and `v |-> v * v` cannot produce a negative value.**

The requirement does not weaken. Under an indefinite form the rank half of the lemma
survives, needing no definiteness, and the inertia half fails, needing a square root.
The witness is small enough to check by hand: one off-line pair with
`Q = t·[[0,1],[1,0]]`, `S = diag(1,-1)`, `c = 2` gives slack `+2.0` at `t = 1` and
`-0.5` at `t = 1.5`. Against 4000 random positive-semidefinite pairs the inequality
was never violated.

So the value lives at a kernel that is not a square, and the machinery only builds
squares.

## 4. Why this is a gap and not a wall, and why that distinction is the point

`hunts/frontier_math` §2 records a genuine wall: passing the band by widening it needs
an unconditional *upper* bound on prime pair correlations, the loss is
`(C-1)·T^(lambda-1)·N/log T` for any constant `C > 1 + o(1)`, and the required input
is Hardy-Littlewood grade. That is a famous open problem and no amount of cleverness
in this laboratory opens it.

**Hunt #110 is not that.** The information is already in hand, already unconditional,
and already measured to be worth something. What is missing is a construction. A gap
of that shape is fundable in a way a wall is not, and telling the two apart is the
main reason this page exists.

## 5. The one measurement that changed the shape of the problem

Sweeping how far past the band the positivity is enforced:

| reach | value | share of the gain |
|---|---|---|
| none | 0.6775676 | |
| 1.25 | 0.6827996 | 60.2% |
| 1.5 | 0.6855095 | 91.4% |
| 2.0 | 0.6858061 | 94.8% |
| 3.0 | 0.6862544 | 100% |

**It saturates almost at once.** Nine tenths of the value is inside `(1, 1.5]`.

That shrinks the construction problem materially. The object nobody has does not need
to be signed on a half-line. It needs to be signed on a narrow strip just outside the
band. Any attempt on §3's obstruction should take that form, and a session that starts
by trying to build a kernel negative everywhere is solving a harder problem than the
one that pays.

## 6. What bounds the result, stated rather than buried

Three things, all in `RESULTS.md` at length.

**The in-band data's provenance is unaudited.** Until someone traces it to an
unconditional source rather than to Montgomery's RH-conditional theorem, `0.6793` is
a class value and not an unconditional one. This is the cheapest next step and it
gates whether any of the rest is worth funding.

**Gate #3 fires.** The isolation input passes on the Davenport-Heilbronn function and
on both discriminant `-23` Epstein forms, so it is prime-blind. That does not kill a
counting bound, since Davenport-Heilbronn has simple zeros to count and the gate
exists to catch claims that *explain* RH. What it does establish is that all
arithmetic content sits on the prime side: a hunt working the zero side can
re-optimise a certificate but can never add arithmetic. That bounds what §4's gap can
ever be worth.

**An argument was withdrawn.** A ratio diagnostic was stated confidently in the first
draft and is wrong: over the measured range both ladders decay at similar rates, so
the ratio is flat under either hypothesis and carries no information. The difference
test with a calibrated error replaced it and reversed the verdict. Recorded because
the withdrawn version nearly shipped as a negative result.

## 7. Where to pick it up

`hunts/outband_intake/` carries `MISSION.md` with the kill conditions, `RESULTS.md`
with the doors ranked, `RUNS.md` with the estimate written before launch, and the two
sweep scripts with their checkpointed artifacts. The doors section ranks three:

1. **The depth-bound lead**, and the follow-up should take this one. Every planted
   off-line configuration left the isolation step holding with slack `+2.01` to
   `+2.67`, and the failure mode arrives exactly when a planted zero leaves the strip.
   If the step survives under a bound on off-line depth, existing machinery consumes
   the information with no new kernel class. Weakly evidenced, cheap to sharpen, and
   it goes *through* the obstruction rather than around it.
2. **The provenance audit**, cheapest, and it gates everything.
3. **The kernel-class construction**, the largest prize and the hardest, now known to
   need signing only on `(1, 1.5]`.
