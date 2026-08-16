# MISSION: The rightmost zeros of the prime zeta function, against OEIS A107311's conjectures

**Opened 2026-08-16.** Nothing in this directory is a result until the case
log in `hunts/README.md` says how it ended. Probe discipline throughout: the
strongest words used are *measured*, *observed* and *decided* (an enclosure
with an exact sign), and the reserved enclosure word belongs to
`zeta/rigor.py` and appears nowhere here.

## The question

OEIS A107311 (decimal expansion of the real root of zeta(x) = 2, called x*
below, x* = 1.72864723899818...) carries two conjectures posted by Artur
Jasinski on 2024-12-21, still standing in the entry as fetched on 2026-08-15:

1. the real parts of the zeros of the prime zeta function
   P(s) = sum_p p^{-s} are not greater than x*;
2. the same bound holds for the zeros of sum_{p in S} p^{-s} for every
   subset S of the primes.

x* is the correct threshold for a *different* family: the partial sums of
zeta (Borwein-Fee-Ferguson-et-al line of work). For P(s) the balance that
governs rightmost zeros is between the first prime term 2^{-s} and the whole
tail over odd primes, so the natural threshold is the root sigma_c of

    2^{-sigma} = sum_{p >= 3} p^{-sigma},    i.e.  P(sigma) = 2^{1-sigma},

and a float-grade scout puts sigma_c = 1.77954465354699... > x*, with
P(x*) - 2^{1-x*} = 0.0169... > 0. If zeros of P accumulate up to sigma_c,
both conjectures are false, and conjecture 2 fails spectacularly: tail
subsets S = {p >= p_k} have thresholds growing without bound.

> **Is x* really an upper bound for the real parts of the zeros of P(s),
> and of every prime-subset series? Or is the true supremum sigma_c?**

## The claim under attack, stated fairly

The conjecture is refuted only by zeros with Re s > x*. The two halves of
the intended replacement theorem are:

- **(no-zeros half, decided)** for sigma > sigma_c, |P(s)| >= 2^{-sigma} -
  sum_{p>=3} p^{-sigma} > 0 by the triangle inequality, so
  sup{Re s : P(s) = 0} <= sigma_c; the numeric content is one
  directed-rounding inequality per sigma plus monotonicity.
- **(existence half, classical machinery)** for every sigma_1 < sigma_c the
  strip sigma_1 < Re s < sigma_c contains zeros of P. The exponents
  {log p} are linearly independent over Q (unique factorisation), so by
  Kronecker's theorem the phase vector (t log p mod 2pi) is dense in the
  torus; a finite truncation of P can therefore be steered inside any
  epsilon of any value in its ring-sum range, which contains 0 strictly
  when sigma < sigma_c; Rouche then converts a steered near-zero of the
  truncation into a zero of P, with the tail controlled by a decided bound.
  This is the standard Bohr-style argument for general Dirichlet series;
  writing it out with explicit constants, and deciding every numeric
  inequality in it, is the hunt's main labour.

The refutation does not depend on exhibiting an explicit zero (the value
margins in (x*, sigma_c) are a few parts in a thousand, so the first
explicit zero may sit at astronomical height); if one falls out cheaply it
is a bonus witness, decided by a box count.

## Work packages

- **WP1**: transcribe the conjecture text verbatim from the OEIS entry into
  `SOURCE.md` (the refutation must not attack a paraphrase).
- **WP2**: decide sigma_c and x* to >= 30 digits by interval Newton on both
  backends; decide the separation sigma_c - x* > 1/20 and the margin
  P(x*) > 2^{1-x*}.
- **WP3**: write the two halves of the replacement theorem with full proofs
  and decided constants; every inequality either decided by directed
  rounding or proved in the text.
- **WP4**: conjecture 2: decide the threshold of S = {p >= 3} (scouted
  1.82522595...) and prove the tail-subset thresholds are unbounded
  (elementary: Bertrand gives a prime in (p_k, 2p_k], so the balance root
  for {p >= p_k} exceeds any bound as p_k grows; write it out).
- **WP5 (calibration control)**: point the same balance machinery at the
  partial sums of zeta and recover the known x* threshold (the same code
  path must reproduce the literature's constant before its verdict on P is
  read).
- **WP6**: bonus witness hunt at sigma about 1.75 by phase steering
  (Kronecker approximation via simultaneous Diophantine approximation of
  the log p), decided by an argument-principle box count if found; budget
  capped, absence changes nothing.
- **WP7**: draft the OEIS correction text as an artifact
  (`OEIS-CORRECTION.md`); actually posting it is an operator action, not
  this hunt's.

## Pre-registered predictions

- P1: sigma_c decided in [1.77954465, 1.77954466] on both backends,
  x* decided in [1.72864723, 1.72864724], separation decided > 1/20.
- P2: the calibration control recovers the partial-sum threshold within its
  published digits.
- P3: the subset {p >= 3} threshold decides in [1.82522, 1.82523].
- P4: no explicit witness zero below t = 10^8 (the margins are thin; this
  prediction failing would be a pleasant surprise, not a problem).

## Scope

**This hunt may write**: `hunts/prime_zeta_rightmost/`, `figures/`, one new
`docs/NN-*.md` if the run earns it, a case-log entry in `hunts/README.md`,
and a pinning test under `tests/`.

**This hunt may not write**: `zeta/`, `ontology/`, `harness/`, `lean/`, and
may not promote its own claim into repo-level status files.

```huntspec
id: prime_zeta_rightmost
question: Is x* = 1.7286... (root of zeta(x)=2) an upper bound for the real parts of the zeros of the prime zeta function and all prime-subset Dirichlet series, as OEIS A107311 conjectures, or is the true supremum sigma_c = 1.7795... (root of P(sigma) = 2^(1-sigma))?
frontier: conjectures posted 2024-12-21, uncorrected in the entry as fetched 2026-08-15; float scout gives sigma_c - x* about 0.0509 and P(x*) - 2^(1-x*) about 0.0169; no literature found naming a rightmost-zero threshold for P
proposed_attack: triangle-inequality wall at sigma_c plus Bohr-Kronecker-Rouche zero existence below it, every numeric inequality decided by directed rounding on both backends
dead_routes:
  - attacking a paraphrase of the conjecture instead of the entry text
  - claiming refutation from inf |P| = 0 alone without the Rouche step that produces actual zeros
  - hunting an explicit witness as the primary deliverable (value margins are parts in a thousand, first witness may sit at astronomical height)
required_oracles:
  - interval Newton with directed rounding on both in-tree backends
  - exact rational arithmetic for series truncations and tail bounds
  - the partial-sums-of-zeta threshold from the literature as a same-code-path calibration control
  - an argument-principle box count for any claimed witness zero
kill_conditions:
  - the Rouche tail control fails to close for the infinite series, in which case only the one-sided wall at sigma_c survives and the hunt reports that it did NOT refute the conjecture
  - a literature source is found proving the sigma_c threshold for P, in which case the finding is reclassified as a rediscovery and the OEIS correction cites that source instead of this work
  - the two backends produce disjoint intervals for any decided constant, which marks the instrument as the artifact
  - the OEIS entry text turns out to mean something narrower than the transcription assumed, in which case the hunt re-scopes against the verbatim text
agents_may:
  - build instruments inside this directory
  - run interval and exact-rational computations and record decided values with backend and precision
  - fetch the OEIS entry and the cited partial-sums literature
  - write measured and decided values into RESULTS.md and results.json
agents_may_not:
  - modify zeta or ontology or harness or lean
  - use the reserved enclosure vocabulary of zeta/rigor.py anywhere in this directory
  - promote this hunt's claim into repo-level status files
  - post anything to OEIS
```

## Vocabulary contract

Measured: one float route. Decided: an interval or ball enclosure whose
exact endpoints settle a sign, stated with backend and precision. The
replacement theorem is a composite: decided inequalities glued by classical
cited arguments (Kronecker, Rouche), and the write-up says exactly which
step carries which grade.
