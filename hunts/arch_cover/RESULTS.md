# RESULTS: arch_cover

**Nothing here is a result about the Riemann Hypothesis.** This is a measurement
of how the three pieces of the Weil functional balance, on two families of test
functions, with enclosures where it is cheap and 30-digit mpmath
elsewhere. Grade: **measured**. No proof, no review.

## 0. What was actually run

| item | command | outcome |
| --- | --- | --- |
| environment | `env -u PYTHONPATH .venv/bin/python` | flint 0.9.0, numpy 2.5.4, mpmath 1.3.0 load |
| local positivity reproduced | `hunts/local_positivity/localpos.py` | 7 rows, 7/7 verdicts match `results.json`, 2.1 s |
| three-piece balance | `hunts/arch_cover/balance.py` | 11 configurations, table below |
| enclosed cover scan | `hunts/arch_cover/cover.py` | Arb at 256 bits, `rows.jsonl` |

Every command runs from the repository root with the repository `.venv` and
`PYTHONPATH` unset. (An operator environment note was removed at landing,
2026-10-30: it described one machine, not the record.)

## 1. The instrument

In this repository's convention (`zeta/weil.py`),

    W(h) = pole + arch + prime,
    pole = h(i/2) + h(-i/2),
    arch = (1/2pi) int h(r) [Re psi(1/4 + ir/2) - log pi] dr,
    prime = -2 sum_n Lambda(n) n^{-1/2} g(log n),

and `W(h) = sum_rho h(gamma_rho)` for every admissible `h`. For `h = |f^|^2`
this says `W >= 0` is RH, and the zero side is then manifestly a sum of
non-negative terms. The only non-trivial content of the identity is that the
*arithmetic* side, three terms each of size O(1), produces that non-negative
number.

Define the cancellation depth

    depth = log10( max(|pole|, |arch|, |prime|) / |W| ),

the number of digits by which the three O(1) pieces cancel to produce `W`.

## 2. Two families that probe opposite regimes

The Gaussian `h = e^{-a r^2}` has Fourier partner `g` proportional to
`e^{-x^2/(4a)}`, a bump at the origin of width `2 sqrt(a)`. The prime sum sees
`g(log n)`, and `log n >= log 2 = 0.693`. So widening `g` (larger `a`) to reach
the primes simultaneously narrows `h`, which pushes zeros out of the sum. Prime
activity and zero activity move together along this family, in opposite
directions.

The comb `f(u) = sum_j c_j exp(-(u - j log 2)^2 / (2 sigma^2))` in
`zeta.weil.autocorrelation_pair` decouples them in the other direction. Its
partner `g` sits on `log 2, 2 log 2, ...`, so the prime side is O(1) by
construction, while `h = |f^|^2` stays broad in `r` and hundreds of zeros
contribute.

The Gaussian does not decouple the two, and at large `a` it is in *both*
regimes at once: `g` is wide enough to reach the primes (prime term 1.24 at
`a = 0.65`) while `h` is narrow enough to leave a single zero. That combination
is where the arithmetic side has to produce an exponentially small number.

## 3. The measurement (dps 30, zero side agrees to 1e-22 or better)

| family | pole | arch | prime | W | depth | zeros |
| --- | --- | --- | --- | --- | --- | --- |
| gaussian a=0.005 | +2.003 | -0.928 | -1.4e-10 | +1.074 | 0.27 | 46 |
| gaussian a=0.05 | +2.025 | -1.909 | -0.116 | +9.18e-5 | 4.34 | 7 |
| gaussian a=0.2 | +2.103 | -1.500 | -0.603 | +8.86e-18 | 17.38 | 2 |
| gaussian a=0.45 | +2.238 | -1.230 | -1.008 | +1.80e-39 | 39.1 | 1 |
| gaussian a=0.65 | +2.353 | -1.113 | -1.240 | +7.98e-57 from the zeros (enclosure band 7e-33) | 56.5 | 1 |
| comb2 s=log2 sigma=0.01 | -1.5e-4 | +0.0642 | **+0.0174** | +0.0814 | -0.10 | 594 |
| comb2 s=log2 sigma=0.02 | -6.1e-4 | +0.0809 | +0.0348 | +0.115 | -0.15 | 249 |
| comb2 s=log2 sigma=0.05 | -3.8e-3 | +0.0533 | +0.0869 | +0.136 | -0.20 | 74 |
| comb2 s=log2 sigma=0.1 | -1.5e-2 | -0.0915 | +0.177 | +0.0706 | 0.40 | 27 |
| comb3 s=log2 sigma=0.01 | +0.0122 | +0.0914 | -0.0470 | +0.0566 | 0.21 | 597 |
| comb3 s=log2 sigma=0.02 | +0.0490 | +0.1021 | -0.0941 | +0.0570 | 0.25 | 250 |
| comb3 s=log2 sigma=0.05 | +0.306 | -0.0414 | -0.236 | +0.0288 | 1.03 | 74 |
| comb3 s=log2 sigma=0.1 | +1.227 | -0.635 | -0.580 | +0.0130 | 1.97 | 28 |

Zero side against arithmetic side: `agreement` between 1e-22 and 1e-32 on every
row, so the three pieces are the true pieces of the identity, not a numerical
artefact.

## 4. What the table says

**(a) The prime side is not always negative.** For the comb at `sigma = 0.01`
it is `+0.0174`: the prime sum *helps* the inequality. The sign follows the
phase-space placement of `f`, because `g` may be negative where the zeros of
the comb are. So my opening framing, "the archimedean term must cover the
prime side", is wrong as a general statement. What has to happen is that the
three-term sum comes out non-negative, and the terms can carry either sign.

**(b) Depth is set by how far the test function sits from the first zero.**
For the Gaussian the zero side is `W = 2 sum_rho e^{-a gamma^2} = 2 e^{-a gamma_1^2}(1 + O(e^{-a(gamma_2^2 - gamma_1^2)}))`,
and the largest piece is `pole = 2 e^{a/4}`. So

    depth = a * (gamma_1^2 + 1/4) / ln 10 = 86.88 * a,

with `gamma_1^2 = 199.79`. Measured against this: 4.344 vs 4.344 (a=0.05),
17.375 vs 17.375 (a=0.2), 26.063 vs 26.063 (a=0.3), 39.094 vs 39.094 (a=0.45),
to every digit `results.json` and a direct sum over the zeros carry. The
statistic carries no information beyond `h(gamma_1)` against the pole term; it
measures the gap between the test function's scale and the first zero, nothing
deeper.

*Corrected 2026-10-30, at landing.* This paragraph first gave
`depth = a gamma_1^2 / ln 10` and "predicted" values 17.36, 26.05 and 39.07,
which match neither that form (17.354, 26.030, 39.046) nor the measurement. The
first form drops the pole's `e^{a/4}`. Against it, the MISSION kill condition
"the closed form depth fails to reproduce a measured row to the printed digits"
fired (17.38 measured against 17.35), and that was not recorded. It is recorded
here: the condition fired against the form as first written, and the corrected
form reproduces every row.

**(c) Both difficulties are active at large `a`, contrary to a first reading of
the small-`a` rows.** The prime side *grows* with `a` (0.116 at 0.05, 0.603 at
0.2, 1.240 at 0.65) while the zero sum collapses onto `gamma_1`. So the hard
regime is not exotic: it is inside the Gaussian family. There the arithmetic
side, three O(1) terms with either sign, has to land on a number of size
`e^{-a gamma_1^2}`. That is the actual shape of the difficulty, and it is a
statement about cancellation on the arithmetic side, not about the zeros: the
zero side `sum h(gamma)` is a sum of non-negative terms and never cancels at all.

**(d) The inequality has no uniform gap.** Along this family `W -> 0` while every
piece stays O(1), so the bottom of the Weil form over the admissible class is 0
and is approached, not attained away from the zeros. Normalized by
`||f||^2 = (1/2 pi) int h = 1/(2 sqrt(pi a))`, the ratio `W / ||f||^2` is about
`4 sqrt(pi a) e^{-a gamma_1^2}` and also tends to 0. Consequence: no inequality
`W(|f^|^2) >= c ||f||^2` with a fixed `c > 0` holds over the admissible class. A proof
must be an identity, or an inequality whose constant degenerates exactly as the
test function concentrates away from the zeros. This is the single most useful
constraint the measurement produces, and it is elementary once stated.

**(e) The enclosed instrument has a floor at ~33 digits, set by prime
truncation.** At `a = 0.65` the enclosure is `[-7.12e-33, +6.36e-34]`, `sign = 0`.
It was reported identical at 256 and 512 bits; only the 256-bit run is committed
(`rows.jsonl`), so the 512-bit half of that statement is unpinned. The binding term is
`prime_tail_bound = 7.76e-33` at the `n_max` cap of `2e6`; arithmetic precision
is irrelevant. The value from the zeros there is `7.98e-57` (first written
"about 4.8e-57"; corrected 2026-10-30). So enclosed positivity
cannot be pushed past roughly 33 digits of cancellation by adding bits: it needs
a different prime-tail argument. Every `UNPROVEN` row in `rows.jsonl` is this
floor, not a failure of the math.

## 5. The door

The measurements above close one route rather than open one: "establish `W > 0`
numerically and extrapolate" is dead, because the quantity to be enclosed is
exponentially small in a parameter while its three pieces are not, and the
arithmetic side is where the cancellation happens.

What survives is the structural question. `W` is linear in `h`, so for a family
`f = sum a_j f_j` the Gram matrix

    M_jk = W(h_jk),  h_jk(r) = f^_j(r) f^_k(r),  G_jk = <f_j, f_k>

gives `W(|f^|^2) = a^T M a`. A proof by positivity would amount to exhibiting
`M = B^T B` with `B` built from arithmetic data alone. The first job of that
instrument is negative-control work: reproduce the known degenerate direction
(concentrated `h`, `a^T M a -> 0`) so that any claimed factorization is tested
against the one case where the answer is known to be zero. That is the next
hunt, not this one; `hunts/arch_cover` measures and does not enclose
`lambda_min`.

## 6. Scope and defects

- Finite families, finite grids. No statement here is uniform in `f`.
- The archimedean term has **no second backend** in this tree:
  `enclose_weil_functional` reports `two_backend_cross_check unavailable` because
  `mpmath.iv` has no enclosed quadrature. A quadrature error in `arch` would
  look like `W` moving, not like an error. This is the single largest unmitigated
  risk in every enclosed number produced here.
- The prime tail is truncated at a hard `n_max = 2e6`, and at narrow `h` that
  truncation, not precision, sets the enclosed floor (`prime_tail_bound =
  7.76e-33` at `a = 0.65`). Raising `prec_bits` from 256 to 512 was reported to
  change the enclosure not at all; that run is not committed. The row that reports `UNPROVEN` at `a = 0.65` is this
  cap; the arithmetic is fine and the true value is ~`e-57`.
- `cover.py`'s cover ratio is undefined when the prime side is positive; the code
  now reports `None` and `prime_positive` instead of dividing. The first version
  asserted positivity of `-prime` and died mid-scan without writing `results.json`;
  `scan()` now appends to `rows.jsonl` after every row.
- No human has reviewed any of this.

## The doors

This hunt measures a ceiling, the 33-digit floor of the enclosed instrument, so
it owes this section. The floor is a measured optimum at one cap, not a proved
ceiling: candidate, Gaussian family `a <= 0.65`, information class the prime sum
truncated at `n_max`, proof status none.

**Active constraints at the optimum.** One binds: `prime_tail_bound` at the
`n_max = 2e6` cap, `7.76e-33` at `a = 0.65`, against a true value of `7.98e-57`.
Arithmetic precision does not bind (256 bits leave the enclosure unchanged on the
committed run). The zero side does not enter the enclosure.

**The frozen-constant inventory.**

| constant | value | what relaxing it trades against |
| --- | --- | --- |
| `n_max` | 2e6 | the tail bound falls as `n_max` grows, against a prime sum whose cost grows with it; this is the door with trade shape |
| the tail argument | the generic bound in `enclose_weil_functional` | a sharper tail estimate for Gaussian `g` would lower the floor without more primes; no cost model exists yet |
| `prec_bits` | 256 | no trade: it does not bind |
| the Gaussian grid | `a` up to 0.65 | beyond it the true value falls further under the floor |

**The information class.** Raising `n_max` or sharpening the tail bound stays
inside the data this family reads (primes, the archimedean integral, the pole).
Neither reads the zeros. Reaching depth 56 at `a = 0.65` enclosed needs the tail
of the prime sum to be bounded to about `1e-57`, which the current bound does not
approach at any affordable `n_max`.

