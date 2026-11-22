# Diagnosis for issue 335: the regime test misreads oscillating weights

This note records why the regime test added in commit `5eed14344`
(2026-08-11) misclassifies conjugate-pair Satake weights in both
directions, what was measured before any repair, and the constraints a
repair has to meet. All numbers below are from actual runs in this
worktree: `reproduce_335.py` for the named cases, and direct weight
inspections quoted with their run values. The repair itself is described
at the end and implemented in `localpos.py`.

## The test that fails

`threshold()` computed the weighted terms `w_m = lambda_m p^(-m/2)` for
`m = 1..M` with `M = _depth(p, tol)`, then read the regime off two terms:

```
w = abs(weights)
nz = flatnonzero(w > 0)
last, prev = nz[-1], nz[max(0, nz.size - 1 - max(1, M // 10))]
ratio = (w[last] / w[prev]) ** (1 / (last - prev))
```

A ratio below `1 - 1e-6` was called summable, above `1 + 1e-6` divergent,
and between them boundary. The spacing `last - prev` is about `M // 10`
nonzero steps: 9 steps at `p = 2` (`M = 94`), 3 steps at `p = 7`
(`M = 34`), and 1 step at the largest default primes, where `M` is about
15. The intent, recorded in commit `5eed14344` and `docs/25` section 6,
was sound for the case that prompted it: for `zeta(s - delta)` the
weights are `w_m = R^m` with `R = p^(delta - 1/2)`, a steady geometric
sequence, and the two-term ratio returns `R` exactly. That repair fixed
a real defect of the 2026-08-10 gate in commit `e3e4426b4`, which had no
regime test and resolved an out-of-control truncation as PASS for
`delta >= 0.5` and as FAIL with witnesses on `delta` in `[0.4877, 0.5]`.

## Why two terms cannot read a conjugate pair

For a conjugate pair `alpha = R sqrt(p) e^(+-i phi)` the weighted terms
are

```
w_m = 2 R^m cos(m phi),
```

so the two-term ratio is

```
ratio = R * |cos(m_last phi) / cos(m_prev phi)| ** (1 / (m_last - m_prev)).
```

The cosine factor is not a small correction. Either sampled term can sit
arbitrarily close to a zero of the cosine, and the small exponent
denominator (9, 3, or 1 steps) amplifies the quotient instead of
averaging it away. The ratio can therefore land on either side of 1 for
any envelope growth rate `R`, which is what `limsup |w_m|^(1/m) = R`
would need it to measure. This is not a tolerance problem and widening
`_RATIO_EPS` cannot fix it: the measured ratios below are wrong by 4 to
24 percent, and in the Davenport-Heilbronn case further down by a factor
of about 591.

## Measured failures before the repair

Output of `reproduce_335.py` on the code as it stood at the start of
this work (ground truth from the least PSD Toeplitz diagonal at
`N = 120` and, inside the bound, from the closed form):

```
inside_bound: radius=0.9 p=2 phi=0.2 expected=PASS, c_p<2 | gate=FAIL regime=divergent truncated_c=1.893747 tail=inf | two_point_ratio=1.038606 (m_prev=85, w=7.0996e-05; m_last=94, w=9.98372e-05) | least_PSD_diag_N120=1.893661 closed_form_c=1.893680
on_bound: radius=1.0 p=2 phi=0.9 expected=INDETERMINATE on bound, c_p=d=2 | gate=FAIL regime=divergent truncated_c=44.265434 tail=inf | two_point_ratio=1.089198 (m_prev=85, w=0.904025; m_last=94, w=1.95048) | least_PSD_diag_N120=2.000000
outside_bound: radius=1.2 p=7 phi=0.4 expected=FAIL, c_p=+inf | gate=PASS regime=summable truncated_c=6398.797920 tail=27192.8 | two_point_ratio=0.964274 (m_prev=31, w=561.837; m_last=34, w=503.745) | least_PSD_diag_N120=12126781403.186378
on_bound_phi2: radius=1.0 p=2 phi=2.0 expected=INDETERMINATE on bound, c_p=d=2 | gate=PASS regime=summable truncated_c=43.845054 tail=491.841 | two_point_ratio=0.992896 (m_prev=85, w=1.87599; m_last=94, w=1.75941) | least_PSD_diag_N120=2.000000
current_gate: PASS=38 FAIL=22 INDETERMINATE=0 of 60
old_gate_2026_08_10_resimulated: FAIL=0 of 60
margin 2-max_c: min=0.343354 max=0.650851
```

Points to note:

1. Inside the bound (`R = 0.9`) the ratio reads 1.038606. The earlier of
   the two sampled terms is the smaller one by cosine phase, not by
   envelope, and 9 steps of supposed growth at 3.9 percent per step
   outweigh the true decay at 10 percent per step in the quotient.
2. Outside the bound (`R = 1.2`, `p = 7`) the spacing is only 3 steps.
   The cosine quotient over those steps overwhelms 20 percent per step
   of true growth and the ratio reads 0.964274. The misread then
   compounds: the summable branch computes a geometric tail from the
   same bogus ratio, `2 * 503.745 * 0.964274 / (1 - 0.964274)`, about
   27192.8, so the truncated `c` of 6398.8 clears no witness threshold
   and the verdict is PASS for an object whose least PSD diagonal at
   `N = 120` already exceeds `1.2e10`.
3. On the bound (`R = 1`) the same instrument says FAIL at `phi = 0.9`
   and PASS at `phi = 2.0`, where the least PSD diagonal is exactly
   `d = 2` in both cases. For steady weights on the bound this gate says
   INDETERMINATE, so both readings depart from the gate's own
   convention, in opposite directions.
4. The 60 angle regression is a multiple-comparisons effect on top of
   the same mechanism. The family is `alpha = e^(+-i phi)` scanned over
   the default 25 primes, so at each place the true envelope rate is
   `1/sqrt(p) <= 0.7071`, far inside the bound, and every truncated
   margin `2 - max_c` is at least 0.343354. But a FAIL at any one of the
   25 places fails the gate, each place samples its own pair of cosine
   phases with its own spacing, and at the largest primes the spacing
   is 1 step, where a single near-zero denominator moves the ratio past
   1 even against decay by a factor of about 10 per step. Measured
   divergent places for the failing angles include single large primes
   such as 31, 79, 83, 89 and 97, which is the signature of the sampling
   mechanism rather than of any envelope growth. The resimulated
   2026-08-10 rule, which had no regime test and decided by the
   truncated `c` alone, passes all 60 angles on the same inputs.

## The same flaw already touched a reference subject

Davenport-Heilbronn at `p = 3` and `p = 7` was also being read as
divergent, which did not change its FAIL verdict but replaced its
finite witnesses from `results.json` with infinite ones. Its weights
have a dominant subsequence on even `m`, where `lambda_m` is `+2` or
`-2`, and a subdominant subsequence on odd `m` whose `lambda_m` decays
to floating point noise at about `1e-15`. The nonzero index list `nz`
contains those noise terms, and the test happened to sample one:
at `p = 3` it compared `m = 53`, with `|w| = 4.03475e-28`, against
`m = 58`, with `|w| = 2.91416e-14`, giving a ratio of 591.206676 for a
sequence whose envelope decays like `(1/sqrt(3))^m`. At `p = 7` the same
sampling gave 387.035620. The general lesson is that a single sampled
term can be small for reasons that have nothing to do with the envelope:
cosine zeros for a conjugate pair, an interleaved subdominant
subsequence here, or exact zeros for pairs such as `+- sqrt(5)`, which
the old test only handled accidentally because `nz` skipped the zeros.

## Constraints on a repair

Measured before the repair, and required to hold after it:

1. The named cases above must classify by their envelopes:
   `R = 0.9` summable and PASS, `R = 1.2` divergent and FAIL, `R = 1`
   boundary and INDETERMINATE, at both `phi = 0.9` and `phi = 2.0`.
2. The 60 angle family must return PASS at all 60 angles, with the same
   truncated margins (minimum 0.343354), since the truncated `c`
   computation is not in question.
3. The reference table must reproduce exactly: zeta 0.828427 PASS,
   L(chi quad mod 5) 0.828427 PASS, degree-2 factor at `phi = 0.9`
   1.579671 PASS, Davenport-Heilbronn 1.836068 FAIL, DH family `t = 0`
   1.333333 FAIL, Epstein principal 5.995074 FAIL, Epstein
   non-principal 6.461868 FAIL, with the finite witnesses recorded in
   `results.json`.
4. The lesion threshold `eps_star = 0.1841018918280497` and the null
   distribution at 300 samples (median 5.881092757081788, 5th
   percentile 0.7444949199285268, DH at the 6.333333 percentile) must
   reproduce. Both were re-measured on the unrepaired code and matched
   `results.json` digit for digit at the printed precision.
5. Steady weights must keep their sharp boundary resolution: for one
   real parameter at `p = 2` and `p = 97`, factors `1 - 2e-6`,
   `1 - 5e-7`, `1 + 5e-7`, `1 + 2e-6` of `sqrt(p)` gave PASS,
   INDETERMINATE, INDETERMINATE, FAIL. Any repair that simply widens
   the boundary band for all sequences breaks this and also endangers
   the Ramanujan violator at `2.3/sqrt(5) = 1.0286`, which must stay
   divergent: its margin past 1 is under 3 percent.
6. The truncated `c` values and the depths they are read at must not
   move. The violator readings 22.4578911763829 at depth 23,
   65.24381124323806 at depth 41 and 110.80151865518991 at depth 52 are
   pinned, and `zeta(s - 0.49)` at `p = 2` reads `c = 15.989` with a
   tail estimate of about 149.9 in the summable regime.

## What a finite window cannot decide, measured

An envelope reading from `|w_m|` alone separates growth from amplitude
only when the window covers the amplitude's own timescale. A first
prototype that regressed block maxima over the second half of the
original depth already fixed the named cases, but on a sweep of
conjugate pairs at `p = 7` with `phi` near 0 or `pi` its envelope
estimate was biased by up to 9.6 percent with a falsely narrow interval:
at `R = 1.0`, `phi = 3.092` it reported 0.9036 with interval
[0.8752, 0.9329]. The reason is structural: at the original depth
`M = 34` the window sees an amplitude factor `|cos(0.05 m)|` falling
smoothly, and over 17 steps a smooth amplitude slope is
indistinguishable from envelope decay by any functional of `|w_m|` that
does not model the signed oscillation. Slow beats near `phi = pi/2`
have the same effect through aliasing of the peak pattern. Two
conclusions follow. First, the regime reading needs a longer window
than the series truncation depth at large primes, which costs 15 terms
at `p = 97`. Second, the reading needs an uncertainty interval derived
from the data, so that windows which cannot separate amplitude from
growth produce INDETERMINATE instead of a confident verdict. A repair
that is decisive everywhere on oscillating weights at fixed depth does
not exist for envelope methods; the honest target is no wrong decisive
verdicts, with near-boundary slow cases admitted as undecided.

## The repair

`threshold()` now keeps the truncated `c` and its depth exactly as
before, and reads the regime from an envelope fit over at least 96
weighted terms (the same `local_lambdas` computation extended, never a
second depth for `c`):

1. The second half of the regime window is split into blocks and each
   block contributes its maximum `|w_m|` at its actual index. A least
   squares line through the log maxima estimates `log R`. Block maxima
   are what fix the named cases: a block that spans a cosine zero still
   contains terms near the envelope, a Davenport-Heilbronn block
   contains its dominant even terms, and for steady weights every block
   maximum lies exactly on the envelope line, so the sharp boundary
   resolution in item 5 above is preserved.
2. The uncertainty interval covers every variant of the estimate
   (three block widths, a block RMS slope, and the two half-window
   slopes), expanded by the variant spread and by a statistical term
   from the main fit, with a floor of `_RATIO_EPS` in log units so the
   old `1e-6` boundary band is recovered when all variants agree
   exactly. Summable requires the whole interval below 1, divergent
   requires the whole interval above 1, and an interval straddling 1 is
   boundary, hence INDETERMINATE in `gate()`.
3. The summable tail estimate uses the fitted envelope level instead of
   the last sampled term: `2 * C_up * R^(M+1) / (1 - R)`, where `C_up`
   is the largest envelope constant implied by a block maximum and `M`
   is the original truncation depth for `c`. For steady weights this
   is the old geometric tail term exactly, which is why the
   `zeta(s - 0.49)` reading near 149.9 and the lesion threshold do not
   move.

On a sweep of conjugate pairs over the same 60 angles at envelope rates
0.8, 0.9, 0.95, 0.99, 1.0, 1.01, 1.05, 1.1 and 1.2, this estimator gave
no wrong decisive verdict in the prototype run: rate 1.0 was boundary
at all 60 angles, and the remaining undecided cases were slow or
near-boundary angles at rates 0.9 to 1.1, reported as boundary rather
than as PASS or FAIL. That limitation is intrinsic to the window, per
the section above, and it is pinned in the tests as a no-wrong-verdict
property rather than as decisiveness everywhere. Nothing here is
evidence for or against RH.
