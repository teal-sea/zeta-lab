# RESULTS: decay_law

**Nothing here is a result about the Riemann Hypothesis.** This is a measurement
of one ratio, on two compact families, on one window. Grade: **measured**.

The kill condition in MISSION.md was committed before this table was computed.
A quadrature check of the tent formulas printed two endpoint margins before
that commit. The tolerance was not changed after that print. Those two margins
alone give the tent's `alpha_m = 5.73`, so the fire on `alpha_m` was knowable when
the tolerance was set: the kill is pre-registered against the recorded run, not
blind on `alpha_m` (landing note, 2026-10-30). The numbers below
are a fresh run of `hunts/decay_law/decay.py`.

## 1. The ratio, and the two families

For either family, with `||f||^2 = 1` and `g` the autocorrelation,

    C = -prime_term = sum_p cost_p
    W_zeros = sum h(gamma)          both signs, verified ordinates, gamma <= 10^4
    margin = cover - 1 = W_zeros / C

The margin is `W` normalized by the prime cost. It is not a statement about
the archimedean term. On the endpoints,

    alpha_X = ln(X(2) / X(8)) / ln(4)

satisfies `alpha_m = alpha_W - alpha_C` exactly.

Both families are parameterized by `b`, the length of the support of `f`, so
`g` is supported on `[-b, b]` in both cases and `g(0) = 1`.

- **Rectangle**, the family of hunt #157, recomputed here as a cross-check.
  `h(r) = b sinc^2(b r / 2)`, decaying as `1/r^2`. This is `b` times the Fejer
  pair at half-width `b/2`. The recomputed zero sum matches that scaled Fejer
  zero sum to `2e-9` relative, and the prime cost matches
  `hunts/weil_split/results.json` to `1e-12` relative, at every landed width.
- **Tent.** `f(x) = sqrt(3/b) (1 - 2|x|/b)_+` on `[-b/2, b/2]`, `g` the
  piecewise cubic in MISSION.md, `h(r) = (3b/4) sinc^4(b r / 4)`, decaying as
  `1/r^4`. The nodes of `h` sit at twice the rectangle's spacing (`4 pi k / b`
  against `2 pi k / b`; first written "half", corrected 2026-10-30). Not a
  rescaling of the rectangle.

The per-place overlap sum equals the prime cost on every row. The largest gap
is `5e-16`.

Primary grid, fixed in MISSION.md: `b = 2 + 0.25 k` for `k = 0` to `24`.
Twenty-five widths, from 2 to 8.

## 2. The kill fired

Rectangle side, from `hunts/weil_split/results.json`, not from the recomputation:

| quantity | rectangle | tent | tent minus rectangle | fires at 0.5? |
| --- | --- | --- | --- | --- |
| `alpha_m` | 3.790 | 5.731 | 1.941 | yes |
| `alpha_W` | 1.395 | 3.470 | 2.074 | yes |
| `alpha_C` | -2.395 | -2.262 | 0.133 | no |

The universal reading is withdrawn. It fired on the margin and on the zero-side
sum. It did not fire on the prime cost.

The recomputed rectangle exponents agree with the landed ones to `1e-9` on
`alpha_m` and exactly, at the printed digits, on `alpha_C`. Substituting the
recomputation would not change the fire.

Endpoint values the exponents come from:

| family | b | W_zeros | prime cost | margin | share of W in the first zero |
| --- | --- | --- | --- | --- | --- |
| rectangle | 2 | 5.307e-2 | 1.746 | 3.040e-2 | 0.377 |
| rectangle | 8 | 7.671e-3 | 48.29 | 1.588e-4 | 6.2e-5 |
| tent | 2 | 5.068e-4 | 0.8125 | 6.238e-4 | 0.590 |
| tent | 8 | 4.130e-6 | 18.69 | 2.210e-7 | 2.6e-9 |

`b = 8` sits 0.003 of a node-spacing from a zero of the rectangle's `h(γ_1)`,
and 0.002 of a node-spacing from a zero of the tent's. The endpoint `alpha_W`
is phase-sensitive. Two checks say the fire is not that one node:

- Adding the density tail estimate to the rectangle's truncated `W` moves
  `alpha_m` by 0.0026, under the tolerance.
- The least-squares fit over all 25 widths, which does not sit on that node,
  still differs by 1.93 on the margin and by 2.09 on `W`. The fit is a check.
  The kill is the endpoint comparison, as written.

## 3. A single exponent is not a defensible summary of either family

The rule was written in MISSION.md before the recorded tent run (two tent
endpoint margins had been printed; see the opening paragraph): a single
exponent is a defensible summary only if the local exponents on this grid span
at most 0.5. Both families fail it.

Log-log least squares of `ln X = A - alpha ln b`, residual in natural-log units
(a residual of 0.7 is a factor of about 2):

| family | quantity | fitted alpha | RMS residual | max absolute residual |
| --- | --- | --- | --- | --- |
| rectangle | margin | 3.395 | 0.207 | 0.469 |
| rectangle | W_zeros | 1.025 | 0.189 | 0.319 |
| rectangle | prime cost | -2.370 | 0.070 | 0.149 |
| tent | margin | 5.323 | 0.734 | 1.444 |
| tent | W_zeros | 3.115 | 0.732 | 1.435 |
| tent | prime cost | -2.208 | 0.022 | 0.053 |

The fitted margin exponents differ by 1.93, the same size as the endpoint
difference. The fitted prime-cost exponents differ by 0.16. The residual says
the margin fit is a poor summary, and the prime-cost fit is a much better one.

Local exponents of the margin, between consecutive widths, rounded. Full values
are in `results.json`.

Rectangle, span 33.5, from -11.0 to 22.6:

    6.2, 0.6, 5.3, 2.9, 2.0, 6.2, -4.8, 11.4, -4.3, 12.0, 0.1, 0.9,
    2.0, 2.3, 10.6, -2.0, 13.9, -8.6, 5.8, 3.1, 7.4, 12.5, -11.0, 22.6

Tent, span 103.2, from -42.4 to 60.7:

    -3.5, 22.6, -0.7, -4.1, 2.3, 34.8, -12.0, -13.5, 26.8, 8.6, -16.2, 3.3,
    37.5, 2.9, -35.3, 35.6, 3.6, -4.4, -13.3, 60.7, -8.1, -42.4, 31.4, 32.4

Hunt #157's five widths gave local margin exponents from 2.23 to 5.58, and an
endpoint ratio of about `b^{-3.8}`. That coarser grid averaged over the
oscillation this grid shows. This grid does not resolve it either: the
rectangle's `γ_1` oscillation has period 0.444 in `b`, so its Nyquist interval is
0.222, below the 0.25 spacing, and the swings above are aliased. The endpoint
ratio is real as a ratio of two numbers. It is not a local decay rate.

On this grid the rectangle margin rises on 5 of the 24 steps (from `b` = 3.5, 4.0,
5.75, 6.25 and 7.5). Hunt #157's "the cover margin collapses" holds as a fall from
`b = 2` to `b = 8`, not as a monotone decay; its record carries a dated note.

The endpoint statistic is itself phase-sensitive. Over the 39 grid pairs with
`b2 / b1 >= 2.5`, the tent-minus-rectangle margin exponent runs from -0.17 to
4.00, and 3 pairs fall inside 0.5 (for example `b` = 2.5 against 7.5). The
tolerance's justification in MISSION.md is numerical precision, which is not the
main uncertainty here; the least-squares fit (section 2) is what supports the fire
on `[2, 8]`. (Added at landing, 2026-10-30.)

## 4. How the decay splits

`alpha_m = alpha_W - alpha_C`. The share of the endpoint decay coming from each
piece:

| family | from W shrinking (`alpha_W / alpha_m`) | from the prime cost growing (`-alpha_C / alpha_m`) |
| --- | --- | --- |
| rectangle | 0.368 | 0.632 |
| tent | 0.605 | 0.395 |

The prime cost grows in both families, by a factor 27.7 (rectangle) and 23.0
(tent) from `b = 2` to `b = 8`, and it grows at every step of the grid. Its
local exponents stay inside an interval of length 1.33 (rectangle, -2.04 to
-3.37) and 0.57 (tent, -2.09 to -2.66). `W` shrinks by a factor 6.9
(rectangle) and 123 (tent), and it increases on 11 of the 24 steps in each
family.

So on this window, `b` from 2 to 8, the piece the two families share, to within
the tolerance, is the prime cost. The piece they do not share is the zero-side sum. The margin inherits
that disagreement. A reading that stays inside the measurement: the fitted
`alpha_W` is 1.03 for the rectangle, whose mean envelope scales as `1/b`, and
3.12 for the tent, whose mean envelope scales as `1/b^3`. Those are the
envelope powers of `sinc^2` and `sinc^4`. The measurement is consistent with
the zero-side decay tracking the decay of `h`, which is family-specific. It
does not establish that tracking beyond these two families.

*Scope, added at landing, 2026-10-30.* The sharing is a property of the window.
By the prime number theorem `C` is about `2 int_0^b e^{u/2} g(u) du`, which is
`8 e^{b/2} / b` for the rectangle (`C b e^{-b/2}` is 7.08 at `b = 8`, rising toward 8)
and of order `e^{b/2} / b^3` for the tent. Neither is a power of `b`, so a log-log
exponent of `C` depends on the window by construction: a reviewer's extension of
the run to `b = 16` found the tent-minus-rectangle `alpha_C` growing from 0.17 on
`[2, 8]` to 1.34 on `[10, 16]` (measured, not committed here). Heuristically the
prefactor difference in `C` cancels the difference in the `W` envelopes, so both
margins would decay like `e^{-b/2}`. The withdrawal of the universal reading
above is a statement about power-law exponents on `[2, 8]`, not about the
asymptotic rate.

## 5. The local-exponent variation is the zero side

`h(γ_1)` was evaluated at the first ordinate of the same list the zero sum
uses, not taken from a remembered constant, through the closed forms
`b sinc^2(b γ_1 / 2)` and `(3b/4) sinc^4(b γ_1 / 4)`. (First written as
"matches the closed form", which cannot fail: `decay.py` computes it from the
closed form. Corrected 2026-10-30.)

The first zero does not dominate the rectangle: its share of `W` runs from
`1.4e-5` to 0.42, and the first three zeros never carry more than 0.515. The
tent is often the first few zeros: the first zero's share runs from `2.6e-9`
to 0.94, and the first three run from 0.085 to 0.986. At a node of `h(γ_1)`
that share collapses and later zeros carry the sum.

Correlation of the local margin exponents with the local exponents of
`h(γ_1)`: 0.85 on the rectangle, 0.50 on the tent. The prime cost has no such
swings on this window. The variation in the local margin exponents is
oscillation from the zero side; the prime cost's own local exponent drifts
slowly (section 4, the `e^{b/2}` law), which on `[2, 8]` is small next to it.

## 6. Arithmetic side against zero side

Where they disagree, the covering ratio is the zero side's. The prime cost is
a finite sum (`e^8` is under the prime-power cap), so the margin is not a
quadrature.

Rectangle. Relative disagreement 4.5e-3 to 8.6e-3. On the Fejer path the
signed difference, arithmetic minus truncated zero sum, equals the density tail
estimate, with leftover at most `2.2e-7` absolute. The disagreement is the
truncation at height `10^4`, not the archimedean integral. Hunt #157's generic
quadrature, without that path, reported agreement of 1e-3 to 8e-3 and took the
ratio from the zero side. This measurement does the same. The tail is under 1%
of `W` and moves `alpha_m` by 0.0026.

Tent. Worst relative disagreement `5.7e-8`, at `b = 3.5`, and the signed
difference matches the tail estimate to `4e-15` absolute. The archimedean
quadrature is not the limit. This is not a few-digit quadrature, and that
floor is not folded into the fit residual. The fit uses `W_zeros` and the
prime cost.

## 7. Scope

- Two families, twenty-five widths, `b` from 2 to 8. Nothing here covers a
  general test function.
- The zero side uses verified ordinates up to `10^4`. The tail beyond that
  height is the disagreement in section 6. It is not zero.
- `b = 8` is near a node of `h(γ_1)` in both families. Section 2 records what
  that does and does not do to the kill.
- This measurement is not a ceiling, so it does not carry a door inventory.
- No human has reviewed any of this.
