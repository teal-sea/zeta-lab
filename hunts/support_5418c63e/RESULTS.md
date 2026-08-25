# ARM B: window asymptotics for the depth-1 damage kernel

**Support run `5418c63e`, 2026-08-24, for run `872d7dce` (`hunts/r_c7f779`).**
Instrument: `probe_arm_b.py` (runs end to end in ~7 s; `--quick` in <1 s).
Data: `results.json`. Nothing here bears on RH (`docs/08`).

## Answer, in one paragraph

**Option (ii), and stronger than asked.** The window centres minus `2 pi d` are
not linear in `d`; they decay like `K/(2 pi d)` with
`K = 0.893732172363013`, so the limiting offset is **exactly 0** and the windows
track `2 pi` with an `O(1/s)` correction whose sign is **positive** (the window
sits slightly to the *right* of the lattice point). No multiple of `2 pi` with
`d >= 1` falls outside a depth-1 window, and this is not a horizon statement:
on the lattice `D(1, .)` collapses to an explicit rational function whose
numerator is a cubic in `s^2` with one nonnegative root at `s = 1.3307`, so
`D(1, 2 pi d) > 0` for **every** integer `d >= 1`, with no `d_max`. The minimum
over `d >= 1` of the distance from `2 pi d` to the nearest window edge is
**0.817252917249998**, attained at `d = 2`, and it is bounded away from 0: the
distance increases monotonically for `d >= 2` toward
`w0 = arccos(sech 1) = 0.8657694832396585`.

**For the caller's purpose: the ceiling `rho* <= 0.153216295` is not threatened
by drift.** The measured input it rested on (`P = 0` on the critical lattice out
to `d = 4000`) is now derived for all `d`, not measured to a horizon.

One caveat worth stating because it is the only exception: **`d = 0` is
outside**, `D(1, 0) = -0.911564713 < 0`. That is harmless here, because `P(T,y)`
sums over `p != q`, so `tau = 0` never occurs, but a reader who takes "every
multiple of `2 pi`" literally will trip over it.

## What is measured and what is derived

| statement | grade |
|---|---|
| `ghat(z) = [alpha z sinh(z/2) + beta cosh(z/2)]/(z^2+2)` | derived (exact identity), checked at 2.9e-12 against `gram_form.damage` and 6.5e-16 against mpmath |
| the `1/s^2, 1/s^3, 1/s^4` expansion of `D(1,s)` | derived, checked to 2.9e-12 relative at `s = 1e5` |
| `w0`, `K`, `W2` (the edge law constants) | derived, checked to 9 digits against high-precision edges |
| `D(1, 2 pi d) > 0` for all `d >= 1` | derived (one cubic, one sign), no horizon |
| edge locations, window count, min margin | **measured**: double-precision scan on `[1e-6, 1e5]`, mpmath `dps=50` confirmation at six `d` |

## 1. The kernel has an exact one-term form

`sinh(zp/2) + sinh(zm/2) = 2 cos(1/sqrt2) sinh(z/2)` and
`sinh(zm/2) - sinh(zp/2) = -2i cosh(z/2) sin(1/sqrt2)`, so putting the two terms
of `ghat` over the common denominator `z^2 + 2` gives, exactly,

    ghat(z) = [ alpha z sinh(z/2) + beta cosh(z/2) ] / (z^2 + 2),
    alpha = 2 cos(1/sqrt2) = 1.5204891941512604,
    beta  = 2 sqrt2 sin(1/sqrt2) = 1.8374507397311368 = 2 * A_CONST.

Checked against `hunts/frontier_math/gram_form.damage` (read-only import) at 24
`(a, s)` points: worst relative difference `2.92e-12`, which is the two-term
form's own cancellation, not a discrepancy. Against an independent mpmath
evaluation of the two-term form at `dps = 50`: worst relative `6.52e-16`.
Squaring and using `sinh^2 = (cosh z - 1)/2`:

    ghat(z)^2 = [ (alpha^2/2) z^2 (cosh z - 1) + alpha beta z sinh z
                  + (beta^2/2)(cosh z + 1) ] / (z^2+2)^2.

## 2. The asymptotic, with the next-order term the caller asked for

Expanding `(z^2+2)^{-2} = z^{-4}(1 - 4z^{-2} + ...)` and `z^{-n}` for
`z = 1 + is`, and taking `D = -Re ghat^2`:

> `D(1,s) = (alpha^2/2)(cosh1 cos s - 1)/s^2 + alpha C sin s / s^3
>          + (E cos s + F)/s^4 + O(s^-5)`
>
> `C = beta cosh1 - alpha sinh1 = 1.0484539380169988`
> `E = cosh1 (alpha^2 - beta^2)/2 + 3 alpha beta sinh1 = 9.028736331391707`
> `F = -(alpha^2 + beta^2)/2 = -2.8440563052346253`

**The caller's hint is right at leading order.** `(alpha^2/2)(cosh1 cos s - 1)`
is exactly `(4 cos^2(sqrt2/2)/s^2)[sinh^2(1/2) cos^2(s/2) - cosh^2(1/2) sin^2(s/2)]`,
`2 pi`-periodic with maxima exactly at `s in 2 pi Z`.

**The next-order term is `alpha C sin s / s^3`, and it is odd.** That is the
whole answer to the drift question: an odd perturbation of an even profile
*translates* it, it does not widen it. Relative error of the truncations
against the exact `D`:

| `s` | order `s^-2` | + `s^-3` | + `s^-4` |
|---:|---|---|---|
| 30 | 5.72e-02 | 1.00e-03 | 7.21e-04 |
| 100 | 2.02e-02 | 1.34e-03 | 2.41e-05 |
| 1000 | 8.72e-03 | 1.47e-05 | 9.25e-08 |
| 10000 | 1.71e-05 | 4.01e-08 | 1.82e-12 |
| 100000 | 1.94e-07 | 4.04e-10 | 2.91e-12 |

## 3. The edge law

Put `s = 2 pi d + x`, multiply by `S^2` with `S = 2 pi d + x`. Zeroth order the
edges satisfy `cos x = sech 1`, so `x = +/- w0`. First order the shift is
`alpha C sin x0 / (c2 cosh1 sin x0)`, and the `sin x0` cancels, so **both edges
move the same way** and the window translates without changing width. Second
order the two shifts are equal and opposite, so they cancel in the centre and
add in the width:

> `centre(d) - 2 pi d = K/s + O(s^-3)`,  no `1/s^2` term
> `half_width(d)      = w0 + W2/s^2 + O(s^-3)`
> `margin(d)          = w0 - K/s + W2/s^2 + O(s^-3)`,   `s = 2 pi d`
>
> `w0 = arccos(sech 1)   = 0.8657694832396585`
> `K  = alpha C/(c2 cosh1) = 0.893732172363013`
> `W2 = Geff/(c2 sinh1)    = 1.779638303047668`

`Geff` keeps the term `-alpha C x sin x` that comes from expanding `1/S` about
`1/s`. **Dropping it is the one mistake this run made and caught**: it gives
`W2 = 2.5534`, 43% too large, and the numerics rejected it before the number
was written down. The corrected `W2` matches high-precision measurement:

| `d` | `(half_width - w0) * s^2` measured (mpmath dps 60) | residual vs derived `W2` |
|---:|---|---|
| 1000 | 1.77963937504 | +1.07e-06 |
| 10000 | 1.77963831377 | +1.07e-08 |
| 100000 | 1.77963830315 | +1.02e-10 |

The residual falls by two decades per decade of `s`, i.e. it is `O(s^-2)`, so
the half-width's next correction after `W2/s^2` is `O(s^-4)` and not `O(s^-3)`:
the odd order drops out of the width, as it did at first order. `W2` is
confirmed to ten digits. (This check has to be done at
`dps = 60`: `half_width - w0` is `4.5e-12` at `d = 1e5`, below what the double
scan can resolve.)

Measured against the double-precision scan, worst `|half_width - (w0 + W2/s^2)|`
over `10 <= d <= 15915` is `2.72e-06`.

## 4. The scan, out to `s = 1e5`

`D(1, .)` scanned on `[1e-6, 1e5]` at step `0.002` (5.0e7 samples), every sign
change bracketed and bisected to double precision:

* **31,830 sign changes**, i.e. `1.999938` per `2 pi` period over
  `15915.49` periods. **No anomalous window anywhere**: `D` is positive at every
  window midpoint and negative at every midpoint between consecutive windows
  (both checks in `results.json`).
* **15,915 windows** containing the `15,915` lattice points `2 pi d`,
  `1 <= d <= 15915`. **Zero lattice points outside a window.**
* The first seven sign changes are `5.398373, 7.284924, 11.749118, 13.506670,
  18.023030, 19.765262, 24.298419`. `s = 0` sits in a *negative* stretch, and
  the first window opens at `5.398373`.

Edges confirmed independently at `dps = 50` with mpmath, through a different
code path (the un-recombined two-term `ghat`): agreement `8.7e-16` at `d = 1`,
`8.5e-12` at `d = 15915` (the latter is the double result's own ulp scale).

| `d` | left edge | right edge | `centre - 2 pi d` | margin |
|---:|---|---|---|---|
| 1 | 5.398372992988 | 7.284924227670 | 5.846330e-02 | 0.884812314192 |
| 2 | 11.749117697109 | 13.506669511906 | 6.152299e-02 | **0.817252917250** |
| 3 | 18.023029600755 | 19.765262417835 | 4.459009e-02 | 0.826526320783 |
| 5 | 30.576150425591 | 32.311382835230 | 2.784009e-02 | 0.839776110307 |
| 100 | 627.454179069564 | 629.185727052340 | 1.422343e-03 | 0.864351648394 |
| 1000 | 6282.319679893085 | 6284.051218949722 | 1.422418e-04 | 0.865627286501 |
| 15915 | 99996.028403217300 | 99997.759942184136 | 8.937599e-06 | 0.865760546 |

`(centre - 2 pi d) * s` goes from `0.367336` at `d = 1` to `0.893732` at
`d = 15915`, against the derived `K = 0.893732172363`; the tail mean over
`d > 1591` is `0.8937322997` with standard deviation `4.1e-07`. A linear fit of
the offset against `d` returns slope `-2.55e-08` per `d`, consistent with zero
and with the wrong functional form, which is the point: **the offset is not
linear in `d`.**

## 5. The lattice is exactly solvable, so there is no horizon

At `s = 2 pi d` we have `cos s = 1`, `sin s = 0`, so `cosh z` and `sinh z` are
*real* at `z = 1 + is`. Then `|(z^2+2)^2|^2 = (s^4 - 2s^2 + 9)^2` and taking
`-Re` gives the **exact identity**

> `D(1, 2 pi d) = P(u) / (u^2 - 2u + 9)^2`,  `u = (2 pi d)^2`,
> `P(u) = p u^3 - (3p - 3q + r) u^2 - (5p + 2q - 10r) u - 9(p + q + r)`,
>
> `p = (1 + cos sqrt2)(cosh 1 - 1) = 0.6277706355638578`
> `q = 2 sqrt2 sin(sqrt2) sinh 1  = 3.2833052932216624`
> `r = 2 (1 - cos sqrt2)(cosh 1 + 1) = 4.293006489071762`

checked against direct evaluation at `d = 1, 2, 3, 10, 100, 4000, 15915, 1e6`
to `8.4e-16` relative or better (worst case `d = 1`). Numerically

    P(u) = 0.6277706 u^3 + 3.6735975 u^2 + 33.2246011 u - 73.8367418.

`u^2 - 2u + 9 = (u-1)^2 + 8 > 0`, so `sign D = sign P`. **Every coefficient of
`P` but the constant is positive**, so `P` is strictly increasing on `u >= 0`
and has exactly one nonnegative root, `u* = 1.7707490180`
(`s* = 1.3306949380`; the cubic discriminant is `-2.224e+05 < 0`, confirming
the other two roots are complex). For every integer `d >= 1`,
`u = (2 pi d)^2 >= 4 pi^2 = 39.478 > u*`, hence

> **`D(1, 2 pi d) > 0` for every integer `d >= 1`.**

That is a derived statement about all `d`, not a scan to a horizon, and it is
exactly what `P(T,y) = 0` on the critical `2 pi` lattice requires (`P` sums
`[-D(2y, tau_pq)]^+` over `p != q`, and on that lattice `tau_pq = 2 pi d` with
`d != 0`; `D` is even in `s`, so `d >= 1` covers it).

## 6. What this does to `rho* <= 0.153216295`

`RESULTS-37fb06a9.md` §2 derives the ceiling from the measured fact that
`P = 0` on the critical lattice out to `d = 4000`. Section 5 replaces that
measurement with a derivation valid for all `d`. So, on this ingredient, **the
ceiling is exact and not "slightly below"**: there is no drift that eventually
carries a lattice point out of a window, because the drift is `+K/s -> 0` and
the margin converges *upward* to `0.86577`.

Two limits on that, stated plainly:

1. This settles only the `P = 0` ingredient. The ceiling also rests on the
   Poisson-summation limit `B/k -> c2(0) - A^2` and on `Shq(1/2)`, neither of
   which this run touched.
2. The derivation in section 5 is a real-coefficient cubic evaluated in double
   precision. Its sign structure (three positive coefficients, one negative
   constant) is robust to that by a wide margin (the smallest
   coefficient is `0.628` and the constant is `-73.8`), but the reserved word is not used and
   this is not enclosure-carrying arithmetic.

## 7. What was not settled

* **No remainder bound on the `O(s^-5)` term.** The edge law in section 3 is an
  asymptotic series checked numerically, not a theorem with explicit constants.
  The `margin >= 0.8172` claim is therefore measured for `d <= 15915` and
  derived-asymptotically beyond it. The *sign* claim (section 5) has no such
  gap; only the *margin size* does.
* **Only `a = 1` (`y = 1/2`) was studied**, because that is what the caller
  asked. The expansion in section 2 is written for general `a` and the leading
  window half-width is `arccos(sech a)`, which degenerates as `a -> 0`; nothing
  here says where that becomes a problem.

## The doors

1. **Active constraint at the optimum.** For the `P = 0` question the binding
   object is the single cubic root `u* = 1.7707`, and it is not close: the
   nearest lattice point sits at `u = 39.478`, a factor of `22.3` above it. This
   constraint has enormous slack and is not what limits `rho*`. **The ceiling's
   binding objects are elsewhere**: `B/k -> c2(0) - A^2` and `Shq(1/2)`,
   and this run says so rather than pretending its own result is the wall.
2. **Frozen-constant inventory.** (i) The scan horizon `s_max = 1e5`, now
   redundant for the sign question, still live for the margin question.
   (ii) The scan step `0.002`, which bounds the width of a feature that could
   have been missed at `1.0e-3`; the `1.999938` sign changes per period says
   nothing was. (iii) `a = 1`, i.e. `y = 1/2`; the whole calculation is
   parametric in `a` and nothing here explores the trade. (iv) The truncation of
   the expansion at `s^-4`, which fixes the accuracy of `W2` and nothing else.
3. **Information class.** The section-5 result reads *less* data than the scan
   did, not more: it needs only the value of `D` on `2 pi Z`, where the kernel
   is rational. Extending it from the sign to the *margin*, a lower bound on
   the distance to the nearest edge for all `d`, requires reading `D` off the
   lattice, where `cos x` and `sin x` re-enter and the object stops being
   rational. That is the next door, and it is a genuinely different information
   class.

---

*Grade: the asymptotic series and the lattice identity are derived; every edge
location, window count and margin is measured in double precision with mpmath
confirmation at `dps = 50`. The reserved word is not used. Nothing here is
evidence for or against RH.*
