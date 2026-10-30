# RESULTS: weil_split

**Nothing here is a result about the Riemann Hypothesis.** This is an exact
place-by-place decomposition of the prime side for one family of compactly
supported test functions. Grade: **measured**, with one exact identity.

## 1. The decomposition, and the identity that was checked

For `f = b^{-1/2} 1_{[-b/2, b/2]}` (so `||f||^2 = 1`), `g = f * f` is the
triangle of half-width `b` and `h = g^` is `(2/b)(1 - cos br)/r^2`. Because `f`
is compactly supported, `Phi_p f = sum_{m>=0} p^{-m/2} f(. - m log p)` has only
finitely many overlapping terms:

    ||Phi_p f||^2 = (1/b) sum_{m,n>=0} p^{-(m+n)/2} (b - |m-n| log p)_+
    Q_p = (1 - 1/p) ||Phi_p f||^2
    cost_p = log p (Q_p - 1)                      exact, rational
    sum_p cost_p = -prime_term                    checked to 1e-16
    W = pole + arch - sum_p cost_p

Only primes with `log p < b` contribute, i.e. `p <= e^b`; the shift series is a
geometric sum beyond that. The check `sum_p cost_p = -prime_term` passes at every
`b` tested, with the residual at the float-sum floor (`1e-16`), so the
decomposition is the same object `zeta.weil` computes, split by place rather than
asserted.

## 2. Where the cost sits

| b | primes contributing | sum of cost | top-3 share | cover `(pole+arch)/cost` | margin | quad-vs-zero |
| --- | --- | --- | --- | --- | --- | --- |
| 2.0 | 4 | 1.745851 | 0.977 | 1.030400439 | 3.04e-2 | 7.5e-3 |
| 3.0 | 8 | 4.085344 | 0.727 | 1.006436469 | 6.44e-3 | 5.3e-3 |
| 4.5 | 24 | 9.835248 | 0.441 | 1.001504129 | 1.50e-3 | 1.4e-3 |
| 6.0 | 79 | 20.158935 | 0.261 | 1.000791320 | 7.91e-4 | 7.8e-3 |
| 8.0 | 429 | 48.293063 | 0.126 | 1.000158833 | 1.59e-4 | 2.2e-3 |

Two monotone facts, and they point the same way:

- **The cost spreads.** At `b = 2` the prime side is three places (p = 2, 3, 5
  carry 98% of it). At `b = 8` it is 429 places and the top three carry 13%.
- **The cover margin collapses.** `cover - 1` falls from 3.0e-2 to 1.6e-4 over
  the same range, roughly like `b^{-2.5}`.

So the archimedean side is asked to cover a sum over an unbounded set of places,
with a margin that shrinks as the test function widens. There is no finite set of
"important" primes doing the work, and no bounded slack.

## 3. A caveat that had to be handled, not hidden

`h` here decays only like `1/r^2` (that is what compact support of `f` costs), so
the archimedean quadrature converges slowly. `explicit_formula_sides` reports
`agreement` between the arithmetic and zero sides of 1e-3 to 8e-3 across the
grid: **three digits only.** So every `cover` above is computed as

    cover = (W_from_zeros - prime_term) / sum_p cost_p,

with `W` from the verified zeros and both other terms exact. That is why the
column is printed to nine digits while the quadrature column is only recorded;
the two differ by the `agreement` column. Anyone quoting `pole_plus_arch_quad`
here is quoting three-digit arithmetic.

## 4. What this adds

`hunts/local_positivity` showed the prime side is a sum of local norms and that
they do not assemble globally. `hunts/arch_cover` showed the form has no uniform
gap on a one-parameter family. This adds the distribution: the prime side is not
carried by finitely many places with a stable covering margin. The margin decays
as more places enter, so any estimate "the archimedean term beats the primes"
gets harder exactly as the prime side becomes global, which is the regime where
it must hold for all `f`.

## 5. Defects and scope

- One-parameter family (rectangles). Nothing here covers a general `f`, and the
  widest member still has `h` of slow decay.
- `cover` uses the zero side for `W`, so it inherits the zero table's 30-digit
  accuracy and the verified range `gamma < 10^4`. The zero tail bound is reported
  by `explicit_formula_sides` and is negligible for these `b`, but it is not zero.
- `Q_p > ||f||^2` for every place measured here, i.e. every `cost_p > 0`. This is
  the opposite sign to the local-positivity reading of `Q_p` as a "norm at every
  place"; that hunt's gate applies to Toeplitz sections of local coefficients,
  not to `||Phi_p f||^2` of a fixed `f`, and the two should not be conflated.
- No human has reviewed any of this.
