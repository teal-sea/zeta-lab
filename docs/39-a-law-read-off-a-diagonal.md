# 39. A law read off a diagonal

**Hunt #121, `hunts/quotient_exponent/`.** Measurements, the fits and the doors
are in `hunts/quotient_exponent/RESULTS.md`. This page is the front door.

Grade: **measured** (floating linear programme, HiGHS dual simplex), with every
optimum recomputed from the returned coefficients through the constraint
definition rather than read off the solver. No asymptotic statement is
established. Nothing here bears on RH (`docs/08`).

## 1. The object

There is an elementary route to prime-counting bounds that this laboratory has
been pricing for two weeks. A certificate is a finite floor sum

    W(t) = sum_{j <= y} c_j floor(t/j),   required to satisfy W >= 1,

and it yields the bound `B(N) = sum_j c_j log(floor(N/j)!)` on `psi(N)`. The
excess `B(N) - psi(N)` is what the route costs, and the smallest excess any
such certificate can have, at a given cutoff `N` and support bound `y`, is the
value of a linear programme.

`hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/` solved
that programme, and `hunts/quotient_certificate/` sharpened it by noticing that
positivity is only needed at the attainable quotients `floor(N/d)`, of which
there are about `2 sqrt(N)` rather than `N`. The relaxed floor is called `T*`,
and the published reading of it is

> T* = (0.18 to 0.23) N^{3/4} over four decades, the fitted exponent from 10^3
> to 10^6 is 0.73

with the barrier conjecture, `E >= c N / sqrt(y)`, "to be read for T* as well,
with constant 0.2".

## 2. Two problems with reading it that way

**The objective cancels.** Minimising `sum_j c_j log(floor(N/j)!)` asks a float
solver for a quantity near `1e4` as a difference of quantities near `1e8`. The
answer lives entirely in the cancelling digits.

The Chebyshev identity rewrites the same programme with every objective
coefficient and every variable non-negative, so the objective *is* the excess
and nothing cancels. The two programmes are algebraically identical and the
identity that makes them so is measured at every cutoff before the solve is
trusted, to `8e-16` relative. That reformulation is why the ladder reaches
`10^7` at all, and it reproduces the four published values to every printed
digit on the way.

**A diagonal cannot see a two-variable shape.** Every published value sits on
`y = floor(sqrt N)`. On that line `y` and `N` move together, so the data only
ever constrains one combination of the two exponents, and an integer floor in
`y` is indistinguishable from either.

## 3. What the grid says

Fit `log E = log C + a log N - b log y`. The conjectured shape is `a = 1`,
`b = 0.5`.

| model | rms of the residual, on the grid | on the diagonal only |
|---|---:|---:|
| free `a` and `b` (`a = 1.159`, `b = 0.874`) | 0.126 | 0.064 |
| conjectured `a = 1`, `b = 0.5` | 0.344 | 0.106 |
| `a = 1`, `b` free (`b = 0.642`) | 0.268 | 0.064 |
| `b = 0.5`, `a` free (`a = 0.982`) | 0.340 | 0.064 |

**On the diagonal, three of the four models are identical to three decimal
places.** On the grid the conjectured shape is 2.7 times worse: a typical
relative miss of 41% against 13%. Fitted on three decades of grid instead of
four, the free exponents were `(1.150, 0.878)` and the ratio was 3.1, so the
separation is not an artefact of where the grid stops.

The quantity the conjectured shape says is constant, `E sqrt(y) / N`, falls by
a factor of 2.1 to 2.8 inside the conjecture's own range as `y` grows. And the
fitted exponents predict the drift the diagonal does show: they say the
diagonal value should fall by a factor `0.77` from `10^3` to `10^7`, and it
falls by `0.74`, from `0.2298` to `0.1704`.

That last number is worth stating separately. The new row at `N = 10^7` puts
`T*/N^{3/4}` at `0.1704`, below the `0.18 to 0.23` band the source reports over
its four decades.

**What this does not say.** The conjecture is a lower bound, and a worse fit of
an equality shape is not a counterexample to an inequality. What it does say is
that `N / sqrt(y)` is not the shape of the optimum, so the constant one reads
off the diagonal is not a property of the family, and a barrier argument aimed
at that form is aimed at a curve the optimum does not follow.

## 4. The staircase

Solving every integer support at `N = 10^3` gives 33 distinct optima across 76
supports. The last four plateaus:

    y  42..47   excess 10.346570
    y  48..50   excess 10.283916
    y  51..55   excess 10.247100
    y  56..62   excess  2.426015
    y  63..77   excess  0

Fourteen supports buy 1% of the excess. The next seven buy a factor of 4.2. The
next one buys the rest. At `N = 10^4` the value `9.406483` holds unchanged
across sixteen consecutive supports and then drops to exactly zero at `y = 173`.

`hunts/quotient_certificate/RESULTS.md` names the support bound as its one
frozen constant "with trade shape". Measured, the trade is not a curve at all.
A plateau means a whole block of added columns changed no optimum, which is a
rank statement about the constraint matrix, and it says the useful door is not
"raise `y`" but "find which two columns did the work".

## 5. Where it reaches zero

| N | y* | attainable cells | ratio |
|---:|---:|---:|---:|
| 10^3 | 63 | 61 | 1.033 |
| 10^4 | 173 | 198 | 0.874 |
| 10^5 | 589 | 630 | 0.935 |

`hunts/quotient_certificate` already refuted a dimension count that inferred
zero excess from having more columns than constrained cells, with an exact
`N = 27, y = 9` example whose minimum excess is `log 2`. That settles that the
count is not sufficient. These rows say the other half: at two of three cutoffs
the zero arrives while the columns are still outnumbered. The count is not
necessary either.

## 6. The general shape

Nothing here is a correction of anyone's arithmetic. Every published number
reproduced exactly, from an independently written programme with a different
objective. The reading was the thing that did not survive, and it did not
survive for a reason with no mathematics in it: the measurements were all taken
along one line through a two-dimensional space, and a line cannot tell you the
shape of a surface.

Three decades of grid is not a proof of anything either, and the write-up says
so. What the grid changes is which question is worth asking next.
