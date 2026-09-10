# Results: the barrier law is not the shape the diagonal suggested

**2026-09-10. Grade: measured (floating LP, HiGHS dual simplex), with every
reported optimum recomputed from the returned coefficients through the
constraint definition rather than read off the solver, and with the two
identities the reformulation rests on measured at every cutoff.** No
asymptotic statement is established and nothing here bears on RH (`docs/08`).

## 1. The verdict

    reproduced, four published diagonal values, to all printed digits
    new diagonal rows            N = 3 x 10^6 and 10^7
    T*(sqrt N, N) - psi(N) at 10^7        30297.736768,  0.1704 N^{3/4}
    published reading                     "(0.18 to 0.23) N^{3/4}, fitted exponent 0.73"
    fitted shape on the grid              E ~ 0.348 N^{1.150} y^{-0.878}
    conjectured shape                     E >= c N y^{-0.5}
    zero excess first reached at          y* = 63, 173, 589 for N = 10^3, 10^4, 10^5
    number of attainable cells            |Q_N| = 61, 198, 630

Three findings, in order of how much they cost the published reading.

**The diagonal cannot see the shape.** Fitting `log E = log C + a log N - b log y`
on the diagonal `y = floor(sqrt N)` alone, the conjectured `(a, b) = (1, 0.5)`
and the free fit `(1.150, 0.878)` have the same residual to three decimal
places, because the diagonal only ever sees `a - b/2`. On the grid they
separate, and the conjectured shape is three times worse.

**The excess is a staircase in `y`, not a curve.** At `N = 10^4` the optimum
holds the value `9.406483` unchanged across sixteen consecutive supports,
`y = 157` to `y = 172`, and then drops to exactly zero at `y = 173`.

**The route reaches zero excess at a support close to the cell count.** Not at
it: `y*/|Q_N|` is `1.033`, `0.874` and `0.935` at `N = 10^3, 10^4, 10^5`, so
the zero arrives before the columns outnumber the constraints at two of three
cutoffs and after at the third.

## 2. The reformulation, and why it is the reason 10^7 was reachable

The Chebyshev identity gives exactly

    B_c(N) - psi(N) = sum_{d >= 2} Lambda(d) [W_c(floor(N/d)) - 1]
                    = sum_{q in Q_N} w_q e_q,
    w_q = sum_{d >= 2, floor(N/d) = q} Lambda(d),   e_q = W_c(q) - 1 >= 0.

Solving in the variables `(c, e)` with objective `sum_q w_q e_q` puts every
objective coefficient and every variable in that sum at or above zero, so the
objective **is** the excess and nothing cancels. The factorial form asks a
float solver for a quantity near `1e4` as a difference of quantities near
`1e8`; this one does not.

The two identities that make the programmes the same are measured, not
assumed, at every cutoff before the solve is trusted:

| N | `|sum_q w_q - psi(N)| / psi(N)` | max relative defect of `sum_q w_q floor(q/j) = log(floor(N/j)!)` |
|---:|---:|---:|
| 10^3 | 1.1e-16 | 2.1e-16 |
| 10^4 | 0 | 3.2e-16 |
| 10^5 | 1.5e-16 | 4.9e-16 |
| 10^6 | 0 | 8.3e-16 |

## 3. The diagonal, extended

| N | y | cells | T* - psi(N) | E / N^{3/4} | local exponent |
|---:|---:|---:|---:|---:|---:|
| 10^3 | 31 | 61 | 41.282169 | 0.2321 | |
| 10^4 | 100 | 198 | 226.832690 | 0.2268 | 0.7399 |
| 10^5 | 316 | 630 | 1035.233934 | 0.1841 | 0.6593 |
| 10^6 | 1000 | 1998 | 6414.832164 | 0.2029 | 0.7921 |
| 3 x 10^6 | 1732 | 3462 | 14477.154080 | 0.2008 | 0.7409 |
| 10^7 | 3162 | 6322 | 30297.736768 | 0.1704 | 0.6134 |

The first four rows are the published ones and they reproduce to every printed
digit from a formulation that shares no objective with theirs. The last two are
new. `E / N^{3/4}` at `10^7` is `0.1704`, below the `0.18 to 0.23` band the
source reports over its four decades, and the local exponent between `3 x 10^6`
and `10^7` is `0.6134`.

Read the oscillation before reading the drift: `y = floor(sqrt N)` is an
integer that lands at a different distance from `sqrt N` at every cutoff, and
that alone moves this column. Which is the reason for the next section.

## 4. The grid, and what it does to the shape

`E sqrt(y) / N` is the quantity the conjectured shape says is a constant.

| N \ alpha | 0.30 | 0.35 | 0.40 | 0.45 | 0.50 | 0.55 |
|---:|---:|---:|---:|---:|---:|---:|
| 10^4 | 0.5244 | 0.4563 | 0.3538 | 0.3152 | 0.2268 | 0.0118 |
| 10^5 | 0.5076 | 0.4206 | 0.4017 | 0.2922 | 0.1840 | 0.0067 |
| 10^6 | 0.4577 | 0.4397 | 0.3714 | 0.3293 | 0.2029 | 0 |

Inside the range the conjecture is stated for (`y <= sqrt N`, i.e. `alpha <= 0.5`)
this falls by a factor of 2.3 to 2.8 as `y` grows. It is not a constant.

Least squares on the 18 positive rows with `alpha <= 0.5`:

| model | rms of the residual in `log E`, grid | same, diagonal only |
|---|---:|---:|
| free `a` and `b` (`a = 1.150`, `b = 0.878`) | 0.1148 | 0.0639 |
| conjectured `a = 1`, `b = 0.5` | 0.3602 | 0.1063 |
| `a = 1`, `b` free (`b = 0.679`) | 0.2475 | 0.0641 |
| `b = 0.5`, `a` free (`a = 0.968`) | 0.3518 | 0.0641 |

On the diagonal the four models are indistinguishable, three of them to three
decimal places. On the grid the conjectured shape is three times worse: a
typical relative miss of 43% against 12%.

**The fitted shape predicts the diagonal drift.** At `(a, b) = (1.150, 0.878)`,
`E sqrt(y) / N` on the diagonal decays like `N^{a - 1 + (0.5 - b)/2} = N^{-0.039}`,
so over the four decades from `10^3` to `10^7` it should fall by a factor
`0.70`. Measured: `0.1704 / 0.2298 = 0.74`.

**What this does and does not say.** The conjecture is a lower bound, and a
worse fit of an equality shape is not a counterexample to an inequality. What
the measurement does say is that `N / sqrt(y)` is not the shape of `T*`, so the
constant one reads off the diagonal is not a property of the family, and a
barrier argument aimed at that form is aimed at a curve the optimum does not
follow. If the fitted exponents persisted, `E sqrt(y) / N` would decrease
without limit and no fixed positive constant would survive; three decades of
grid do not establish that they persist, and this hunt does not claim it.

## 5. The staircase

Solving every integer support at `N = 10^3` gives 33 distinct optima across 76
supports, and at `N = 10^4`, 9.406483 unchanged from `y = 157` through
`y = 172`, then exactly zero at 173.

    N = 10^3, the last five plateaus
      y  42..47   10.346570
      y  48..50   10.283916
      y  51..55   10.247100
      y  56..62    2.426015
      y  63..77    0

Fourteen supports from 42 to 55 buy 1% of the excess; the next seven buy a
factor of 4.2; the next one buys the rest. The doors of
`hunts/quotient_certificate/RESULTS.md` record the support bound as the frozen
constant "with trade shape", and the trade, measured, is not smooth: most steps
along it are worth nothing and two are worth everything.

A step means a whole block of added columns changed no optimum at all. That is
a rank statement about the constraint matrix `floor(q/j)` and it is the shape
any law fitted through this family has to live with.

## 6. Where the excess reaches zero

Bisected on `y`, with each zero re-checked by evaluating the excess directly
from the returned coefficients:

| N | y* | `|Q_N|` | y*/`|Q_N|` | alpha of y* | last positive value |
|---:|---:|---:|---:|---:|---:|
| 10^3 | 63 | 61 | 1.0328 | 0.5998 | 2.426015 |
| 10^4 | 173 | 198 | 0.8737 | 0.5595 | 9.406483 |
| 10^5 | 589 | 630 | 0.9349 | 0.5540 | 28.364327 |

`hunts/quotient_certificate/RESULTS.md` section 3 refuted a dimension count
that inferred zero excess from having more columns than constrained cells, with
an exact `N = 27, y = 9` example whose minimum excess is `log 2`. That settles
that the count is not sufficient. These rows say the other half: at `N = 10^4`
and `10^5` the zero arrives while the columns are still outnumbered, `0.87` and
`0.93` of the cell count, so the count is not necessary either.

## 7. The doors

1. **Active constraints at the optimum.** Positivity binds on 31, 103, 321,
   1011, 1746 and 3193 cells at the six diagonal cutoffs, which is 0.504 to
   0.520 of the cells every time.

   That looks like a regularity and it is not one. A vertex of a linear
   programme has as many active constraints as it has variables, there are `y`
   of those, and the diagonal fixes `y = floor(sqrt N)` while the cell count is
   `2 floor(sqrt N) - 1`. Half is arithmetic. The measurement that is not
   forced is the small excess over `y` itself: binding/`y` runs
   `1.000, 1.030, 1.016, 1.011, 1.008, 1.010`, so the optimum is very slightly
   degenerate and by a shrinking amount. That is a door only if someone wants
   the degeneracy; it is recorded because the ratio looks meaningful and is
   not, which is worth one paragraph to anyone reading the same numbers.
2. **Frozen-constant inventory.**
   - **The support bound `y`**, now measured as a staircase rather than a
     trade. Relaxing it is worth nothing across most of its range and
     everything at two points. The door with real shape is not "raise `y`" but
     "find which columns are the two that matter", which is a question about
     the rank of `floor(q/j)` and is answerable exactly.
   - **Consecutive denominators `j = 1..y`.** Every certificate in this family
     takes its support as an initial segment. The staircase says most of that
     segment is inert, so a support chosen for rank rather than for being an
     interval is the obvious untested variation, and it costs one LP per
     candidate set.
   - **The attainable-cell relaxation itself.** It sits between the prime-aware
     `P*` and the all-cell `V*`. Its zero threshold (`alpha` about 0.55 to
     0.60) sits between theirs (`0.53` to `0.55` for `P*`, `0.75` to `0.77` for
     `V*`), which is the consistency check this hunt can offer and does.
   - **The `10^7` ceiling**, which is memory, not time: the constraint block is
     dense `2 sqrt(N) x y` and at `N = 10^8` it is 3.2 GB. A column-generation
     solve, which the source already uses for `V*`, moves that ceiling.
3. **Information class.** Everything above stays inside the floor-sum span and
   reads no prime locations. The two doors that read more are the ones the
   source already names, prime-awareness below `sqrt N` and an exactly-evaluable
   dictionary whose fluctuation is not sawtooth-shaped. This hunt adds a third
   that reads *less*: the staircase says the family's own information is
   concentrated in a few columns, so the question of how few is a compression
   question about the same data, not a request for more of it.
