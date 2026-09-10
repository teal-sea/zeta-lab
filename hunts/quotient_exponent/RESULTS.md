# Results: the barrier law survives the grid; the constant is what moves

**2026-09-10. Grade: measured (floating LP, HiGHS dual simplex), with every
optimum recomputed from the returned coefficients through the constraint
definition.** No asymptotic statement is established and nothing here bears on
RH (`docs/08`).

**This page was rewritten after an independent adversarial audit.** The audit is
in `AUDIT.md`: fifteen attacks, four of which landed, and one of the four took
the first version's headline down. That version said the conjectured shape
`E >= c N / sqrt(y)` "is not the shape of `T*`". It is. What the grid shows is
that the **constant** in front of it depends on the support exponent, which
`BARRIER.md` had already said in its own words, and which the first version's
model comparison hid by pitting a three-parameter free fit against a
one-parameter reading of the conjecture.

## 1. The verdict

    reproduced, four published diagonal values      to 14-15 significant digits
    new diagonal rows                               N = 3 x 10^6 and 10^7
    T*(sqrt N, N) - psi(N) at 10^7                  30297.736768, 0.1704 N^{3/4}
    published reading                               "(0.18 to 0.23) N^{3/4}"
    the conjectured inequality on all 20 grid rows  E >= 0.1704 N/sqrt(y), holds
    the published constant for T*                   0.2, which is 15% too large
                                                    at the 10^7 diagonal point
    zero excess first reached at y* =               63, 173, 589, 1938
                                                    for N = 10^3 .. 10^6
    alpha* = log y* / log N                         0.5998, 0.5595, 0.5540, 0.5479

Three things this hunt adds, and one it withdraws.

**Withdrawn:** that the conjectured shape is wrong. Section 4.

**The ladder, extended two decades**, with the first constant that falls outside
the published band.

**The excess is a staircase in `y`**, not a curve, with long plateaus and a
collapse to exactly zero at a support this hunt locates for four cutoffs.

**What keeps the excess positive is the cells with no prime mass at all.** Only
40, 99 and 275 of the 61, 198 and 630 attainable cells carry weight at
`N = 10^3, 10^4, 10^5`, and `W = 1` on those alone is satisfiable far below
`y*`. The binding requirement is `W >= 1` at the zero-weight cells.

## 2. The reformulation, and what it is not

The Chebyshev identity gives exactly

    B_c(N) - psi(N) = sum_{q in Q_N} w_q e_q,   w_q >= 0,  e_q = W_c(q) - 1 >= 0,

so solving in `(c, e)` with objective `sum_q w_q e_q` makes the objective the
excess itself. The identities that make the two programmes the same are measured
at every cutoff before the solve is trusted:

| N | `|sum_q w_q - psi(N)| / psi(N)` | max relative defect of `sum_q w_q floor(q/j) = log(floor(N/j)!)` |
|---:|---:|---:|
| 10^3 | 1.1e-16 | 2.1e-16 |
| 10^4 | 0 | 3.2e-16 |
| 10^5 | 1.5e-16 | 4.9e-16 |
| 10^6 | 0 | 8.3e-16 |
| 3 x 10^6 | 0 | 2.3e-15 |
| 10^7 | 0 | 2.4e-15 |

**The first version claimed this reformulation was necessary, and that is
false.** It argued that the factorial objective asks a float solver for a
quantity near `1e4` as a difference of quantities near `1e8`, and that this one
does not. The arithmetic is right and the consequence is not: solved in the
factorial form, the same optimum comes back at

| N | factorial form | reformulated | relative difference |
|---:|---:|---:|---:|
| 10^3 | 41.28216944295832 | 41.2821694429594 | 2.7e-14 |
| 10^4 | 226.83268961231443 | 226.8326896123210 | 2.9e-14 |
| 10^5 | 1035.2339342959604 | 1035.2339342959353 | 2.4e-14 |
| 10^6 | 6414.83216371364 | 6414.83216371319 | 7.0e-14 |

HiGHS absorbs the cancellation. The reformulation is better conditioned in
principle, it is what these numbers were computed with, and it is not the reason
`10^7` was reachable. The reason is stated in door 2 and it is memory.

## 3. The diagonal, extended

| N | y | cells | T* - psi(N) | E / N^{3/4} | local exponent |
|---:|---:|---:|---:|---:|---:|
| 10^3 | 31 | 61 | 41.282169 | 0.2321 | |
| 10^4 | 100 | 198 | 226.832690 | 0.2268 | 0.7399 |
| 10^5 | 316 | 630 | 1035.233934 | 0.1841 | 0.6593 |
| 10^6 | 1000 | 1998 | 6414.832164 | 0.2029 | 0.7921 |
| 3 x 10^6 | 1732 | 3462 | 14477.154080 | 0.2008 | 0.7409 |
| 10^7 | 3162 | 6322 | 30297.736768 | 0.1704 | 0.6134 |

The first four are the published rows. They agree with the source to 14 and 15
significant digits against the exact-rational pins in its `DUAL_WITNESS.md`
(`41.28216944295942` here against `41.28216944295939183...`), which is float
agreement and not reproduction "to every printed digit", as the first version of
this page said. The last two rows are new.

`E / N^{3/4}` at `10^7` is `0.1704`, below the `0.18 to 0.23` band the source
reports over its four decades. That is the one number here that contradicts a
published reading, and it does so by 15 percent at one point.

## 4. The grid, and the headline that was wrong

`E sqrt(y) / N` is what the conjectured shape says is constant:

| N \ alpha | 0.30 | 0.35 | 0.40 | 0.45 | 0.50 |
|---:|---:|---:|---:|---:|---:|
| 10^4 | 0.5244 | 0.4563 | 0.3538 | 0.3152 | 0.2268 |
| 10^5 | 0.5076 | 0.4206 | 0.4017 | 0.2922 | 0.1840 |
| 10^6 | 0.4577 | 0.4397 | 0.3714 | 0.3293 | 0.2029 |
| 10^7 | | | 0.3662 | 0.3460 | 0.1704 |

It is not constant. It falls by a factor of 2.1 to 2.8 as `y` grows inside the
conjecture's own range.

**The first version read that as the shape being wrong. That reading does not
survive a like-for-like comparison.** `BARRIER.md` section 3 states the
conjecture with a moving constant, in its own words: away from `y = sqrt(N)` the
constant moves but the exponent does not. Fitted that way, on the same 20 rows
with `alpha <= 0.5`:

| model | parameters | rms of the residual in `log E` |
|---|---:|---:|
| free `a`, `b`, constant `C` | 3 | 0.1258 |
| conjectured `(1, 1/2)`, constant `C` | 1 | 0.3435 |
| **conjectured `(1, 1/2)`, `log C` linear in `alpha`** | **2** | **0.1198** |
| conjectured `(1, 1/2)`, `log C` linear in `alpha` and `log N` | 3 | 0.1187 |
| free `a`, `b`, `log C` linear in `alpha` | 4 | 0.1173 |

**The conjectured exponents fit better than the free ones, with one parameter
fewer.** And once the constant is allowed to move, the free exponents come back
to `a = 1.042`, `b = 0.609`, near `(1, 0.5)` rather than the `(1.159, 0.874)`
the first version reported. The `2.7 times worse` figure it quoted compared a
three-parameter model against a one-parameter one.

**The conjecture is a lower bound, and every measured point satisfies it.**
`E >= 0.1704 N / sqrt(y)` holds at all 20 rows. The only thing the measurement
touches is the published constant `0.2`, at the single new `10^7` diagonal point,
by 15 percent. That is the measurement's actual bite and the first version never
stated it.

What remains true, and is worth keeping: **on the diagonal alone none of these
models can be told apart**, because the diagonal only ever constrains
`a - b/2`. Separating them needs the grid. The grid then says the exponents are
where the conjecture puts them and the constant is not.

## 5. The staircase

Every integer support at `N = 10^3`: 33 distinct optima across 76 supports.

    y  42..47   excess 10.346570
    y  48..50   excess 10.283916
    y  51..55   excess 10.247100
    y  56..62   excess  2.426015
    y  63..77   excess  0

Fourteen supports from 42 to 55 buy 1% of the excess. The next seven buy a factor
of 4.2. The next one buys the rest. At `N = 10^4` the value `9.406483` holds
unchanged across sixteen consecutive supports, `y = 157` to `172`, then zero at
173.

`hunts/quotient_certificate/RESULTS.md` names the support bound as its one frozen
constant "with trade shape". Measured, the trade is not a curve. A plateau means
a block of added columns changed no optimum, which is a rank statement about
`floor(q/j)`, and it says the door is not "raise `y`" but "find which columns did
the work".

## 6. Where it reaches zero, and what holds it up

| N | y* | attainable cells | ratio | alpha* | cells with prime mass |
|---:|---:|---:|---:|---:|---:|
| 10^3 | 63 | 61 | 1.033 | 0.5998 | 40 |
| 10^4 | 173 | 198 | 0.874 | 0.5595 | 99 |
| 10^5 | 589 | 630 | 0.935 | 0.5540 | 275 |
| 10^6 | 1938 | 1998 | 0.970 | 0.5479 | |

`alpha*` falls monotonically, by about `0.007` per decade.

`hunts/quotient_certificate` refuted a dimension count that inferred zero excess
from having more columns than constrained cells, with an exact `N = 27, y = 9`
example whose minimum excess is `log 2`, so the count is not sufficient. Two of
these four rows have the zero arriving while the columns are still outnumbered,
so it is not necessary either.

**But `|Q_N|` is the wrong denominator.** Only 40, 99 and 275 of the 61, 198 and
630 attainable cells carry any prime mass, and `W = 1` on those alone is
satisfiable well below `y*`. What keeps the excess positive up to `y*` is the
requirement `W >= 1` at the cells with **no weight at all**: cells that
contribute nothing to the objective and constrain the feasible set anyway. That
is a sharper statement than a ratio against a mixed denominator, and it is the
door section 7 ranks first.

## 6a. The door, tested: consecutive support is what the barrier is about

Doors item 2 below names "a support chosen for rank rather than for being an
interval" as the obvious untested variation. A scouting pass in the same session
reported that freeing the positions reaches zero excess. It does, and the
interesting version of that is not the obvious one.

**Freeing the positions with no limit on how many says nothing.** Allow every
`j <= N/2` and the excess is zero, but with 5000 columns available at `N = 10^4`
that is unsurprising: the threshold run above already reaches zero at 173
consecutive columns.

**At a comparable support size it says a lot.** Excess is `sum_q w_q e_q` with
every term non-negative, so zero excess is exactly `W(q) = 1` at every cell
carrying prime mass and `W(q) >= 1` at the rest. Minimising the coefficient mass
under that and counting the positions the optimum uses:

| N | sqrt(N) | free positions for zero excess | max j used | mass | consecutive `y*` |
|---:|---:|---:|---:|---:|---:|
| 10^3 | 31 | **35** | 201 | 45.5 | 63 |
| 10^4 | 100 | **109** | 1251 | 114.7 | 173 |
| 10^5 | 316 | **285** | 14286 | 389.1 | 589 |

**Freely chosen positions reach zero excess on roughly half the support that
consecutive ones need**, and at `N = 10^5` on fewer than `sqrt(N)` of them.
Against the consecutive family at `y = sqrt(N)`, where the excess is 41.28,
226.83 and 1035.23, the same count of positions chosen freely gives zero.

**At `N = 10^3` this is exact.** The float solution rounded to rationals over
`10^9` was re-checked with Python integers on all 61 attainable cells: no cell
has `W(q) < 1`, and `W(q) = 1` at all 40 prime-mass cells, so the excess is
exactly zero. The `10^4` and `10^5` rows are float LP values whose reported
minimum slack is slightly negative (`-8e-13`, `-6e-12`) and are **measured
only**; they have no exact witness here.

**What it costs, and why this is not a free win.** The positions are few but
they reach far: `max j` is `201`, `1251`, `14286`, about `N^{0.77}`, `N^{0.77}`
and `N^{0.83}`. The source's own criterion asks for excess and mass both under
`N^{1/2+eps}`, and both hold here (`mass ~ N^{0.52}` at `10^5`), but it says
nothing about how far the support may reach, and evaluating such a certificate
costs `max j`, not the count.

So the barrier this hunt measured is a property of **consecutive** support. It
is not a property of the floor-sum family, and the conjecture as stated does not
speak to the family with free positions, which is a different object and not one
these three points settle.

## 7. The doors

1. **Active constraints at the optimum.** Positivity binds on 31, 103, 321,
   1011, 1746 and 3193 cells at the six diagonal cutoffs, which is `0.504` to
   `0.520` of the cells every time. That looks like a regularity and is not: a
   vertex has as many active constraints as variables, there are `y` of those,
   and the diagonal fixes `y = floor(sqrt N)` while the cell count is
   `2 floor(sqrt N) - 1`. Half is arithmetic. What is not forced is the small
   excess over `y`: binding/`y` runs `1.000, 1.030, 1.016, 1.011, 1.008, 1.010`.
   **The binding constraint that is not arithmetic is the zero-weight cells**,
   per section 6: they cost nothing in the objective, they are more than half the
   constraint set, and they are what the support has to grow past.
2. **Frozen-constant inventory.**
   - **The zero-weight cells**, newly identified as the binding thing. The trade:
     they are exactly the cells `floor(N/d)` for `d` composite, and dropping them
     is not free, because the Chebyshev identity needs `W >= 1` wherever
     `Lambda(d) > 0`, which is where they are not. The question with real shape
     is how much of the excess survives if positivity is required only on a
     sublattice, and it is one LP per choice.
   - **The support bound `y`**, now measured as a staircase. Most of its range is
     inert and two points are worth everything. "Find which columns matter" is a
     rank question about `floor(q/j)` and is answerable exactly.
   - **Consecutive denominators `j = 1..y`, now tested** (section 6a). Freely
     chosen positions reach zero excess on roughly half the support consecutive
     ones need, exactly at `N = 10^3` and measured at `10^4` and `10^5`. The
     trade is reach: the positions run out to about `N^{0.8}`, and evaluation
     cost follows the largest one rather than the count. The next question is
     the one this does not answer, whether a support bounded in BOTH count and
     reach still beats the interval.
   - **The `10^7` ceiling, which is memory.** The constraint block is dense
     `2 sqrt(N) x y`, which at `N = 10^8` is `1.6 GB` before the solver's own
     copy, and `lp.py` builds a CSR copy of it, which doubles that. Column
     generation, which the source already uses for `V*`, is the way past it.
3. **Information class.** Everything stays inside the floor-sum span and reads no
   prime locations. The doors that read more are the source's own: prime
   awareness below `sqrt N`, and an exactly evaluable dictionary whose
   fluctuation is not sawtooth-shaped. This hunt adds one that reads **less**:
   the staircase and the zero-weight cells both say the family's information is
   concentrated in a small part of its own constraint set, so how small is a
   compression question about the same data.
