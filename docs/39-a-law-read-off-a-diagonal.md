# 39. A law read off a diagonal, and a headline read off a bad comparison

**Hunt #121, `hunts/quotient_exponent/`.** Measurements and doors in
`hunts/quotient_exponent/RESULTS.md`; the audit that rewrote this page's
conclusion in `AUDIT.md`.

Grade: **measured**. No asymptotic statement is established. Nothing here bears
on RH (`docs/08`).

## 1. The object

There is an elementary route to prime-counting bounds that this laboratory has
been pricing. A certificate is a finite floor sum
`W(t) = sum_{j<=y} c_j floor(t/j)` required to satisfy `W >= 1`, and it yields a
bound on `psi(N)` whose excess is what the route costs. The smallest excess any
such certificate can have, at a cutoff `N` and support bound `y`, is the value of
a linear programme, and the relaxation that only requires positivity at the
attainable quotients is called `T*`.

The published reading is `T* = (0.18 to 0.23) N^{3/4}` over four decades, with a
barrier conjecture `E >= c N / sqrt(y)` "to be read for `T*` as well, with the
constant `0.2`".

Every published value sits on the diagonal `y = floor(sqrt N)`. On that line `y`
and `N` move together, so the data only ever constrains one combination of the
two exponents. That is a real limitation and it is what this hunt set out to fix.

## 2. What the grid found

Extending the ladder to `10^7` puts `T*/N^{3/4}` at `0.1704`, below the
published band. And `E sqrt(y) / N`, the quantity the conjectured shape says is
constant, falls by a factor of 2.1 to 2.8 as `y` grows inside the conjecture's
own range.

The first version of this page read that as the shape being wrong. It fitted
`log E = log C + a log N - b log y`, got `(1.159, 0.874)` against the conjectured
`(1, 0.5)`, found the conjectured shape 2.7 times worse on the grid and
indistinguishable from everything else on the diagonal, and concluded that
`N / sqrt(y)` is not the shape of the optimum.

## 3. Then an adversary read the comparison

Fifteen attacks. Four landed. One of them was this:

**The comparison was not like for like.** It pitted a three-parameter free power
law against a one-parameter reading of the conjecture. But `BARRIER.md` states
the conjecture with a moving constant, in its own words: away from
`y = sqrt(N)` the constant moves and the exponent does not. Fitted that way, on
the same 20 rows:

| model | parameters | rms of the residual in `log E` |
|---|---:|---:|
| free `a`, `b`, constant `C` | 3 | 0.1258 |
| conjectured `(1, 1/2)`, constant `C` | 1 | 0.3435 |
| **conjectured `(1, 1/2)`, `log C` linear in `alpha`** | **2** | **0.1198** |
| free `a`, `b`, `log C` linear in `alpha` | 4 | 0.1173 |

The conjectured exponents fit better than the free ones with one parameter
fewer. And once the constant is allowed to move, the free exponents come back to
`a = 1.042`, `b = 0.609`, near where the conjecture puts them.

**The conjecture is a lower bound and every measured point satisfies it.**
`E >= 0.1704 N/sqrt(y)` holds at all twenty rows. The only thing the measurement
touches is the published constant `0.2`, at one point, by 15 percent. That is
the whole bite, and the first version never stated it while claiming something
much larger.

Three more attacks landed, all on stated reasons rather than on numbers:

- **The reformulation's justification was false.** The page argued that the
  factorial objective asks a solver for a quantity near `1e4` as a difference of
  quantities near `1e8`, and that rewriting it was why `10^7` was reachable.
  Measured, the factorial form returns the same optimum to `2.7e-14`. The solver
  absorbs the cancellation. The reason `10^7` was reachable is memory, which the
  same page said in its own doors section two screens later.
- **"Reproduces to every printed digit" was not measured.** The source prints two
  of its values to 40 digits; these floats agree to 14 and 15.
- **A conclusion was false over half its own grid.** "If the fitted exponents
  persisted, no fixed positive constant would survive" holds only for
  `alpha > 0.425`; below that the same fit predicts the opposite.

And one correction went the other way. The audit found that claim about the
zeros is **understated**: exact rational witnesses exist for them, and exact
Farkas certificates for the strict positivity one support below, so that part of
the hunt sits a rung higher than the page had claimed for it.

## 4. What survives, and is new

**The excess is a staircase in `y`.** At `N = 10^3`, 33 distinct optima across 76
supports; fourteen supports from 42 to 55 buy 1% of the excess, the next seven
buy a factor of 4.2, and the next one buys the rest. At `N = 10^4` the value
`9.406483` holds unchanged across sixteen consecutive supports and then drops to
exactly zero.

**Zero excess is reached at a locatable support.** `y* = 63, 173, 589, 1938` for
`N = 10^3` to `10^6`, with `alpha* = log y*/log N` falling monotonically
`0.5998, 0.5595, 0.5540, 0.5479`.

**And the thing that holds the excess up is not the thing anyone was counting.**
Only 40, 99 and 275 of the 61, 198 and 630 attainable cells carry any prime mass
at all, and `W = 1` on those alone is satisfiable far below `y*`. What keeps the
excess positive is the requirement `W >= 1` at the cells with **no weight**:
cells that contribute nothing to the objective and constrain the feasible set
anyway. That is the door the hunt now ranks first, and neither version of this
page would have found it without an audit that asked whether `|Q_N|` was the
right denominator.

## 5. What this episode is

Not an arithmetic error. Every published number reproduced, from an
independently written programme. Every new number stands. What failed was a
comparison, and it failed in the most ordinary way a comparison fails: the model
under test was given fewer degrees of freedom than the model doing the testing,
and the difference was reported as a finding.

The conjecture's own source had already recorded the moving constant. Reading
that sentence would have prevented the whole headline. An adversary read it.
