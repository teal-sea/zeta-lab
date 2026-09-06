# Lean frontier for URMS2-051

## Status

The `HigherXi`, `LogMeanValue`, `ComplexLogMeanValue`, `TwoRangeWeights`,
`PowerMargin`, `MeanSquareAssembly`, `AristotleRAMS2`, and
`RC2PrefixAssembly` modules are the first formal slices of the rebuilt
level-two bridge. The Lean kernel accepts them with no `sorry` declarations.

This is not yet a Lean derivation of URMS2-051. The module intentionally stops
before the analytic inputs which remain absent from the formal tree.

## What is in the kernel

The modules contain:

1. The exact rational witness

   \[
   \alpha=51/100,\quad \delta=3/4,\quad
   \gamma=21/20,\quad \epsilon=1/100,
   \]

   including the margins `6/25`, `9/1000`, `1/4`, and `7399/10000`, and the
   far-cutoff coefficient ratio `14/5`.

2. The logarithmic frequency estimate

   \[
   \frac1{n+1}\leq \log(n+1)-\log n,
   \qquad
   \bigl(\log(n+1)-\log n\bigr)^{-1}\leq 2n.
   \]

3. Unit Fourier atoms and their conjugation and multiplication laws.

4. The finite Dirichlet polynomial

   \[
   P(t)=\sum_{n\in S}c_n e^{-it\lambda_n}
   \]

   and its exact pre-inequality expansion

   \[
   \overline{P(t)}P(t)
   =\sum_{m,n\in S}\overline{c_m}c_n
      e^{-it(\lambda_n-\lambda_m)}.
   \]

5. The corresponding integrated sharp-block identity. This identity retains
   every lower/upper cross term automatically.

6. The multiplicity inequality, both pointwise and summed over a finite zero
   set:

   \[
   N_{2,\mathrm{simple}}
   \geq 2N_2-\sum_jm_j^2.
   \]

7. Positivity of the exact rational downstream value and its enclosure

   \[
   0.01477 < L < 0.01478.
   \]

The final rational is currently an input numeral to Lean. Its reconstruction
from all 40 corrected coefficients and the analytic tail allowance remains a
separate formal obligation.

8. The exact sharp-block kernel bound

   \[
   |K_U(\theta)|\leq 2/|\theta| \qquad (\theta\ne0),
   \]

   and the arbitrary positive-integer logarithmic gap estimate

   \[
   \frac{n-m}{n}\leq \log n-\log m \qquad (1\leq m<n).
   \]

9. An elementary application-specific substitute for the general weighted
   Montgomery--Vaughan theorem. For real coefficient magnitudes it gives

   \[
   \sum_{m<n\leq W}
     \frac{2|c_m||c_n|}{\log n-\log m}
   \leq 3H_W\sum_{n\leq W}n c_n^2.
   \]

   Both orientations in the exact sharp-block expansion therefore cost at
   most

   \[
   6H_W\sum_{n\leq W}n c_n^2.
   \]

   The proof is finite and explicit. It allocates each pair to its two
   endpoint energies, reflects and translates the strict triangular rows,
   and bounds each resulting reciprocal row by `H_W`. Mathlib's bound
   `H_W <= 1 + log W` is also connected to the local definition. The extra
   logarithm is absorbed by the strict power margin in the analytic audit.

10. The complex-coefficient lift used by RC2, including both orientations of
    every strict pair, the exact logarithmic integral expansion, and the
    diagonal identity.

11. The exact two-range algebra at `sigma=3/2`: removal of the common phase,
    shared `log n` frequencies, lower and upper amplitudes, disjoint range
    partition, and the square weights

    \[
    n/x^2,\quad x^2/n^3
    \]

    for the diagonal and

    \[
    n^2/x^2,\quad x^2/n^2
    \]

    for the endpoint-weighted energy.

12. A finite square-sum partition and the assembled RC2 mean-square bound:

    \[
    \left|\int_U^{2U}|P(t)|^2dt
      -U\sum_{n\leq W}|c_n|^2\right|
    \leq 6H_W\sum_{n\leq W}n|c_n|^2.
    \]

    The same theorem is instantiated directly with the two-range coefficient.

13. The exact `6/25` exponent margin absorbs every fixed logarithmic power and
    the actual cutoff envelope `1+(21/20) log H`.

14. Exact finite Abel summation and both RC2 endpoint-energy consequences.
    Aristotle supplied a lower bound and a cutoff-independent inverse-square
    tail with constant `10`:

    \[
    \sum_{X<n\leq W}\frac{|a(n)|^2}{n^2}
    \leq \frac{10C(1+\log X)}{X}.
    \]

    Multiplication by `X^2` gives the required `O(CX(1+log X))` upper-range
    endpoint energy uniformly in `W`. The lower `n^2` sum has the matching
    order after division by `X^2`. A proposed independent improvement to
    constant `4` failed a clean merged-tree build and is not retained.

15. Conditional assembly of the RAMS2 prefix bound into the finite RC2
    mean-square estimate. If

    \[
    \sum_{n\leq N}|a(n)|^2\leq C N(1+\log N),
    \]

    then for natural `1 <= X <= W` the exact two-range endpoint energy obeys

    \[
    E_{X,W}\leq 11 C X(1+\log X),
    \]

    uniformly in `W`, and the finite off-diagonal remainder obeys

    \[
    |R_{U,X,W}|\leq
      66 H_W C X(1+\log X).
    \]

    The arithmetic prefix estimate remains a hypothesis. The new module does
    not assert the connected-cluster asymptotic or contour transfer.

16. A finite signed-to-nonnegative majorant for the connected two-colour
    matching mass. Pointwise bounds on every monomer and dimer weight now lift
    to the connected mass on one support and to its finite prefix sum. A
    second finite step bounds the connected mass by the square of the explicit
    all-matching polynomial

    \[
    \left(\sum_{0\leq a\leq r/2}N(r,a)w_a\right)^2,
    \qquad
    N(r,a)=\frac{r!}{2^a a!(r-2a)!}.
    \]

    The exact matching-slice cardinality theorem now discharges the
    concrete-family fibre count. The one-matching weight bound remains the
    explicit finite interface. The prime-simplex,
    support-density, and uniform-growth estimates remain analytic hypotheses;
    this step does not establish the RAMS2 asymptotic.

17. Local structure of a two-colour matching union. Each colour contributes
    at most one incident edge at a vertex, so the coloured degree is at most
    two, and distinct incident union edges have opposite colours. The existing
    cut predicate forces a connected pair on at least two support vertices to
    cover the full support, hence every support vertex has coloured degree one
    or two. Degree one is the endpoint case; degree two supplies exactly one
    edge of each colour. If every vertex has degree two, both colours are
    perfect matchings with equal edge counts and the support cardinality is
    even. This is the finite alternating path/even-cycle constraint, not a
    global component-classification theorem.

18. The abstract weighted-simplex induction that creates the exact
    `j! (2j-1)!` denominator. If an order-`j` nonnegative mass obeys the
    one-label insertion recurrence

    \[
    (j+1)(2j)(2j+1)A_{j+1}\leq B A_j,
    \]

    then Lean derives

    \[
    A_j\leq \frac{A_1 B^{j-1}}{j!(2j-1)!}.
    \]

    The prime-specific Chebyshev/insertion estimate establishing this
    recurrence for distinct-prime logarithmic weights remains an analytic
    input; the abstract theorem does not assert it.

19. The concrete finite distinct-prime logarithmic mass

    \[
    A_j(X)=\sum_{\substack{|S|=j\\\prod_{p\in S}p\leq X}}
      \left(\sum_{p\in S}\log p\right)^2
      \prod_{p\in S}(\log p)^2.
    \]

    Marking one prime in an order-`j+1` support is proved to count that support
    exactly `j+1` times. The resulting deletion mass is connected to the
    abstract weighted-simplex theorem, so a first-order bound and the single
    prime-specific estimate

    \[
    (2j)(2j+1)D_j(X)\leq B A_j(X)
    \]

    imply the full `j!(2j-1)!` denominator. Establishing this inequality from
    a weighted Chebyshev estimate remains the analytic input; it is not
    asserted by the Lean module.

20. **The `hprime` gate is retargeted, and the reason is measured**
    (2026-08-12). Two independent derivation attempts and one adversarial pass
    agree: item 19's inequality **cannot be proved as stated** by a Chebyshev
    route, and the obstruction is not a missing trick.

    *The recurrence is asymptotically tight.* Measured for `X` from `10^2` to
    `10^7` (SPF sieve, exact enumeration of every squarefree support): the
    ratio `(j+1)(2j)(2j+1)A_{j+1}/A_j` is maximal at `j = 1` at every cutoff,
    strictly decreasing in `j`, and

    \[
    r_1(X)=12A_2/A_1=(\log X)^2-2\log X+O(1)=(1-o(1))(1+\log X)^2 .
    \]

    The extremal family is pairs `{p,q}` with `pq` near `X`, whose weight has
    the `Beta(2,2)` split profile. Measured `D` with
    `B^*(X) <= D(1+\log X)^2`: 0.383 at `10^2` rising monotonically to 0.724
    at `10^7`; a linear-in-log envelope is **refuted** (that ratio grows
    without bound). So `(1+\log X)^2` is exactly the right order and any
    absolute `D` must satisfy `D >= 1`.

    Consequently `hprime` needs an order-uniform *lower* bound on `A_j` with a
    matching constant. Chebyshev is an upper bound; a route through separate
    upper and lower bounds inherits a `(C/c)^j` mismatch incompatible with an
    absolute `D`. Recorded as a dead route, with its mechanism.

    *What survives, and it is what the mathematics consumes.* Nothing
    downstream uses the recurrence, `RAMS2-CLUSTER.md` §6 consumes only the
    endpoint display. The display survives domination, so the gate becomes a
    plain domination against an explicit majorant:

    \[
    M_j(X)=c\,B^{j-1}X(1+\log X)^{2j+1}/\bigl(j!(2j-1)!\bigr),
    \]

    which satisfies the insertion recurrence **with equality** at
    `B(1+\log X)^2`: the factorial denominator is built so that
    `(j+1)(2j)(2j+1)` is exactly `denominator(j+1)/denominator(j)`. So the
    tightness that defeats `hprime` on the true masses is precisely the
    equality the majorant enjoys. Kernel-checked in
    `ZetaLean/MajorantBypass.lean`: `mass_le_of_dominated_majorant`,
    `powerMajorant_step` (the equality), and
    `distinctPrimeLogMass_le_of_dominated`.

    Both derivation routes then proved `A_j <= M_j` on paper, by integral
    comparison in log coordinates, the argument
    `RAMS1-ATTACK.md` §4.2 already sketches. Route A gives `D = \log 16
    = 2.7726`; route B gives `D = 60\log 4 = 83.18`. Route A is the one to
    formalise. Every intermediate inequality of both chains was verified
    numerically at `X = 250` and `X = 5000`, and both dominate the measured
    `r_1` with margin, so the retarget is not a weakening of the endpoint.

    **The remaining formal obligation is therefore exactly one hypothesis**,
    `hdom : A_j(X) <= powerMajorant c B X j`, a domination, not tight, and
    strictly weaker than `hprime`. Its Lean cost is real analysis: an Abel
    comparison against `\int_0^V te^tg(t)\,dt` and the exact identity
    `\int_0^V te^tE_j(V-t)\,dt = E_{j+1}(V)` by Fubini on a triangle.

    **Both chains are captured in full in `HPRIME-ROUTES.md`**, every lemma
    with its formalisation cost, every numeric margin, and both obstruction
    arguments including route B's measured impossibility of any subset-local
    charging scheme (it crosses at `X ~ 2e4` and diverges like `sqrt(X)/log X`).
    They existed only in a transient agent transcript; do not re-derive them.

    Already unconditional and kernel-checked in `ZetaLean/ChebyshevBounds.lean`:
    `theta_le_mul_log_four` (Mathlib's `Chebyshev.theta_le_log4_mul_x`,
    re-expressed over this tree's index set), `theta_sq_le` and
    `theta_pow_succ_le` (absent from Mathlib), the base bound
    `distinctPrimeLogMass_one_le : A_1(X) <= (\log X)^3X\log 4`, and
    `logSum_le_log_of_mem_distinctPrimeSupports`.

## First missing analytic inputs

The exact dependency boundary is now:

1. The RAMS2 connected-cluster square-density asymptotic, including uniformity
   on the fixed ratio band through `14/5`.
2. The marked-cluster derivative estimate used for height freezing.
3. The smoothed contour transfer from the level-two arithmetic resolvent to
   the zero statistic.
4. Reconstruction of the exact downstream rational from the 40 coefficient
   data and its tail bound inside Lean.

The spacing-sensitive finite mean-value input, complex lift, two-range weight
algebra, diagonal/off-diagonal assembly, partial-summation endpoint bounds, and
logarithmic-loss absorption are no longer open formal dependencies for this
application. The finite harmonic-loss theorem is weaker than the sharp general
Montgomery--Vaughan inequality, but it is strong enough for the strict exponent
margin recorded in `URMS2-051.md`.

## Reproduction

```bash
cd lean
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.HigherXi
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.LogMeanValue
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.MeanSquareAssembly
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.AristotleRAMS2
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.ClusterMajorant
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.MatchingPairStructure
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.WeightedSimplex
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.PrimeSimplex
PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.RC2PrefixAssembly
PATH="$HOME/.elan/bin:$PATH" lake build
```
