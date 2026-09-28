# Mission: scale-dependent coefficients and arithmetic-cap savings

Checkpoint `paid-scaling-01`, base
`4efa72ad70a1e535709c33d0eded886d29c19274`.

The target is an explicit family of coefficients for which the complete paid
upper bound is `N+O(sqrt(N) log(N)^2)` uniformly as integer `N` grows.
An exact finite improvement, a bound conditional on an unproved cancellation
estimate, or a restricted obstruction is a useful result but not that target.

The approved pass has two parts: construct a scale-dependent family, and
independently bound the saving available from perfect-power capacities.
The main writer owns this directory and its eventual test and case-log entry.
The cap reviewer is read-only, anchored at the base above. No Ostoyae,
Fulcrum, paid service, Lean run, or large optimization campaign is involved.

First construction: for integer support `y>=2`, take `c_j=mu(j)` for
`j<y`, and `c_y=-y sum_{j<y}mu(j)/j`. This has exact coverage on integer
`1<=q<y` and zero harmonic drift. The new input relative to the old
pointwise-ceiling experiments is that uncovered cells are allowed and fully
priced, including a comparison with perfect-power capacities. No assumption
of global positivity or full-lift coverage is made for this family.

First finite discriminator: exact floor identities and complete costs at
`N=144,576,2304,9216,36864`, with `y=sqrt(N)`. Compare against the old
base-6 truncated lift at support no greater than `y`. Any further experiment
must distinguish a named mathematical alternative, not merely add a larger N.

Second discriminator, added after the initial five-cutoff diagnostic: average
the balanced prefixes over `ceil(y/2)<=h<=y`. This tests whether spreading the
balancing correction reduces the complete cost relative to putting it all at
`j=y`. The cutoff set stays unchanged and no numerical optimizer is introduced.

Third discriminator: uniform averaging worsened four of the five complete
costs. Select the least complete cost among the same finite cutoff range
instead. The comparison uses only integers `d<=N/ceil(y/2)` because the
common large-d contribution cancels exactly. This is a bounded enumeration
of at most 97 explicitly given cutoffs, not a free-coefficient optimization.

Fourth discriminator, prompted by the measured decomposition: at the largest
cutoff the factorial part is only `N+9.667993`, whereas the perfect-power
repair bill is `867.584200`. Keep the coefficients and N values unchanged;
exclude ordinary composites witnessed by divisibility by 2, then by
2,3,5,7. Prime powers of those primes retain their correct cap. This changes
the arithmetic information, not the cutoff grid or coefficient search.

An unavailable broad cancellation estimate is not a universal no-go. Existing
results and output hashes remain unchanged. Preserve new outputs separately.

```huntspec
id: paid_shortfall_scaling
question: Can scale-dependent balanced coefficients lower the complete paid excess, and how much can perfect-power caps contribute?
frontier: The fixed-seed truncation bill is controlled but its linear excess survives; the N14 capacity improvement has no established scaling law
proposed_attack: Analyze balanced Mobius-prefix coefficients with paid deficits and independently derive a uniform perfect-power saving bound
dead_routes:
  - inferring a uniform estimate from the N14 exact comparison
  - hiding growing coefficient mass in a fixed-seed error constant
  - assuming positivity for a balanced Mobius prefix
required_oracles:
  - exact rational floor and divisor identities
  - independent integer factorization for finite Mangoldt weights
  - independently implemented logarithm enclosures
kill_conditions:
  - a capacity falls below a true prime-power mass
  - a full-cost inequality omits a positive term
  - the proposed family fails its explicit uniform hypotheses
agents_may:
  - derive and challenge exact candidate bounds
  - run bounded deterministic discriminating checks
  - preserve restricted obstructions without closing broader methods
agents_may_not:
  - claim RH or novelty from finite experiments
  - edit earlier research evidence
  - use external services or large searches
```
