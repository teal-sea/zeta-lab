# Mission: finite saturation of the local paid repair

This hunt evaluates one finite arithmetic diagnostic at
`N=144,576,2304,9216,36864`. It imports the balanced-prefix cutoff choice
from `hunts/paid_shortfall_scaling/scaling.py` unchanged. For the selected
support `y`, its local repair range is `2 <= d <= X=floor(N/y)`.

For each such range, test every prime through `floor(sqrt(X))`. Removing all
powers of a tested divisor exposes every ordinary composite and assigns it
zero local capacity. Prime powers retain their perfect-power capacity. The
diagnostic checks this finite statement against the independently factored
Mangoldt vector, then prices the exact factorial discrepancy, exact repair,
removed ordinary-composite overpayment, remaining prime-power surplus, and
complete total. It records exact prime-log coefficient vectors separately from
the two directed logarithm-enclosure evaluations.

This is finite evidence only. It makes no asymptotic, RH, or novelty claim.

```huntspec
id: paid_shortfall_saturation
question: Does full trial division through floor(sqrt(floor(N/y))) make the local repair cap equal the Mangoldt weight for the five fixed selected-prefix cases?
frontier: Fixed small-prime exclusions leave rough ordinary composites in the local repair bill; the earlier finite endpoint cases do not test complete local saturation
proposed_attack: Use the already-selected balanced prefixes and exhaust the finite small-prime test range while retaining prime powers
dead_routes:
  - changing the coefficient family or cutoff selection
  - treating five finite cases as an asymptotic estimate
  - replacing exact prime-log vectors with rounded decimal arithmetic
required_oracles:
  - exact rational floor and divisor identities
  - independent trial factorization for Mangoldt vectors
  - two directed logarithm enclosure implementations
kill_conditions:
  - an ordinary composite survives the finite local saturation test
  - a prime power loses local capacity
  - a saturated local cap differs from its Mangoldt vector
agents_may:
  - run the five deterministic finite cases
  - record exact vectors and numerical enclosure checks
  - compare the named paid-cost components
agents_may_not:
  - modify source coefficients or cutoff selection
  - infer a general rate from this finite diagnostic
  - claim RH or novelty
```
