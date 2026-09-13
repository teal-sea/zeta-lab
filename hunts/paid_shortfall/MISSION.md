# Mission: a constructive paid-shortfall bound

Base: `a3acc741396940273ec388548d52752f839593c3`.

Continue the paid-shortfall idea preserved in the September 7 conversation.
The ultimate target remains a uniform upper bound on `psi(N)-N`. This bounded
attempt asks whether early truncation of an explicit factorial certificate
has a controllable complete cost. It does not treat a small finite excess
over measured `psi(N)` as an estimate for `psi(N)-N`.

For `Q_N={floor(N/d):2<=d<=N}`, use
`W_c(q)=sum_j c_j floor(q/j)`, `B_N(c)=sum_j c_j log(floor(N/j)!)`,
and `w_q=sum_{floor(N/d)=q} log d`. The paid bound is
`C_N(c)=B_N(c)+sum_q w_q max(0,1-W_c(q))`.

Write scope: this directory and `tests/test_paid_shortfall.py`, plus its
case-log entry and generated `CONTEXT.md`. Preserve earlier research files.
No core changes, optimizer, large numerical search, Lean run or paid service.

Ancillary preservation repair: isolate global precision in the restored
baseline and joint checker tests, and make the knownness low-precision
negative control explicit. Original archived checkers and outputs stay
byte-for-byte unchanged. This fixes the import-state regression observed in
main CI after the preservation merge; it does not change a research result.

The construction is an early-truncated balanced seed lift. The explicit
base-6 seed is `floor(t)-floor(t/2)-floor(t/3)-floor(t/6)`. A general lemma
may reuse the existing pilot's validated finite-seed hypotheses. A small
perfect-power cap example tests whether additional arithmetic changes the
admissible artificial measures, without starting a second search.

```huntspec
id: paid_shortfall
question: Can an early-truncated explicit factorial lift have a proved full paid-shortfall budget at square-root support?
frontier: The paid bound and capped dual were proposed in conversation, while the old pilot lifts through the full cutoff and fixed seeds retain a leading constant greater than one
proposed_attack: Bound the omitted lift by its sparse small-integer support, retain every factorial remainder, and check an exact perfect-power capacity example
dead_routes:
  - treating a finite reduction in B-minus-psi as a bound on B-minus-N
  - applying a finite-seed height bound to an unbounded nested lift
required_oracles:
  - exact rational floor identities and prime-exponent comparisons
  - independently factored finite von Mangoldt sums
  - interval logarithms with precision refinement
kill_conditions:
  - a shortfall occurs outside the proved support
  - the full cost omits a positive remainder
  - the claimed capacity is smaller than a true prime-power mass
agents_may:
  - derive explicit coefficients and full-cost inequalities
  - run small deterministic checks
  - challenge the exact argument
agents_may_not:
  - declare novelty or RH
  - promote an asymptotic conclusion from finite checks
  - edit earlier research evidence
```
