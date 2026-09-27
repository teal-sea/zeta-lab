# Multi-prime Mobius orbits toward the RH cancellation target

Owner-authorized RH research, performed in an isolated worktree from
`8941a80`. This is one bounded attempt, not a change of the objective to a
simple-zero proportion. The original checkout and earlier research records
are read-only. No publication, hosted compute, paid jobs or Lean build.

Compare the arithmetic multi-prime orbit construction with the exact
floor-level Mertens representation. Preserve the joint target
`|S_smooth + Sigma1 + Sigma2| = O_epsilon(N^(1/2+epsilon))` from
`../prime_pair_error/FACTORIZATION_NEXT_STEP.md`. Work on Sigma2 alone
cannot silently discharge the other terms. Keep all orbit boundaries.

```huntspec
id: mobius_orbits
question: Can complete multi-prime Mobius orbits supply cancellation beyond the p=2 majorant in the RH-linked Sigma2 sum?
frontier: the p=2 absolute-value majorant has leading order N log^3 N divided by 192; the signed joint D_N bound remains open
proposed_attack: retain the exact complete-orbit floor kernel and every incomplete orbit, then compare with an exact floor-level Mertens expansion
dead_routes:
  - treating the p=2 constant gain as an improvement of the N exponent
  - dropping incomplete orbit boundary terms
  - promoting finite arithmetic checks to an all-N RH estimate
required_oracles:
  - integer sieve cross-checked against independent trial division
  - exact integer and rational enumeration of direct and regrouped sums
  - separately written mathematical challenge of the fixed-P asymptotic
kill_conditions:
  - an exact direct sum disagrees with its orbit or floor-level reconstruction
  - missing-boundary and sign lesions are not detected
  - a fixed-P gain changes only a constant rather than the growth rate needed for RH
agents_may:
  - derive and challenge candidate identities in this directory
  - run small serial exact arithmetic checks
  - record an unreviewed ordinary argument with every dependency explicit
agents_may_not:
  - claim RH from a finite check
  - claim novelty or promote their own claim
  - alter the core or earlier hunts
  - publish or launch heavy computation
```
