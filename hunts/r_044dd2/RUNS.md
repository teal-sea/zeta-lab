# Run ledger

## R-044DD2-PILOT

```runmanifest
id: r_044dd2-pilot
hunt: r_044dd2
started: 2026-08-22T00:15:38-05:00
finished: 2026-08-22T00:18:35-05:00
ran:
  - orbit 0 with repeated bounded support minimization and 48 lazy cuts per round
  - independent direct replay of the final candidate
outcome: killed the repeated-optimization configuration after the unresolved coloring count rose from 117 to 1002; no mathematical conclusion
artifacts:
```

## R-044DD2-CENSUS

```runmanifest
id: r_044dd2-census
hunt: r_044dd2
started: 2026-08-22T00:19:11-05:00
finished: 2026-08-22T01:05:19-05:00
ran:
  - all 31 target-matching branches with one support-minimization round followed by exact lazy feasibility cuts
  - separate direct replay of 6561 colorings and the star, pair-pencil, and full-column conditions for every returned support
outcome: all 31 branches returned independently verified support survivors; support size 76 to 132, median 118
artifacts:
  - results.json
```

## R-044DD2-LAURENT-01-03

```runmanifest
id: r_044dd2-laurent-01-03
hunt: r_044dd2
started: 2026-08-22T01:08:31-05:00
finished: 2026-08-22T01:12:44-05:00
ran:
  - exact target-zero and literal binomial-trinomial sieve on the sparsest orbit-18 support
  - exact signed-lattice Laurent sieve on three successive orbit-18 supports
  - independent replay of each zero binomial, zero trinomial, exponent identity, odd sign, and forced nonzero monomial
outcome: the elementary sieve found no collision; three successive supports were excluded by independently verified Laurent certificates of l1 sizes 1, 3, and 1
artifacts:
  - artifacts/orbit18-support-01.json
  - artifacts/orbit18-laurent-01.json
  - artifacts/orbit18-support-02.json
  - artifacts/orbit18-laurent-02.json
  - artifacts/orbit18-support-03.json
  - artifacts/orbit18-laurent-03.json
```
