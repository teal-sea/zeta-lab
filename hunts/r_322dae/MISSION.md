# Hunt R-322DAE: Krenn-Gu 8x3: port the verified 6x3 orbit census and measure the next exact frontier

The 3000 euro Krenn-Gu conjecture asks whether there exists an edge-weighted graph whose monochromatic matching polynomial satisfies specific quantum interference conditions. The 6x3 instance has been closed (no complex witness exists). The next open instance is 8x3 (8 vertices, 3 colors), comprising 105 perfect matchings, 105^3 = 1157625 monochromatic matching triples, and a symmetry group S8 x S3 of order 241920.

This hunt reproduces the 6x3 census checksum (15 matchings, 3375 triples, 8 S6 x S3 orbits), and parameterizes the exact orbit census layer for n=8.

```huntspec
id: r_322dae
question: What is the exact orbit census and stabilizer decomposition of the 1157625 monochromatic matching triples in the Krenn-Gu 8x3 problem under S8 x S3 symmetry?
frontier: the 6x3 instance is closed with 15 matchings, 3375 triples and 8 S6 x S3 orbits; the 8x3 instance has 105 matchings, 1157625 triples, 252 variables and 6561 polynomial equations, with orbit structure previously unmeasured
proposed_attack: precompute the S8 permutation action on all 105 perfect matchings, apply the direct product action of S8 x S3 on the 1157625 triples, compute the Burnside fixed-point counts, extract canonical representatives, orbit sizes, and stabilizer sizes, and verify exact partition coverage
dead_routes:
  - rebuilding full polynomial equations or running floating-point weight search before the orbit census layer is parameterized
  - unverified combinatorial bounds without exhaustive orbit-stabilizer partition verification
required_oracles:
  - the Burnside orbit-counting lemma applied to S8 x S3 conjugacy classes
  - exhaustive bitset and array partition verification over all 1157625 triples
kill_conditions:
  - the 6x3 census checksum fails to reproduce 15 matchings, 3375 triples, or 8 S6 x S3 orbits
  - the sum of orbit sizes for n=8 fails to equal 1157625 or leaves unvisited triples
  - the orbit-stabilizer product fails to equal 241920 for any orbit
  - memory consumption exceeds 8 GB or runtime exceeds 45 minutes
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```
