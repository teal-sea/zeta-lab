# Hunt #80: where the variable-radius Bloch certificate ends

Third application of the lab's procedure for a published computer-assisted bound
(after the two seven-point simple-zero certificates of Hunt #79): reproduce the bound
from its own verifier, find the constants left at round numbers, locate the floor of the
functional numerically, verify at the optimum with the author's own Arb machinery, bracket
the ceiling, and read the verifier for soundness.

The subject is Wikström, *An improved lower bound for Bloch's constant*, arXiv 2608.17660
(2026-08-18), with code and certificates at Zenodo `10.5281/zenodo.21975862`
(`bloch-computations-1.0.0.zip`, MIT, AI-assisted per the paper's tool disclosure). The
bound is `B >= sqrt(3)/4 + 0.0153`. The proof is a dichotomy on `|a_3|` with threshold
`ETA = 0.70` (a round number): below it, point-value certificates extend `Re f > 0` from
Bonk's radius `1/sqrt(3)` to `LARGE_RAD = 0.5815218918243517` and one integral cut at
that radius gives the near gain `0.0153040536989472`; above it, 47 fixed-radius cuts and
an adaptive Arb subdivision over balanced three-atom measures clear `0.0153` in 24 phase
sectors. The author computes the fixed-radius ceiling (`0.01519720970909415`, below
`0.0152`) and does not compute the variable-radius ceiling. This hunt locates it.

Nothing here audits the analytic bridge (Bonk's theorem, the moment inequality, the
three-atom extreme-point reduction, the centre-placement lemma); those are the paper's
hand proofs and are read, not re-proved.

```huntspec
id: bloch_ceiling
question: How far above 0.0153 can the variable-radius dichotomy for Bloch's constant be pushed with the author's own cuts, grid and Arb verifier when ETA, LARGE_RAD and the point-certificate resolution are moved off their chosen values, and is the published verification sound as shipped?
frontier: Chen-Gauthier sqrt(3)/4 + 2e-4, Xiong + 3e-4, Wikström + 0.0153 (near branch 0.0153040536989472, away branch cleared at 0.0153 in 24 sectors); fixed-radius ceiling 0.01519720970909415 (author, Arb); variable-radius ceiling not computed by the author
proposed_attack: reproduce every printed statistic on the pinned archive; sweep the near gain in the larger radius, the admissible radius in ETA and in the point-node count, and the away-branch float minimum in ETA, all through the author's search and verification routines; read the verifier for constants that encode other constants and for float comparisons inside the rigorous loop
dead_routes:
  - raising the fixed-radius target, the author's own Arb witness caps that reduction below 0.0152
  - pinning higher Taylor coefficients at the fixed radius, excluded by the even-function antipodal argument in the paper's last section
required_oracles:
  - the archived Arb verification programs at the pinned Zenodo version, run on Modal and locally, compared field by field against expected-output/verification.md and the 24 reference-run logs
  - the author's branch_verify at the author's 40x40 grid, whose terminal-box count per sector is order-free and must equal the reference log's count
  - the author's verify_positivity and verify_near_moment in Arb at every parameter point this hunt proposes
  - exact rational arithmetic on the one binary64 comparison inside the rigorous loop
kill_conditions:
  - a reproduced sector count or a reproduced Arb enclosure differs from the reference record
  - an Arb-verified near gain at a proposed radius is below the float search value that proposed it by more than the printed enclosure radius
  - the away-branch float minimum at a proposed ETA falls below the near gain there, which would move the binding constraint and void the near-branch ceiling reading
  - a soundness finding that changes an accepted sector into a refused one
agents_may:
  - run the archived programs and record every field
  - call the author's search and verification routines with different constants and label the float results apparent
  - scan the rotated-antipodal boundary the archived reconnaissance skips
  - state a ceiling estimate labelled INFERRED with what would make it rigorous
agents_may_not:
  - declare the theorem verified, only its finite certificates and printed statistics are
  - promote a float minimum to a bound
  - claim a higher target without the author's own verifier accepting it in both branches
  - post to the author, to Zenodo or to arXiv
```

Related: `hunts/ainta_seven_point/` (the procedure, applied twice), `CONTRIBUTING.md`,
`hunts/HUNTSPEC.md`.
