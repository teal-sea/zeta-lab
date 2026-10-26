# Rival-gate challenge: positivity_geometry

Role: rival-gate challenger, 2026-10-26. I did not build this mechanism. The
independent calculation is `rival_gate.py`; it imports no file from the
mechanism. Its committed output is `results_rival.json`, pinned by
`test_rival_gate.py`.

## Scorecard

### 1. Disposition

**Unresolved.** The proposed number-field target H_Q is equivalent to Weil
positivity and hence to RH (`NOTES.md` lines 86-97). The load-bearing object,
an ambient arithmetic surface with a trace pairing and a Hodge-index theorem,
was not constructed (`NOTES.md` lines 562-576). The finite-field construction
does not supply that object over the number field. This is an unresolved
attempt, not a refutation of the target and not an obstruction to every
geometric construction.

There is a narrower obstruction in the builder's record: the golden fake is a
witness against arguments using only G1, G2, the functional equation and
rationality-type finite data in a function-field-transferable form
(`NOTES.md` lines 562-576). My independent exact calculation reproduces its
first six point counts as 1, 11, 76, 451, 2501, 13376, its first six closed
place counts as 1, 5, 25, 110, 500, 2215, positive closed-place counts through
degree 80, normalized root moduli 1.61803398874989484820458683437 and
0.618033988749894848204586834366, and its first Castelnuovo-Severi margin as
-5. This supports the finite part of the witness. The builder's extension to
every degree is a derived, self-reviewed argument, so the restricted-class
obstruction remains at that review grade.

### 2. Grade per step

| Step | Claimed status | Rival-challenge grade |
| --- | --- | --- |
| Finite-field intersection matrix from point counts | exact computations and derived intersection formulas (`NOTES.md` lines 100-185) | hardened for the tested curves because exact integer arithmetic and two inertia routes agree; derived, self-reviewed for the general formulas |
| First 2g Frobenius powers decide the finite-field shadow | derived proof with exact sharpness examples (`NOTES.md` lines 151-194) | derived, self-reviewed; the examples are hardened finite checks |
| Prime data give the number-field Weil form, G1 and G2 | explicit-formula dictionary (`NOTES.md` lines 399-414) | derived, self-reviewed, with the rival values measured independently below |
| H_Q is Weil positivity | projection off the hyperbolic plane (`NOTES.md` lines 86-97) | derived, self-reviewed, subject to the stated admissible-test-class hedge |
| Arithmetic data construct an ambient surface and trace pairing | required in `NOTES.md` lines 463-475 | missing |
| Riemann-Roch gives Hodge index on that surface | required in `NOTES.md` lines 234-250 and 562-568 | missing; on the proposed form it is the RH-equivalent sign step |
| Weil positivity implies RH | cited equivalence (`NOTES.md` lines 89-97) | cited classical implication, not independently source-checked in this challenge |

There is no completed construction-to-RH composite to grade. Its weakest
links are missing, so the mechanism is unresolved. The strongest completed
subchain is the finite-field shadow, not a number-field result.

### 3. The Euler-product step

It is named precisely. G1 identifies proper intersections of Frobenius graphs
with point counts, which on the number-field side requires nonnegative
logarithmic-derivative coefficients supported on prime powers. G2 supplies one
pole pair (`NOTES.md` lines 399-414). The structural positivity step G3 is
separate and uses the missing ambient surface.

My recurrence, independent of the mechanism code, recovered the following
through n = 60 at 50 decimal digits:

| Function | first negative logarithmic-derivative coefficient | first non-prime-power support | coefficient defect at (2,3) |
| --- | --- | --- | --- |
| zeta | none | none | 0 |
| DH | n = 3, -0.312092728516163622 | n = 6, 1.93635607662103879 | 1.08070090314928289 |
| Epstein (1,1,6) | n = 48, -7.74240202181578186 | n = 6, 3.58351893845611 | 2 |
| W_1/4 | none | none | -1.07e-50 |
| zeta(s - 0.1) | none | none | 2.67e-51 |

Thus DH and Epstein fail G1. W_1/4 and shifted zeta pass G1, showing that G1
is a precondition rather than the source of positivity. W_1/4 fails G2 because
it has two pole pairs. Shifted zeta has one pole, but at 1.1, and its completion
is symmetric about 0.6 rather than 0.5. The fixed-center defect at the test
point 0.37 + 7.25i is 0.0103207777726, while the defect about the actual center
is 2.09e-53. Normalization is therefore a complete hypothesis, not cosmetic.

### 4. Finite stand-ins

No finite computation establishes H_Q. The n <= 60 rival table is only a
diagnostic. The eight curve computations and the window examples are finite
checks of the finite-field shadow. They do not stand in for the all-window
number-field statement. The 2g argument is a derived finite-rank theorem in
the shadow; `NOTES.md` lines 186-194 explicitly state that zeta has infinite
rank and no deciding finite window is known.

### 5. Novelty search

Present but limited. `NOTES.md` lines 650-659 record two web searches and say
that arXiv, zbMATH and MathSciNet full text were not searched. The builder
claims original provenance for the golden fake, the 2g window statement and
the G1/G2 reading, but does not claim world novelty.

### 6. Rival results on complete hypotheses

The residuals below were recomputed at 50 decimal digits: 5.01e-49 for DH at
0.80851718245663738 + 85.69934848537759i, 4.30e-11 for Epstein (1,1,6) at
0.9532604748 + 16.2902157204i, 3.62e-35 for W_1/4 at
0.75 + 14.1347251417346937904572519836i, and 5.19e-32 for zeta(s - 0.1) at
0.6 + 14.1347251417346937904572519836i. These are measured residuals, not
zero proofs.

| Rival | Complete-hypothesis result |
| --- | --- |
| DH | Lacks G1 and G2. Its off-line zero therefore does not refute the full construction. The computation rejects it at the named Euler-product step. |
| Epstein (1,1,6) | Has one pole pair but lacks G1, first visibly at support n = 6 and sign n = 48. It is not a full counterexample. |
| W_1/4 | Passes G1 through n = 60, and the closed formula gives the pass at every n, but has two pole pairs. It passes only the shared prime-side lemma and gives no verdict on the full construction. |
| zeta(s - 0.1) | Passes G1 through n = 60, with the derived all-n formula Lambda(n)n^0.1, and has one pole. It lacks the fixed normalization: pole 1.1 and symmetry center 0.6. Recentered, it is zeta itself. It passes shared arithmetic data but is not a counterexample to the normalized construction. |

No one of these four meets every hypothesis and violates the conclusion. The
golden fake meets the weaker function-field aggregate hypotheses and violates
the shadow conclusion, which is why the restricted statement must remain
restricted to that information class.

### 7. Circularity

H_Q itself is RH-equivalent (`NOTES.md` lines 86-97). No input to the
finite-field calculation assumes RH, but moving Hodge index from the genuine
surface to the formal number-field pairing without constructing an ambient
geometry would assume the missing sign. The notes do not claim that move.
The attempt is therefore an explicit reformulation with a missing structural
step, not a circular proof claim.

## Run record

```runmanifest
id: rh_moonshot-positivity_geometry-rival-2026-10-26
hunt: rh_moonshot
started: 2026-10-26T13:03:00Z
finished: 2026-10-26T13:04:31Z
ran:
  - /Users/thomas/zeta-lab/.venv/bin/python hunts/rh_moonshot/positivity_geometry/challenge/rival_gate.py --write hunts/rh_moonshot/positivity_geometry/challenge/results_rival.json
  - /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/positivity_geometry/challenge/test_rival_gate.py
outcome: all four required rivals and the golden fake were recomputed independently; none of the four meets every normalized hypothesis, and the mechanism remains unresolved at the missing ambient geometry
artifacts:
  - hunts/rh_moonshot/positivity_geometry/challenge/rival_gate.py
  - hunts/rh_moonshot/positivity_geometry/challenge/results_rival.json
  - hunts/rh_moonshot/positivity_geometry/challenge/test_rival_gate.py
  - hunts/rh_moonshot/positivity_geometry/challenge/CHALLENGE_RIVAL.md
```
