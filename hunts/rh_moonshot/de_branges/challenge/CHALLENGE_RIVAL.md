# Rival-gate challenge: de_branges

Role: rival-gate challenger, 2026-10-26. I did not build this mechanism.
`rival_gate.py` imports no mechanism or other-hunt module. It evaluates the
Hermite-Biehler defect directly from the public completed functions in
`zeta.core` and `zeta.epstein`, at a failure point and a control point for each
required rival.

## Scorecard

### 1. Disposition

**Unresolved.** The Lagarias family is valid, but its decisive condition is an
exact reformulation. For the stated symmetry and Hadamard hypotheses,

    E_h is Hermite-Biehler

is equivalent to having no zero with real part greater than 1/2 + h
(`NOTES.md` lines 97-111). Therefore proving the condition for every h > 0 is
quasi-RH at every abscissa, not an estimate toward it. The known arithmetic
input only supplies the already known zero-free range, h >= 1/2 classically
and h > 3/8 from the 7/8 strip (`NOTES.md` lines 84-88 and 113-120).

This is a located obstruction and triggers the mission's reformulation kill
condition, but it is not a theorem that RH cannot be proved by establishing
those zero-free half-planes. I therefore do not upgrade the obstruction to a
restricted-class impossibility result.

### 2. Grade per step

| Step | Evidence in the construction | Rival-challenge grade |
| --- | --- | --- |
| Define E_h(z) = Lambda(1/2 + h - iz) and its defect | `NOTES.md` lines 68-82 | derived, self-reviewed |
| E_h is Hermite-Biehler exactly when Re rho <= 1/2 + h for every zero | Lagarias's factor argument plus the zero of E_h exhibited at `NOTES.md` lines 97-111 | derived, self-reviewed; the rival extension assumes the stated Hadamard normalization |
| The 7/8 zero-free strip gives the property for h > 3/8 | `NOTES.md` lines 113-120 | derived, self-reviewed, conditional on the recorded 7/8 result and its review conditions |
| Hermite-Biehler gives real, simple, interlacing zeros of A and B | Lagarias Lemma 2.2 and Theorem 2.1, recorded at `NOTES.md` lines 42-52 | cited primary-source theorem; source not independently rechecked by this challenger |
| The property for every h > 0 and Hurwitz give RH | `NOTES.md` lines 79-82 and 103-111 | derived, self-reviewed, but its all-h premise is RH-equivalent and unproved |

The finite rival defects below are measured by one independent numerical
route. The complete RH chain has no composite grade because its all-h premise
is absent.

### 3. The Euler-product step

The construction names the arithmetic input as a zero-free half-plane derived
from the Euler product (`NOTES.md` lines 84-88). It also shows that individual
Euler factors do not have the Hermite-Biehler sign (`NOTES.md` lines 122-128),
so the desired inequality is not assembled locally from positive factors.

The independent cells confirm the actual discriminator. DH and Epstein lack a
scalar Euler product and their defects turn positive at their off-line zeros.
W_1/4 has a scalar Euler product, nonnegative log-derivative coefficients and
the fixed functional equation, yet its defect is positive for h = 0.2. Thus
those coarse Euler-product properties do not imply the needed zero-free
half-plane. Its nonunitary local roots move a zero to real part 0.75.

### 4. Finite stand-ins

The builder's grid has |x| <= 100, except Epstein ends at 40, with seven h
values and two main y values (`NOTES.md` lines 130-145). Negative defects on
that grid do not establish the inequality throughout the upper half-plane.
The independent challenge uses one failure point and one control point per
rival, all at y = 0.05. Those points test the exact zero-offset prediction but
do not replace an all-z or all-h statement. The exact equivalence, not the
finite grid, supplies the obstruction.

### 5. Novelty search

The builder records searches for Conrey and Li and two Lagarias papers, then
reads the available arXiv sources (`NOTES.md` lines 17-56). It finds that
Conrey and Li refute different Hilbert-space positivity conditions, not this
E_h family (`NOTES.md` lines 90-95). No novelty search beyond those sources is
recorded for the extension to h > 3/8 or for the exact equivalence
(`NOTES.md` lines 113-120). No novelty claim is made here.

### 6. Rival results on complete hypotheses

| Rival | Complete-hypothesis result |
| --- | --- |
| DH | It has the fixed-half functional equation and reality, but no scalar Euler product. At x = 85.6993484853775922 and y = 0.05, the defect is 2.3441483868663243899 for h = 0.25 and -2.1334132025776454372 for h = 0.375. Its completed-function residual at the stated zero with real part 0.808517182456637386 is 5.12e-77. It fails the zero-free conclusion-producing hypothesis exactly where predicted, so it is not a counterexample to the equivalence. Range and grade: two points, measured. |
| Epstein (1,1,6) | It has the fixed-half functional equation and reality, but no scalar Euler product. At x = 16.2902157204 and y = 0.05, the defect is 1.3494121383316399218 for h = 0.375 and -3.5506433820889641886 for h = 0.5. The completed residual at real part 0.9532604748 is 2.28e-21. It lacks the zero-free hypothesis and is not that counterexample. Range and grade: two points, measured. |
| W_1/4 | It has the fixed functional equation and a scalar Euler product, but nonunitary local roots. At the first zeta ordinate and y = 0.05, the defect is 62.923988502644232857 for h = 0.2 and -63.336207588322219641 for h = 0.3. The off-line zero at real part 0.75 has residual 3.62e-35. This refutes any implication from only the scalar Euler product, nonnegative coefficients and functional equation to the Hermite-Biehler condition. It lacks the required zero-free half-plane. Range and grade: two points, measured. |
| zeta(s - 0.1) | Its symmetry center is 0.6, not 0.5. The fixed-half functional-equation defect at 0.37 + 7.25i is 0.010320777772574, while the defect about center 0.6 is 6.91e-53. At the first zeta ordinate and y = 0.05, its Hermite-Biehler defect changes from 63.150172698616547874 at h = 0.05 to -63.150172698616547874 at h = 0.15. It lacks the fixed functional equation, so the equivalence's complete hypotheses refuse it. Range and grade: three points, measured. |

No rival meets the conclusion-producing zero-free hypothesis and violates the
Hermite-Biehler conclusion. W_1/4 does meet the weaker Euler-product package
and refutes that weaker implication.

### 7. Circularity

The construction's critical input is already the desired zero-free statement.
By the exact equivalence at `NOTES.md` lines 97-111, proving the
Hermite-Biehler condition for each h is neither weaker than nor independent of
proving the corresponding quasi-RH half-plane. Taking every h > 0 is RH. The
family therefore provides a correct reformulation, not a new estimate.

The challenger evaluates completed functions directly. Known rival zeros are
used only to choose falsifying points and to check residuals. The zeta control
at h = 0.1 has defect -1.0992890467837299957 at one point; it is not evidence
for the all-z inequality.

## Run record

```runmanifest
id: rh_moonshot-de-branges-rival-2026-10-26
hunt: rh_moonshot
started: 2026-10-26T14:37:00Z
finished: 2026-10-26T14:39:43Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/de_branges/challenge/rival_gate.py --write hunts/rh_moonshot/de_branges/challenge/results_rival.json
  - nice -n 10 .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/de_branges/challenge/test_rival_gate.py
outcome: every off-line rival flips the defect at its predicted offset; W_1/4 refutes the coarse Euler-product package, shifted zeta lacks the fixed symmetry, and the Lagarias family remains an exact unresolved zero-free reformulation
artifacts:
  - hunts/rh_moonshot/de_branges/challenge/rival_gate.py
  - hunts/rh_moonshot/de_branges/challenge/results_rival.json
  - hunts/rh_moonshot/de_branges/challenge/test_rival_gate.py
  - hunts/rh_moonshot/de_branges/challenge/CHALLENGE_RIVAL.md
```
