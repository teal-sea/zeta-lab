# Rival-gate challenge: ccm_arithmetic

Role: rival-gate challenger, 2026-10-26. I did not build this mechanism.
`rival_gate.py` independently assembles the even-sector Galerkin matrices
from the displayed formulas, using 70-decimal mpmath arithmetic. It imports
no construction or other-hunt module. Only public completed functions from
`zeta.core` and `zeta.epstein` are used to form the radical diagnostics.

## Scorecard

### 1. Disposition

**Unresolved.** The construction identifies the needed step correctly, but
does not prove it for an infinite family of windows. The target requires
simplicity and evenness for every c and locally uniform convergence of the
ground-state transforms to Xi on a neighbourhood containing |Im z| < 1/2
(`NOTES.md` lines 21-38). The reported zeta evidence is a finite grid, and
the attempted perturbative capture bound is vacuous. No rival meets every
proposed arithmetic hypothesis and retains capture at all windows, so the
implication is not refuted. No uniform estimate establishing it is present.

### 2. Grade per step

| Step | Evidence in the construction | Rival-challenge grade |
| --- | --- | --- |
| Lowest eigenvalue is simple, isolated and even for every c | ratios on 30 finite cells (`NOTES.md` lines 76-116) | measured on the stated grid; not established for every c |
| Prop. 4.1 gives only real zeros of F_v from step 1 | cited result (`NOTES.md` lines 21-38) | cited; primary source not rechecked here |
| Arithmetic captures v_c near the radical subspace | finite zeta, DH, Epstein, Dedekind and W_a cells (`NOTES.md` lines 118-160) | measured; the independent cells below agree with the reported transitions |
| Radical capture gives F_v to Xi locally uniformly in the needed strip | real-axis and Im z = 0.45 diagnostics (`NOTES.md` lines 76-116, 174-177) | unresolved; no decay bound in c and no normal-family or tail argument |
| Hurwitz converts locally uniform convergence to RH | cited chain (`NOTES.md` lines 29-38) | derived from a classical theorem once the missing convergence hypotheses hold |

The composite chain has two missing uniform steps, so it has no completed
grade. Its finite numerical statement remains measured. A high-precision
Rayleigh value is a value for the computed vector, not an eigenvalue bracket,
as the notes themselves state.

### 3. The Euler-product step

The notes name link 2, survival of radical capture through every window, as
the distinguishing step (`NOTES.md` lines 118-126). This is the right place:
link 1 applies to any real distribution, while DH's off-line pair forbids its
transform sequence from converging locally uniformly to Xi_DH.

The independent direct-formula route recomputed these cells:

| Rival and cell | lowest value | radical misfit |
| --- | --- | --- |
| DH, c = 31, N = 64 | -3.809628551006827e-30 | 0.000113323990464075 |
| DH, c = 33, N = 64 | -1.531230134619622e-23 | 0.9999033630510974 |
| Epstein (1,1,6), c = 29, N = 32 | 0.0005679762325516534 | not computed |
| Epstein (1,1,6), c = 29.5, N = 32 | -0.002045659166301485 | not computed |
| W_1/4, c = 2, N = 32 | 0.002450607259226494 | 0.1877794832369723 |
| W_1/4, c = 3, N = 32 | -0.0007055346303098329 | 0.9987359365546526 |

For the Epstein and W_a cells, ordinary double-precision eigenvalues agree
with the 70-decimal route to between 1e-15 and 1e-14. For DH the lowest scale
is far below double precision: numpy returned values near 1e-15, so those
numbers are not used for the DH sign. The 70-decimal DH values independently
agree with the construction's recorded high-precision values, but remain
measured rather than ball-bracketed in this challenge.

The DH pair also shows that positivity and capture do not change at precisely
the same instant: the c = 31 form already has a negative direction while the
ground vector remains close to the radical. Capture is lost by c = 33.

### 4. Finite stand-ins

The entire positive case is finite: c <= 60, N <= 128, real-axis height at
most 100, and one offset line Im z = 0.45. The notes explicitly say no result
is uniform in c (`NOTES.md` lines 162-177 and 191-196). These computations do
not stand in for every window, an increasing band, or locally uniform
convergence in a complex neighbourhood. The match at interpolation nodes is
built into the radical definition and is a diagnostic, not convergence.

### 5. Novelty search

Absent. `NOTES.md` lines 198-209 say no novelty search was made and identify
the zero-matching phenomenon as a reproduction of CCM.

### 6. Rival results on complete hypotheses

| Rival | Complete-hypothesis result |
| --- | --- |
| DH | Has the required real symmetry but no scalar Euler product. My independent cells find negative form values at c = 31 and c = 33, capture at c = 31, and loss of capture by c = 33. It lacks the arithmetic hypothesis and is refused at the proposed distinguishing step. |
| Epstein (1,1,6) | Has a functional equation and an off-line zero but no scalar Euler product. The independent N = 32 form changes sign between c = 29 and c = 29.5. It lacks the named arithmetic input and is not a full counterexample. |
| W_1/4 | Has a scalar Euler product and central symmetry, but local root moduli p^(1/4) and p^(-1/4) are not unitary. The independent N = 32 cells show a positive value with partial capture at c = 2 and a negative value with misfit above 0.998 at c = 3. It lacks unitarity and is not a counterexample to a unitary-local-root capture theorem. |
| zeta(s - 0.1) | Has a scalar Euler product but is symmetric about 0.6, not 0.5, and has nonunitary local coefficients n^0.1. At the fixed half-center it lacks the even functional equation, so the even-sector cell is inapplicable. Recentered at 0.6, its data reduce exactly to zeta's and the independent (c, N) = (13, 32) cell has lowest value 2.258931190572945e-49 and radical misfit 0.0002269225529380233. It meets the recentered hypotheses and the conclusion, so it is not a counterexample. |

#### Dated amendment, 2026-10-26

The wave-2 challenge ran the previously missing shifted-zeta cell with delta =
0.1. On the fixed line, the first node for c = 13 has evenness defect
0.00988960093269. Thus the real even-sector construction does not apply there.
The earlier symmetry check agrees: the defect about center 0.6 is 2.09e-53,
while the fixed-half defect is 0.0103207777726.

Recentring gives an exact rather than empirical identification. With center
0.6, the gamma parameter is (0.6 - 0.1)/2 = 1/4, each raw prime weight
Lambda(n)n^0.1 is multiplied by n^-0.6 and becomes Lambda(n)n^-1/2, and the
two pole offsets are again plus or minus 1/2. The test
`test_shifted_zeta_recentered_cell_is_exactly_the_zeta_cell` independently
assembles both (c, N) = (6, 4) matrices and finds maximum entry defect below
1e-50. At (13, 32), the recentered shifted cell has lowest value
2.258931190572945e-49 and radical misfit 0.0002269225529380233. Ordinary
double precision gives -1.4025498905815245e-15 at this scale and is discarded
for the sign. The recentered rival passes capture because it is zeta under a
coordinate translation. It also has its zeros on its own symmetry line, so it
does not violate the conclusion.

No listed rival meets every complete hypothesis and violates the conclusion.
The computations therefore locate discrimination but do not prove the zeta
capture theorem.

### 7. Circularity

The matrix is assembled from archimedean, pole and prime data; it does not
import zeros. The radical diagnostic reads Xi values, but Xi can be evaluated
from its defining completion without a zero list. Thus the finite diagnostic
is not logically circular. It would become circular if closeness to the
radical were assumed instead of proved uniformly. The notes do not do that.

The risk is instead equivalence without progress: a proof of all-window
capture may have to deliver Weil positivity to exponentially small slack
(`NOTES.md` lines 162-170). Until an arithmetic estimate proves capture, the
statement is an RH-directed target, not an RH proof.

## Run record

```runmanifest
id: rh_moonshot-ccm_arithmetic-rival-2026-10-26
hunt: rh_moonshot
started: 2026-10-26T13:13:00Z
finished: 2026-10-26T13:16:02Z
ran:
  - nice -n 10 /Users/thomas/zeta-lab/.venv/bin/python hunts/rh_moonshot/ccm_arithmetic/challenge/rival_gate.py --write hunts/rh_moonshot/ccm_arithmetic/challenge/results_rival.json
  - /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/ccm_arithmetic/challenge/test_rival_gate.py
outcome: independent Galerkin assembly locates capture loss for DH and W_1/4 and a sign change for Epstein, while shifted zeta fails the fixed normalization; no rival refutes the complete implication and the zeta convergence step remains unresolved
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/challenge/rival_gate.py
  - hunts/rh_moonshot/ccm_arithmetic/challenge/results_rival.json
  - hunts/rh_moonshot/ccm_arithmetic/challenge/test_rival_gate.py
  - hunts/rh_moonshot/ccm_arithmetic/challenge/CHALLENGE_RIVAL.md
```

```runmanifest
id: rh_moonshot-ccm-arithmetic-rival-shifted-zeta-2026-10-26
hunt: rh_moonshot
started: 2026-10-26T13:35:00Z
finished: 2026-10-26T13:36:56Z
ran:
  - nice -n 10 /Users/thomas/zeta-lab/.venv/bin/python hunts/rh_moonshot/ccm_arithmetic/challenge/rival_gate.py --write hunts/rh_moonshot/ccm_arithmetic/challenge/results_rival.json
  - nice -n 10 /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/ccm_arithmetic/challenge/test_rival_gate.py
outcome: shifted zeta fails the fixed-half even-sector hypothesis; after recentering at 0.6 its Galerkin matrix and radical are exactly zeta's, and its measured c = 13, N = 32 cell is captured
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/challenge/rival_gate.py
  - hunts/rh_moonshot/ccm_arithmetic/challenge/results_rival.json
  - hunts/rh_moonshot/ccm_arithmetic/challenge/test_rival_gate.py
  - hunts/rh_moonshot/ccm_arithmetic/challenge/CHALLENGE_RIVAL.md
```
