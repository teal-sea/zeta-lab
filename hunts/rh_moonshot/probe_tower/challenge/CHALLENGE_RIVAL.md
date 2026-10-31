# Rival-gate challenge: probe_tower

Role: rival-gate challenger, 2026-10-26. I did not build this mechanism. The
exact template and rival calculations in `rival_gate.py` are an independent
implementation and import no mechanism file. `results_rival.json` is the
committed output and `test_rival_gate.py` pins it.

## Scorecard

### 1. Disposition

**Restricted class obstructed.** The class is explicit: power-residue probes
of order k >= 2 whose principal frequencies are k-th powers, whose comparison
pole is 1/k, and whose signal, direct bound, dual-length constraint and floor
rows retain the paper-form expressions (`NOTES.md` lines 77-128 and 457-468).
Inside that class, exact rational algebra gives

    sigma_0(k) = 1 - 1/k + (M - 2 ell)/(2k),

which is strictly increasing in k for every admissible geometry. The LP dual
identity gives the floor wall 1 - 4/(5k), whose minimum for k >= 2 is 3/5.
My implementation independently reproduces the builder's formulas and dual
identity. This is a proof about the stated algebraic template class. The
claim that every intended order-k analytic construction has exactly these
forms remains an inferred reading of the source (`NOTES.md` lines 79-94), so
the obstruction does not extend beyond the defined class.

### 2. Grade per step

| Step | Claimed status | Rival-challenge grade |
| --- | --- | --- |
| The source's sextic frequencies and pole 1/6 generalize to order k and pole 1/k | source lines plus structural reading (`NOTES.md` lines 79-94) | cited at k = 6; inferred for general k, not independently source-checked here |
| The signal and direct-bound exponents give sigma_0(k) | algebra in `NOTES.md` lines 96-113 | hardened as algebra: exact rational reimplementation agrees independently; still conditional on the inferred k-reading |
| sigma_0 increases to 1 | formula in `NOTES.md` lines 130-142 | hardened exact algebra under the template hypotheses; paper geometry gives 7/8 at k = 6, 25/28 at k = 7, increment 1/56 |
| Floor wall and dual-length wall | LP and dual multipliers in `NOTES.md` lines 143-181 | hardened exact algebra under the stated constraints; independently checked on 10 orders and 1,080 exact identity instances |
| Formal k = 1 endpoint requires the Littlewood Moebius bound | `NOTES.md` lines 183-193 | derived reading resting on a cited classical equivalence; not source-checked here |
| Continuation criterion plus sigma_0(k) tending to 1/2 would imply RH | `NOTES.md` lines 64-74 | derived from the cited criterion and functional equation; no such sequence is constructed |

The strongest composite statement about actual higher-order probes keeps the
weakest grade, **inferred**, because the order-k source dictionary is inferred.
The theorem about the explicitly defined algebraic template is derived and
independently checked.

### 3. The Euler-product step

The step is named as E_k (`NOTES.md` lines 307-334): the principal row reads
the target coefficients through a squarefree Moebius sum R_f and needs a
factorization R_f = H_f/L_f with H_f uniformly close to 1 after a finite
deletion. Unitarity also enters the direct bound and local identity
(`NOTES.md` lines 392-421).

My independent DH calculation at s = 2 gives the squarefree row
0.975580687977358506 and the linear combination of constituent reciprocals
0.975580681462599327, a gap of 6.51e-9. The scalar reciprocal of DH differs
from that row by 0.0243509788826. At DH's off-line zero the computed
|H - 1| is 1. This locates its failure before any conclusion about RH.

For zeta(s - 0.1), the squarefree row at s = 2 is
0.571511566866106290 against 1/zeta(1.9) = 0.571511380120929532, a finite
truncation gap of 1.87e-7 at n <= 20000. The exact Euler identity is
R = 1/zeta(s - 0.1). This rival passes the shared reciprocal step. Its local
coefficient at 2 has modulus 1.07177346253629317, so it is not a finite-order
unitary character.

### 4. Finite stand-ins

The tower direction and walls do not rely on a finite k scan. They are exact
formulas in symbolic k, with a dual identity proving the floor wall. The
tests over k <= 100 and random rational geometries are regression checks of
that derivation, not its quantifier.

The rival zero residuals and the Euler products cut off at n = 20000 or
p = 100000 are finite measured diagnostics only. They do not establish a
uniform half-plane estimate. The notes label the rival scans as finite and
do not use them to prove the all-k obstruction (`NOTES.md` lines 447-451).

### 5. Novelty search

Absent. `NOTES.md` lines 526-538 state that no arXiv, zbMATH or OEIS search
was made for the order-k pricing or tower statement. This changes no grade.

### 6. Rival results on complete hypotheses

The measured zero residuals are 5.01e-49 for DH at
0.80851718245663738 + 85.69934848537759i, 4.30e-11 for Epstein (1,1,6) at
0.9532604748 + 16.2902157204i, 3.62e-35 for W_1/4 at
0.75 + 14.1347251417346937904572519836i, and 5.19e-32 for zeta(s - 0.1) at
0.6 + 14.1347251417346937904572519836i. They confirm the test points only.

| Rival | Complete-hypothesis result |
| --- | --- |
| DH | Lacks a scalar Euler product. Its principal row is the linear combination of the constituent reciprocals, not the reciprocal of DH, and gives |H - 1| = 1 at the off-line zero. It lacks a named hypothesis and is not a counterexample to the full probe. |
| Epstein (1,1,6) | Is not a primitive finite-order GL1 target and its normalized coefficients have multiplicativity defect 2 at (2,3). It lacks the scalar target hypothesis and is not a full counterexample. |
| W_1/4 | Its finite Euler correction at the off-line zero gives |H_W - 1| = 0.235972896729 with primes through 100000, so it passes the shared contraction diagnostic there. Its two local root moduli at p = 2 are 1.18920711500272107 and 0.840896415253714543, not 1. It lacks unitarity and is not a full counterexample. |
| zeta(s - 0.1) | Passes the reciprocal identity exactly and has an off-center zero, but its local coefficient has modulus 2^0.1 > 1 and its symmetry center is 0.6. It lacks finite-order unitarity and the fixed normalization, so it passes only a shared lemma. |

No required rival meets every hypothesis and violates the conclusion. The
rival gate therefore does not refute the probe implication. The mechanism is
instead obstructed internally by the direction and floor of its template.

### 7. Circularity

The formal order k = 1 has sigma_0 = 1/2, but its direct bound is the
Littlewood square-root Moebius estimate, an RH-equivalent input
(`NOTES.md` lines 183-193). It cannot be used as a proof step. For k >= 2 the
obstruction is not circular: exact template algebra keeps the boundary at or
above 3/5 and sends it toward 1. The construction makes no finite computation
stand in for the missing all-degree analytic family.

## Run record

```runmanifest
id: rh_moonshot-probe_tower-rival-2026-10-26
hunt: rh_moonshot
started: 2026-10-26T13:08:00Z
finished: 2026-10-26T13:10:00Z
ran:
  - .venv/bin/python hunts/rh_moonshot/probe_tower/challenge/rival_gate.py --write hunts/rh_moonshot/probe_tower/challenge/results_rival.json
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/probe_tower/challenge/test_rival_gate.py
outcome: exact independent algebra obstructs the stated order-k template at a 3/5 floor, while every required rival lacks at least one complete hypothesis
artifacts:
  - hunts/rh_moonshot/probe_tower/challenge/rival_gate.py
  - hunts/rh_moonshot/probe_tower/challenge/results_rival.json
  - hunts/rh_moonshot/probe_tower/challenge/test_rival_gate.py
  - hunts/rh_moonshot/probe_tower/challenge/CHALLENGE_RIVAL.md
```
