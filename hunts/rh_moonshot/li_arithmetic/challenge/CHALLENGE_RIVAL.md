# Rival-gate challenge: li_arithmetic

Role: rival-gate challenger, 2026-10-26. I did not build this mechanism.
`rival_gate.py` imports none of the mechanism modules. It independently
extracts small Li coefficients by a roots-of-unity Cauchy sum, reconstructs
log-derivative coefficients by a local Dirichlet recurrence, and recomputes
the high-index W_1/4 value from zero quadruples and a smooth zero-density
tail. Public completed functions and the public zeta zero table are used only
for the stated rival diagnostics.

## Scorecard

### 1. Disposition

**Unresolved.** The exact target is the all-n inequality P_n <= M(n)
(`NOTES.md` lines 47-56). The construction gives no uniform signed estimate
for P_n. Its pointwise absolute-value route fails throughout the tested range
where M(n) is positive, and its mean-square route fails outside n in
[32, 1258] (`NOTES.md` lines 92-108). Those two sub-routes are refuted at the
reported parameters, but their failure does not refute P_n <= M(n). The
finite zeta calculation through n = 5000 cannot establish the all-n target.

The W_1/4 result does refute a weaker proposed implication: a scalar Euler
product, nonnegative prime-power log-derivative coefficients, and a central
functional equation do not imply nonnegative Li coefficients. A stronger
zeta-specific statement, for example one adding unitary local roots, remains
unformulated and unproved.

### 2. Grade per step

| Step | Evidence in the construction | Rival-challenge grade |
| --- | --- | --- |
| Li's all-n criterion is equivalent to RH | classical sources cited at `NOTES.md` lines 17-27 | derived in the cited literature; not independently reviewed here |
| The split lambda_n = A(n) + T(n) | formulas and tests at `NOTES.md` lines 29-45 | derived, self-reviewed by the builder; finite identities hardened by multiple numerical routes |
| The prime-side identity reduces positivity to P_n <= M(n) | derivation at `NOTES.md` lines 47-56 | derived, self-reviewed by the builder; finite prime sums measured |
| Pointwise or mean-square control proves P_n <= M(n) | measured bounds at `NOTES.md` lines 84-108 | refuted for the stated routes and ranges; neither supplies the target estimate |
| P_n <= M(n) holds for every n | only n <= 5000 computed at `NOTES.md` lines 84-91 | unresolved; no all-n grade exists |
| All Li coefficients are nonnegative, hence RH | depends on the preceding all-n inequality | unresolved |

The complete proof chain has no composite grade because its decisive all-n
step is absent. The strongest positive arithmetic statement remains measured
on n <= 5000. The sign of lambda_8260 for W_1/4 is hardened: the builder's
two Cauchy radii and its separate zero-side calculation agree (`NOTES.md`
lines 75-82), and `test_wa_negative_li_value_is_reproduced_from_zeros`
recomputes the zero-side value without mechanism imports.

### 3. The Euler-product step

The construction names the correct step: P_n <= M(n), with the Euler product
entering through psi and the prime-power coefficients Lambda(m)
(`NOTES.md` lines 47-56 and 110-127). The independent recurrence in
`test_log_derivative_coefficients_separate_the_rivals` finds no negative or
off-prime-power coefficient through index 60 for zeta, W_1/4, or
zeta(s - 0.1). It finds the first negative coefficient at 3 and the first
off-prime-power coefficient at 6 for DH. For Epstein (1,1,6), those indices
are 48 and 6.

This challenge also independently obtains

    lambda_8260(W_1/4) = -122.315821669551207

from 1000 zeta zeros plus the smooth tail. Thus positivity and prime-power
support of the log derivative, even together with the functional equation,
are insufficient. The missing discriminator identified by the construction
is unitarity of the local roots (`NOTES.md` lines 123-127). No estimate using
that stronger input is constructed.

### 4. Finite stand-ins

The zeta and DH split is evaluated only for n <= 5000, the zeta prime-side
integral only for n <= 5000 and x <= 10^8 before modeled tails, and W_1/4
only for n <= 9000 (`NOTES.md` lines 58-108). The rival recurrence here ends
at coefficient index 60; the independent Cauchy extraction ends at n = 12;
the W_1/4 zero sum uses 1000 zeros and a smooth tail. These computations test
identities and reject weak hypotheses. None stands in for the required
inequality at every n. In particular, zeta positivity through n = 5000 says
nothing about a later off-line zero, as the onset discussion at `NOTES.md`
lines 129-146 explains.

### 5. Novelty search

Absent. `NOTES.md` lines 166-178 identify the classical sources for the split
and state that no search was made for the measured failure of the
absolute-value routes. Absence changes no grade.

### 6. Rival results on complete hypotheses

| Rival | Complete-hypothesis result |
| --- | --- |
| DH | Lacks the named scalar Euler product and nonnegative prime-power coefficients. The recurrence through index 60 finds a negative coefficient at 3 and off-prime-power support at 6. Independent Cauchy values are positive for n = 1 through 12, agreeing with the builder's finite positivity through 5000. It lacks a named hypothesis and is not that counterexample. Range and grade: n <= 12 and coefficient index <= 60, measured. |
| Epstein (1,1,6) | Lacks a scalar Euler product. Its recurrence has off-prime-power support at 6 and a negative coefficient at 48. Its reported off-line zero gives a completed-function residual 4.31e-11. It lacks a named hypothesis and is not that counterexample. Range and grade: coefficient index <= 60 and one approximate zero, measured. |
| W_1/4 | Meets the weaker stated package of a scalar Euler product, nonnegative prime-power log-derivative coefficients, and central functional equation, yet lambda_8260 is negative. This refutes the implication from that package. It lacks unitary local roots, since their moduli are p^(1/4) and p^(-1/4), so it is not a counterexample to a stronger theorem that explicitly assumes unitarity. Range and grade: recurrence index <= 60 and n = 8260, with the sign hardened by independent routes. |
| zeta(s - 0.1) | Has a scalar Euler product with nonnegative prime-power coefficients, but its local modulus at p = 2 is 2^0.1 = 1.0717734625 and its symmetry center is 0.6. At 0.37 + 7.25i, the defect about 0.6 is 6.26e-53 while the defect about 0.5 is 0.0103207778. It lacks unitarity and the fixed-half normalization, so it is not that counterexample. Range and grade: coefficient index <= 60, one symmetry point and one shifted zero, measured. |

The construction has not stated a complete sufficient-hypothesis theorem
beyond zeta itself. Consequently the W_1/4 row refutes the explicit coarse
package, while the other rows locate hypotheses a stronger theorem would
need. No rival here refutes a theorem combining fixed-half normalization,
unitary local roots, and whatever signed estimate is still missing.

### 7. Circularity

The target is explicitly RH-equivalent (`NOTES.md` lines 17-27). Rewriting it
as P_n <= M(n) is not progress unless a new unconditional estimate proves the
inequality. The pointwise tail uses Schoenfeld's RH-conditional envelope and
the mean-square tail uses Cramer's RH mean square as a model
(`NOTES.md` lines 92-102). Either would be circular if used in an RH proof,
and neither reaches the required inequality on the full tested range anyway.

The builder does not use a zero list as positive evidence for zeta. This
challenge's zero-side W_1/4 calculation is only an independent falsification
check for a negative rival value. It is not an input to the proposed
prime-side proof. The small Cauchy calculation evaluates completed functions
directly and imports no zero list.

## Run record

```runmanifest
id: rh_moonshot-li_arithmetic-rival-2026-10-26
hunt: rh_moonshot
started: 2026-10-26T13:19:00Z
finished: 2026-10-26T13:22:20Z
ran:
  - nice -n 10 /Users/thomas/zeta-lab/.venv/bin/python hunts/rh_moonshot/li_arithmetic/challenge/rival_gate.py --write hunts/rh_moonshot/li_arithmetic/challenge/results_rival.json
  - nice -n 10 /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/li_arithmetic/challenge/test_rival_gate.py
outcome: the independent recurrence separates non-Euler rivals, the zero-side route reproduces the negative W_1/4 value, and shifted zeta fails unitarity and fixed-half normalization; the zeta all-n signed estimate remains unresolved
artifacts:
  - hunts/rh_moonshot/li_arithmetic/challenge/rival_gate.py
  - hunts/rh_moonshot/li_arithmetic/challenge/results_rival.json
  - hunts/rh_moonshot/li_arithmetic/challenge/test_rival_gate.py
  - hunts/rh_moonshot/li_arithmetic/challenge/CHALLENGE_RIVAL.md
```
