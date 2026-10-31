# Rival-gate challenge: spectral_operator

Role: rival-gate challenger, 2026-10-26. I did not build this mechanism.
`rival_gate.py` imports no mechanism or other-hunt module. It independently
assembles full, even and odd truncated Weil matrices from public arithmetic
coefficients, constructs the CCM rank-one operator, checks the intertwining
identity, and compares its real spectrum with each rival's off-line zero.

## Scorecard

### 1. Disposition

**Unresolved.** The finite operator is a valid self-adjoint construction under
the even-simple hypothesis, and its zeta spectrum is not merely a counting
function fit. However, self-adjointness is arithmetic-free: replacing T by
W = T - epsilon_N makes W nonnegative for any real symmetric T, and the same
operator construction works for DH (`NOTES.md` lines 89-110). All RH content
remains in link 3, convergence of the finite real spectra to the zeros as c
and N grow (`NOTES.md` lines 112-132). No uniform convergence theorem or
arithmetic estimate is supplied.

The self-adjointness step is therefore refuted as a discriminator, but the
complete convergence mechanism is not refuted for zeta. A finite
counterexample does not defeat a convergence claim that has not yet been
formulated with sufficient hypotheses.

### 2. Grade per step

| Step | Evidence in the construction | Rival-challenge grade |
| --- | --- | --- |
| Assemble T from the archimedean term, pole and prime powers | provenance account and planted scan at `NOTES.md` lines 39-60 | derived and source-scanned by the builder; independently reassembled here at float grade |
| The ground eigenvalue is simple and even | ball-inertia cells at `NOTES.md` lines 62-79 | hardened only on the builder's finite cells; measured on the four independent rival cells below |
| W = T - epsilon_N intertwines D' and makes the quotient operator self-adjoint | CCM Lemma "key" and Theorem "finmain", `NOTES.md` lines 18-37 | cited theorem; independent commutator defects below agree numerically |
| The finite spectrum follows zeros rather than only their count | zeta residual and Gram control at `NOTES.md` lines 95-105 | measured on the stated finite cells |
| The spectra converge to all zeros as c, N tend to infinity | named link 3 at `NOTES.md` lines 112-132 | unresolved; no uniform statement or rate is proved |

The complete chain has no composite grade because its limiting step is absent.
The independent rival cells are measured, not ball-bracketed.

### 3. The Euler-product step

The construction correctly locates the only possible arithmetic step at link
3, convergence of the spectrum (`NOTES.md` lines 112-121). Links 1 and 2 use a
real truncated form and an even-simple ground state, not an Euler product.
This challenge independently obtains commutator defects between 6.05e-60 and
2.02e-55 for DH, Epstein and W_1/4, while every computed spectrum is real to
ordinary eigensolver precision.

Thus a rival without an Euler product passes the self-adjointness lemma. The
finite real spectrum then cannot converge to that rival's nonreal zero. This
locates the failure at link 3, but the construction gives no arithmetic
hypothesis that proves link 3 for zeta. W_1/4 further shows that a scalar Euler
product is insufficient when the local roots are nonunitary.

### 4. Finite stand-ins

Every operator here depends on a window c and band N. The builder's largest
cell is N = 200 and its most accurate high window is c = 60
(`NOTES.md` lines 71-85). The independent cells use (c, N) = (13, 40) for DH,
(13, 20) for Epstein, (2, 8) for W_1/4 and (13, 16) for recentered shifted
zeta. A positive finite gap and a real finite spectrum establish neither
even-simplicity for every cell nor convergence in a two-parameter limit.
Finite agreement with any initial zero list is not the missing limit.

### 5. Novelty search

The candidate is explicitly the published CCM construction, with the arXiv
source hash and exact results recorded at `NOTES.md` lines 16-37. The builder
claims no novelty and describes its computation as a reproduction
(`NOTES.md` lines 166-175). No separate novelty search is recorded for the
finite measurements or the reformulation obstruction. No novelty claim is
made here.

### 6. Rival results on complete hypotheses

| Rival | Complete-hypothesis result |
| --- | --- |
| DH | At (c, N) = (13, 40), the independent form has even gap 1.16743757395679982e-7. The rank-one operator has commutator defect 2.02e-55 and a real spectrum. Its nearest real spectral point to ordinate 85.6993484853775922 is 85.362912874843, at complex distance 0.45647756999337 from the off-line zero, necessarily at least its real offset 0.30851718245664. DH lacks a scalar Euler product. It passes only links 1 and 2 and fails the convergence conclusion, so it gives no verdict on an unformulated arithmetic link 3. Range and grade: one cell, measured. |
| Epstein (1,1,6) | At (13, 20), the even gap is 0.888998489033791321, the commutator defect is 6.05e-60 and the spectrum is real. The nearest point to ordinate 16.2902157204 is 16.787936567771, at complex distance 0.67317984218483 from the zero with real offset 0.4532604748. It lacks a scalar Euler product. It passes the shared self-adjointness lemma and cannot satisfy link 3. Range and grade: one cell, measured. |
| W_1/4 | At (2, 8), the even gap is 0.17805736552302542, the commutator defect is 1.20e-59 and the spectrum is real. The nearest point to the first off-line zero's ordinate is 14.370473990543, at complex distance 0.34362409652796 and hence at least the real offset 0.25. It has a scalar Euler product and fixed symmetry but lacks unitary local roots. It passes links 1 and 2, refuting any use of those links or the scalar Euler product alone as the discriminator. Range and grade: one cell, measured. |
| zeta(s - 0.1) | At the fixed half-center it lacks the even symmetry, with defect 0.010320777772574. Recentered at 0.6, its full (6, 4) form agrees with zeta's to 1.56e-61, and its (13, 16) cell has even gap 8.60834077616982704e-32, commutator defect 2.32e-104 and spectral imaginary part at most 6.04e-105. Its nearest point to the first zero differs by 3.55e-29. Recentered, it meets the hypotheses and conclusion because it is zeta under translation; at the fixed center it lacks a named hypothesis. Range and grade: two cells, measured. |

No rival meets a stated unitary arithmetic hypothesis for link 3 and violates
its conclusion, because no sufficient hypothesis for link 3 has been stated.
All three centered off-line rivals do show that self-adjointness is a shared
lemma, not an RH discriminator.

### 7. Circularity

The operator definition does not import zeros. The builder's provenance scan
and planted fault support that claim (`NOTES.md` lines 51-60), and the
independent code uses zeros only after constructing each spectrum, to select a
comparison ordinate. Self-adjointness itself is not circular. It is automatic
after shifting by the lowest eigenvalue and therefore too weak.

Circularity would enter if spectral convergence to the zeros were assumed in
order to identify the limiting operator. Link 3 is the same unresolved
capture-and-convergence content isolated by `ccm_arithmetic`; assuming it would
place the RH conclusion in the premise. The finite comparisons here are
falsification diagnostics only.

## Run record

```runmanifest
id: rh_moonshot-spectral-operator-rival-2026-10-26
hunt: rh_moonshot
started: 2026-10-26T14:42:00Z
finished: 2026-10-26T14:47:18Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/spectral_operator/challenge/rival_gate.py --write hunts/rh_moonshot/spectral_operator/challenge/results_rival.json
  - nice -n 10 .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/spectral_operator/challenge/test_rival_gate.py
outcome: DH, Epstein and W_1/4 independently pass finite even-simplicity and the shared self-adjointness lemma but their real spectra cannot converge to their off-line zeros; shifted zeta is inapplicable at center 0.5 and becomes zeta when recentered; link 3 remains unresolved
artifacts:
  - hunts/rh_moonshot/spectral_operator/challenge/rival_gate.py
  - hunts/rh_moonshot/spectral_operator/challenge/results_rival.json
  - hunts/rh_moonshot/spectral_operator/challenge/test_rival_gate.py
  - hunts/rh_moonshot/spectral_operator/challenge/CHALLENGE_RIVAL.md
```
