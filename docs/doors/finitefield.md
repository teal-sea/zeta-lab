# Department: `finitefield`

Curves over F_p, department #2, and the first second subject: the same
referee architecture under a property that is **decidable**.

**Declared in** `harness/departments/finitefield_department.py`.
**Audited by** `tests/test_department_conformance.py`.

## What it studies

The Riemann hypothesis that is a theorem (Hasse, 1933; Weil, 1948): for a
non-singular curve over F_p, every Frobenius eigenvalue sits on the circle
|α| = √p, equivalently |a_p| ≤ 2√p. Point counts over the extension tower,
the Lefschetz fixed-point formula, functional-equation self-duality αβ = p,
Sato–Tate statistics, all implemented in `zeta.finitefield` with the
Lefschetz predictions pinned against brute-force enumeration.

Module: `zeta.finitefield`.

First command:

```bash
.venv/bin/python scripts/11_finite_field_rh.py
```

## What can refute a claim here

| Role | Members | What they are |
|---|---|---|
| **Rivals** (2) | counterfeit Lefschetz profiles, traces 70 and 200 at p = 1009 | integer positive counts with exact self-duality and both roots off the circle, the count-shape without the theorem |
| **Decoys** (2) | count jitter on the Hasse–Weil scale; tower permutation | the sequence without the eigenvalue pair; the numbers without the tower |
| **Surrogates** (2) | uniform-angle and Sato–Tate-angle trace draws | the Hasse bound satisfied by construction, from no curve at all |
| **Lesions** (3) | counterfeit profiles at traces 64, 80, 128 (magnitudes 0.129, 1.02, 2.76 off the circle) | planted violations for detector-power measurement |

Two facts worth knowing before bringing a claim:

- **The payload is counts and nothing else.** Every subject hands claims
  `{"p", "counts"}`; no field says which subject it is. A claim distinguishes
  the target by mathematics or not at all.
- **Lesions are quantised.** The smallest integer trace violating Hasse at
  p = 1009 is 64, so no lesion smaller than magnitude 0.129 can be planted
  without breaking integrality, which would be detectable for the wrong
  reason. Department #1 plants δ = 0.001; this department provably cannot.
  Detector power below the floor is unmeasurable here, and that is a fact
  about the subject, not a defect of the battery.

## Why a counterfeit is a fair rival

Hasse's theorem is *exactly* the statement that no curve realises the
counterfeit profiles: they satisfy every structural constraint the counting
data wears on its sleeve (integrality, positivity, the Lefschetz recursion,
the functional equation) and violate RH. A claim that fires for them is
leaning on structure that provably does not force the property, the same
modus tollens the Davenport–Heilbronn function supplies in department #1,
made exact.
