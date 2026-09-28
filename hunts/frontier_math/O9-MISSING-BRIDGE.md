# O9: the assembly is blocked by an identity nobody proved

**2026-08-13.** Found by trying to perform the final assembly and failing.
Nothing here is kernel-checked, nothing here is evidence about RH.

## The finding

The O9 soundness chain has two halves that have never been connected in Lean.

**The analysis half** lives in `EForm3/`. `Qre` and `Qim` are *integrals*:

```lean
noncomputable def Qre (a b : ℝ) : ℝ := ∫ u : ℝ, g u * Real.cosh (a * u) * Real.cos (b * u)
noncomputable def Qim (a b : ℝ) : ℝ := ∫ u : ℝ, g u * Real.sinh (a * u) * Real.sin (b * u)
```

`Dam`, the damage O9 bounds, is `Qim² − Qre²`. Every soundness lemma proved this
session, the `y = 0` split, both modes, `dam_le_of_branch`, is stated about
these.

**The interval half** lives in `BandCert/`. `Phi2` is a *closed form*:

```lean
noncomputable def Phi2 (z : ℂ) : ℂ := sfunC (z + √2) + sfunC (z - √2)
```

and `boxParts`, `qreIv`, `rIv` compute enclosures of *that*, through
`Phi2_closed`'s single-fraction form `2(z sin(z/2)cos(√2/2) − √2 cos(z/2)
sin(√2/2)) / (z² − 2)`.

**Nothing relates them.** Measured, not inferred:

```
mentions of Qre/Qim anywhere in BandCert/ (where Phi2 lives):        0
mentions of Phi2 in EForm3/ClosedForm.lean (where Qre_closed lives): 0
```

The identity the chain needs is

    Re (Phi2 (s + i y)) = Qre y s        and        Im (Phi2 (s + i y)) = − Qim y s

It is recorded in `arm_identification.py` as `ghat z = Phi2 (-I z)`, and it is
repeated in several Lean docstrings, including ones this session wrote. It is
proved in no Lean file.

## Why this was not visible until now

Every piece on either side is individually sound, and each side is internally
consistent, so nothing failed to compile and no `#print axioms` reported
anything unusual. The gap is not in a proof; it is *between* two towers of
proofs that were built from opposite ends and never joined.

It became visible only on trying to instantiate the final statement, which
needed `Qre y s` on one side and `qreIv`'s enclosure on the other and had no
lemma to put between them.

This is the defect class `PROOF-LEDGER.md` logs repeatedly, *a quantity
carried across contexts without being re-derived in the context it is used*.
Here the carrier was a Python script and a docstring, and the contexts were two
Lean directories.

## What it costs

Not fatal, and not small.

The structural route is visible: `Qre_closed` already gives `Qre a b` in the
two-pole form (a sum of two fractions with denominators `a² + (b ± √2)²`), and
`Phi2_closed` gives the single-fraction form over `z² − 2`. Those are the same
function written two ways, so the identity is algebra over the reals once
`sfunC` is expanded at a complex argument into real and imaginary parts, not a
new integral computation, and not new mathematics.

But it is a real proof obligation of its own, and it is load-bearing: **without
it, every O9 soundness lemma proved this session is a true statement about
`Dam` that the table cannot reach**, because the table decides facts about
`Phi2`.

## Status

O9 remains open, and the honest statement of where it stands is:

* the 699-cell table decides at kernel grade, all 18 chunks;
* the generator's leaves and compositions are pinned to Lean's own integers
  (14/14 and 10/10);
* twenty-four soundness lemmas are kernel-checked, covering both modes, both
  compositions, all seven `boxParts` fields, the removable branch and its
  truncation bound;
* and none of that yet proves `Dam y s ≤ c y²`, because the bridge above does
  not exist.

No `sorry` stands in for it, and none should.
