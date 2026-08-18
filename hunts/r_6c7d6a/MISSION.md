# Hunt R-6C7D6A: the numerator-side `boxParts` fields

Run `4df2ee65-1c9a-4e3b-8f7d-2a6b9c4e0f11`, branch `hunt/r-6c7d6a-4df2ee65`,
budget 75 minutes, no operator supervision. Case-log entry: **Hunt #42**,
assigned by the brief and free when claimed (the log's highest existing
number was #37).

## The question

Supply the numerator-side `boxParts` fields of the O9 two-dimensional
checker: the trig and hyperbolic leaf enclosures, in the style `O9Parts.lean`
used for the denominator, so that the composition lemmas of `O9Assemble.lean`
can consume them.

## What this hunt may write

`hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/*` inside the vendored
`Zeta23Ext` Lean package, this directory, and one case-log entry in
`hunts/README.md`. Nothing else. Two other runs were live in this repository
in disjoint lanes (`hunts/frontier_math/*.py`, and `scripts/6*_rung3_*` with
`lean/ZetaLean/Pub1/`); neither was touched and no collision was observed.

## The situation as found, which is not the situation as briefed

The brief was written from `O9Parts.lean`'s own header, which says the
numerator side "is not in this file and no `sorry` stands in for it". That
sentence was true when written and was superseded seven minutes later by
commit `6f81078`, "O9: the numerator half, and every `boxParts` field is now
sound". So `O9Num.lean` already existed on both `main` and this branch,
carrying `reNum_mem` and `imNumOverY_mem` with zero sorrys.

That commit's message overstates its own reach, and finding out how is what
this hunt actually did. `Parts` has **seven** fields, not six. Six had
enclosure lemmas. The seventh, `imNum`, had none, and it is a hypothesis of
`qreIv_mem` — so the `Qre` composition could not be instantiated at a box.
The remaining numerator field was `imNum`, and this hunt supplies it.

```huntspec
id: r_6c7d6a
question: Can every numerator-side boxParts field of the O9 two-dimensional checker be given a zero-sorry enclosure lemma, so that the qreIv and rIv composition lemmas can be instantiated at a box?
frontier: O9Parts supplies reDen, imDen, imDenOverY, denAbs2; O9Num supplies reNum and imNumOverY; the seventh field imNum has no lemma, and qreIv_mem takes one as a hypothesis
proposed_attack: derive imNum from imNumOverY times the box's Y with the component left abstract, in the idiom O9Seam and O9Assemble already use, then discharge every hypothesis of the two composition lemmas at one box
dead_routes:
  - writing the trigonometric expressions out at the composition layer, which couples it to the leaves and forces a reproof when they move
  - a sorry standing in for any field, which the Lean arm counts as nothing
  - weakening a field statement to make it close
required_oracles:
  - the Lean 4 kernel via lake build, zero sorrys and standard axioms only
  - print axioms over every new declaration, aggregated in O9Audit
kill_conditions:
  - the toolchain will not install or Mathlib will not fetch
  - the 75 minute budget is exhausted
  - a field would need a weakened statement
agents_may:
  - search
  - derive
  - code
  - formalize
  - report an exact obstruction as the result
agents_may_not:
  - assign epistemic status to their own output
  - claim the reserved certification word outside zeta/rigor.py and the Lean arm
  - claim O9 soundness closed unless the chain closes
  - touch meta/, harness/, any root markdown file, or the other live lanes
```

## Standing rules

Nothing here is evidence for or against RH (`docs/08`). Nothing in `hunts/`
is a result until it has been through the battery or the funnel.
