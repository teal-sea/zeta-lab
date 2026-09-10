# euler_defect_axis: run manifests

```runmanifest
id: euler_defect_axis-2026-09-09-entitlement
hunt: euler_defect_axis
started: 2026-09-09T23:00-05:00
finished: 2026-09-10T00:10-05:00
ran:
  - .venv/bin/python hunts/euler_defect_axis/probe.py
outcome: a(1) is exactly 1 on the 14 principal forms and exactly 0 on the other 27; the identity residual is machine zero on the entitled rows and bounded away from zero on the rest, worst 189.6888; no non-principal form represents only multiples of its least represented value; the class-number-one control c(n) = Lambda(n)(1 + chi_d(n)) agrees with the recursion to 2.8e-30
artifacts:
  - hunts/euler_defect_axis/artifacts/axis.json
```

```runmanifest
id: euler_defect_axis-2026-09-10-audit
hunt: euler_defect_axis
started: 2026-09-10T00:20-05:00
finished: 2026-09-10T00:35-05:00
ran:
  - an independent adversarial audit by a separate agent, given the write-up and the repository and told to break the claim rather than review it
  - .venv/bin/python -c "recount the forms, check R against |1 - a(1)| max|c|, check the 1 + Z_Q reading, re-measure the axis at cutoffs 61, 121, 201, 401"
outcome: verdict survives-with-corrections after eight attacks; eleven overclaims found in the write-up; the three carrying numbers recomputed here before the corrections were accepted (41 forms not 44, R = |1 - a(1)| max|c(n)| to 0.0 on 40 of 41 rows, the published non-principal numbers are the composite defect of 1 + Z_Q(s) to 0.0 on all 27); the axis has no scale, the band running 2.9608-5.0847 at cutoff 61 and 5.0196-10.5748 at cutoff 401 with the ordering unchanged
artifacts:
  - hunts/euler_defect_axis/AUDIT.md
  - hunts/euler_defect_axis/artifacts/cutoff.json
  - hunts/euler_defect_axis/RESULTS.md
  - hunts/euler_defect_axis/PROPOSAL.md
```

## Notes

- **The audit is the reason this hunt's write-up changed, and the claim did not.**
  It ran with the repository in front of it and no part in producing the result.
  It attacked `a(1)` from the definition rather than from the artifact, derived
  the identity from `-f'/f` itself, checked the Kronecker symbol against an
  independent implementation, and searched by least squares for any
  integer-indexed `c` solving the identity for a non-principal form (residual
  2.18 to 5.79, so none exists). Nothing moved the claim. Eleven sentences moved.
- The corrected axis is not this hunt's own reading of the family. It is the
  smallest statement the entitled rows support, and the audit's cutoff sweep is
  the reason it is stated as an ordering rather than as a range.

```runmanifest
id: euler_defect_axis-2026-09-10-ordering
hunt: euler_defect_axis
started: 2026-09-10T04:05-05:00
finished: 2026-09-10T04:10-05:00
ran:
  - .venv/bin/python hunts/euler_defect_axis/ordering.py
outcome: the ordering claim in RESULTS.md section 5 was false and is corrected; the nine discriminants do NOT rank identically at cutoff 61 and 401, -23 and -24 transpose; six of nine positions are fixed at every cutoff and all movement is inside the -20/-23/-24 block; Spearman against cutoff 61 is 0.9500 at 121 and 0.9833 at 201 and 401; the ordering settles by 201, where 201 and 401 agree at rho = 1.0000
artifacts:
  - hunts/euler_defect_axis/ordering.py
  - hunts/euler_defect_axis/artifacts/ordering.json
```

- **Correction, 2026-09-10.** The `outcome:` line of the audit manifest above,
  and five sentences derived from it, said the axis runs from one band to another
  "with the ordering unchanged". That is false. The manifest is left as recorded
  because it is the record of what that run reported; `ordering.py` and the
  manifest directly above this note are the correction, and the five sentences
  are fixed in place in `RESULTS.md`, `PROPOSAL.md` and `hunts/README.md`.

  Two things about how it got in are worth more than the number itself. The
  claim entered during the rewrite the audit prompted, which means it was
  written *after* the adversary had finished and was never attacked by anything.
  An audit fixes the sentences it read; it does not cover the ones its own
  findings cause you to write. And the false version was the stronger and
  tidier claim, "exactly the same order" against "six of nine positions hold",
  which is the direction a summary drifts when nobody is checking. The true
  statement is also the more useful one: the tail of the list is rigid, the head
  is not, and the quantity needs a couple of hundred composites before it orders
  anything reliably.
