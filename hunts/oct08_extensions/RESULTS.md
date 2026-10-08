# October 8 research outcome

Assume QRH(7/8): every nontrivial zero of the Riemann zeta function has real
part at most 7/8. Then every integer n>=1 has a prime strictly between n^7
and (n+1)^7. This is a written conditional implication, independently audited
with source checks and interval arithmetic. It is not Lean-formalized and no
worldwide priority claim is made. The source audit originally omitted the historical critical-line correction
and low-height rounding justification; audits/kln-restoration/ supplies that
argument and Acb verification. The application of the cited KLN density
lemma and the prime-interval calculations are unchanged. The bounded search in literature/prime-gap.md
compares all-n results under full RH and eventual unconditional results;
priority for this precise weaker-assumption statement remains unresolved.

The principal improvement over PR276 is the use of cumulative density layers
with positive coefficients. See routes/prime-gap-multistrip/RESULTS.md for the
proof and exact KLN source rows, and audits/prime-gap-multistrip/ for independent
reconstruction. The 764-cell cover has margin >0.13045; the infinite-tail error
is <0.012961; nine small cases have exact trial-division witnesses. The audit
independently implements the new moments but shares the disclosed inherited
base-bound routine. The eighth-power predecessor and full explicit-formula
source authentication remain under audits/prime-gap/. Sixth powers fail this
particular bound near log(n)=29; this is not a counterexample to prime existence.

The DFT route validates a parameterized form of the upstream network, h>=22,
with an h24 quantitative exponent improvement. Literature checking classifies
that as an optimized instantiation, not a new mechanism. A separate application of a classical fixed-cardinality relation
removes the dependent total-sum wire, attaining central rank h, optimal
for the same side correction. See routes/dft-central-compression/PROOF.md for
its precise exact-complex-field contract. Independent audit passed; see
audits/dft-central-compression/AUDIT.md. At h=24 it gives the conditional
exact-complex cost O(n(log n)^(1-51/10^11)). The 1/3
coefficient prevents automatic transplantation to Gaussian-dyadic integer
multiplication. No practical, numerical-stability or bit-complexity gain is
asserted. All-length transfer remains dependent on pinned upstream lemmas.
The bounded prior-art trace in literature/dft-compression.md identifies
Alon-Babai-Suzuki (1991) as an antecedent for the eliminated dependency.
The circuit application is a checked corollary, not a new compression principle.

Genus-aware partial-form counting is a classical structural filter, improving
1918 of 4055 small cases; it does not establish class-number-list completeness.
The explicit D=-39 omission example defeats that interpretation. The source
leaf and independent audit of this auxiliary route remain open; no H1500 gain
is established. Cremona-Sutherland's earlier GRH table through h1000, including
even class numbers, is acknowledged.

No accepted new primality algorithm resulted. The external model response had
concrete errors; routes/algorithm/RESULTS.md and falsify.py preserve their
rejection, while raw operational records remain outside the hunt. Unsuccessful
routes are not impossibility results.

## Reproduction and provenance

Original research base f4ef0715bbe2f4890b3dcea034757ef0c823053a.
Publication package rebased locally onto public main
ff6ff91456fa5b693de832153266671b869c71a1, branch research/oct08-consequences.
The local commit packages the hunt and two index entries. No push or merge. See MISSION.md for the
three prior PR source SHAs and route contracts. Run Python scripts from the
isolated lab root using .venv/bin/python; scripts locate sibling source files
relative to their own path. CHECKSUMS.sha256 records the imported snapshot.
Run evidence and audit reports disclose exact versions and precision.
Required lab checks: 52 passed, 5 slow tests deselected, 3 expected failures; context check passed.
No full baseline test suite or Lean replay was run.

## Remaining doors

Seventh-power conditional proof has passed ordinary independent audit; external
human review, formalization and a comprehensive novelty search are separate.
The sixth-power bound loses at the height transition. Central rank is optimal
only for a fixed linear correction; new side matrices or binary label families
remain open. Class-list completeness requires information beyond balanced genus
counts. No paid compute or shared worktree changes were required.
