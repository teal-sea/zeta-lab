# Upper bound for nonnegative halving-fold coefficients

Continue PR #207 from `cce45bd2bb3a9c1715ef2d4ad6269481dda5ed42`.
Input comparison: Fable's PR #208 at
`a343fed9b396bfa32b7f415576842e8c051458b5`. Leave both PRs open.
The 615-unit bundle is completed work and must not be regrouped or checked
again in this continuation.

Independently verify the coordinator's rational B/1387 on every attainable
halving-fold column at N=10000,y=100, including empty-source columns.
Enclose its logarithmic cost and prove the upper-bound signs. Identify
exactly the nonnegative coefficient family that cannot attain the saved
132.729535 prefix-exchange gain. Check the descending signed-fold
recurrence and completeness under attainable-prefix assumptions, including
prefix reconstruction. This is triangular algebra, not a new arithmetic
estimate or a rule selecting feasible signed coefficients.

Ownership: new note, exact checker, input, output and computation manifest
in this hunt, one focused test, generated CONTEXT.md. Fable owns converting
the existing witness and its construction search. No new optimizer,
matching-optimum calculation, witness-coordinate search, larger-N batch or
background research job. One numerical thread; fixed bounded checks only.
Preserve all prior outputs. Commit and push to #207 without merging.
