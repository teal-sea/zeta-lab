# Compensated-fold capacity continuation

Continue PR #207 from `02e6780d6c81e91d5151f93a89fb14ec13664cca`.
Consume Fable's latest fold definition from PR #208 at
`f4ae24f027f07916037ca8fe6c56c95a29cbf4d7`, especially Section 8 and
`fold_family.py`. Preserve all earlier results and leave both PRs open.

Independently verify the coordinator's fixed bundle at N=1000,y=31:
Fold(76)+2 Fold(200)+Fold(333). Derive a quantitative sufficient repair
lemma for prescribed components, controlling empty-cell deficits,
nonempty-cell capacity and gain sacrificed by repairs. Separate the
proved conditional mechanism from unproved arithmetic hypotheses needed
for a family. The lemma must do more than restate final feasibility.

Ownership: new notes, exact checks and output in this hunt, a focused test
and generated CONTEXT.md. Fable owns repair construction. No search for
bundles, optimization, larger-N batch, background job or another isolated
top-half counterexample. Use one numerical thread. Commit and push to
#207, leaving it open for cross-review without a merge.
