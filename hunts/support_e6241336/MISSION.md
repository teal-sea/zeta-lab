# MISSION: support run `e6241336`

A support run, not an open hunt. Another run asked one bounded question and is
waiting on the answer, so this directory records the answer and the evidence
behind it, and then it is closed.

**The question, verbatim.** Independently compute
`abs(epstein_completed(0.8+85.7i, (2,1,3)))` at `dps=60` and say whether it
agrees with `1.6e-58` to within an order of magnitude.

**Scope.** One evaluation, one form, one precision, plus whatever validation
that one number needs to be worth quoting. Nothing here is a result about the
Riemann hypothesis and nothing here is evidence for or against it
(`docs/08-why-it-is-hard.md`).

**May write.** `hunts/support_e6241336/` and one case-log entry in
`hunts/README.md`. Nothing else: not `zeta/`, not `harness/`, not `lean/`,
not `meta/`, not another hunt, not a root markdown file.

**Independence.** The parent supplied the number to check. The parent's number
was not consulted while measuring, and the check was not stopped at "it looks
right": three cross-checks were run against routes that do not share
`epstein_completed`'s cancellation, and one defect in the first pass was found
and corrected. See `RESULTS.md`.
