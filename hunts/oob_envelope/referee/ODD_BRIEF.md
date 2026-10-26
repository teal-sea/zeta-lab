# Odd-sector independent review, L = 119/100

Owner: Claude Code referee, branch `teal-sea/oob-odd-referee`, this checkout only. Thomas approved the follow-up. Commit scoped work, do not push or open a PR without supervisor review. Write under `hunts/oob_envelope/referee/` only. Repo instructions apply, including the banned reserved word under hunts and no em dashes in authored prose. Do not edit the numerics lane.

## Target and independence

Independently reconstruct the real odd-sector lower bound for the Weil form at half-width L = 1.19 with the sine:16 out-of-band envelope. The first implementation is at `../oob-odd/hunts/oob_envelope/numerics/` (commit 08ff0491), with main endpoint 3.42853488205e-44 and even endpoint 5.71789230595e-48. That code and result are **comparison targets, not source code to copy**. Build on the independently authored referee code under this directory from the prior even-sector campaign, plus Zhu arXiv:2608.24827v2 §6 and the published analytic theory. Freeze your formulas and target shift before reading the odd worker implementation. No shared quadrature or Bessel/tail helper functions from the odd implementation.

1. Audit the odd reduction: Fourier basis/sign (`j_(2i+1)`), pole vector and **negative** rank-one pole term, odd tails with first omitted order 1001, exact support cancellation of H (including frequency 2L), complex and parity split, all inequalities and norms. State whether any gap invalidates the full-complex claim.
2. Independent computation on Modal, preferably the existing referee Clenshaw-Curtis/Arb pathway adapted to odd basis, at L=4/5, T#=150, H=0 matching Zhu §6.2, then L=119/100, T#=500, same sine:16 envelope. Build independent interval enclosures of head entries, integration error, tail and coupling, and a dyadic LDL/factor residual. A positive lower endpoint should be safely below 3.428e-44 yet above zero. If calculation cannot close, give an honest failed/inconclusive verdict.
3. One fault injection that distinguishes odd pole sign or odd indices at L=1.19 and genuinely affects the result, plus a negative control that returns no positive bound. Compare against first implementation only after independent result frozen. Record successes, failures, inconclusives separately.
4. Save source, inputs, full error budget, controls, Modal app IDs and state, exact endpoint representation, versions, measured runtime, and SHA-256 manifest under `referee/outputs_odd/`; concise `referee/ODD_REVIEW.md` with verdict and shortcomings. Every mathematical assertion is traced to a source or proved. Do not call a single software route kernel-checked or peer reviewed.

## Budget and host

- No heavy work on Ghost. Modal profile `teal-sea` only for computation; worktree is local for editing, reading, py_compile, and tiny sanity tests.
- Cap incremental odd-review Modal input compute at 4 core-hours. Time one unit, write the extrapolated estimate to `referee/ODD_RUNS.md` **before** main launch. Checkpoint each unit. Stop and report if the estimate exceeds the cap. No indefinite, detached app; watch terminal states and stop owned apps.
- Start from the prior referee's CC implementation but derive odd mathematics yourself. Avoid costly reconstruction if the old code has reusable quadrature bounds; do not import from the numerics worker.
- Run affected repo hygiene and contribution tests off-host if needed. Reserve publication and cross-domain decision for supervisor.

Five-line final: verdict, independent odd endpoint (or blocker), validation vs Zhu, execution counts/core-hours/app states, commit hash and any unresolved caveat.
