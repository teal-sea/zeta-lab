# Aristotle handoff for the RAMS2 partial-summation layer

## Purpose

The finite logarithmic mean square is now present in Lean. Its RC2
specialization reduces the remaining coefficient bookkeeping to two explicit
endpoint-energy sums. This handoff records how Harmonic Aristotle is being
used on the next bounded formal task.

No Aristotle output is accepted directly into the formal tree. Every returned
file must compile under the repository's pinned Lean toolchain, contain no
`sorry` or `admit`, introduce no new axiom, and survive the existing regression
battery.

## Submitted jobs

### Full-project job

- Project: `0701719a-f8ee-4a1c-8caf-b028c852dd3b`
- Task: `b4e953db-32be-4421-a495-c7266ab9cf87`
- Input: the complete `lean/` project
- Requested output: a `RAMS2PartialSummation` module containing finite Abel
  summation and weighted-energy consequences
- Toolchain issue: the repository pins Lean `v4.33.0-rc2`, while the service
  currently recommends Lean `v4.28.0`

### Narrow control job

- Project: `0c219065-d00c-497c-9e3c-f5ea2fbdacb1`
- Task: `4dc6435e-61b1-4814-9a15-f534f145b8e4`
- Input: a minimal Lean `v4.28.0` project with one theorem
- Requested output: the exact finite Abel identity on positive natural
  indices

The narrow job separates theorem-search difficulty from whole-project upload,
dependency, and toolchain effects. Agreement between the two jobs is useful,
but local kernel acceptance under `v4.33.0-rc2` is still mandatory.

## Exact target

For

\[
 A(N)=\sum_{1\leq n\leq N} b_n,
\]

the first target is

\[
 \sum_{1\leq n\leq N} b_n w_n
 =A(N)w_N+
 \sum_{1\leq n<N}A(n)(w_n-w_{n+1}).
\]

The RC2 application takes `b_n=|a_2(n)|^2`. From a prefix estimate

\[
 A(y)\leq C y(1+\log y),
\]

the desired consequences are

\[
 x^{-2}\sum_{n\leq x}b_n n^2\ll Cx(1+\log x)
\]

and

\[
 x^2\sum_{x<n\leq W}b_n n^{-2}
 \ll Cx(1+\log x),
\]

with the second bound independent of `W`.

## Promotion checklist

1. Download the returned source without overwriting repository files.
2. Inspect theorem statements for weakening, added assumptions, or convention
   changes.
3. Port the proof to the pinned toolchain.
4. Run the target Lean build and the full Lean build.
5. Scan the new module for `sorry`, `admit`, and new axioms.
6. Connect the result to `twoRangeEndpointEnergy_eq` and
   `norm_twoRange_mean_square_sub_diagonal_le`.
7. Update `LEAN-FRONTIER.md` only with what survives the local build.

## Throughput measurement

The effect of Aristotle is measured here rather than described from
impression. The comparison unit is a locally accepted theorem line, not an API
submission or a generated file.

### Manual and parallel-agent baseline

The immediately preceding finite-mean-square batch produced four Lean modules:

| module | Lean lines |
| --- | ---: |
| `PowerMargin` | 88 |
| `TwoRangeWeights` | 259 |
| `ComplexLogMeanValue` | 227 |
| `MeanSquareAssembly` | 111 |
| total | 685 |

The first module commit was recorded at `2026-08-11 22:51:34 -05:00`; the
integrated assembly commit was recorded at `23:45:06`. The observable
commit-to-integration window was therefore 53 minutes 32 seconds. This is a
lower bound on total work because it excludes activity before the first
commit. Three isolated worktrees handled the independent modules in parallel.

### Aristotle batch

| event | local time | status |
| --- | --- | --- |
| full-project submission | `2026-08-11 23:55:20 -05:00` | complete |
| narrow Abel submission | `2026-08-12 00:03:27 -05:00` | complete |
| narrow completion | `2026-08-12 00:16:32 -05:00` | 13m 04.763s service wall time |
| broad completion | `2026-08-12 00:26:57 -05:00` | 31m 37.411s service wall time |
| broad pinned-toolchain acceptance | `2026-08-12 00:32` | unchanged source |
| integrated broad commit | `2026-08-12 00:32:41 -05:00` | `25c166d` |

The broad artifact contains 393 total lines and 310 non-comment, nonblank Lean
lines. It supplies half-open Abel summation, the lower `n^2` endpoint bound,
and a cutoff-independent inverse-square tail with explicit constant `10`.
The theorem statements were not weakened. The service worker built under Lean
`v4.28.0`. A clean merged-tree build under Lean `v4.33.0-rc2` required one
compatibility repair: deleting a redundant `ring` after `simp` had already
closed the narrow control case. Repair time was under one minute. The source
scan found no `sorry`, `admit`, declared axiom, `unsafe`, or `native_decide`.

The broad service produced 9.80 accepted non-comment lines per minute. From
submission to the integrated commit, the window was 37m 21s, or 8.30 accepted
non-comment lines per minute. The previous three-worktree baseline was 685
total Lean lines in 53m 32s, or 12.80 total lines per minute. These rates do
not establish a raw wall-clock speedup because the theorem sets and line-count
definitions differ. The measured Aristotle advantage in this batch is
different: autonomous closure of both endpoint bounds with a one-line local
repair after submission.

An independent local lane proposed the same cutoff-independent structure with
the sharper constant `4`. Its isolated-branch report claimed a passing build,
but a clean merged-tree build exposed parser errors and unfinished
elaboration. The module was removed and the constant `4` is not part of the
formal result. This lesion is useful: branch-local status is not evidence
until the merged tree rebuilds the source.

A second local Abel control used a different `Finset.sum_Ico_by_parts` route,
but its final build was interrupted under concurrent compiler load, so it is
not counted as an accepted comparison.

The primary comparison is end-to-end time per locally accepted theorem. A
secondary comparison records human repair time. Parallel service time and
parallel local-agent time remain separate columns, since collapsing them would
overstate either method.

## Boundary after this handoff

The finite partial-summation bounds are closed. They do not formalize the
RAMS2 cluster asymptotic itself. The next genuine input is now the uniform
prefix square-density theorem for the level-two coefficient family, followed
by the marked-cluster height-freezing estimate.
