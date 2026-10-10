# Palomar preparation, updated 2026-09-29

**Lab module/toolchain port and exported-proof comparison verified.** The
stronger proof and its interface build on Lean 4.35. Lean, NanoDa and con-ron
accepted the exported solution, and all 645 tracked Lean headers passed the
compiler's parser. This is not a Palomar submission or registry verdict.
Historical build evidence below remains at its original pins.

**The submission package, 2026-10-10.** The registry-ready form of this
project lives on branch `codex/palomar-root-package` (head `980bf37`), not on
main. Commit `74611e8` there adds `lakefile.toml`, `lake-manifest.json` and
`lean-toolchain` at the repository root, because Palomar's renderer rejects a
nested project path; `980bf37` adds the pinned render check. Palomar's own
pipeline (`PalomarRegistry/PalomarSubmission` at `65f0154`) passed its full
preflight on the nested snapshot `020a974` (run 36733933889) and on the root
package `74611e8` with an empty project path (run 36873320494), and the
original renderer accepted the root package. The packet, the bounded-memory
build and the retained preflight reports are on that branch, built up in PRs
#263, #264 and #265, which were closed rather than merged so that main's root
stays a single project. Submitting `74611e8` is the remaining step. Nothing
has been submitted, so this is still not a registry verdict.

## Mathematical target and provenance

The candidate parameters are `(n,c,m,p) = (4,2330/1000000,432,2500)`.
The advertised coefficient is
`(14400000 H - 17240)/14366681`, where
`H = 3/2 - cot(1/sqrt(2))/sqrt(2)`.
An 80-digit numerical evaluation during this intake gave
`0.67286035883886665950020530055393105169837094679127`.
This decimal is a numerical evaluation of the exact theorem coefficient.

The candidate was generated in commit
`d28df5f992479cd32751cb90c8c88551550582a3` on September 5.
Hermes supplied the module-root repair at
`5522b96314f7f63198ae3ec4e71d954255f93d1a`.
The source preflight passes with 1516 cell lemmas, 11863 leaves, 220 chunks,
13 boxes, and 64 dispatch cases. No proof-bypassing tokens were found in the
candidate Lean source. Hermes published the successful build record at
`5723f194ba1c510f1cf480a5404b3147d61a7c89`: 49 successful receipts
(preflight and 48 build layers), zero sorry warnings, and six axiom reports
containing only `propext`, `Classical.choice`, and `Quot.sound`.
The intake audit reproduced both recorded source-tree hashes from Git
objects at `5522b963` and retained a per-file manifest. The candidate was
byte-identical to those 51 source files at integration commit `4888f310`.
The subsequent module-format port changes headers and public visibility;
it requires a fresh build and does not inherit the old build's status.

This is the lab's kernel-checked result at the pinned revision, not an
independent replay or a registry verification. The saved-image build spans
several launches; missing earlier launch logs and incomplete image-lineage
records are stated in [the evidence record](evidence/README.md). No fresh
Lean build of the merged checkout was performed during intake.

[SamiYaya's issue #254](https://github.com/teal-sea/zeta-lab/issues/254)
reports a separate parameter tuple, `(4,2320/1000000,434,2500)`, with
coefficient approximately `0.6728536987726761`. Its exact source has not
been rebuilt as part of this intake. Credit that contribution as separately
reported; do not attribute the September 5 candidate to it or imply that its
proof has been incorporated here. Preserve the existing credits to the
upstream zeta formalization and Ainta's argument.

## Registry requirements and intake baseline

Checked against these exact upstream revisions:

- [PalomarPolicy CONTRIBUTING.md at 96b034cc](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md),
  sections 2.1, 2.2, and 6.4.
- [PalomarSubmission toolchains.json at 65f0154e](https://github.com/PalomarRegistry/PalomarSubmission/blob/65f0154ed776cd26c224254aa57b379137f28b0d/toolchains.json).

The minimum accepted toolchain is `v4.35.0-rc2`. At intake, the candidate and
its bridge pinned `v4.33.0-rc2`. The selected toolchain must also match the
authenticated Mathlib revision, so editing the version string alone is not a
port.

New submissions and revisions require the Lean module system throughout the
submitted repository, with at most 10000 physical lines per Lean source
file. The candidate sources did not use that module format at intake. A static
scan of the integration tree found 324 of 326 tracked Lean source files
without a `module` header, and zero files over the line limit. A compiler
port must set declaration visibility and recheck the proofs, not merely
prepend headers.

Contained path dependencies are now explicitly supported. The candidate's
dependency on `lean/bridge` therefore does not by itself require copying the
generated proof into that directory. Challenge and Solution must be separate
modules inside the selected project. The Challenge's transitive imports may
not include this project's proof development.

## Submission boundary

The stronger interface is paired with its own metadata under
`hunts/ainta_seven_point/lean-four-point`: `comparator.json` selects
`StrongerChallenge` and `StrongerSolution`, and `formalization.yaml` describes
exactly the two selected declarations. Existing registered statements are
unchanged. The lab's incremental build and comparison do not substitute for
Palomar's fresh protected-source pipeline or its editorial decision.

No new Palomar submission, registration, or external mathematical review has
occurred. An external human review is not listed here as a prerequisite
imposed by Palomar.

## Port start, 2026-09-28

The owner authorized issue #260's compiler and module-format port. All six
contained Lake packages now target Lean `v4.35.0-rc2`, with canonical Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The previously pinned Zeta23
source is retained as a contained dependency with its licence and attribution,
because upstream itself still uses Lean 4.33.

The initial 643-file Lean inventory has module headers, public imports and
exposed public sections. This is source preparation, not proof verification.
The first CI pilot builds `Zeta23.Defs.Counting` on the new toolchain to
measure one unit before allocating the full build. Cache retrieval must
succeed; the pilot will not silently compile Mathlib from source. Its build
is bounded at 15 minutes, checkpoints its Lake state, and publishes logs,
source SHA, artifact counts and a terminal verdict, including failures.

The analytic bridge subsequently passed in Actions run `36505843011` at
`e9621a24948224acebca6e39980bdb0ea57db788`: all 157 local modules in the
target's import closure built, and `n_point_bound` prints only the standard
axioms. Its raw evidence is in `port-evidence/36505843011/`. This verifies
the analytic dependency, not the generated stronger certificate or a
Challenge/Solution comparison. Those remain separate obligations.

The certificate pilot also passed: `Base` and `Cells0` compiled in run
`36506410217` at `f7c904f5`, with no candidate proof-body changes. All 25
remaining cell modules passed in run `36507629432` at `caf8a5b3`. The
16 chunk modules passed across pilot `36602330694` at `30423c16` and
matrix `36604651267` at `265191fd`. Raw per-unit evidence is retained under
`port-evidence/`. Final assembly and both interfaces subsequently passed in
run `36633942493` at `a6e55b69`, with six final theorem axiom reports and two
interface reports using exactly the standard three axioms.

The stronger interface is prepared in the candidate project as
`StrongerChallenge.lean`, `StrongerSolution.lean` and `comparator.json`, in
the distinct namespace `Zeta23Ext.PalomarFourPoint`. It selects the bound
and ratio statements, with the exact coefficient above and no certificate
hypothesis. Challenge imports Mathlib alone and has exactly two deliberate
statement placeholders. Solution imports the candidate proof, not Challenge,
and ties the copied counting functions and constant to that development.
Static tests compare both statements with the candidate source and check
the import separation. Matching metadata is paired through
`lean/palomar-pairs.json`. Existing registered statements and their comparator
are unchanged.

The [verifier at PalomarSubmission commit `65f0154e`](https://github.com/PalomarRegistry/PalomarSubmission/blob/65f0154ed776cd26c224254aa57b379137f28b0d/scripts/verify_submission.py)
uses the selected
release's bundled `lake comparator`, `leanexport` and `leanchecker`, with
NanoDa and con-ron as its two external kernels. This is the setup to check
after compilation, not the separate legacy Comparator repository's build.
The local precheck now compares release-candidate versions against the
actual `v4.35.0-rc2` floor. Its output remains a partial preparation check,
not a substitute for the authoritative verifier.

## Port verification, 2026-09-29

[Actions run 36637271632](https://github.com/teal-sea/zeta-lab/actions/runs/36637271632)
at `3ee65788397d0eed8c4743704492dae159cde521` passed the stronger-pair
comparison. Lean default, NanoDa and con-ron each accepted the solution.
The matching control passed; the intentionally mismatched statement was
rejected as a statement mismatch, not an infrastructure error. Lean's
`--deps-json` parser accepted all 645 tracked source headers as modules.
The comparison procedure took 1272.61 seconds including controls and exports.

All 48 original candidate proof bodies are unchanged after normalizing only
the module-format additions. The consumed analytic import closure and both
new interface modules were built. Unused vendored modules and unrelated
Lean package targets were header-checked, not all build-verified. This exact
scope, the incremental checkpoints, earlier failed attempts and historical
evidence limitations remain part of the record; none implies registry
acceptance or outside mathematical review.
