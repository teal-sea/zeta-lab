# Palomar preparation, 2026-09-28

**Lab kernel build recorded; module/toolchain port in progress.** The proof
handoff is complete. The port is not yet build-verified or ready for Palomar
submission. Historical build evidence below remains at its original pins.

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

## Remaining work

1. Port the submission and its consumed dependencies to an accepted toolchain
   and module format, then build the complete intended submission surface.
2. Prepare a separate Challenge/Solution pair and matching metadata for the
   stronger coefficient. Preserve the existing registered statements.
3. Run Comparator and both kernel checks on the final commit, and stage the
   exact project, comparator and metadata paths.

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
`36506410217` at `f7c904f5`, with no candidate proof-body changes. The other
25 cell modules, 16 chunk modules, final assembly and final axiom audit
remain to be rebuilt on Lean 4.35.

The stronger interface is prepared in the candidate project as
`StrongerChallenge.lean`, `StrongerSolution.lean` and `comparator.json`, in
the distinct namespace `Zeta23Ext.PalomarFourPoint`. It selects the bound
and ratio statements, with the exact coefficient above and no certificate
hypothesis. Challenge imports Mathlib alone and has exactly two deliberate
statement placeholders. Solution imports the candidate proof, not Challenge,
and ties the copied counting functions and constant to that development.
Static tests compare both statements with the candidate source and check
the import separation. Compilation, Comparator, NanoDa and matching
formalization metadata are still pending. Existing registered statements
and their comparator are unchanged.
