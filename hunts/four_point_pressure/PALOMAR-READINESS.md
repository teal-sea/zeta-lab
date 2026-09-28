# Palomar preparation, 2026-09-28

**Not ready for submission.** The proof handoff and the registry's current
compatibility requirements are separate obligations.

## Mathematical target and provenance

The candidate parameters are `(n,c,m,p) = (4,2330/1000000,432,2500)`.
The advertised coefficient is
`(14400000 H - 17240)/14366681`, where
`H = 3/2 - cot(1/sqrt(2))/sqrt(2)`.
An 80-digit numerical evaluation during this intake gave
`0.67286035883886665950020530055393105169837094679127`.
This is a numerical evaluation of the expression, not a completed proof check.

The candidate was generated in commit
`d28df5f992479cd32751cb90c8c88551550582a3` on September 5.
Hermes supplied the module-root repair at
`5522b96314f7f63198ae3ec4e71d954255f93d1a`.
The source preflight passes with 1516 cell lemmas, 11863 leaves, 220 chunks,
13 boxes, and 64 dispatch cases. No proof-bypassing tokens were found in the
candidate Lean source. The successful complete build log and axiom output
reported by Hermes have been requested but are not present at that revision.
The static scan and arithmetic preflight do not substitute for those records.

[SamiYaya's issue #254](https://github.com/teal-sea/zeta-lab/issues/254)
reports a separate parameter tuple, `(4,2320/1000000,434,2500)`, with
coefficient approximately `0.6728536987726761`. Its exact source has not
been rebuilt as part of this intake. Credit that contribution as separately
reported; do not attribute the September 5 candidate to it or imply that its
proof has been incorporated here. Preserve the existing credits to the
upstream zeta formalization and Ainta's argument.

## Current registry compatibility

Checked against these exact upstream revisions:

- [PalomarPolicy CONTRIBUTING.md at 96b034cc](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md),
  sections 2.1, 2.2, and 6.4.
- [PalomarSubmission toolchains.json at 65f0154e](https://github.com/PalomarRegistry/PalomarSubmission/blob/65f0154ed776cd26c224254aa57b379137f28b0d/toolchains.json).

The minimum accepted toolchain is `v4.35.0-rc2`. This candidate and its
bridge pin `v4.33.0-rc2`. The selected toolchain must also match the
authenticated Mathlib revision, so editing the version string alone is not a
port.

New submissions and revisions require the Lean module system throughout the
submitted repository, with at most 10000 physical lines per Lean source
file. The current candidate sources do not use that module format. A static
scan of this integration tree found 324 of 326 tracked Lean source files
without a `module` header, and zero files over the line limit. A compiler
port must set declaration visibility and recheck the proofs, not merely
prepend headers.

Contained path dependencies are now explicitly supported. The candidate's
dependency on `lean/bridge` therefore does not by itself require copying the
generated proof into that directory. Challenge and Solution must be separate
modules inside the selected project. The Challenge's transitive imports may
not include this project's proof development.

## Remaining work

1. Bind the successful Hermes build and six axiom lines to the exact source
   revision, toolchain and dependency pins. Record any uncommitted repairs.
2. Complete an independent rebuild of the selected source on permitted cloud
   compute before promoting the integrated result.
3. Port the submission and its consumed dependencies to an accepted toolchain
   and module format, then build the complete intended submission surface.
4. Prepare a separate Challenge/Solution pair and matching metadata for the
   stronger coefficient. Preserve the existing registered statements.
5. Run Comparator and both kernel checks on the final commit, and stage the
   exact project, comparator and metadata paths.

No new Palomar submission, registration, external mathematical review, or
toolchain migration has occurred in this intake. An external human review is
not listed here as a prerequisite imposed by Palomar.
