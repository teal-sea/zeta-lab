# Palomar toolchain and module-format port

Owner-directed continuation of issue #260, starting from `e4945c4b`.

Port the stronger four-point theorem and its consumed proof dependencies to
Lean `v4.35.0-rc2` and the matching canonical Mathlib revision. All regular
Lean sources in this submission repository must use the module system,
including contained projects. Preserve theorem statements, parameter values,
source attribution and historical evidence. No new missing proofs or axioms.

The upstream Zeta23 dependency is still on Lean 4.33. Retain its pinned
source and Apache-2.0 licence in a contained package while porting it; do not
modify the upstream repository or present its work as this lab's.

Allowed scope: Lean sources, their generators, Lake pins/manifests, focused
port tests, staged CI builds, and research evidence documenting this port.
Build on GitHub Actions, not the operator's machines. Checkpoint long runs
and record terminal outcomes, exact revisions, counts and axiom audits.

Completion requires actual builds of the intended submission surface and
its dependencies, not just a lexical header check. Preserve the existing
registered statements and prepare a distinct stronger-result interface.
Do not claim a new Palomar registration as a consequence of this port.
