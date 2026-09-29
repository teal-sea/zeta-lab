# Contained Zeta23 dependency

Source: https://github.com/anthropics/zeta-23-lean at
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, the same revision previously
consumed as a Git dependency. Copyright, Apache-2.0 `LICENSE`, `NOTICE`, and
the original `AUDIT.md` are retained. This laboratory does not claim authorship
of the upstream mathematics or proofs.

Included: the complete `Zeta23/` proof library and `Zeta23.lean`, with their
Lake configuration. The upstream comparator wrappers are not consumed by
the lab's proof and are not copied or declared as libraries here.

This copy permits an in-repository compiler and module-system port without
altering the upstream project. The initial migration adds `module`, public
imports, and exposed public sections. It pins canonical Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55` and Lean `v4.35.0-rc2`.
These edits are not a successful build claim. Build evidence and any
necessary proof-compatibility repairs are recorded by the port's CI runs.
