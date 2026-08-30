/-
Root of the `Erdos` library.

Erdős-problem statements live under `Erdos/` and each begins with
`import FormalConjecturesUtil`, exactly as the upstream
`FormalConjectures/ErdosProblems/*.lean` files do. This root exists so that
`lake build Erdos` resolves the vendored `FormalConjecturesUtil` (and through
it `FormalConjecturesForMathlib`) even before any problem file is added; the
`Erdos.*` glob in `lakefile.toml` picks up `Erdos/*.lean` automatically.
-/
import FormalConjecturesUtil
