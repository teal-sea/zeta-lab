# external/ — cloned outside repositories (untracked, like `automation/`)

Fetched 2026-08-11. Nothing here is part of the laboratory; these are other
people's artifacts, kept local so instruments and literature checks can
collide with them offline. Re-clone to update; all are `--depth 1`.

| directory | what it is | why it is here |
| --- | --- | --- |
| `alphaproof-nexus-results` | DeepMind's kernel-checked Lean proofs (9 formerly-open Erdős problems, 44 OEIS conjectures) + prose proofs. A Lean package (`lakefile.toml`, pinned toolchain) — the proofs can be lake-built and kernel-checked *here*, not taken on faith. | prior-art surface for the literature scout; worked corpus of machine-generated formal proofs |
| `formal-conjectures` | DeepMind's collection of open conjectures formalized in Lean — includes `Millenium/RiemannHypothesis.lean`, `Wikipedia/RiemannZetaValues.lean`. | canonical formal statements to target or cite; candidate statements for the proof-agent adapter |
| `alphaevolve_results` | DeepMind's published AlphaEvolve result artifacts. | reference for what the closed system produced |
| `alphaevolve_repository_of_problems` | DeepMind's problem suite for AlphaEvolve-class systems. | benchmark problems for any oracle-scored evolution instrument |
| `openevolve` | Open-source AlphaEvolve implementation (v0.3.2 also installed in `.venv-tools`). | the runnable evolution instrument; LLM endpoint configurable |
| `science-codeevolve` | CodeEvolve — open framework, matches/beats AlphaEvolve on 5/9 of its own benchmarks (arXiv 2510.14150). | second, independent evolution implementation |
| `alphaevolve-on-googlecloud` | Google's client examples for the GA AlphaEvolve service (Gemini Enterprise Agent Platform, generally available since July 2026). | the path to the *real* AlphaEvolve: client-side evaluator + cloud API |

## Tool interpreters

`.venv-tools/` at the repository root — a venv **separate from the lab's pinned
`.venv`** (never install tooling into the lab venv while agents are live).
Installed: `openevolve 0.3.2`, `aristotlelib 2.1.0`.

## What still needs a human

- **AlphaEvolve (the real one)**: a Google Cloud account + Agent Platform
  onboarding (`console.cloud.google.com/agent-platform/overview`). The
  evaluator runs client-side; only the mutation engine is theirs.
- **Aristotle**: DONE (2026-08-11) — key created by the operator, stored in
  `~/.zshrc` as `ARISTOTLE_API_KEY`, authenticated live; submit/collect via
  `lean/proof_adapter.py` with `.venv-tools/bin/python`.
- **OpenEvolve/CodeEvolve**: an LLM endpoint (any OpenAI-compatible URL) in
  their config before a run.

House rules still apply to anything these produce: an external system's
output is input, not evidence — Lean artifacts count when *this* repo's
`lake build` shows zero `sorry`s, and numeric claims count when the lab's
own instruments enclose them.
