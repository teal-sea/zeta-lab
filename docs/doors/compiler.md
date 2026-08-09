# Department: `compiler`

LLVM IR rewrites — department #3, and the first whose subject shares no
vocabulary with the mathematics: programs, not functions. It exists because
the harness claims to be domain-agnostic, and a claim like that is an argument
until a foreign subject arrives to measure it.

**Declared in** `harness/departments/compiler_department.py`.
**Audited by** `tests/test_department_conformance.py`.
**History in** `compiler/FINDINGS.md` — it spent its first day as an
unregistered candidate, and the findings document records the two measured
blockers and what cleared them.

## What it studies

Whether a proposed peephole rewrite deserves belief, separated from whether it
is shorter. Every program is eight lines of IR with the signature
`i8 @f(i8 %x, i8 %y)`, so the whole input space is 65536 points and a human
can check each fixture by eye.

Modules: `compiler.semantics`, `compiler.catalog`.

First command:

```bash
.venv/bin/python -m pytest -q -o addopts='' tests/test_compiler_candidate.py
```

## The evidence ladder

Two backends, which check each other at every point where both can speak —
the same two-backend habit as `zeta/rigor.py`, without borrowing that
module's vocabulary:

1. **`clang.exhaustive_i8`** — compile both programs and compare outputs on
   all 65536 inputs at `-O0` and `-O2`. Establishes agreement on the
   enumerated domain; *provably blind to poison*, because a compiled binary
   returns the wrapped value either way.
2. **`pymodel.refinement_i8`** — a hand-written poison-aware model of the
   supported subset, run exhaustively. Decides refinement *with respect to
   the model*: it sees value disagreements, the poison class, and immediate
   UB. Its claims are about the model's reading of the LangRef, not about
   LLVM — which is why the cross-check against compiled output exists and is
   pinned for every fixture.
3. **Alive2** (absent) — refinement under LLVM's own semantics; the rung this
   department still does not have, named in `backend_status()` rather than
   hidden.

## What can refute a claim here

| Role | Members | What they are |
|---|---|---|
| **Rivals** (3) | `sdiv2_to_ashr`, `udiv4_to_ashr`, `slt_to_sign_of_difference` | rewrites a competent person has written on purpose, each matching the target's instruction count exactly, each wrong on 16384–32768 of 65536 inputs |
| **Decoys** (2) | narrow input window; constant input set | same *number* of tests, no reach — the sdiv rival scores 0.75 on the full domain and a perfect 1.00 on both decoys |
| **Surrogates** (3) | unguided opcode mutants, seeds 11/23/57 | the search generator with the part that knows what it is doing removed |
| **Lesions** (4) | predicate signedness, strict→non-strict, single-point special case, `nsw` on a wrapping shift | planted violations spanning four orders of magnitude, one of them invisible to rung 1 by construction |

Two facts worth knowing before bringing a claim:

- **Shorter is not evidence.** All three rivals match the target's
  instruction count. The rejected reference claim (`no_more_instructions`)
  makes that a measurement rather than a maxim.
- **The two detectors have measured, different power.** The concrete run
  finds one wrong answer in 65536 and misses a poison violation covering
  half the domain (`blind_to` names it); the model detector sees all four
  lesions at exactly their declared magnitudes. Which detector a verdict
  used is part of the verdict — quote `EVIDENCE_EXHAUSTIVE_I8` or
  `EVIDENCE_MODEL_I8` with it, verbatim.
