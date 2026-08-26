#!/usr/bin/env python3
"""Assemble the riemannzeta.fun one-file submission from lean/bridge.

The site takes one Lean file, at most 2,000,000 bytes (MAX_DIRECT_SOLUTION_BYTES
in josusanmartin/riemann, src/lib/direct-submission.ts), importing
ChallengeDeps.CandidateSpec, with every helper inline. Its verifier checks out
anthropics/zeta-23-lean at 3635e74826a4 -- the commit lean/bridge already
requires -- so Zeta23 and Mathlib are imported rather than inlined; only this
repository's own modules are concatenated.

Run from lean/bridge:  python3 ../../hunts/riemann_fail/assemble.py > Solution.lean
"""
import pathlib, sys

HERE = pathlib.Path(__file__).parent
ORDER = (HERE / "module_order.txt").read_text().split()
TAIL = HERE / "submission_tail.lean"
EXTERNAL = [
    "Zeta23.ThmD.Mult", "Zeta23.ThmD.ZeroSideD", "Zeta23.PrimeSideA.EndsE1",
    "Zeta23.ZeroSide.RankTraceMult",
    "Mathlib.Analysis.SpecialFunctions.Integrals.Basic",
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc",
    "Mathlib.Analysis.Real.Pi.Bounds",
]

out = ["/-\n  Riemann.fail submission -- teal-sea/zeta-lab, three-point unconditional bound.\n"
       "  Assembled from lean/bridge (MIT, Copyright (c) 2026 Zeta Lab).\n-/",
       "import ChallengeDeps.CandidateSpec"]
out += [f"import {m}" for m in EXTERNAL] + [""]

for f in ORDER:
    src = pathlib.Path(f).read_text(encoding="utf-8")
    # internal imports become concatenation order; #print axioms would pollute
    # the verifier's own axiom audit output
    src = "\n".join(l for l in src.split("\n")
                    if not l.startswith("import ") and not l.startswith("#print axioms"))
    out.append(f"\n/- ===== {f} ===== -/\n" + src)

out.append(TAIL.read_text(encoding="utf-8"))
sol = "\n".join(out)
n = len(sol.encode("utf-8"))
if n > 2_000_000:
    sys.exit(f"assembled {n} bytes, over the 2,000,000 cap")
print(sol, end="")
sys.stderr.write(f"assembled {n:,} bytes, {2_000_000-n:,} under the cap\n")
