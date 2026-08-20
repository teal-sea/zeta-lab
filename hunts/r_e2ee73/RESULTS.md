# Hunt R-E2EE73: Scope caveat: compiler verdicts rest on a hand-written model, not LLVM semantics (Alive2 absent)

## Summary

This hunt establishes, measures, and records the exact scope caveats bounding all claims made by the `compiler/` department.

Because Alive2 (`alive-tv`) is absent on this machine, the department's refinement verdicts rest on a pure-Python, hand-written interpreter (`pymodel.refinement_i8`, rung 2) rather than LLVM's formal SMT-based semantics (rung 3). The exposure of this hand-written model is bounded through an exhaustive two-backend cross-check against compiled Clang binaries (`clang.exhaustive_i8`, rung 1) across all 10 fixtures (655,360 total points evaluated, 0 mismatches), combined with explicit `ModelUnsupported` exception barriers on out-of-scope IR constructs.

## 1. Backend Census: The Evidence Ladder

| Backend | Status | Rung | Implementation / Tool | Scope / What it Establishes |
|---|---|---|---|---|
| `clang.exhaustive_i8` | **available** | 1 | Apple Clang (`/usr/bin/clang`) compiling `-x ir` | Concrete output agreement over all 65536 `(i8, i8)` pairs at `-O0` and `-O2`. Blind to poison and undef. |
| `pymodel.refinement_i8` | **available** | 2 | Hand-written Python model in `compiler/semantics.py` | Exhaustive refinement over 65536 points with first-class poison and immediate UB modeling for the supported subset. |
| `alive2.refinement` | **ABSENT** | 3 | `alive-tv` (not on PATH) | Formal refinement under full LLVM semantics via SMT/Z3. Unavailable. |

Every verdict emitted by `compiler.semantics` returns an explicit evidence caveat (`EVIDENCE_EXHAUSTIVE_I8` or `EVIDENCE_MODEL_I8`) so no consumer can cite a passing result without quoting its semantic regime.

## 2. Two-Backend Cross-Check (655,360 Comparable Points)

Where both backends can speak (at all inputs where the hand-written model claims a defined value), the compiled output of Apple Clang at both `-O0` and `-O2` must match bit-for-bit.

Across all 10 fixtures in `compiler/fixtures/`, the cross-check demonstrates exact agreement:

| Fixture | File | Comparable Points | Clang -O0 / -O2 Mismatches | Overall Agreement |
|---|---|---|---|---|
| `host_src` | `compiler/fixtures/host_src.ll` | 65,536 | 0 | 100.0000% |
| `host_tgt` | `compiler/fixtures/host_tgt.ll` | 65,536 | 0 | 100.0000% |
| `mul2_add_src` | `compiler/fixtures/mul2_add_src.ll` | 65,536 | 0 | 100.0000% |
| `mul2_add_tgt` | `compiler/fixtures/mul2_add_tgt.ll` | 65,536 | 0 | 100.0000% |
| `sdiv2_add_src` | `compiler/fixtures/sdiv2_add_src.ll` | 65,536 | 0 | 100.0000% |
| `sdiv2_add_tgt` | `compiler/fixtures/sdiv2_add_tgt.ll` | 65,536 | 0 | 100.0000% |
| `slt_src` | `compiler/fixtures/slt_src.ll` | 65,536 | 0 | 100.0000% |
| `slt_sub_tgt` | `compiler/fixtures/slt_sub_tgt.ll` | 65,536 | 0 | 100.0000% |
| `udiv4_add_src` | `compiler/fixtures/udiv4_add_src.ll` | 65,536 | 0 | 100.0000% |
| `udiv4_add_tgt` | `compiler/fixtures/udiv4_add_tgt.ll` | 65,536 | 0 | 100.0000% |
| **Total** | **10 fixtures** | **655,360** | **0** | **100.0000%** |

## 3. Detector Power and the Measured Blind Spot

The boundary between rung 1 and rung 2 is measured by evaluating both detectors against the 4 planted lesions in `compiler.catalog`:

| Lesion | Declared Magnitude | Concrete Run Disagreements (`clang.exhaustive_i8`) | Model Violations (`pymodel.refinement_i8`) | Model Violation Breakdown (Value / Poison / UB) | Status |
|---|---|---|---|---|---|
| `signed_to_unsigned_predicate` | 0.500000 | 32,768 (0.500000) | 32,768 (0.500000) | 32,768 value / 0 poison / 0 UB | Detected by both |
| `strict_to_nonstrict_predicate` | 0.003906 | 256 (0.003906) | 256 (0.003906) | 256 value / 0 poison / 0 UB | Detected by both |
| `single_point_special_case` | 0.000015 | 1 (0.000015) | 1 (0.000015) | 1 value / 0 poison / 0 UB | Detected by both |
| `nsw_flag_on_a_wrapping_shift` | 0.500000 | **0 (0.000000)** | **32,768 (0.500000)** | **0 value / 32,768 poison / 0 UB** | **Concrete detector BLIND; Model detector FULL POWER** |

The concrete detector has `has_power = False` with `blind_to = ('nsw_flag_on_a_wrapping_shift',)`. The model detector has `has_power = True` with `blind_to = ()`.

## 4. Calibration: Rivals, Decoys, and Surrogates

All battery calibration checks re-derive from first principles:

- **Rivals (3)**: All match target instruction count (instructions removed = 0). Concrete disagreements and model refinement violations agree independently on all 3:
  - `sdiv2_to_ashr`: 16,384 disagreements (value violations)
  - `udiv4_to_ashr`: 32,768 disagreements (value violations)
  - `slt_to_sign_of_difference`: 16,384 disagreements (value violations)
- **Decoys (2)**: Input ablation on `sdiv2_to_ashr` shifts agreement from 0.7500 (full domain) to 1.0000 (narrow `[0, 7]` and constant `{0}` suites).
- **Surrogates (3)**: Unguided mutation agreement fractions under seeds 11, 23, 57 measure at 0.0039, 0.0078, 0.0078, well below the 0.50 threshold.

## 5. Rejection Safety: Unsupported IR Taxonomy

The hand-written model must refuse out-of-scope IR constructs rather than guessing. An audit of unsupported constructs confirms safe rejection:

| Construct | Example Probe | Behavior | Exception Raised |
|---|---|---|---|
| Floating point arithmetic | `fadd i8 %x, %y` | Rejected | `ModelUnsupported` (unimplemented opcode) |
| Memory operations | `alloca`, `load`, `store` | Rejected | `ModelUnsupported` (unrecognised line) |
| Control flow / CFG | `br label %next` | Rejected | `ModelUnsupported` (unrecognised line) |
| Phi nodes | `phi i8 [ %x, %t ], [ %y, %f ]` | Rejected | `ModelUnsupported` (unrecognised line) |
| Freeze instruction | `freeze i8 %x` | Rejected | `ModelUnsupported` (unrecognised line) |
| Non-deterministic undef | `undef` operand | Rejected | `ModelUnsupported` (unrecognised line) |

Every raised exception is a subclass of `IRRejected`, ensuring consumers treating backend refusals uniformly stay correct.

## 6. Verification Path Independence

Formal comparison of `VerificationPath` declarations between the two backends:
- **Path A (`clang.exhaustive_i8`)**: `["LLVM IR text", "clang frontend parser/lowering", "code generation/compilation to native binary", "driver harness execution over 65536 inputs", "stdout byte capture", "exhaustive byte table comparison"]`
- **Path B (`pymodel.refinement_i8`)**: `["LLVM IR text", "regex IR parser (_parse)", "Python AST evaluation (_eval_program)", "poison and immediate UB propagation", "exhaustive tuple generation (65536 points)", "refinement relation check (value/poison/UB)"]`
- **Independence Radius**: 1 of 6 (the paths diverge immediately after the input IR text).
- **Shared Layers**: `("LLVM IR text",)`
- **Distinct Layers**: 5 distinct layers in each path.
- **Agreement Bound**: Agreement between the two backends is evidence about execution semantics of the straight-line subset; it provides no evidence about out-of-scope LLVM semantics (memory, CFG, undef, vectorization) or LLVM optimization passes.

## 7. Settlement and Boundaries

1. **What is settled**:
   - The standing scope limitation is documented, quantified, and bounded.
   - Refinement verdicts hold exclusively over the enumerated i8 domain with respect to the hand-written model (`EVIDENCE_MODEL_I8`).
   - The hand-written model's defined-value claims are cross-checked across 655,360 points against Apple Clang with 0 mismatches.
   - The model reliably catches the poison hazard that concrete execution cannot see (32,768 poison violations on `nsw_flag_on_a_wrapping_shift`).
   - The model safely rejects out-of-scope IR with `ModelUnsupported`.

2. **What cannot be settled within budget**:
   - Installing Alive2 (`alive-tv`): Alive2 requires a full LLVM toolchain build with Z3 SMT solver libraries, which is absent from this container environment. Without `alive-tv` on PATH, rung 3 cannot be made available.

## Loose threads

1. **Bitwidth Handling in Parser vs Evaluator**: The regex parser `_LINE_BINOP` matches arbitrary integer widths (e.g. `i32`), but `_eval_program` hardcodes `%x` and `%y` inputs as 8-bit unsigned values in `range(-128, 128)`. An IR function declared with `i32` signature parses and evaluates without raising `ModelUnsupported`, but tests only an 8-bit slice of the 32-bit input space. This could allow multi-byte integer semantics to be evaluated inadvertently under a truncated 8-bit harness. The first step would be to restrict the regex parser in `_parse` to accept only `i8` (and `i1` for conditions), raising `ModelUnsupported` on wider types.

2. **SMT / Z3 Bounded Refinement Alternative**: `z3-solver` can be installed via Python without building full `alive-tv`. An SMT-based straight-line solver for the supported subset would provide symbolic proof over arbitrary bitwidths as an intermediate rung between Python enumeration and full Alive2.
