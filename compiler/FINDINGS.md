# Department #2, attempted: LLVM IR rewrites

**Verdict: PROVISIONAL.** The subject fits the protocol better than expected —
all four roles have natural compiler-domain analogues, and both calibration
directions work on the first attempt. It is not admitted for two reasons, both
measured below: the only installed detector is **blind to the poison/`undef`
class**, which is not a corner of this subject but its central semantic hazard;
and admission would require changing `tests/test_department_conformance.py`,
because that file — not `harness/protocol.py` — turns out to encode department
#1's payload shapes in three places.

This is the experiment log, not a brochure. Everything asserted here is pinned
by `tests/test_compiler_candidate.py` (30 tests, ~24 s) and re-derived rather
than trusted.

---

## 1. Environment

| Backend | Status |
|---|---|
| `clang.exhaustive_i8` | **available** — `/usr/bin/clang` (Apple clang 17.0.0) accepts LLVM IR as input |
| `alive2.refinement` | **ABSENT** — `alive-tv` not on PATH; rung 3 unavailable, so no refinement checking |
| SMT / rung 2 | not implemented; `z3-solver` is a pip install away and was deliberately not taken |

No LLVM utilities are installed on this machine — no `opt`, no `llvm-as`, no
`lli`. The experiment did not install any. What made rung 1 reachable anyway is
that Apple clang consumes a `.ll` file directly (`clang -x ir foo.ll`), so a
program can be compiled, linked against a C driver and run over its entire input
space with tooling that was already present. **Infrastructure work consumed
none of the milestone.**

`compiler.semantics.backend_status()` reports present *and* absent backends, and
`available_backends()` follows the `zeta/rigor.py` pattern deliberately.

## 2. The evidence ladder, and where this stands on it

Rung 1 only. The exact claim, quoted verbatim from
`compiler.semantics.EVIDENCE_EXHAUSTIVE_I8`, is returned alongside every verdict
so a caller cannot print one without the other:

> exhaustive agreement over all 65536 (i8, i8) inputs, compiled by this clang at
> -O0 and -O2; not equivalence, not refinement, and blind to poison/undef
> because a compiled binary observes neither

Every program is `i8 @f(i8 %x, i8 %y)`, eight lines, in `compiler/fixtures/`, so
the whole input space is 65536 points and a human can check each fixture by eye.

## 3. The role mappings

| Role | Compiler analogue | Verdict |
|---|---|---|
| Subject | a `Transformation`: one source program, one proposed replacement | **NATURAL** |
| Rival | a rewrite sharing every cheap property of the target, and wrong | **NATURAL** |
| Decoy | substitution on **the set of inputs the verdict was measured over** | **NATURAL** |
| Surrogate | a candidate from an unguided mutation generator | **NATURAL** |
| Lesion | a planted corruption of a rewrite already shown to agree | **STRAINED** |

### Rival — NATURAL

The three rivals are not strawmen; each is a transformation a competent person
has written on purpose, and each matches the target's instruction count
*exactly*:

| Rival | Why it is wrong | Disagreements / 65536 |
|---|---|---|
| `sdiv2_to_ashr` | `sdiv` truncates toward zero, `ashr` floors | 16384 |
| `udiv4_to_ashr` | arithmetic shift sign-extends where `udiv` does not | 32768 |
| `slt_to_sign_of_difference` | the sign bit of `x - y` is wrong when the subtract overflows | 16384 |

*Motivating practice:* this is what a peephole test suite is for, and what
Alive2 exists to automate. Nothing was invented for admission.

### Decoy — NATURAL, and the best surprise of the experiment

The obvious mapping is to ablate the *program*. The better one ablates **the
input set**: the substantive input to any test-based verdict about a rewrite is
which inputs were tested, and a verdict that does not move when a diverse input
set is swapped for a degenerate one of the same size was never reading it.

This produced the department's sharpest result. Over the whole i8 range the
`sdiv`-to-`ashr` rewrite agrees **0.75** of the time. Over a same-sized test set
crushed into `[0, 7]`, or one collapsed to all zeros, it agrees **1.0** —
perfect. Nothing about the rewrite changed; only the reach of the tests did.

> **Weak evidence looking convincing, and a control exposing it, in one number:
> 0.75 → 1.00.**

*Motivating practice:* input-space coverage and boundary-value selection.

*Honesty note.* I found the conformance suite's hardcoded decoy probe
(`list(range(2, 60))`, a list of integers) **before** settling on this mapping,
and a decoy that acts on a list of integers happens to satisfy it. The mapping
is defended on its merits above, but a reader should know the order in which it
was found.

### Surrogate — NATURAL

`compiler.catalog.random_mutant` swaps one opcode within a family, under a fixed
seed — the same *kind* of generator a superoptimiser search would use, with the
part that is supposed to know what it is doing removed. Mutants stay compilable
on purpose: a null that mostly failed to build would flatter the detector by
never reaching it.

Observed agreement for the target: **1.000000**. For the three surrogates:
**0.0039, 0.0078, 0.0078**. No surrogate reproduces the observation.

### Lesion — STRAINED

Two mismatches, neither fatal, both real.

**(a) Zeta's lesions are additive; this subject's are substitutions.** The zeta
lesion appends planted zeros to a zero list, so `apply(())` is meaningful. The
compiler-domain lesions that matter — `sgt`→`ugt`, `>`→`>=`, adding an `nsw`
flag — *replace* text. Applying a substitution to an empty program yields an
empty program. Three of the four lesions here are substitutions; the one that is
additive (`single_point_special_case`) is additive by accident, not by nature.

**(b) `magnitude` has two candidate units and they come apart.** The protocol
asks for a magnitude "in whatever units the department uses". The obvious unit
is the share of the domain on which a concrete run disagrees — but that unit
makes the poison lesion *zero*, i.e. reports the department's most important
planted violation as no violation at all. The unit used here is instead the
share of the domain on which the candidate stops being a valid stand-in for the
source: a property of the **violation**, not of the detector. That keeps the
blind spot reportable as a number.

This distinction did not exist in department #1, where the two units coincide.
It is the one place the compiler subject taught the abstraction something.

## 4. Calibration: both directions work

| Reference claim | Declared | Measured | How |
|---|---|---|---|
| `no_more_instructions` | killed | **killed** | fires for the target, shared with all three rivals |
| `exhaustive_agreement_i8` | distinguishes | **distinguishes** | fires for the target, for no rival, no errors |

The negative claim is not a strawman: it is real, cheap, entirely true of the
target, and true of three transformations that are wrong. **Shorter code is not
evidence of a correct rewrite**, stated as a measurement rather than a maxim.

## 5. Detector power — the blind spot, as a number

`run_power` over the four planted lesions, detector = the exhaustive concrete run:

| Lesion | Magnitude | Detected? |
|---|---|---|
| `signed_to_unsigned_predicate` | 0.5 | ✅ |
| `nsw_flag_on_a_wrapping_shift` | **0.5** | ❌ **blind** |
| `strict_to_nonstrict_predicate` | 0.00390625 | ✅ |
| `single_point_special_case` | 0.0000152587890625 | ✅ |

`has_power = False`. `blind_to = ('nsw_flag_on_a_wrapping_shift',)`.
`smallest_detected = 1.5e-05`.

The detector finds a single wrong answer in 65536 — one part in 65536, four
orders below the largest lesion — and completely misses a violation covering
**half the domain**. The source multiplies by two and wraps; the candidate adds
`nsw`, promising it never overflows, which makes it poison for every `|x| ≥ 64`.
A compiled binary still hands back the wrapped value, so the output tables agree
byte for byte. The rewrite is invalid and rung 1 cannot say so.

This is not a tuning problem. It is the boundary between rung 1 and rung 3, and
it is why the verdict is PROVISIONAL: **poison/`undef`/UB is the class LLVM
transformations most often get wrong**, and this department currently cannot see
any of it.

`tests/test_compiler_candidate.py::test_the_detector_is_blind_to_the_poison_lesion`
asserts the failure on purpose so it cannot be quietly lost.

## 6. Self-attacks

| Attack | Outcome |
|---|---|
| Strip `PATH` so no backend exists | `SemanticsUnavailable` raised; **no claim returns a verdict**. Pinned by a subprocess test, not a skip. |
| Feed malformed IR | `IRRejected`; never read as agreement or as disagreement |
| Feed a rival in as the target | `target=False`, `distinguishes=False` — "does not fire for the target" |
| Lesion whose pattern is absent | refuses loudly rather than silently planting nothing |
| Identity lesion (returns its input) | **passes the current conformance check**; caught by the proposed one |
| Substitute a decoy for the real input set | 0.75 → 1.00, exactly as intended |
| Are `-O0` and `-O2` independent? | **No.** Both caught all three rivals; neither caught anything the other missed. Pinned as a measurement, and the docstring no longer implies otherwise. |

The last one deserves emphasis: two optimisation levels through the same clang
is not two checks. It can catch a program that disagrees with *itself* (which
would mean UB), and it caught nothing extra here.

## 7. Generic harness changes

**Made: none.** `harness/protocol.py` is untouched, and the candidate's
`Department` validates against it with `department_reasons() == ()`.

Three of the four instrument runners — `run_ablation`, `run_nulls`, `run_power`
— had **never been driven by a real department**. Department #1 declares decoys,
surrogates and lesions but only ever calls `run_battery` (noted in
`HANDOFF.md:237`); the other three were exercised only by float stand-ins in
`tests/test_harness_protocol.py`. This experiment is the first time all four ran
against a subject, and all four worked unmodified. That is the strongest single
piece of evidence the experiment produced *for* generality.

### Proposed and deliberately NOT made

Running the real conformance suite against the candidate gives **13 passed, 3
failed**. One failure is the graduation step (no `docs/doors/compiler.md`,
correctly absent). The other two — plus one the candidate happens to dodge —
are the finding:

| Conformance test | Assumption | Zeta shape it encodes |
|---|---|---|
| `test_every_lesion_plants_something` | `lesion.apply(())` returns something non-empty | lesion payload is an appendable sequence of zeros |
| `test_every_surrogate_draws_a_sample` | `len(sample) > 0` | surrogate sample is a sized intensity array |
| `test_every_decoy_changes_what_it_is_given` | `decoy.substitute(list(range(2, 60)))` | decoy payload is a list of integers standing in for primes |

**`harness/protocol.py` is domain-agnostic — enforced three ways and holding.
`tests/test_department_conformance.py` is not, and it is the file that is
supposed to be reusable, because it is parametrized over every department.**

The protocol already anticipates this: `run_ablation` and `run_power` take an
explicit `payload=` precisely because "the four instruments legitimately consume
different objects", and the docstring warns that forcing one payload type
"would make the protocol tidier and the departments dishonest". The conformance
suite then hardcodes a guess at those payloads anyway.

The proposed fix, answering the five questions:

1. **What exposed it?** Lesions consume a program pair, not a sequence;
   surrogates draw a program pair, which has no length. Both are natural to the
   subject, not contrived.
2. **Why not solve it inside the department?** Only by teaching the lesion to
   accept `()` and the surrogate to return something sized — polymorphism that
   would exist purely to satisfy a test probe. That is faking the fit.
3. **Is it domain-general?** Yes. Let each instrument optionally expose a
   `probe` attribute — a representative payload of the shape it consumes — and
   have the conformance suite use it when present, falling back to today's
   values. Read via `getattr`, so **`protocol.py` need not change at all**.
4. **Does zeta still make sense?** Unchanged: it declares no `probe` and gets
   today's defaults.
5. **Improving an abstraction, or weakening a criterion?** Strengthening. The
   replacement rule for lesions — `apply(probe) != probe`, the same rule the
   decoy test already uses — catches an identity lesion that `len(apply(())) > 0`
   passes today. Demonstrated in
   `test_conformance_leak_the_current_lesion_check_passes_an_identity_lesion`.

It was **not made**, because a probe should not modify the shared audit before
it has earned a place in it. The three leaks are instead pinned by
`conformance_leak` tests that will start failing the day the audit is fixed.

## 8. Could the department game the protocol?

Yes, in one way worth recording. `validate_battery` requires lesions to *exist*,
not that any detector pass them. A department can therefore declare four
lesions, be blind to all four, and still be structurally admissible — as this
one nearly is. `PowerVerdict.has_power` records the blindness, but nothing in
the admission rule consults it. That is arguably correct (the protocol's job is
to make blindness *measurable*, not absent), but it means "admissible" and "has
a working detector" are independent, and only the first is enforced.

## 9. Answers to the milestone questions

1. Natural counterparts to the required roles? **Yes** — four of four, one strained.
2. A tiny known-good rewrite represented and evaluated? **Yes.**
3. A known-bad rewrite that survives a naive test and is killed by stronger machinery? **Yes** — `sdiv2_to_ashr` is perfect on a narrow input set and wrong on 16384 of 65536 points.
4. Does the detector catch deliberately inserted defects? **Three of four**, down to one part in 65536; blind to the fourth.
5. Is missing infrastructure unmistakable? **Yes** — absent backends are named in `backend_status()`, and with no backend every claim raises rather than answering. No skips.
6. Both calibration directions? **Yes**, re-derived rather than declared.
7. Did it require generic harness changes? **No changes to `protocol.py`. Three needed in the conformance suite, proposed and not made.**
8. Are those changes domain-general? **Yes** — see §7, and they strengthen the audit.
9. Admission without weakening the rules? **Not yet.**

## 10. Did this experiment provide evidence that the harness is domain-independent?

**Partially, and more than I expected going in.**

For: the four roles carved a subject with no mathematical content at all —
programs, not functions — without a single change to `protocol.py`. Both
calibration directions worked on the first attempt. Three instrument runners
that had never met a real department worked unmodified. The `Rival` role in
particular transferred perfectly: "shorter code is not evidence" is the same
modus tollens as "a shared functional equation is not evidence", in a subject
that shares no vocabulary with the first.

Against: the reusable *audit* was not reusable, in three places, all of them the
same mistake — guessing a department's payload shapes. The abstraction is
domain-independent; the harness around it had one department's habits baked in,
and nobody could have known which until a second subject arrived. And the
`Lesion` role needed its units renegotiated to stay honest.

The honest summary is that `harness/protocol.py` earned its claim and
`tests/test_department_conformance.py` did not.

## 11. What admission would require

1. A rung-2 or rung-3 backend that can see the poison lesion — an SMT model of
   the supported IR subset (`z3-solver`, one pip install) or Alive2. Until then
   `has_power` is `False` on the subject's central hazard.
2. The conformance-suite fix in §7, reviewed on its own merits rather than
   because a candidate needs it.
3. `docs/doors/compiler.md`, and one line in `KNOWN_DEPARTMENTS`.

Steps 1 and 2 are independent and either can be done first. Step 3 is the
graduation and must be last.

## 12. Preserved false starts

* **The first lesion host was the comparison rewrite alone**, so the `nsw`
  lesion had to be planted as a *dead* `add nsw`. Dead poison is unused poison,
  and unused poison is not a semantic change — the lesion was a no-op dressed as
  a violation. It was replaced with a host containing both a comparison and an
  arithmetic op so the `nsw` value is genuinely consumed. Had this not been
  caught, the department would have reported a blind spot that was not there.
* **The first vocabulary test banned the bare word "equivalence"**, and failed
  on `EVIDENCE_EXHAUSTIVE_I8`, which says *"not equivalence, not refinement"*.
  A scan that punishes the disclaimer is worse than no scan. It now checks
  affirmative phrasings only, and exempts docstrings.
