# Does the validation harness work? — evaluation report

**Repository:** `teal-sea/zeta-lab` · **Date:** 2026-08-13
**Subsystem under test:** `harness/` — a subject-independent validation framework
(departments, batteries, four control roles, integrity grading)
**Question, as posed:** does using the harness improve the correctness of
research-claim evaluation, versus the same agent workflow without it, at
comparable budget?

## Answer

**Not demonstrated.** Four pre-registered experiments, three subjects, 74 agent
runs. The harness arm never once out-performed the control. The control was
never wrong.

Separately, and more cheaply decisive: **nothing in the repository uses the
harness.**

---

## 1. Results

| | subject | design | control | harness | b − c | verdict |
|---|---|---|---|---|---|---|
| v1 | croniter | 12 items × 2 arms | 12/12 | 12/12 | 0 | FAIL (ceiling) |
| v2 | croniter | 14 items × 2 arms | 13/13 | 13/13 | 0 | FAIL (ceiling) |
| v3 | croniter | 12 items, control-only pilot | 6/6 | not run | — | ABORTED |
| v4 | LLVM IR rewrites | 6 items × 2 arms | 6/6 | 6/6 | 0 | FAIL |

Criterion, frozen before each run: **b** = items the harness arm got right and
the control got wrong; **c** = the reverse. Pass required `b − c ≥ 3` (v1–v3) or
`≥ 2` (v4, a 6-item screen). A ceiling — both arms perfect — was pre-committed as
a FAIL in every protocol and never reinterpreted afterwards.

**Cumulative control accuracy: 37/37.**

Each protocol was committed and pushed *before* any arm ran; items and answer
keys were held outside the repository during execution and their SHA-256 digests
frozen in the protocol, then re-verified afterwards. Scoring was mechanical
string comparison against the key — no scorer judgment.

## 2. Why the first three failed, and why v4 is the one that counts

v1 and v2 failed on **no headroom**: the subject was deterministic and fully
enumerable, and neither arm was deprived of a shell, so any factual claim was
settled by running it. v3 failed on **no positive class**: my ground-truth key
was built from 21 hand-written code mutations, and the control found valid
counterexamples in four code paths I had not thought of — all six "sufficient
evidence" items were refuted and voided. Those are defects in my experiments,
not findings about the harness, and they are recorded as such.

**v4 removed both defects, by measurement taken before the run.** The subject is
LLVM IR rewrite validity, where correctness was verified by complete enumeration
of the entire 65,536-point input domain:

- 3 rewrites genuinely valid → a real positive class existed (v3's failure fixed)
- 3 rewrites achieving **byte-identical output on all 65,536 inputs at two
  optimisation levels while being invalid** — the defect is in LLVM poison
  semantics, which concrete execution provably cannot observe (v1/v2's failure
  fixed: running the artifact could not settle it)

The control settled it anyway, 6/6. It read the `nsw`/`nuw`/`exact` flags
directly off the IR and stated why the evidence it had been handed was
worthless: *"65536/65536 agreement at -O0 and -O2 is exactly what an `nsw`
violation looks like when observed by execution."* Both arms produced identical
counterexamples on all three traps.

## 3. The cheaper evidence, which the experiments were not needed to obtain

```
call sites of run_battery / validate_battery / audit_department / ClaimReport
outside harness/ and tests/ :   0
```

Zero — not few. Meanwhile ten files under `hunts/` (the repository's live
research) implement the same concepts by hand. `hunts/wide_search/probe.py`
carries comments reading `# control 1 — rival` and
`# control 2/3 — surrogate and lesion` — the harness's own four-role vocabulary
— then imports `math`, `mpmath`, `numpy` and `zeta.epstein`, and writes 167
lines of it from scratch.

Someone who needed exactly this abstraction, and had it installed, chose to
rebuild it. That is the strongest adoption signal a codebase emits, and it
predates every experiment above.

## 4. Cost, replicated three times

For **identical** correctness:

| | tokens | wall-clock (median) | tool uses (median) |
|---|---|---|---|
| v1 | 1.15× | 3.22× | 3.40× |
| v2 | 1.11× | 2.72× | 2.43× |
| v4 | 1.67× | 3.93× | 5.00× |

This is the most robust quantity the whole exercise produced: **3–5× the effort
for the same answers**, across three independent claim sets.

## 5. Threats to validity — stated, not buried

- **Structural bias against finding an effect.** "I can construct an answer key"
  and "the control cannot work it out" are close to contradictory requirements.
  Every domain testable this way is therefore one favourable to controls. This
  does not rescue the harness, but it bounds the claim: no correctness headroom
  was found *in domains that admit ground truth*.
- **Single model, single workflow** (`claude-opus-5`), n = 6–14 items per
  experiment. Only a large, consistent effect was detectable — appropriate,
  since only a large effect would justify the complexity, but small n is real.
- **v4 declared confound**, stated in the protocol before the run: the compiler
  department ships the adequate detector, so a PASS could not have separated
  "the harness supplied the instrument" from "the harness instilled the habit of
  checking instrument adequacy." Moot given the FAIL.
- **v4 disclosed defect**: one item's source and target were byte-identical (a
  no-op edit from a register-name mismatch), so effective n = 5. Recorded rather
  than swapped, because items were frozen. The ceiling holds on the other five.
- **Outcome variable is verdict correctness only.** See §6.

## 6. What the harness demonstrably did, that the score does not capture

Recorded because it is true, not to soften the verdict — none of it changed an
answer:

Every harness-arm run in v4 surfaced its own department's integrity grade
`DETECTOR_INADEQUATE` and carried it with the verdict, and reported that the
concrete detector has `has_power=False`,
`blind_to=('nsw_flag_on_a_wrapping_shift',)` — i.e. the machinery told the agent,
by measurement, that the evidence in its prompt was a known blind spot. On one
item that grade caused the agent to refuse to stop at the model's verdict and
obtain independent confirmation from real LLVM: `opt -passes=instcombine` folds
the `nuw` variant to `ret i1 false` while the source variant stays live;
compiled and executed, the two disagree at the predicted input.

That is a second independent line of evidence the control never produced. It is
a contribution to *evidence quality and declared scope*, which this gate does not
score, in a domain where the answers were already easy.

Also genuine and independent of adoption: the measured fact that exhaustive
concrete testing over all 65,536 inputs cannot detect poison-class defects, with
a planted fault pinning it.

## 7. Scope — what was **not** tested

The experiments touched `harness/` only. Untouched, and unaffected by any of
this:

- `zeta/` — 25 modules, the mathematics
- `tests/` — 1,754 test functions, cross-checked against mpmath's independent
  implementations as an oracle
- `lean/` — 45 files, kernel-checked, zero `sorry`s
- 390 commits of project history

The zero-call-sites finding cuts both ways: the harness was never in the causal
path of any mathematical result in this repository, so none of those results
depend on it.

## 8. Recommendation

1. **Stop developing `harness/`.** Six departments exist and nothing imports
   them. The adoption evidence is unambiguous and was available before any
   experiment.
2. **Keep `compiler/semantics.py` and the measured detector blind spots.** That
   is real knowledge about the limits of exhaustive testing, true regardless of
   whether anything imports it.
3. **Keep the negative results on the record.** Four pre-registered failures with
   an unmoved criterion is a stronger artifact than an untested framework.
4. **If anyone wants to argue the harness earns its complexity**, they need a
   different outcome variable than verdict correctness — evidence quality and
   scope discipline are where it visibly acted — and a domain where the control
   is not already at ceiling. Neither has been found in four attempts, and I
   would want a cheap adoption test (does live research reach for it?) to pass
   before spending on another correctness test.

---

**Artifacts.** Branch `claude/harness-gate`, not merged to main. Each protocol
frozen in its own commit before execution, results in a later commit:
`c77a5a3`/`aa0de70` (v1), `8bf77e2`/`445363e` (v2), `548f3da`/`3773ed5` (v3),
`0518847`/`0843188` (v4). Every prompt, item set, answer key, scorer and raw run
record is committed under `gate/`, `gate2/`, `gate3/`, `gate4/`.
