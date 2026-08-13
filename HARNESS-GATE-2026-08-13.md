# Harness gate test — frozen protocol

**Status at this commit: pre-registration. No arm has run. No result exists.**
The claims and the answer key are deliberately **not in this commit** — agents in
this experiment have repository access, so committing the key would break
blinding. Only their digest is frozen here. Both are committed after execution,
and the digest is what makes that ordering checkable.

---

## 1. The one question

> Does using the lab's current harness improve the correctness of research-claim
> evaluation, compared with the same agent workflow without the harness, under
> comparable model budget?

That is the whole question. This protocol does **not** decompose the harness into
its components, does not attempt to improve it, and does not investigate why it
does or does not work. If the gate passes, characterization is a later
experiment. If it fails, the negative result is the deliverable.

## 2. Subject and claims

**Subject:** `harness/departments/croniter_fixtures/frozen_croniter.py` — a
byte-pinned implementation of cron day-of-month/day-of-week union semantics under
the `#` and `W` special forms, authored outside this repository. Chosen for three
reasons: it is a registered department with a real battery, it runs with none of
the laboratory's numerical dependencies, and being foreign-born it is the least
contaminated by this tree's own reference claims.

**Claims:** 12 factual assertions about the observable behaviour of that
implementation over the fully enumerable window 2024-01-01 to 2025-01-01.

**Ground truth is established by exhaustive enumeration**, by a script frozen
with the claims — *not* by the harness's own `distinguishes` criterion. That
choice is load-bearing: defining truth as "the battery says it distinguishes"
would make a PASS circular, since a tool that computes X trivially helps you
compute X. Every claim here is true or false as a matter of counting, and would
be so if the harness had never existed.

**Balance as enumerated: 7 SOUND, 5 DEFECTIVE.** The design target was 6/6; the
enumeration returned 7/5 and the claims were **not** adjusted afterwards, because
editing a claim set after reading its truth values is choosing after the data.

**Frozen digest** of `claims.json` + `key.json`, concatenated in that order:

```
77ff70172a89c43d6b84b59f38a4a6e291e5ddfc6ef5cf5a7cb404366f6c41d9
```

## 3. Arms

Both arms are the same model, the same agent workflow, and the same task. They
differ in exactly one thing: whether the harness is available and its use
instructed.

| | Arm A — control | Arm B — treatment |
|---|---|---|
| Model | `claude-opus-5` | `claude-opus-5` |
| Subject source | full read access | full read access |
| Python interpreter | yes | yes |
| `harness/` | **not mentioned; instructed not to use it** | **available, and its use instructed** |
| Invocations per claim | 1 | 1 |
| Output contract | identical | identical |

Paired design: **every claim is evaluated by both arms**, so claim difficulty
cannot differ between arms. 12 claims × 2 arms = 24 runs.

## 4. Comparable model budget — what is equalized, and what is not

Equalized by construction: identical model, identical reasoning effort, exactly
one agent invocation per claim per arm, identical subject access, identical
output contract, and a single-pass instruction in both arms (no arm is told to
iterate more than the other).

**Not equalized, and stated rather than hidden:** Arm B's prompt is necessarily
longer, because the treatment *is* the harness instruction. This is inherent to
the comparison — an arm told to use a tool must be told the tool exists — and it
is the one budget asymmetry that cannot be removed without removing the
treatment.

**Not measurable here:** input, output and cache token counts, and provider cost.
This environment exports none of them to a session (`RUN-TELEMETRY.md` §7). Both
arms are therefore reported with **wall-clock** and **response character count**
as declared proxies for effort, and the gate criterion does not depend on either.
This is a real limitation of the budget comparison and is recorded as one.

## 5. Blinding

- Each agent receives exactly one claim, in a fresh context, with no ground
  truth, no arm label, no other agent's output, and no statement of how many
  claims exist or what the balance is.
- The answer key is held outside the repository during execution.
- Agents are not told the experiment exists.
- Scoring is a mechanical string comparison of the declared verdict against the
  frozen key. No scorer judgment is involved, so scorer blinding is moot.

## 6. Output contract (identical in both arms)

The final line of the response must be exactly one of:

```
VERDICT: SOUND
VERDICT: DEFECTIVE
```

`SOUND` means the claim is true of the implementation as stated. `DEFECTIVE`
means it is not. A response whose final line matches neither is scored as
**incorrect** — an unparseable verdict is a failed evaluation, not a missing
datum, and this rule applies identically to both arms.

## 7. The predefined binary criterion

Paired, over the 12 claims:

- **b** = claims where Arm B is correct and Arm A is wrong
- **c** = claims where Arm A is correct and Arm B is wrong

> ## GATE PASSES if and only if **b − c ≥ 3**.
> ## Any other outcome is a FAIL.

A tie, a negative margin, a margin of 1 or 2, and a ceiling in which both arms
answer every claim correctly all count as **FAIL** — the harness did not
demonstrate an improvement. Ceiling and floor, if they occur, are reported with
the raw counts so the reason for the failure is legible, but they do not soften
the verdict.

Reported alongside, and **not** part of the gate: total correct per arm, the
per-class split, the exact-binomial p over discordant pairs, wall-clock and
response length per arm.

## 8. Failure handling, frozen

| Condition | Consequence |
|---|---|
| A run errors or returns nothing | re-run **once** from the byte-identical prompt |
| It fails again | that claim is **void for both arms** and drops out of the pair count |
| A verdict line is unparseable | scored incorrect (§6), not re-run |
| Any claim's ground truth is found wrong after execution begins | claim voided for both arms, reported, key **not** silently amended |
| The harness is modified during execution | experiment void |

## 9. What this cannot conclude

- It is one task class in one domain — a decidable, executable-oracle domain,
  which is the setting most favourable to controls of any kind. A PASS does not
  generalize to open mathematics; a FAIL does not prove the harness worthless in
  domains this does not touch.
- It compares the harness as a whole against its absence. It says nothing about
  which part of the harness did or did not carry the effect, by design.
- n = 12 pairs. Only a large, consistent effect is detectable, which is
  appropriate: only a large effect would justify the harness's complexity.

---

**Freeze.** This commit contains this protocol and nothing else. The claims, the
key, the runner and the results follow in a later commit, and must hash to the
digest in §2.
