# HuntSpec — the machine-readable contract a new hunt carries

Adopted on probation, 2026-08-11 (`ROADMAP.md`, "The outside memos, triaged",
adopted build 3). A HuntSpec is a fenced block inside a hunt's `MISSION.md`
that states, in a form a validator can read: the question, the frontier it
starts from, the routes already known dead, the non-model oracles that are
allowed to assign truth, the conditions under which the hunt kills its own
claim, and what its agents may and may not do.

The rule it encodes is the phase charter's: **no agent without an oracle** —
agents generate, derive, code, attack and formalize; they do not assign
epistemic status to their own outputs. A HuntSpec makes that allocation of
authority a declared, checkable artifact instead of a habit.

## Probation terms

- **New hunts carry one; existing hunts are not retrofitted.** The hunts
  live before this date run to their own kill conditions as written.
- **The validator checks any `MISSION.md` that contains a block.** A hunt
  without a block is out of scope for the validator (and, if created after
  2026-08-11, out of compliance with this page — that half is review
  discipline, stated here rather than pretended into a test).
- **The primitive is on the dossier rule**: it earns promotion to a real
  module the first time a kill condition fires mechanically or an oracle
  requirement blocks an ungrounded status claim. Until then the parser and
  validator live in `tests/test_huntspec.py` and nowhere else.

## Format

A fenced code block tagged `huntspec`, containing a strict flat subset of
YAML — single-line scalars and lists of strings only, no nesting, no
quoting rules, no dependencies:

    key: single-line value
    key:
      - list item
      - list item

Required keys:

| key | form | rule |
| --- | --- | --- |
| `question` | scalar | the one question the hunt exists to answer |
| `frontier` | scalar | where the known boundary stands, with numbers when there are numbers |
| `dead_routes` | list | routes already known dead — the do-not-refund list |
| `required_oracles` | list, non-empty | the non-model authorities that assign truth; an entry naming a model is refused |
| `kill_conditions` | list, non-empty | observations on which the hunt withdraws its own claim |
| `agents_may` | list, non-empty | the permitted actions |
| `agents_may_not` | list, non-empty | the withheld authorities |

Optional keys: `id`, `proposed_attack`.

`required_oracles` entries are checked lexically: an entry containing a
model or vendor word (`model`, `llm`, `gpt`, `claude`, `gemini`, `agent`)
fails validation. This is crude on purpose — it cannot certify that a listed
oracle is genuinely non-model, but it refuses the declaration that says the
quiet part out loud, and the crude check is the one that runs.

## Template

The template below is itself parsed and validated by
`tests/test_huntspec.py` — if this page drifts from the validator, a test
fails.

```huntspec
id: example_hunt
question: Does X improve the current bound on Y?
frontier: lower 0.0000000 (pinned by Z), upper 0.0000001 (paper W)
proposed_attack: the one mechanism this hunt tries
dead_routes:
  - the route HANDOFF already records as killed, with its mechanism
required_oracles:
  - exact small-N enumeration
  - rational certificate checked by an independent implementation
kill_conditions:
  - the null recovers the effect without the structure
  - the result deteriorates under refinement
  - a realizable counterexample violates the candidate inequality
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```
