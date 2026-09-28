# boards

Ostoyae boards for this repository's hunts. A board is an execution plan: which work items a
run may attempt, their checks, and the append-only record of every attempt made against them.

## Why they are here and not in `hunts/<name>/`

`hunts/outband_certificate/board.json` set the precedent, and it is the right instinct: a
hunt's board belongs with its hunt. That board has never been run, which is the only reason it
sits there without trouble.

A board that **has** run stores agent-written text: task instructions, mapper proposals, and
the judge's verdicts on them. On 2026-09-10 a mapper wrote a sentence *disclaiming* the word
this repository reserves for `zeta/rigor.py`. Three of this tree's rules then collide, and any
two of them can be satisfied while all three cannot:

- `tests/test_hunt_probe_discipline.py` bans that word anywhere under `hunts/`, reading bytes
  on the filesystem so that intent can never exempt a file. That intent-blindness is the point
  of it and is stated in `CLAUDE.md`.
- A board's `attempts[]` is append-only. Ostoyae's own rule is never to hand-edit it. One copy
  of the offending sentence is in there, so the file cannot be made lexically clean.
- A hunt's board belongs with its hunt.

Moving the board one directory up satisfies the first two exactly and bends the third least: it
is still in this repository, still tracked, still beside the science it plans, and no guard was
loosened and no record was edited to get there. **This is an interim placement pending a ruling**,
not an argument that boards do not belong to hunts. The alternatives are to exempt boards from
the lexical scan, which contradicts what `CLAUDE.md` says that scan is for, or to forbid agents
from ever naming a reserved word even to ban it, which the board's seed text now does.

Runtime state (`*.run.json`, `*.live.json`) is gitignored: `graph.schema.md` says the heartbeat
is runtime state and not the record.
