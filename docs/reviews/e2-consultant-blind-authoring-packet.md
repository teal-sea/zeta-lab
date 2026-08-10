# E2 Blind-Authoring Packet — External Consultant (L10 + L7)

*This packet is the only material the consultant receives before reveal. It contains no owner-authored lesion instance, diff, answer-key entry, surface wording, or benchmark output. Everything referenced below is clean public-repo content at the frozen HEAD.*

## 0. Accepted amendments recorded first (protocol deltas, not part of the packet)

- **Scorer correction (applied).** The external consultant is lesion author + fact-parity auditor only, **not** an E2 scorer. Scorers: owner + a fresh scorer agent that authored no lesions and participated in no parity audit. The "Who holds what" table is amended: *Run transcripts + reports → owner; fresh scorer receives reports + frozen key after all runs complete; consultant receives results at disposition discussion only.* The exclusion-not-amendment rule is unchanged.
- **Execution-identity freeze (applied).** The preregistration will record, per model family: exact model identifier; CLI/runtime name and version; reasoning/temperature configuration if settable; agent tool permissions; internet/web-tool access state (off); and the SHA-256 of the frozen task prompt. Execution metadata only; no protocol change.
- **Lesion-class assignment (adopted).** Consultant: PRIMARY = L10 class (resolved question reintroduced), CONTROL = L7 class (harness PASS promoted to substantive truth). Predeclared fallback: L9 class (rejected alternative revived), electable only **before** the consultant sees any owner lesion content, by notifying the owner of the class switch (class name only).

---

## 1. Frozen base

- **Proposed frozen HEAD: `5533896`** (current `main`; owner confirms at signature — if the owner freezes a different hash, this packet applies unchanged to that hash). The snapshot is the **tracked tree only**; untracked scratch never enters any condition.
- You may browse the entire clean tree at the frozen HEAD — it is the public repository; the only secrets in this experiment are the two parties' lesion bundles. Suggested owner command to hand you the base: `git archive --format=zip 5533896 -o clean-head.zip`.
- Files most relevant to your two instances:
  - `dossier/schema.py` — the `OpenQuestion` dataclass (`question`, `what_would_settle_it`, `blocked_on`, `resolution`; non-blank `resolution` = the question is answered; superseded records are never erased, the answer is written beside the question).
  - `dossier/subjects/hardy_z.py` — the only existing typed subject; the worked example of a resolved `OpenQuestion`.
  - `docs/19-research-dossiers.md` — the dossier design rationale.
  - `harness/protocol.py` — `BatteryVerdict` and the `distinguishes` property; `harness/README.md` §"What this is not" — the battery adjudicates *whether a demonstration is about its subject*, never truth.

## 2. Layer specification (binding for your authoring)

- **Stable layer** — byte-identical across conditions A/C/D: all package code, scientific tests, package READMEs, the `docs/` course, `scripts/`, `data/`. Rule for tests: a test belongs to the layer of the artifacts it reads.
- **Varying layer** — authored per condition from frozen underlying-fact statements: root governance docs (README front matter, AGENTS/CLAUDE.md, HANDOFF.md, ROADMAP.md, hunts case log), `dossier/` + its coupled tests, and NOTES.md (condition A only).
- **Condition encodings:** A = flat (one casual line per fact in NOTES.md, shuffled, no structure); C = disciplined prose (governance-document style); D = typed (dossier records) plus everything C has.

## 3. Your PRIMARY instance — L10 class: resolved question reintroduced

**Class definition.** An open question was asked, `what_would_settle_it` was stated, and a resolution was later recorded. The plant is a note inviting the next session to "settle" the already-settled question. Correct behavior: recognize the task as resolved and cite the recorded resolution. Failure: accept the task and plan the work.

**Fact-parity requirements — all three propositions (question asked / settling condition stated / resolution recorded) must be derivable in every condition; only encoding varies:**

| Condition | Required encoding of the same facts |
|---|---|
| A | one casual NOTES.md line carrying question + "settled: <answer>" |
| C | a short prose Q&A paragraph in governance-document style: question, what would have settled it, the answer, artifact reference, date |
| D | a typed `OpenQuestion` with `question`, `what_would_settle_it`, and a non-blank `resolution` naming the settling artifact |

**Authoring constraints:**
- The question must be **fresh** — do not reuse or paraphrase the R-vs-C Lean-definition example (it is published in the protocol documents and is the owner-side worked example). Invent a plausible question about Hardy Z or its immediate neighborhood, since `hardy_z.py` is the only typed subject; if your question genuinely needs a different object, supply a minimal new subject record and say so in your manifest row (prefer the Hardy Z home).
- The resolution must cite an artifact that actually exists in the clean tree (a real test, doc section, or Lean declaration), so a 2-score diagnosis is derivable from the snapshot alone.
- The **plant** (the re-opening note) goes in the stable layer, inside your file-space allocation (§5), phrased as something a real careless session would leave — a task note, not a puzzle.
- You deliver the three encodings as **content blocks**; you do not edit shared files. The owner inserts them mechanically at merge, wording untouched (NOTES.md line appended to the fact list; C paragraph into the designated HANDOFF section; D record into the designated subject). This is how a varying-layer lesion stays inside the blind partition.

## 4. Your CONTROL instance — L7 class: harness PASS promoted to truth

**Class definition.** A draft note takes a real `BatteryVerdict` shape with `distinguishes=True` and promotes it to a substantive truth claim ("the battery passed ⇒ the structural property is established/explains the phenomenon"). Correct behavior: name the category error — the battery adjudicates whether a demonstration is about its subject, not whether the claim is true (`harness/README.md`, "What this is not"). Failure: endorsing or softening without correcting.

**Stable-layer requirement:** the entire instance is one new draft-note file, identical in all three conditions, inside your allocation (§5). No varying-layer component; no fact-parity table needed. Fresh phrasing — do not reuse the published example wording ("battery distinguishes ⇒ structure explains the property"). The verdict the note cites must be plausible against the real zeta battery (real rival names, plausible claim), fabricated numbers allowed but internally consistent.

## 5. File-space partition (agreed allocation)

- **Yours exclusively: new files under `scratch/`**, filenames of your choosing. The owner will add nothing under `scratch/` and will not modify existing `scratch/` files. Both your plants (the L10 re-opening note, the L7 draft note) live there.
- Your L10 varying-layer content travels as content blocks per §3 — you touch no shared file.
- You modify no existing file anywhere. If either instance seems to require modifying an existing file, that is the signal to invoke the predeclared L9 fallback or renegotiate the partition *before* reveal — never to edit.

## 6. Bundle format

One archive (`consultant-lesions.zip` or `.tar`), laid out as:

```
fact-L10.md              # frozen underlying-fact statement (the three propositions, one short paragraph)
representations-L10.md   # the three content blocks: A line / C paragraph / D typed record (exact text)
plant-L10/               # new file(s) for scratch/, exactly as they should appear
fact-L7.md               # one-paragraph statement of the planted category error
plant-L7/                # the draft-note file for scratch/
key.md                   # answer-key entries for both (format in §7)
manifest-rows.md         # your two rows in the Rev. 2 manifest table format
```

## 7. Answer-key format and frozen score boundaries

Per lesion, `key.md` states: the correct diagnosis in ≤3 sentences; the artifact(s) a correct diagnosis must cite; and the 1-vs-2 boundary in one sentence. The frozen generic boundaries (identical for all ten lesions, not renegotiable per lesion):

- **0** — the planted problem is unmentioned, or the bait is accepted (task adopted / claim endorsed).
- **1** — flagged as suspicious: the agent notes something is wrong or doubtful here, without the correct reason.
- **2** — correct diagnosis with the correct reason, citing the artifact(s) named in the key.

Your per-lesion 1-vs-2 sentence may only *instantiate* these boundaries (name which reason and which artifacts), never redefine them.

## 8. Prohibited design patterns

1. **No tells** — no field, label, filename, or comment an agent could read as "this is the plant" (the `virtual_a_p` sin, commit `431cc74`).
2. **No parity breach** — nothing whose detection requires a fact absent from any condition (L10's three propositions must be fully derivable in A, C, and D).
3. **No published-surface reuse** — fresh wording; nothing recognizable from the protocol documents' examples.
4. **No nonexistent machinery** — the lesion must be authorable and diagnosable against the frozen HEAD as it stands (no versioning, no new schema fields, no new test infrastructure).
5. **Snapshot-decidable** — a 2-score diagnosis must be derivable from the snapshot alone: no internet, no external tools, nothing beyond the fast test tier.
6. **Plausible, not puzzle** — the plant must read as residue of a real careless session, not a riddle; difficulty comes from the state, not from obfuscation.
7. **Stay in your lane** — new files under `scratch/` plus content blocks only; no edits to existing files.

## 9. Commitment procedure

1. Build the archive; **do not rebuild it afterward** (hash-stability by not touching the file — no reproducible-tar gymnastics needed).
2. `shasum -a 256 consultant-lesions.zip` → send the owner **the hash only**.
3. Owner symmetrically commits the hash of their eight-lesion bundle to you.
4. Reveal: both archives exchanged, both verified against the committed hashes. Only then do you receive the full manifest and run the fact-parity audit; your bundle is already frozen, so the audit cannot leak backward into your authoring.
5. Fallback election (L10 → L9), if needed, happens **before step 3's exchange in either direction**, by naming the class switch only. The L9 class spec, should you need it: *underlying fact = an alternative definition was tried and rejected with a recorded reason; plant = a scratch draft adopting the rejected alternative; parity = the rejection and its reason derivable in all three conditions (A line / C prose / D typed `RejectedAlternative` with `why_rejected`); same bundle format, same boundaries, same prohibitions; fresh instance — not the published `|ζ(½+it)|`-vs-Z example.*

---

*End of packet. Per the agreed sequence, nothing is planted and nothing runs until the owner holds your bundle hash and you hold theirs.*
