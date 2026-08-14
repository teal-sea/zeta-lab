# R-03A798 — what the hunt lexical guard actually reads

**Status: settled.** The guard's boundary is a case-insensitive match on one
literal substring. Everything outside that substring passes, including the
four words the repository's own documentation says are banned — and the
"other checks" the question attributes them to do not exist.

Reproduce: `python hunts/r_03a798/probe.py` (~40 s, no mpmath, no network).
Data: `results.json`.

## Method

The guard source is not re-implemented, which would only measure my reading of
it. `tests/test_hunt_probe_discipline.py` is copied **unmodified** into a
sandbox repo root in a tempdir, given a minimal `hunts/README.md` that
satisfies its sibling guards, and run by pytest against one planted specimen
file at a time. The verdict per specimen is the guard's own exit status.

The control that makes the rest readable: with an empty specimen the sandbox
guard is **green** (`specimen_baseline.empty_specimen_guard_green: true`), so
each failure below is caused by the specimen and not by the sandbox.

## Result 1 — the specimen battery

| class | n | detected | what it means |
|---|---|---|---|
| reserved word, plainly | 5 | **5/5** | the guard does its stated job, including inside a sentence disclaiming the word, in a JSON value, and in any casing |
| reserved-word morphology | 3 | **0/3** | *certify*, *certification*, *certifiable* — the same claim, a different inflection, all pass |
| typographic evasion | 5 | **0/5** | hyphen-broken across a line, markdown emphasis mid-word, zero-width space, Cyrillic homoglyph, letter-spaced |
| the four documented bans | 4 | **0/4** | *verified*, *confirmed*, *definitively*, *proves* all pass |
| fresh overclaim vocabulary | 9 | **0/9** | *establishes*, *settles*, *we have shown*, *beyond doubt*, *QED*, *Theorem (this hunt)*, *conclusively demonstrates*, *guarantees*, and a false claim of being kernel-checked by Lean |
| sanctioned vocabulary | 3 | **0/3** | *measured*, *observed*, *consistent with* — correctly silent, no false positives |

The premise handed to this hunt is borne out on its main point and wrong on
its subordinate one. The guard does not detect synonyms — true. They are
"separately banned but by other checks" — **false**; see result 2.

Two gaps the premise did not raise, and which I think matter more:

- **The guard is not even tight on its own word.** Eight of the thirteen
  reserved-word specimens pass. A hunt that writes the claim as *certify* or
  breaks it with a zero-width space is not caught. This is not a proposal to
  chase homoglyphs — an adversary is the wrong model here. But *certify* and
  *certification* are what an honest writer types by accident, and the
  hyphen-break is what a line-wrapping editor does unbidden.
- **The guard cannot tell a claim from a discussion of the rule.** It caught
  `Nothing here is <reserved>; that word belongs to zeta/rigor.py` — a
  sentence enforcing the rule. `CLAUDE.md` states this is deliberate
  ("intent does not exempt a file; the test reads the bytes"), and it has a
  cost this hunt paid: `probe.py` cannot spell the word it studies, so it
  assembles it at runtime and redacts it from `results.json`. Only
  `hunts/README.md` has an exemption. This is a real design choice with a
  real price, not a defect — recorded so the price is visible.

## Result 2 — the census: what enforcement exists

Mechanically, over every `tests/*.py` that both addresses `hunts/` and reads
file text:

| test file | scans hunts/ tree | enforces any of the four bans |
|---|---|---|
| `test_hunt_probe_discipline.py` | yes, whole tree, all `.py/.md/.json` | **no** |
| `test_huntspec.py` | `MISSION.md` fenced blocks only | **no** |
| `test_frontier_math_clean_kill.py` | one hunt subdirectory | **no** |
| `test_zeta23ext_imports.py` | one hunt subdirectory, `.lean` only | **no** |
| `test_harness_referee_department.py` | no (matched on the English word "hunts") | **no** |

`documented_bans_with_no_enforcing_test` in `results.json` is
`["verified", "confirmed", "definitively", "proves"]` — all four. **There is
exactly one whole-tree lexical guard over `hunts/`, and it scans one word.**

*(Correction to the probe's own output: its coarse `scans_whole_hunts_tree`
flag also marks `test_zeta23ext_imports.py`, which in fact rglobs only within
`hunts/frontier_math/zeta23ext`. The flag is a keyword heuristic; the table
above is the hand-checked reading of the same five files.)*

This was already known and written down — `hunts/wide_search/HANDOFF.md`
records "banned by documentation but not by a test" as a session note. What
was not known is that the statement one paragraph above it in `CLAUDE.md` —
"the lexical rules are lexical … the test reads the bytes" — is true of the
reserved word and **not** true of the other four. A rule that reads as
machine-enforced and is not is worse than a rule that reads as review
discipline, because it spends credibility it has not earned.

## Result 3 — the gap is already realised, not hypothetical

Occurrences of the four words in the committed `hunts/` tree today, with the
suite green (this hunt's own directory excluded):

| word | total | use | rule-mention |
|---|---|---|---|
| verified | 13 | 8 | 5 |
| confirmed | 9 | 4 | 5 |
| definitively | 5 | 0 | 5 |
| proves | 6 | 3 | 3 |

The `use` / `rule-mention` split is a **heuristic** (a line naming two or more
of the four is read as quoting the rule), and reading the hits shows it
over-counts: `hunts/frontier_math/zeta23ext/README.md:158` says the *source
paper* proves the lemmas, which is a statement about the literature and
perfectly proper. Do not read "15 uses" as "15 violations" — I did not
adjudicate them one by one, and that is the point. The durable finding is not
a count of offences; it is that **the count is unknown to the tree**, because
nothing measures it. A few are plainly the overclaiming shape the rule exists
to stop, e.g. `hunts/higher_xi/LEAN-FRONTIER.md:292` ("Every intermediate
inequality of both chains was verified") and
`hunts/frontier_math/PROOF-LEDGER.md:645` ("top-3 verified on explicit K=1200
matrices").

## What I chose, and why

**I did not write the missing guard.** Three reasons, in order of weight.
First, it is outside this hunt's scope — `tests/` is not mine to write, and
the brief's kill condition is explicit. Second, the repository's own design
discipline says an abstraction needs a live consumer and the smallest thing
that works; a vocabulary list is a policy decision about what the lab is
willing to fail a build over, and `harness/VERDICT.md` is what happens when
that decision is made by whoever is holding the keyboard. Third, and most
substantively: **a wider word list is not obviously the right fix.** The
false-positive cost is real and this hunt measured a sample of it — the
reserved-word guard already fails sentences that enforce the rule, and
`proves` in "the source paper proves" is correct English that a lexical ban
would break. A ban list scoped to whole-file text is a blunt instrument; the
cheap honest options are (a) extend the list and accept the friction with an
explicit exemption mechanism, or (b) demote the four words in `hunts/README.md`
and `CLAUDE.md` from implied-enforced to stated review discipline. Both are
defensible. Choosing is the operator's, and the choice is named in
`HANDBACK.json`.

**I did not chase evasions as an adversary model.** The homoglyph and
zero-width results are in the table because they were cheap and they bound the
guard's shape, not because I think a hunt will smuggle a claim past it. The
morphology gap (*certify*, *certification*) is the one with an innocent
failure mode, and it is the one worth acting on.

## What I could not settle

- **Whether the four words should be enforced at all.** This is a policy
  question about the lab's tolerance for false positives, not a measurable
  one, and I deliberately did not answer it.
- **How many of the 15 `use`-class hits are genuine overclaims.** Requires
  reading each in context and a judgment about the claim behind it. I read
  four; the rest are listed in `results.json` with file and line for whoever
  does.
- **Whether the guard is bypassable in ways I did not think to try.** The
  battery is 29 specimens I chose. Absence of detection is measured; absence
  of *other* gaps is not, and I make no claim about it.

## A blocker the operator has to clear

Creating `hunts/r_03a798/` makes
`tests/test_hunt_probe_discipline.py::test_every_hunt_directory_is_covered_by_the_case_log`
fail, because every hunt directory must appear in `hunts/README.md`'s case log
and this hunt's brief forbids writing outside `hunts/r_03a798/`. **The failure
is on the branch as landed and I did not hide it.** One line in
`hunts/README.md`'s case log clears it. This is a structural collision between
the case-log guard and the write-scope rule that every scoped hunt brief will
hit, not a mistake in this one — see the first loose thread.

## Loose threads

1. **Every scoped hunt brief collides with the case-log guard.** A brief that
   says "write only inside `hunts/<name>/`" cannot satisfy a guard that
   requires an entry in `hunts/README.md`. Any hunt opened this way lands the
   branch red. *Why it might matter:* it trains agents to either violate their
   write scope or hand back a red suite, and both are bad habits to install.
   *First step:* decide which side gives — either briefs grant a one-line
   exemption for the case log, or the guard learns to accept a hunt directory
   whose `MISSION.md` carries a valid `huntspec` block as self-classifying.
2. **The morphology gap has an innocent failure mode.** *certify* and
   *certification* are what someone writes without meaning to claim anything,
   and they pass. *Why it might matter:* it is the only gap here that a
   careful writer hits by accident rather than by intent. *First step:* change
   the guard's needle from the full word to its six-letter stem and run the
   suite — the corpus scan in `results.json` gives the false-positive count
   before anyone commits to it.
3. **The guard has no exemption mechanism except one hard-coded path.** Only
   `hunts/README.md` may discuss the rule; a hunt that studies the guard must
   obfuscate itself, as this one does. *Why it might matter:* it makes the
   lexical guards themselves the one part of the tree that resists being
   studied in place. *First step:* consider a per-file opt-out marker the
   guard honours, and count how many files would legitimately claim it (right
   now: one).
4. **`hunts/director_run/CLAIMS.md` uses `FORMALLY VERIFIED` as a status
   label.** *Why it might matter:* it is the banned vocabulary functioning as
   a disposition in a claims ledger, which is exactly the load-bearing use the
   rule targets — as opposed to prose about the literature. *First step:* read
   that file's disposition vocabulary against `CLAUDE.md`'s certainty ladder
   and see whether the labels and the rungs agree.
