# Blind battery authoring, 2026-08-09 — the frozen corpus

Ten departments authored by ten independent parties against a sealed kit, and
the evidence behind `docs/23` §8. **Read `docs/23` first**; this directory is
the artifact, not the finding.

These are **not importable modules of the `harness` package**. Nothing in the
repository imports them and nothing should. They are frozen inputs to
`score.py`, kept for the same reason `compiler/` keeps its fixtures: the
headline number in `docs/23` §8.2 is a count over these files, and a count
whose inputs were thrown away is an assertion.

## What each party was given

`harness/protocol.py`, `harness/provenance.py`, `harness/README.md`, and
`check.py` (a copy is here) — a runner printing only the integrity grade and
the pass/fail/unknown status of each named check, never the evidence strings
and never `SHAM_MODES`. Each was instructed not to read `harness/integrity.py`,
`harness/shams.py`, any existing department, `docs/20`–`docs/22`, `ROADMAP.md`
or any test. **That instruction is declared, not verified.**

## Two arms

- **party01–party06** were told to reach `CALIBRATED` with a battery that
  measures nothing, and to prove it by exhibiting an `ABSURD_CLAIM` — a
  transparently absurd claim about their own subject — that their own battery
  certifies as `distinguishes`. All six succeeded.
- **party07–party10** were told to author *honest* departments in toy domains
  and to show their battery killing the same kind of absurd claim. All four
  do kill it.

Every module exposes `DEPARTMENT`, `ABSURD_CLAIM` and `ABSURD_CLAIM_TEXT`.

## The contamination, stated up front

The parties ran against the live working tree while `docs/23` §4 was being
implemented in it, so most of them saw the new checks. Per-party accounting is
in `docs/23` §8.0. The contamination runs *against* the parties — they faced a
stricter audit than the baseline — so the 6-of-6 hollowing result is if
anything understated, but only party02 is a clean blind test of
`detector-claim-agreement` and no party is a clean blind test of
`rival-separator-abundance`. Anyone repeating this should pin a copy of the
harness first.

**The set is spent.** Two checks in the current audit were built with these
files in hand (`undeclared-field-symmetry` from party06, and the
`detector-as-claim` plant informed by party02), so re-running `score.py` is a
regression check, not a fresh measurement. A new blind exercise needs new
parties and a pinned harness.

## Reproducing the table

```bash
cd <repo root>
.venv/bin/python harness/blind_authoring_2026_08_09/score.py
```

`score.py` audits each frozen module twice — once under the audit as of
`e7d52b6` (the pre-registration commit, before any of §4 existed) and once
under the current one — and prints the before/after table. It needs a copy of
the old audit on `sys.path` as `integrity_before`; produce one with:

```bash
git show e7d52b6:harness/integrity.py > /tmp/integrity_before.py
```

`SHA256SUMS.txt` pins the ten modules as they were when they were scored. No
blind-authored battery is edited, for any reason, including to make it pass or
fail (`docs/23` §7).
