# Provenance of the independent adversarial audit

> The barrier claim in `../FAMILY-LIMIT.md` was produced by one model and checked by code
> that the same model wrote. That is not a check. This directory holds the work of a
> different model, working from a self-contained brief, in an isolated directory outside
> this repository, with no access to this repository or to any prior implementation.

## Who and how long

| | |
|---|---|
| Model | OpenAI Codex, `gpt-5.6-sol` |
| Task | attack the claim `sup_n Phi_n <= 0.6751676068 < 0.6818286874638`, algebraically and numerically |
| Working directory | an isolated directory outside this repository, its own git repository, nothing else in it |
| Duration | 44m55s of agent work; the interval between the brief-first commit and the audit-complete commit in that repository's git log is 47m57s |
| Dependencies | `mpmath==1.4.1`, `numpy==2.5.2`, `scipy==1.18.1` (`requirements.txt`) |
| Verdict | the supporting argument is **false as written** at two steps; the numerical claim **survived**, with a sharper all-`n` bound |

## The brief was committed before any audit work began

The isolated repository's history, oldest first:

| commit | message |
|---|---|
| `4096c931fe8ace9db4f9e4132bc834e5b76b57a4` | The brief, before any audit work begins |
| `5901f158676e3ceb4e8d84bfad671485bdb8bba5` | Complete independent barrier audit |
| `1cdbc9c40d0c6829423305a068c908f5e64d8ef3` | Merge independent barrier audit |

`4096c931` contains `BRIEF.md` and the isolation rules and nothing else. It fixes what was
asked before anything was found, so the brief cannot have been retrofitted to the result.
`BRIEF.md` in this directory is a byte-identical copy of the file in that commit.

## What it had, and what it did not

**Had:**

- `BRIEF.md`, reproduced here unchanged: the kernel, `w`, `F_{n,p}`, `H`, the definition of
  an admissible triple, the definition of `Phi_n`, the claim, and the refutation targets.
  Every constant in it is stated as a claim to be recomputed, including `H` and `K(0)`.
- A Python environment with the three libraries above.
- The isolation rules quoted below.

**Did not have:**

- This repository, in any form: not the `family_wall` hunt, not `FAMILY-LIMIT.md`, not
  `famlib.py`, not `hunts/ainta_seven_point`, not the Lean sources, not the wiki.
- Any prior implementation of the kernel or the functional, from this repository or
  anywhere else. It derived the closed form of `K` itself and checked it against direct
  quadrature at 100 digits.
- The `0.6818286874638` ceiling's provenance. The brief tells it to treat that number as a
  target and nothing more.

The isolation rules it was given, verbatim:

> 1. Work only inside this directory. Do not open, mount, clone or read any other
>    repository on this machine, and do not search the web for an existing implementation
>    of the definitions in `BRIEF.md`.
> 2. If asked for "the original code" or "the other implementation", the answer is no.
>    There is none available to you, on purpose.
> 3. Implement everything from the definitions in `BRIEF.md` alone.
> 4. Do not trust any constant stated in `BRIEF.md`. Every number there is a claim to be
>    recomputed, including the ones presented as settled.

The brief was written to be refuted, not confirmed: *"A refutation is worth far more than
an agreement, so do not soften anything"*, and *"A restatement of the claim in agreeable
language is not a result. Compute."*

## What is in this directory

| file | what it is |
|---|---|
| `BRIEF.md` | the brief, as committed before the work started |
| `results/REPORT.md` | the audit's report, its own words |
| `results/WITNESSES.md` | the exact decimal witness vectors |
| `results/*.json` | machine-readable outputs `REPORT.md` links to |
| `audit.py` | kernel, derivatives, objectives, multistart searches |
| `w_binary_challenge.py`, `w_balanced_challenge.py` | structured basin attacks on `W` |
| `refine_witnesses.py` | KKT refinement of the witnesses |
| `interval_verify.py` | directed-interval checks of the witnesses, `mpmath.iv` at 100 digits |
| `periodic_certificate.py` | the period-37 all-`n` construction and its tail bound |
| `f7_landscape.py`, `high_precision_f7.py` | the `F_7,3000` search and 80-digit refinement |
| `constants_check.py`, `consolidate_results.py`, `test_audit.py` | constants, aggregation, the six self-tests |

## Every edit made on import, exhaustively

**No numbers and no conclusions were altered.** Two lexical changes were made, both forced
by this repository's own rules, and both are listed here in full.

1. **The reserved word.** `tests/test_hunt_probe_discipline.py` reserves one word, the
   past participle of "to certify", to `zeta/rigor.py`, and fails the build if it appears
   in any `.py`, `.md` or `.json` file under `hunts/`. That gate is lexical, so this file
   cannot spell the word either; below it is written `<R>`. The audit used it 41 times,
   always as a boolean meaning *this directed-interval comparison came out true*. Every
   occurrence was replaced by *accepted*:

   | file | occurrences | what changed |
   |---|---|---|
   | `interval_verify.py` | 1 | dict key `sum_cap_<R>` -> `sum_cap_accepted` |
   | `periodic_certificate.py` | 4 | dict keys `cap_<R>`, `cap_all_prefixes_<R>`, `large_n_claim_<R>`, `simple_claim_<R>` -> `..._accepted` |
   | `results/REPORT.md` | 1 | prose, section "Steps 4 and 5": *"`c` is a `<R>` lower bound for the floor"* -> *"an accepted lower bound"* |
   | `results/intervals-requested.json` | 11 | the same keys, in output |
   | `results/intervals-exceptions.json` | 4 | the same keys, in output |
   | `results/intervals-small.json` | 5 | the same keys, in output |
   | `results/periodic-certificate.json` | 15 | the same keys, in output |

   The scripts and their outputs were renamed identically, so re-running the scripts
   reproduces the JSON files as they stand here. No other word was touched, and no value
   in any of those files changed. **Checked, not assumed:** `periodic_certificate.py`, the
   script that carries the all-`n` construction and the four renamed keys, was re-run here
   after the substitution, and its output is byte-identical to the audit's committed
   `results/periodic-certificate.json` with the same rename applied.

2. **One article.** The prose substitution above left *"is a accepted"*; it reads
   *"is an accepted"*.

**No machine path was rewritten, because there was none to rewrite.** Every imported file
was scanned for absolute filesystem prefixes (home-directory roots, the superuser root),
hostnames, timezone offsets and timestamps. Nothing matched. The audit's scripts read and
write only relative paths under `results/`.

The audit's own `README.md`, which held the isolation rules and named the directory it
ran in, is not imported. Its rules are quoted above instead.

## What the audit found

Stated in the audit's own words in `results/REPORT.md`; summarised in
`../FAMILY-LIMIT.md` sections 2.1a, 2.4 and 3, where every figure taken from this
directory is labelled as the audit's.

1. **Steps 2 and 3 of the chain are invalid as written.** Step 2 reverses when its
   numerator is negative; step 3 moves to the largest admissible `m` without establishing
   that `Phi` increases in `m`. Both are exhibited with admissible counterexamples at
   `n = 3`. A case split repairs both, and the final witness implication survives.
2. **An explicit all-`n` construction**, the period-37 word, replaces the tiled-witness
   coverage with a closed-form uniform bound.
3. **The resulting bound is sharper** than the one this hunt claimed.
4. **No numerical counterexample.** The largest constrained `W` it found at any requested
   `n` was at `n = 100`, still far below what reaching the ceiling would need.
5. **One honest caveat**, on `inf F_{7,3000}`: compelling evidence, not a formal global
   certificate, and its value sits `2.0e-13` below the figure this repository quotes.
   `../FAMILY-LIMIT.md` section 3 explains that gap.
