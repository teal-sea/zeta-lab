# MISSION: Hunt R-4166B0 (#109): reproduce and freshness-check the EF zkVM soundness accounting

Source: `teal-sea/zeta-lab` issue #140. Started 2026-08-24.

## The question

The Ethereum Foundation's zkEVM Security Sprint publishes `ethereum/soundcalc`:
an executable checker, its inputs (one TOML per zkVM), its outputs
(`reports/`), pinned versions, and an external deadline (M3, early December
2026: 128 provable bits, proofs at or under 300 KiB, formal recursion
argument).

This is the first instance of this laboratory's reproduction procedure applied
**outside mathematics**. It is a transfer test first and a funnel second, and
the two are kept apart.

Ten units: the eight in `reports/summary.md` plus RISC0 and Miden. Each unit
gets **two independent verdicts, never merged into one**:

1. **REPRODUCTION**, the version they claimed. Does the checked-in TOML follow
   from the vendor's own tree at the version the TOML names?
   `match` / `mismatch` / `no-generator` / `build-required`.
2. **FRESHNESS**, the vendor's current release. Does the same TOML still
   describe it? `unchanged` / `drifted` / `unable-to-regenerate`.
   **Drift is not a security finding and is not reported as one.**

Plus, recorded only: the vendor's own published bits beside soundcalc's figure.

## Scope

Not in this instance: any ceiling or retuning computation. The question is
whether the procedure crosses a domain without the mathematics carrying it.
The transfer measure is **hand interventions per unit**; above about two the
procedure has not crossed yet, and that number is the result.

Nothing here bears on RH (`docs/08`). Nothing here is a statement about a
vendor, a team, or the security of any deployed system: every statement is
scoped to **the artifact at the pinned commit**.

## Disclosure discipline

A REPRODUCTION `mismatch` whose discrepancy could plausibly affect soundness is
**HELD**: named in `RESULTS.md` as held, with no technical detail anywhere in
this repository, and routed to the operator. Ethereum's and Immunefi's programs
forfeit rewards on prior public disclosure. Clean and drift-only units publish
normally, with their reproducers. No agent posts anything to any vendor, to the
EF, to soundcalc issues, or to any bounty program.

```huntspec
id: soundcalc_reproduction
question: Do the ten zkVM soundness figures published by ethereum/soundcalc reproduce to the bit from the vendors' own trees at the versions the TOMLs name, and do the same TOMLs still describe the vendors' current releases?
frontier: summary.md at soundcalc d9078d64c9c3ae15b0931f6d249b2dc073194f15 (2026-07-23), read 2026-08-24 - Airbender 67, Pico 53, OpenVM 100, OpenVM2 100, SP1 100 (6.1.0), Venus 128, ZisK 128, zkDTVM 128; RISC0 and Miden have reports but are absent from the summary
proposed_attack: per unit, regenerate the parameter file from the vendor tree at the named version and at the latest tag, diff both against the checked-in TOML, rerun soundcalc at its pinned commit, compare every regime figure to the published summary
dead_routes:
  - treating a freshness drift as a reproduction failure, they are different questions with different verdicts
  - computing a retuned ceiling for any unit in this instance
required_oracles:
  - soundcalc itself at commit d9078d64c9c3ae15b0931f6d249b2dc073194f15, run unmodified on the checked-in TOMLs and on any regenerated ones
  - the vendors' own generators and source files at the pinned tags where they exist, read or run unmodified
  - byte-level diff of TOML files and exact integer comparison of bit figures per regime
  - the GitHub contents and tags API for tag, commit and file existence at a pinned ref
kill_conditions:
  - soundcalc at the pinned commit does not reproduce its own summary.md from its own TOMLs
  - a regenerated parameter file cannot be produced for a unit by any documented path, that unit is recorded no-generator and not guessed
  - any figure that would require reading a vendor's intent rather than a vendor's file
agents_may:
  - clone, pin and read vendor trees and soundcalc, and record every field
  - read vendor source to locate parameters, citing file and line at the pinned commit
  - count and record their own hand interventions per unit
agents_may_not:
  - post to any vendor, to the EF, to soundcalc issues, or to any bounty program
  - open or merge a pull request in this repository
  - state a security level for any system, only whether the artifact reproduces
  - alter a TOML or a vendor tree except by the vendor's own generator
  - merge the reproduction and freshness verdicts into one
  - publish any technical detail of a held unit
```
