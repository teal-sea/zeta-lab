# `docs/reviews/` — external review and experiment design

Not part of the numbered reading course in `docs/`. These are working artifacts
about the laboratory rather than about ζ: an outside thesis evaluated against
the tree, and the design for an experiment that has not been run.

> **Nothing here is a result.** No claim in this directory has been through a
> battery, and the E1–E3 documents describe an experiment whose outcome does not
> exist yet.

## The blind pair

`analysis.md` and `consultant-thesis-analysis.md` are two independent
evaluations of the same outside "productization thesis" against the same commit
(`5533896`), written without either seeing the other — the second states
explicitly that it did not open the first. They are kept as a matched pair
because that independence is the only thing that makes either of them evidence
of anything, and it is verifiable from their own chronology rather than from a
declaration. Same reasoning as the frozen corpus in
`harness/blind_authoring_2026_08_09/`.

Redacted before landing: four private sibling repositories and one adjacent
private repository are referred to by role rather than by name or path. The
arguments that relied on them are unchanged and were already flagged in the text
as unverifiable from this tree alone.

## The E1–E3 protocol

Five documents, in dependency order, asking one question: **is a meaningful part
of this lab's operating discipline carried by transferable artifacts and
machinery, or mainly by the original operator's unstated judgment?**

| File | What it is |
|---|---|
| `e1-e3-experiment-protocol.md` | v0 of the protocol — E1 intervention ledger, E2 Lab Rotation Benchmark, E3 staleness/flattening |
| `e1-e3-protocol-revision-2.md` | supersedes the affected sections of v0, answering five objections |
| `e1-e3-protocol-rev-2.1-patch.md` | four specification holes; patch only, Rev. 2 otherwise unchanged |
| `e1-e3-implementation-logistics.md` | sequencing, plus the blind lesion-authoring procedure the contract references but does not define |
| `e2-consultant-blind-authoring-packet.md` | the only material an external lesion author receives before reveal |

The contract is **Rev. 2 + the Rev. 2.1 patch**; read v0 only for the sections
neither of those touches.

**A caution on the packet, and it is the reason the packet is the one file here
that carries a cost.** It names the lesion classes assigned to the external
author. Anyone who reads it before the runs are scored is contaminated as a
scorer, and the protocol's own exclusion rule then applies to them. If E1–E3
is still unrun, treat this directory as read-only for anyone who might score it.

Freezing, if the experiment goes ahead: `harness/preregistration.py` records
digests of the evidence that already existed at freeze time, so contamination
and criteria drift are derived from artifacts rather than read off a
declaration. That is the mechanism these documents should be frozen with, and
the commit that lands them is the timestamp.
